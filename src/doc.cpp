#include "analyze.hpp"
#include "ast_render.hpp"
#include "codegen.hpp"
#include "compiler.hpp"
#include "doc.hpp"
#include "ir.hpp"
#include "parser.hpp"

struct DocGen;
struct DocImport;
struct DocItem;

enum DocItemType {
    DocItemTypeFnDef,
    DocItemTypeVarDecl,
};

struct DocItemFnDef {};

struct DocItemVarDecl {};

struct DocGen {
    CodeGen *g;
    HashMap<Buf *, DocImport *, buf_hash, buf_eql_buf> imports;
    ZigList<Buf *> import_queue;
    size_t import_queue_index;
    Buf *out; // entire doc-IR contents
    bool include_std;
    bool include_builtin;
};

struct DocImport {
    ImportTableEntry *entry;
    HashMap<Buf *, DocItem *, buf_hash, buf_eql_buf> items;
};

struct DocItem {
    Tld *tld;
    Buf *symbol;
    Buf *qualified_name;
    // When searching for a symbol in scope, climb parents and search for relevant decl
    DocItem *parent;
};

static DocImport *doc_import_create(DocGen *d, ImportTableEntry *entry);
static DocItem *doc_item_create(DocGen *d, DocItem *parent, Tld *tld, Buf *prefix);
static void doc_collect_import(DocGen *d, ImportTableEntry *entry);
static void doc_collect_decls(DocGen *d, DocItem *parent, ScopeDecls *decls, Buf *prefix);
static void doc_collect_tld(DocGen *d, DocItem *parent, Tld *tld, Buf *prefix);
static void doc_collect_fn_decl(DocGen *d, DocItem *parent, TldFn *fn, Buf *prefix);
static void doc_collect_test(DocGen *d, DocItem *parent, TldFn *fn, Buf *prefix);
static void doc_collect_var_decl(DocGen *d, DocItem *parent, TldVar *var, Buf *prefix);
static void doc_collect_container(DocGen *d, DocItem *parent, ZigType *t, Buf *prefix);
static void doc_render(DocGen &d);
static void doc_render_import(DocGen &d, DocImport *import);
static void doc_render_fn(DocGen &d, DocItem *item);
static void doc_render_var_decl(DocGen &d, DocItem *item);
static void doc_render_type(DocGen &d, DocItem *item, AstNode *node);
static void doc_render_value(DocGen &d, DocItem *item, AstNode *node);
static void doc_render_expr(DocGen &d, DocItem *item, AstNode *node);
static void doc_render_container_decl(DocGen &d, DocItem *item, AstNodeContainerDecl *container_decl);
static void doc_render_err_set_decl(DocGen &d, AstNodeErrorSetDecl *err_set_decl);
static void doc_render_doc_comment(DocGen &d, Buf* comment);
static void doc_render_link(DocGen &d, DocItem *item, Buf *symbol);
static Buf* symbol_buf_from_node(AstNode *node);
static bool symbol_is_primitive_type(Buf *buf);

void doc_generate(CodeGen *g, Buf *out_dir, Buf *root_src_dir, Buf *root_src_path) {
    codegen_set_out_name(g, buf_create_from_str("doc")); // satisfy init(g) assert
    g->root_package = codegen_create_package(g, buf_ptr(root_src_dir), buf_ptr(root_src_path));
    codegen_analyze_only(g);

    DocGen d;
    d.g = g;
    d.imports.init(1);
    d.out = buf_alloc();
    d.import_queue = {0};
    d.import_queue_index = 0;
    d.include_std = 0; // TODO: Fix "concurrent modification" of hash map
    d.include_builtin = 0; // TODO: Fix "concurrent modification" of hash map

    doc_collect_import(&d, g->root_import);
    doc_render(d);

    // TODO: emit to doc IR file and spawn child process
    fprintf(stdout, "%s\n", buf_ptr(d.out));
}

static DocImport *doc_import_create(DocGen *d, ImportTableEntry *entry) {
    Buf *root_src_dir = &entry->package->root_src_dir;
    if (!d->include_std) {
        if (buf_starts_with_buf(root_src_dir, get_zig_lib_dir()))
                return nullptr;
    }
    if (!d->include_builtin) {
        Buf *builtin_dir = buf_alloc();
        os_path_join(get_stage1_cache_path(), buf_create_from_str("builtin"), builtin_dir);
        bool is_builtin = buf_starts_with_buf(root_src_dir, builtin_dir);
        buf_deinit(builtin_dir);
        if (is_builtin)
            return nullptr;
    }

    DocImport *import = allocate<DocImport>(1);
    auto old = d->imports.put_unique(entry->path, import);
    if (old) {
        free(import);
        return nullptr;
    }
    import->entry = entry;
    import->items.init(1);
    return import;
}

// If item already exists, return null
static DocItem *doc_item_create(DocGen *d, DocItem *parent, Tld *tld, Buf *prefix) {
    DocImport *import;
    auto entry = d->imports.maybe_get(tld->source_node->owner->path);
    if (entry)
        import = entry->value;
    else
        import = doc_import_create(d, tld->source_node->owner);
    assert(import);
    Buf *qualified_name = buf_create_from_buf(prefix);
    Buf *symbol = symbol_buf_from_node(tld->source_node);
    buf_append_buf(qualified_name, symbol);

    DocItem *item = allocate<DocItem>(1);
    auto old = import->items.put_unique(qualified_name, item);
    if (old) {
        buf_deinit(qualified_name);
        free(item);
        return nullptr;
    }
    item->tld = tld;
    item->symbol = symbol;
    item->qualified_name = qualified_name;
    item->parent = parent;

    return item;
}

static void doc_collect_import(DocGen *d, ImportTableEntry *entry) {
    DocImport *import = doc_import_create(d, entry);
    if (import == nullptr) // already collected; prevent infinite loop
        return;
    Buf *prefix = buf_alloc();
    buf_init_from_str(prefix, "");
    doc_collect_decls(d, nullptr, import->entry->decls_scope, prefix);
}

static void doc_collect_decls(DocGen *d, DocItem *parent, ScopeDecls *decls, Buf *prefix) {
    auto iter = decls->decl_table.entry_iterator();
    for (auto entry = iter.next(); entry; entry = iter.next()) {
        doc_collect_tld(d, parent, entry->value, prefix);
    }
}

static void doc_collect_tld(DocGen *d, DocItem *parent, Tld *tld, Buf *prefix) {
    if (tld->visib_mod != VisibModPub)
        return;

start:
    switch (tld->resolution) {
        case TldResolutionUnresolved:
            assert(tld->source_node);
            resolve_top_level_decl(d->g, tld, false, tld->source_node);
            goto start;
        case TldResolutionResolving:
            fprintf(stderr, "TLD is mid-resolution\n");
            zig_unreachable();
        case TldResolutionInvalid:
            fprintf(stderr, "TLD is invalid type\n");
            exit(1);
        case TldResolutionOk:
            break;
    }

    switch (tld->id) {
        case TldIdFn:
            doc_collect_fn_decl(d, parent, (TldFn *)tld, prefix);
            break;
        case TldIdVar:
            doc_collect_var_decl(d, parent, (TldVar *)tld, prefix);
            break;
        case TldIdContainer:
            fprintf(stderr, "TODO: TldContainer -- what do?\n");
            break;
        case TldIdCompTime:
            fprintf(stderr, "TODO: TldCompTime\n");
            break;
    }
}

static void doc_collect_fn_decl(DocGen *d, DocItem *parent, TldFn *fn, Buf *prefix) {
    assert(fn->fn_entry);
    if (fn->fn_entry->is_test)
        return doc_collect_test(d, parent, fn, prefix);
    doc_item_create(d, parent, &fn->base, prefix);
}

static void doc_collect_test(DocGen *d, DocItem *parent, TldFn *fn, Buf *prefix) {
    // TODO: I think this is never reached; tests aren't pub?
    fprintf(stderr, "TODO: collect test (%s)\n", buf_ptr(fn->base.name));
}

static void doc_collect_var_decl(DocGen *d, DocItem *parent, TldVar *var, Buf *prefix) {
    if (!var->var)
        return;
    DocItem *item = doc_item_create(d, parent, &var->base, prefix);
    ConstExprValue *value = var->var->value;
    switch (value->type->id) {
        case ZigTypeIdNamespace:
            doc_collect_import(d, value->data.x_import);
            return;
        case ZigTypeIdMetaType:
            {
                Buf *ns = buf_create_from_buf(prefix);
                buf_append_buf(ns, &var->var->name);
                buf_append_char(ns, '.');
                doc_collect_container(d, item, value->data.x_type, ns);
            }
            return;
        case ZigTypeIdInvalid:
            fprintf(stderr, "WARN: skipping invalid var decl type at %s:%s%s\n",
                buf_ptr(var->base.import->path),
                buf_ptr(prefix),
                buf_ptr(&var->var->name));
            return;
        default:
            // fprintf(stderr, "INFO: skipping other zig type: %s\n", buf_ptr(&value->type->name));
            return;
    }
}

static void doc_collect_container(DocGen *d, DocItem *parent, ZigType *t, Buf *prefix) {
    ScopeDecls *decls = nullptr;
    switch (t->id) {
        case ZigTypeIdStruct:
            decls = t->data.structure.decls_scope;
            break;
        case ZigTypeIdEnum:
            decls = t->data.enumeration.decls_scope;
            break;
        case ZigTypeIdUnion:
            decls = t->data.unionation.decls_scope;
            break;
        // case ZigTypeIdNamespace: // TODO: I don't think this is needed
        default:
            break;
    }
    if (decls != nullptr)
        doc_collect_decls(d, parent, decls, prefix);
}

static void doc_render(DocGen &d) {
    auto import_iter = d.imports.entry_iterator();
    for (auto import = import_iter.next(); import; import = import_iter.next()) {
        doc_render_import(d, import->value);
    }
}

static void doc_render_import(DocGen &d, DocImport *import) {
    buf_append_char(d.out, '^');
    buf_append_buf(d.out, import->entry->path);
    buf_append_char(d.out, '\n');

    assert(import->entry->root->type = NodeTypeContainerDecl);
    Buf *file_comment = import->entry->root->data.container_decl.doc_comment;
    doc_render_doc_comment(d, file_comment);

    auto item_iter = import->items.entry_iterator();
    for (auto item = item_iter.next(); item; item = item_iter.next()) {
        Tld *tld = item->value->tld;
        switch (tld->id) {
            case TldIdFn:
                doc_render_fn(d, item->value);
                break;
            case TldIdVar:
                doc_render_var_decl(d, item->value);
                break;
            default:
                break;
        }
    }
    buf_append_char(d.out, '<');
}

static void doc_render_fn(DocGen &d, DocItem *item) {
    assert(item->symbol);

    buf_append_char(d.out, 'F');
    buf_append_buf(d.out, item->symbol);
    buf_append_char(d.out, '\n');

    assert(item->tld->source_node->type == NodeTypeFnProto);
    AstNodeFnProto fn_proto = item->tld->source_node->data.fn_proto;
    doc_render_doc_comment(d, fn_proto.fn_def_node->data.fn_def.doc_comment);

    for (size_t i = 0; i < fn_proto.params.length; i++) {
        AstNode *param = fn_proto.params.at(i);
        assert(param->type == NodeTypeParamDecl);

        buf_append_char(d.out, ',');
        if (param->data.param_decl.name != nullptr) {
            buf_append_char(d.out, 'n');
            buf_append_buf(d.out, param->data.param_decl.name);
            buf_append_char(d.out, '\n');
        }
        // param->data.param_decl.is_noalias
        // param->data.param_decl.is_inline // TODO: WAT?
        if (param->data.param_decl.is_var_args)
            buf_append_char(d.out, '_');
        else if (param->data.param_decl.name)
            doc_render_type(d, item, param->data.param_decl.type);
        buf_append_char(d.out, '<');
    }
    buf_append_char(d.out, 'r');
    doc_render_type(d, item, fn_proto.return_type);
    buf_append_char(d.out, '<');
}

static void doc_render_var_decl(DocGen &d, DocItem *item) {
    AstNodeVariableDeclaration *var_decl = &item->tld->source_node->data.variable_declaration;
    assert(var_decl->symbol);

    buf_append_char(d.out, '=');
    buf_append_buf(d.out, var_decl->symbol);
    buf_append_char(d.out, '\n');

    doc_render_doc_comment(d, var_decl->doc_comment);
    if (var_decl->is_const)
        buf_append_char(d.out, 'C');
    if (var_decl->is_comptime)
        buf_append_char(d.out, 'T');
    if (var_decl->is_export)
        buf_append_char(d.out, 'P');
    if (var_decl->type != nullptr)
        doc_render_type(d, item, var_decl->type); // explicit LHS type annotation
    if (var_decl->expr != nullptr)
        doc_render_value(d, item, var_decl->expr); // type inferred from RHS expression
    buf_append_char(d.out, '<');
}

static void doc_render_type(DocGen &d, DocItem *item, AstNode *node) {
    if (node == nullptr)
        return;
    buf_append_char(d.out, 't');
    doc_render_expr(d, item, node);
    buf_append_char(d.out, '<');
}

static void doc_render_value(DocGen &d, DocItem *item, AstNode *node) {
    if (node == nullptr)
        return;
    buf_append_char(d.out, 'v');
    doc_render_expr(d, item, node);
    buf_append_char(d.out, '<');
}

static void doc_render_expr(DocGen &d, DocItem *item, AstNode *node) {
    if (node == nullptr)
        return;
    switch (node->type) {
        case NodeTypeArrayType:
            buf_append_char(d.out, '[');
            if (node->data.array_type.is_const)
                buf_append_char(d.out, 'C');
            if (node->data.array_type.is_volatile)
                buf_append_char(d.out, 'V');
            if (node->data.array_type.size != nullptr) {
                buf_append_char(d.out, 's');
                doc_render_expr(d, item, node->data.array_type.size);
            }
            doc_render_expr(d, item, node->data.array_type.child_type);
            break;
        case NodeTypePointerType:
            buf_append_char(d.out, '*');
            if (node->data.pointer_type.is_const)
                buf_append_char(d.out, 'C');
            if (node->data.pointer_type.is_volatile)
                buf_append_char(d.out, 'V');
            doc_render_expr(d, item, node->data.pointer_type.op_expr);
            break;
        case NodeTypePrefixOpExpr:
            switch (node->data.prefix_op_expr.prefix_op) {
                case PrefixOpOptional:
                    buf_append_char(d.out, '?');
                    break;
                case PrefixOpAddrOf:
                    buf_append_char(d.out, '&');
                    break;
                default:
                    fprintf(stderr, "TODO: prefix op %d\n", node->data.prefix_op_expr.prefix_op);
                    break;
            }
            doc_render_expr(d, item, node->data.prefix_op_expr.primary_expr);
            break;
        case NodeTypeSymbol:
            buf_append_char(d.out, '$');
            buf_append_buf(d.out, node->data.symbol_expr.symbol);
            buf_append_char(d.out, '\n');
            doc_render_link(d, item, node->data.symbol_expr.symbol);
            break;
        case NodeTypeFloatLiteral:
            buf_append_char(d.out, 'y');
            {
                // TODO: this is so fallable I can't even
                char buf[50] = {0};
                snprintf(buf, 50, "%lf", bigfloat_to_f64(node->data.float_literal.bigfloat));
                buf_append_str(d.out, buf);
            }
            buf_append_char(d.out, '\n');
            break;
        case NodeTypeIntLiteral:
            buf_append_char(d.out, 'i');
            {
                // TODO: you're so vain I bet you think this unsafe way of encoding an integer is about you
                char buf[50] = {0};
                snprintf(buf, 50, "%ld", bigint_as_signed(node->data.int_literal.bigint));
                buf_append_str(d.out, buf);
            }
            buf_append_char(d.out, '\n');
            break;
        case NodeTypeStringLiteral:
            buf_append_char(d.out, node->data.string_literal.c ? 'c' : '"');
            buf_append_buf(d.out, node->data.string_literal.buf);
            buf_append_char(d.out, '\n');
            break;
        case NodeTypeCharLiteral:
            buf_append_char(d.out, '\'');
            buf_append_char(d.out, node->data.char_literal.value);
            break;
        case NodeTypeContainerDecl:
            doc_render_container_decl(d, item, &node->data.container_decl);
            break;
        case NodeTypeErrorSetDecl:
            doc_render_err_set_decl(d, &node->data.err_set_decl);
            break;
        case NodeTypeBoolLiteral:
            buf_append_char(d.out, node->data.bool_literal.value ? 'B' : 'b');
            break;
        case NodeTypeGroupedExpr:
            buf_append_char(d.out, '(');
            doc_render_expr(d, item, node->data.grouped_expr);
            buf_append_char(d.out, '<');
            break;
        case NodeTypeFnCallExpr:
            {
                // AstNodeFnCallExpr fn_call = node->data.fn_call_expr;
                // if (fn_call.is_builtin) {
                //     AstNodeFnProto fn_proto = fn_call.fn_ref_expr->data.fn_proto;
                //     if (buf_eql_str(fn_proto.name, "import")) {
                //         // Buf *path = resolve_string_value(fn_proto.params.at(0));
                //         // d.
                //     }
                // }
            }
            // node->data.fn_call_expr.fn_ref_expr
            // node->data.fn_call_expr.params
            // TODO: handle @import
        case NodeTypeFieldAccessExpr:
            // node->data.field_access_expr.struct_expr
            // node->data.field_access_expr.field_name
        case NodeTypeBinOpExpr:
            // node->data.bin_op_expr.bin_op
            // node->data.bin_op_expr.op1
            // node->data.bin_op_expr.op2
        case NodeTypeContainerInitExpr:
            // node->data.container_init_expr.entries
            // node->data.container_init_expr.kind
            // node->data.container_init_expr.type
        default:
            buf_append_char(d.out, 'Z');
            fprintf(stderr, "TODO: type %s\n", node_type_str(node->type));
            break;
    }
}

static void doc_render_container_decl(DocGen &d, DocItem *item, AstNodeContainerDecl *container_decl) {
    buf_append_char(d.out, '{');
    switch (container_decl->kind) {
        case ContainerKindEnum:
            buf_append_char(d.out, 'E');
            break;
        case ContainerKindStruct:
            buf_append_char(d.out, 'S');
            break;
        case ContainerKindUnion:
            buf_append_char(d.out, 'U');
            break;
        default:
            zig_unreachable();
            break;
    }
    for (size_t i = 0; i < container_decl->fields.length; i++) {
        AstNode *field = container_decl->fields.at(i);
        buf_append_char(d.out, ',');
        buf_append_char(d.out, 'n');
        buf_append_buf(d.out, field->data.struct_field.name);
        buf_append_char(d.out, '\n');
        doc_render_type(d, item, field->data.struct_field.type);
        // field->data.struct_field.value // TODO when default values are supported
        buf_append_char(d.out, '<');
    }
    buf_append_char(d.out, '<');
}

static void doc_render_err_set_decl(DocGen &d, AstNodeErrorSetDecl *err_set_decl) {
    buf_append_char(d.out, '{');
    buf_append_char(d.out, '%');
    for (size_t i = 0; i < err_set_decl->decls.length; i++) {
        buf_append_char(d.out, ',');
        buf_append_buf(d.out, err_set_decl->decls.at(i)->data.symbol_expr.symbol);
        buf_append_char(d.out, '\n');
    }
    buf_append_char(d.out, '<');
}

static void doc_render_doc_comment(DocGen &d, Buf* comment) {
    if (comment == nullptr)
        return;
    buf_append_char(d.out, '#');
    for (size_t i = 0; i < comment->list.length; i++) {
        char c = comment->list.at(i);
        switch (c) {
            case '\0':
                goto done;
            case '\\':
                buf_append_str(d.out, "\\\\");
                continue;
            case '\n':
                buf_append_str(d.out, "\\n");
                continue;
            default:
                buf_append_char(d.out, c);
                continue;
        }
    }
done:
    buf_append_char(d.out, '\n');
}

// TODO:
// 1. This only works for bare symbols, not field accesses. Field access will have to check if
//    indexing into structure or namespace
// 2. This doesn't work for "use"d symbols.
static void doc_render_link(DocGen &d, DocItem *item, Buf *symbol) {
    if (symbol_is_primitive_type(symbol))
        return;
    // parent->tld->parent_scope->scope_decls->decl_table
    while (item) {
        assert(item->tld->parent_scope->id == ScopeIdDecls);
        ScopeDecls *decls = (ScopeDecls*)item->tld->parent_scope;
        auto iter = decls->decl_table.entry_iterator();
        for (auto entry = iter.next(); entry; entry = iter.next()) {
            Tld *tld = entry->value;
            if (buf_eql_buf(tld->name, symbol)) {
                buf_append_char(d.out, 'L');
                buf_append_buf(d.out, tld->import->path);
                buf_append_char(d.out, ':');
                buf_append_buf(d.out, item->qualified_name);
                buf_append_char(d.out, '\n');
                return;
            }
        }
        item = item->parent;
    }
}

static Buf* symbol_buf_from_node(AstNode *node) {
    switch (node->type) {
        case NodeTypeFnProto:
            return node->data.fn_proto.name;
        case NodeTypeVariableDeclaration:
            return node->data.variable_declaration.symbol;
        case NodeTypeContainerDecl: // top level
            return buf_create_from_str("(top level)");
        default:
            fprintf(stderr, "node type was %d\n", node->type);
            zig_unreachable();
    }
}

static bool symbol_is_primitive_type(Buf *buf) {
    if (buf->list.length < 2) return false;

    if (buf->list.at(0) == 'u' || buf->list.at(0) == 'i') {
        for (size_t i = 1; i < buf->list.length; i++) {
            char c = buf->list.at(i);
            if (!c) break;
            if (c < '0' || c > '9') goto reserved;
        }
        return true;
    }

reserved:
    // TODO: look up in a map
    return buf_eql_str(buf, "type")
        || buf_eql_str(buf, "noreturn")
        || buf_eql_str(buf, "void")
        || buf_eql_str(buf, "bool")
        || buf_eql_str(buf, "isize")
        || buf_eql_str(buf, "usize")
        || buf_eql_str(buf, "f16")
        || buf_eql_str(buf, "f32")
        || buf_eql_str(buf, "f64")
        || buf_eql_str(buf, "f128")
        || buf_eql_str(buf, "comptime_int")
        || buf_eql_str(buf, "comptime_float")
        || buf_eql_str(buf, "c_short")
        || buf_eql_str(buf, "c_ushort")
        || buf_eql_str(buf, "c_int")
        || buf_eql_str(buf, "c_uint")
        || buf_eql_str(buf, "c_long")
        || buf_eql_str(buf, "c_ulong")
        || buf_eql_str(buf, "c_longlong")
        || buf_eql_str(buf, "c_ulonglong")
        || buf_eql_str(buf, "c_longdouble")
        || buf_eql_str(buf, "c_void");
}
