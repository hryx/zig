/*
 * Copyright (c) 2015 Andrew Kelley
 *
 * This file is part of zig, which is MIT licensed.
 * See http://opensource.org/licenses/MIT
 */

#ifndef ZIG_AST_RENDER_HPP
#define ZIG_AST_RENDER_HPP

#include "all_types.hpp"
#include "parser.hpp"

#include <stdio.h>

void ast_print(FILE *f, AstNode *node, int indent);

void ast_render(CodeGen *codegen, FILE *f, AstNode *node, int indent_size);

const char *container_string(ContainerKind kind);
const char *node_type_str(NodeType node_type);

#endif
