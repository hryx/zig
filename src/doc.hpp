#ifndef ZIG_DOC_HPP
#define ZIG_DOC_HPP

#include "all_types.hpp"

void doc_generate(CodeGen *g, Buf *out_dir, Buf *root_src_dir, Buf *root_src_path);
void comment_parse(Buf *src, Buf *dst);

#endif
