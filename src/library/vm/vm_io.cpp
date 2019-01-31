/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <vector>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include "util/name.h"
#include "runtime/io.h"
#include "library/vm/vm.h"

namespace lean {
obj_res vm_io_prim_handle_mk(b_obj_arg s, obj_arg mode, obj_arg bin, obj_arg w) {
    return io_prim_handle_mk(s, unbox(mode), unbox(bin), w);
}

void initialize_vm_io() {
    DECLARE_VM_BUILTIN(name({"io", "prim", "put_str"}), io_prim_put_str);
    DECLARE_VM_BUILTIN(name({"io", "prim", "get_line"}), io_prim_get_line);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "mk"}), vm_io_prim_handle_mk);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "is_eof"}), io_prim_handle_is_eof);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "flush"}), io_prim_handle_flush);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "close"}), io_prim_handle_close);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "get_line"}), io_prim_handle_get_line);
}

void finalize_vm_io() {
}
}
