/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {

void initialize_vm_nat() {
    DECLARE_VM_BUILTIN(name({"nat", "add"}),        nat_add);
    DECLARE_VM_BUILTIN(name({"nat", "mul"}),        nat_mul);
    DECLARE_VM_BUILTIN(name({"nat", "sub"}),        nat_sub);
    DECLARE_VM_BUILTIN(name({"nat", "div"}),        nat_div);
    DECLARE_VM_BUILTIN(name({"nat", "mod"}),        nat_mod);
    DECLARE_VM_BUILTIN(name({"nat", "dec_eq"}),     nat_dec_eq);
    DECLARE_VM_BUILTIN(name({"nat", "dec_le"}),     nat_dec_le);
    DECLARE_VM_BUILTIN(name({"nat", "dec_lt"}),     nat_dec_lt);
}

void finalize_vm_nat() {
}
}
