/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"

namespace lean {
void initialize_vm_int() {
    DECLARE_VM_BUILTIN(name({"int", "of_nat"}),           nat2int);
    DECLARE_VM_BUILTIN(name({"int", "nat_abs"}),          nat_abs);
    DECLARE_VM_BUILTIN(name({"int", "neg_succ_of_nat"}),  int_neg_succ_of_nat);
    DECLARE_VM_BUILTIN(name({"int", "add"}),              int_add);
    DECLARE_VM_BUILTIN(name({"int", "sub"}),              int_sub);
    DECLARE_VM_BUILTIN(name({"int", "mul"}),              int_mul);
    DECLARE_VM_BUILTIN(name({"int", "neg"}),              int_neg);
    DECLARE_VM_BUILTIN(name({"int", "quot"}),             int_div);
    DECLARE_VM_BUILTIN(name({"int", "rem"}),              int_rem);
    DECLARE_VM_BUILTIN(name({"int", "dec_eq"}),           int_dec_eq);
    DECLARE_VM_BUILTIN(name({"int", "dec_le"}),           int_dec_le);
    DECLARE_VM_BUILTIN(name({"int", "dec_lt"}),           int_dec_lt);
}

void finalize_vm_int() {
}
}
