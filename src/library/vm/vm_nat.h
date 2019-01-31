/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <limits>
#include "library/vm/vm.h"

namespace lean {
inline optional<unsigned> try_to_unsigned(vm_obj const & o) { return is_scalar(o) ? some(unbox(o)) : optional<unsigned>(); }

void initialize_vm_nat();
void finalize_vm_nat();
}
