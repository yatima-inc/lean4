/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "library/vm/vm.h"

namespace lean {
void initialize_vm_string();
void finalize_vm_string();
}
