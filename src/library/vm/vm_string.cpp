/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/interrupt.h"
#include "runtime/utf8.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_option.h"

namespace lean {

object * vm_string_push(object * s, object * c) { return string_push(s, unbox(c)); }
object * vm_string_iterator_curr(b_obj_arg it) { return box(string_iterator_curr(it)); }
obj_res vm_string_iterator_set_curr(obj_arg it, obj_arg c) { return string_iterator_set_curr(it, unbox(c)); }
obj_res vm_string_iterator_has_next(b_obj_arg it) { return box(string_iterator_has_next(it)); }
obj_res vm_string_iterator_has_prev(b_obj_arg it) { return box(string_iterator_has_prev(it)); }

void initialize_vm_string() {
    DECLARE_VM_BUILTIN(name({"string", "mk"}),             string_mk);
    DECLARE_VM_BUILTIN(name({"string", "data"}),           string_data);

    DECLARE_VM_BUILTIN(name({"string", "length"}),            string_length);
    DECLARE_VM_BUILTIN(name({"string", "push"}),              vm_string_push);
    DECLARE_VM_BUILTIN(name({"string", "append"}),            string_append);
    DECLARE_VM_BUILTIN(name({"string", "mk_iterator"}),       string_mk_iterator);
    DECLARE_VM_BUILTIN(name({"string", "dec_eq"}),            string_dec_eq);
    DECLARE_VM_BUILTIN(name({"string", "dec_lt"}),            string_dec_lt);

    DECLARE_VM_BUILTIN(name({"string", "iterator", "curr"}),           vm_string_iterator_curr);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "set_curr"}),       vm_string_iterator_set_curr);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "next"}),           string_iterator_next);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "prev"}),           string_iterator_prev);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "has_next"}),       vm_string_iterator_has_next);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "has_prev"}),       vm_string_iterator_has_prev);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "insert"}),         string_iterator_insert);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "remove"}),         string_iterator_remove);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "remaining"}),      string_iterator_remaining);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "offset"}),         string_iterator_offset);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "to_string"}),      string_iterator_to_string);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "to_end"}),         string_iterator_to_end);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "remaining_to_string"}), string_iterator_remaining_to_string);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "prev_to_string"}), string_iterator_prev_to_string);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "extract"}),        string_iterator_extract);

    DECLARE_VM_BUILTIN(name({"string", "iterator", "mk"}),              string_iterator_mk);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "fst"}),             string_iterator_fst);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "snd"}),             string_iterator_snd);
}

void finalize_vm_string() {
}
}
