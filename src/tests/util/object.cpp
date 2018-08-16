/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
// #include "util/test.h"
#include "runtime/debug.h"
#include "runtime/stackinfo.h"
#include "util/object_ref.h"
#include "util/init_module.h"
#include "util/timeit.h"
using namespace lean;

object * f(object *) {
    std::cout << "executing f...\n";
    return box(10);
}

object_ref mk_thunk_ref(object_ref const & c) {
    inc(c.raw());
    return object_ref(mk_thunk(c.raw()));
}

static void tst1() {
    object_ref c(alloc_closure(f, 1, 0));
    object_ref t = mk_thunk_ref(c);
    object * r1 = thunk_get(t.raw());
    object * r2 = thunk_get(t.raw());
    std::cout << "thunk value: " << unbox(r1) << "\n";
    std::cout << "thunk value: " << unbox(r2) << "\n";
}

static unsigned g_g_counter = 0;

object * g(object *) {
    g_g_counter++;
    return box(g_g_counter);
}

static void tst2() {
    object_ref c(alloc_closure(g, 1, 0));
    object * r1 = apply_1(c.raw(), box(0));
    object * r2 = apply_1(c.raw(), box(0));
    lean_assert(unbox(r1) == 1);
    lean_assert(unbox(r2) == 2);
    object_ref t = mk_thunk_ref(c);
    object * r3 = thunk_get(t.raw());
    object * r4 = thunk_get(t.raw());
    lean_assert(unbox(r3) == 3);
    lean_assert(unbox(r4) == 3);
}

static unsigned g_h_counter = 0;

object * h(object *) {
    g_h_counter++;
    return box(0);
}

/* Make sure box(0) is not mistaken by cached value has not been initialized yet.

   The thunk implementation relies on the fact that nullptr is not a scalar nor a valid
   Lean object. */
static void tst3() {
    object_ref c(alloc_closure(h, 1, 0));
    object_ref t = mk_thunk_ref(c);
    lean_assert(g_h_counter == 0);
    object * r3 = thunk_get(t.raw());
    lean_assert(g_h_counter == 1);
    object * r4 = thunk_get(t.raw());
    lean_assert(g_h_counter == 1);
    lean_assert(unbox(r3) == 0);
    lean_assert(unbox(r4) == 0);
}

object * r(object *) {
    return mk_string("hello world");
}

static void tst4() {
    object_ref c(alloc_closure(r, 1, 0));
    object_ref t = mk_thunk_ref(c);
    object * r3  = thunk_get(t.raw());
    object * r4  = thunk_get(t.raw());
    lean_assert(string_eq(r3, "hello world"));
    lean_assert(string_eq(r4, "hello world"));
}

inline void array_set_obj1(object * o, size_t i, object * v) {
    if (LEAN_LIKELY(!is_shared(o))) {
        obj_set_data(o, sizeof(array_object) + sizeof(object*)*i, v); // NOLINT
    } else {
    }
}

static void tst6(unsigned n, unsigned sz) {
    timeit timer(std::cout, "tst6");
    object * a = alloc_array(sz, sz);
    for (unsigned i = 0; i < n; i++) {
        for (unsigned j = 0; j < sz; j++) {
            array_set_obj1(a, j, box(j));
        }
    }
    dec_ref(a);
}

static object * map1(object * l) {
    if (obj_tag(l) == 0) {
        return l;
    } else {
        object * h     = cnstr_obj(l, 0);
        object * t     = cnstr_obj(l, 1);
        object * new_h = box(unbox(h) + 1);
        object * new_t = map1(t);
        object * r     = alloc_cnstr(1, 2, 0);
        cnstr_set_obj(r, 0, new_h);
        cnstr_set_obj(r, 1, new_t);
        return r;
    }
}

static object * map2(object * l) {
    if (obj_tag(l) == 0) {
        return l;
    } else {
        object * h     = cnstr_obj(l, 0);
        object * t     = cnstr_obj(l, 1);
        inc(t);
        dec(l);
        object * new_h = box(unbox(h) + 1);
        object * new_t = map2(t);
        object * r     = alloc_cnstr(1, 2, 0);
        cnstr_set_obj(r, 0, new_h);
        cnstr_set_obj(r, 1, new_t);
        return r;
    }
}

static object * map3(object * l) {
    if (obj_tag(l) == 0) {
        return l;
    } else {
        object * h = cnstr_obj(l, 0);
        object * t = cnstr_obj(l, 1);
        bool s = is_shared(l);
        if (s) {
            inc(t);
            dec(l);
        }
        object * new_h = box(unbox(h) + 1);
        object * new_t = map3(t);
        object * r;
        if (s) {
            std::cout << "FUCK\n";
            r = alloc_cnstr(1, 2, 0);
        } else {
            r = l;
        }
        cnstr_set_obj(r, 0, new_h);
        cnstr_set_obj(r, 1, new_t);
        return r;
    }
}

static object * mk_list(unsigned n) {
    object * r = box(0);
    while (n > 0) {
        object * h = box(n);
        object * new_r = alloc_cnstr(1, 2, 0);
        cnstr_set_obj(new_r, 0, h);
        cnstr_set_obj(new_r, 1, r);
        r = new_r;
        --n;
    }
    return r;
}

static void tst7(unsigned n) {
    timeit timer(std::cout, "tst7");
    object * l = mk_list(10000);
    for (unsigned i = 0; i < n; i++) {
        object * l2 = map3(l);
        // dec(l);
        l = l2;
    }
    dec(l);
}

static void tst8(unsigned n) {
    timeit timer(std::cout, "tst7");
    object * l = mk_list(100000);
    for (unsigned i = 0; i < n; i++) {
        object * l2 = map3(l);
        l = l2;
    }
    dec(l);
}


int main() {
    save_stack_info();
    initialize_util_module();
    // tst1();
    // tst2();
    // tst3();
    // tst4();
    // tst6(1000000, 10000);
    tst8(1000);
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
