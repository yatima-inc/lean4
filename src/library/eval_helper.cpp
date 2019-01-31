/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/eval_helper.h"
#include "library/io_state.h"
#include "runtime/io.h"

namespace lean {

eval_helper::eval_helper(environment const & env, options const & opts, name const & fn) :
        m_env(env), m_opts(opts), m_tc(env, opts, transparency_mode::None),
        m_vms(env, opts), m_prof(m_vms, opts), m_fn(fn) {
    auto d = env.get(m_fn);
    m_ty = m_tc.whnf(d.get_type());

    if (auto vm_decl = m_vms.get_decl(m_fn)) {
        m_arity = vm_decl->get_arity();
    } else {
        throw exception(sstream() << "no vm declaration found for " << m_fn);
    }
}

object_ref eval_helper::invoke_fn() {
    /* We use `scope_vm_state` to set thread local g_vm_state which is used
       to collect performance numbers when profiling. */
    scope_vm_state scope(m_vms);
    unsigned arity = m_vms.get_decl(m_fn)->get_arity();
    if (arity > m_args.size()) {
        throw exception(sstream() << "cannot evaluate function: " << m_args.size()
                                  << " arguments given but expected " << arity);
    }
    std::reverse(m_args.begin(), m_args.end());
    // TODO(Sebastian): what if the return value is borrowed?
    return object_ref(m_vms.invoke(m_fn, m_args.size(), m_args.data()));
}

optional<object_ref> eval_helper::try_exec_io() {
    if (is_app_of(m_ty, get_io_name(), 1)) {
        m_args.push_back(mk_vm_simple(0)); // "world state"
        auto r = invoke_fn();
        /* TODO? if (auto error = is_ioe_error(r)) {
            throw exception(io_error_to_string(*error));
        } else if (auto result = is_ioe_result(r)) {
            return result;
        } else {
            throw exception("unexpected vm result of io expression");
        }*/
        return some(object_ref(get_io_result(r.raw()), true));
    }
    return optional<object_ref>();
}

optional<object_ref> eval_helper::try_exec() {
    if (auto res = try_exec_io()) return res;
    return optional<object_ref>();
}

}
