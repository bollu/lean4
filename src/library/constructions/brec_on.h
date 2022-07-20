/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Given an inductive datatype \c n in \c env, add
    <tt>n.below</tt> auxiliary construction for <tt>n.brec_on</t>
    (aka below recursion on) to the environment.
*/
environment old_mk_below(environment const & env, name const & n);
environment old_mk_ibelow(environment const & env, name const & n);

environment old_mk_brec_on(environment const & env, name const & n);
environment old_mk_binduction_on(environment const & env, name const & n);

environment mk_below(uint64_t maxHeartbeats, environment const & env, name const & n);
environment mk_ibelow(uint64_t maxHeartbeats, environment const & env, name const & n);

environment mk_brec_on(uint64_t maxHeartbeats, environment const & env, name const & n);
environment mk_binduction_on(uint64_t maxHeartbeats, environment const & env, name const & n);
}
