(*  Title:    Zippy/enumerable_util.ML
    Auor:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_ParaT_nargs "ENUMERABLE_UTIL"\<close> =
sig
  structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>

  val enum : (@{ParaT_args} 'zs, 'z) CO.C.cat -> (@{ParaT_args} 'z, 'z) CO.C.cat ->
    (@{ParaT_args} 'zs, (@{ParaT_args} 'a, 'z) CO.coroutine) CO.C.cat
  val list : (@{ParaT_args} 'zs, 'z) CO.C.cat -> (@{ParaT_args} 'z, 'z) CO.C.cat ->
    (@{ParaT_args} 'zs, 'z list) CO.C.cat
end

functor \<^eval>\<open>sfx_ParaT_nargs "Enumerable_Util"\<close>(
    CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "ENUMERABLE_UTIL"\<close> =
struct

structure CO = CO

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(CO.C)
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Arrow"\<close>(CO.AA) open SC A
in
fun enum first next = first >>> arr (fn x => CO.cons (K x) (CO.enum next x))
fun list first next = enum first next >>> arr CO.list_of >>> CO.AA.app' ()
end

end