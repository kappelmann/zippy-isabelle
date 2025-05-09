(*  Title:    Zippy/enumerable_util.ML
    Auor:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_ParaT_nargs "ENUMERABLE_UTIL"\<close> =
sig
  structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>

  val enum : (@{ParaT_args} 'zs, 'z) Co.C.cat -> (@{ParaT_args} 'z, 'z) Co.C.cat ->
    (@{ParaT_args} 'zs, (@{ParaT_args} 'a, 'z) Co.coroutine) Co.C.cat
  val list : (@{ParaT_args} 'zs, 'z) Co.C.cat -> (@{ParaT_args} 'z, 'z) Co.C.cat ->
    (@{ParaT_args} 'zs, 'z list) Co.C.cat
end

functor \<^eval>\<open>sfx_ParaT_nargs "Enumerable_Util"\<close>(
    Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "ENUMERABLE_UTIL"\<close> =
struct

structure Co = Co

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Co.C)
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Arrow"\<close>(Co.AA) open SC A
in
fun enum first next = first >>> arr (fn x => Co.cons (K x) (Co.enum next x))
fun list first next = enum first next >>> arr Co.list_of >>> Co.AA.app' ()
end

end