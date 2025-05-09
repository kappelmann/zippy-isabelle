(*  Title:      Zippy/zippy_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PRESULTS_MIXIN =
sig
  include ZIPPY_PRESULTS_MIXIN_BASE

  val empty_aco : @{ParaT_args encl = "(" ")"} Co.AE.exn -> (@{ParaT_args} 'a, 'b, 'c) Co.acoroutine
  val empty_presults : @{ParaT_args encl = "(" ")"} Co.AE.exn -> @{AllT_args} presults

  val run_presults : @{AllT_args} presults -> (@{ParaT_args} @{AllT_args} zipper,
    prio * (@{ParaT_args} @{AllT_args} zipper, result, prio) Co.acoroutine) Co.C.cat
  val get_run_presults : (@{ParaT_args} @{AllT_args} zipper,
    prio * (@{ParaT_args} @{AllT_args} zipper, result, prio) Co.acoroutine) Co.C.cat

  val gen_presults_from_sq :
    (*coroutine in case of an empty sequence*)
    (@{ParaT_args} @{AllT_args} zipper, result, prio) Co.acoroutine ->
    (*create next priority while (optionally) updating the sequence*)
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.coroutine ->
    result Seq.seq -> @{AllT_args} presults

  val presults_from_sq : @{ParaT_args encl = "(" ")"} Co.AE.exn ->
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.coroutine ->
    result Seq.seq -> @{AllT_args} presults

  (** create priorities **)
  val update_prio_co : (@{ParaT_args} @{AllT_args} zipper * prio, prio) Co.coroutine ->
    prio -> (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.coroutine
end

functor Zippy_PResults_Mixin(
    structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
    structure PResults : ZIPPY_PRESULTS_MIXIN_BASE
    where type (@{ParaT_args} 'a, 'b) Co.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
  ) : ZIPPY_PRESULTS_MIXIN =
struct

open PResults
structure U = Zippy_Monad_Util(K.M); open U

fun empty_aco e = Co.throw e
fun empty_presults e = presults (empty_aco e)

fun run_presults presults = dest_presults presults |> Co.resume
fun get_run_presults z4 = L.getter z4 |> (fn presults => run_presults presults z4)

local open Mo SC A
in
fun gen_aco_from_sq aco_empty_sq mk_prio_sq_c sq =
  let
    fun update mk_prio_sq_c sq =
      arr (fn z => Seq.pull sq |> Either.of_opt |> Either.map_left (Library.K z))
      >>> AC.merge (Co.resume aco_empty_sq)
        (second (arr (gen_aco_from_sq aco_empty_sq mk_prio_sq_c)))
      |> Co.acoroutine
  in
    arr (rpair sq)
    >>> Co.resume mk_prio_sq_c
    >>> arr (fn ((prio, sq), mk_prio_sq_c) => (prio, update mk_prio_sq_c sq))
    |> Co.acoroutine
  end

fun gen_presults_from_sq aco_empty_sq mk_prio_sq_c sq =
  gen_aco_from_sq aco_empty_sq mk_prio_sq_c sq |> presults

fun presults_from_sq e = gen_presults_from_sq (Co.throw e)

fun update_prio_co prio_co p =
  (fn (z, sq) => Co.resume prio_co (z, p)
    >>= arr (fn (p, prio_co) => ((p, sq), update_prio_co prio_co p)))
  |> Co.coroutine
end

end
