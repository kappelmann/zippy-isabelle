(*  Title:      Zippy/zippy_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PRESULTS_MIXIN =
sig
  include ZIPPY_PRESULTS_MIXIN_BASE

  val empty_presults : @{ParaT_args encl = "(" ")"} Co.ME.exn -> @{AllT_args} presults

  val run_presults : @{AllT_args} presults -> (@{ParaT_args} @{AllT_args} zipper,
    prio * (@{ParaT_args} @{AllT_args} zipper, result, prio) Co.Co.acoroutine) cat
  val get_run_presults : (@{ParaT_args} @{AllT_args} zipper,
    prio * (@{ParaT_args} @{AllT_args} zipper, result, prio) Co.Co.acoroutine) cat

  val gen_presults_from_sq :
    (*coroutine in case of an empty sequence*)
    (@{ParaT_args} @{AllT_args} zipper, result, prio) Co.Co.acoroutine ->
    (*create next priority while (optionally) updating the sequence*)
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.Co.coroutine ->
    result Seq.seq -> @{AllT_args} presults

  val presults_from_sq : @{ParaT_args encl = "(" ")"} Co.ME.exn ->
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.Co.coroutine ->
    result Seq.seq -> @{AllT_args} presults

  (* create priorities *)
  val mk_prio_res_co : (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio) Co.Co.coroutine ->
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.Co.coroutine

  val enum_prio_res_co : (@{ParaT_args} prio, prio) cat -> prio ->
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.Co.coroutine
end

functor Zippy_PResults_Mixin(
    PResults : ZIPPY_PRESULTS_MIXIN_BASE
  ) : ZIPPY_PRESULTS_MIXIN =
struct

open PResults
structure MU = Zippy_Monad_Util(K.M); open MU

local open Mo SC A Co
in
fun empty_presults e = presults (Co.throw e)

fun run_presults presults = dest_presults presults |> Co.resume
fun get_run_presults z4 = L.getter z4 |> (fn presults => run_presults presults z4)

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

(* create priorities *)
fun mk_prio_res_co prio_co = (fn (z, sq) => Co.resume prio_co (z, sq)
  >>= arr (fn (p, prio_co) => ((p, sq), mk_prio_res_co prio_co)))
  |> Co.coroutine

fun enum_prio_res_co next p =
  let
    val prio_co = Co.enum next (A.K p)
    fun mk_co prio_co = (fn _ => Co.resume prio_co () >>= A.second (arr mk_co)) |> Co.coroutine
  in mk_prio_res_co (mk_co prio_co) end
end
end
