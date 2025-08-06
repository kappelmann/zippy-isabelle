(*  Title:      Zippy/zippy_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PRESULTS_MIXIN =
sig
  include ZIPPY_PRESULTS_MIXIN_BASE

  val empty_presults : @{ParaT_args encl: "(" ")"} Co.ME.exn -> @{AllT_args} presults

  val run_presults : @{AllT_args} presults -> (@{ParaT_args} @{AllT_args} zipper,
    prio * (@{ParaT_args} @{AllT_args} zipper, result, prio) Co.Co.acoroutine) morph

  val gen_presults_from_sq :
    (*coroutine in case of an empty sequence*)
    (@{ParaT_args} @{AllT_args} zipper, result, prio) Co.Co.acoroutine ->
    @{AllT_args} prio_sq_co -> result Seq.seq -> @{AllT_args} presults

  val presults_from_sq : @{ParaT_args encl: "(" ")"} Co.ME.exn -> @{AllT_args} prio_sq_co ->
    result Seq.seq -> @{AllT_args} presults

  (* create priorities *)
  val mk_prio_sq_co : (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio) Co.Co.coroutine ->
    @{AllT_args} prio_sq_co

  val enum_prio_sq_co : (@{ParaT_args} prio) emorph -> prio -> @{AllT_args} prio_sq_co
end

functor Zippy_PResults_Mixin(
    PResults : ZIPPY_PRESULTS_MIXIN_BASE
  ) : ZIPPY_PRESULTS_MIXIN =
struct

open PResults
structure MU = Zippy_Monad_Util(M); open MU

local open Mo SC A Co
in
fun empty_presults e = presults (Co.throw e)

fun run_presults presults = dest_presults presults |> Co.resume

fun gen_aco_from_sq aco_empty_sq prio_sq_co sq =
  let
    fun update mk_prio_sq_co sq =
      arr (fn z => Seq.pull sq |> Either.of_opt |> Either.map_left (Library.K z))
      >>> AC.merge (Co.resume aco_empty_sq)
        (second (arr (gen_aco_from_sq aco_empty_sq mk_prio_sq_co)))
      |> Co.acoroutine
  in
    arr (rpair sq)
    >>> Co.resume prio_sq_co
    >>> arr (fn ((prio, sq), mk_prio_sq_co) => (prio, update mk_prio_sq_co sq))
    |> Co.acoroutine
  end

fun gen_presults_from_sq aco_empty_sq prio_sq_co sq =
  gen_aco_from_sq aco_empty_sq prio_sq_co sq |> presults

fun presults_from_sq exn = gen_presults_from_sq (Co.throw exn)

(* create priorities *)
fun mk_prio_sq_co prio_co = (fn (z, sq) => Co.resume prio_co (z, sq)
  >>= arr (fn (p, prio_co) => ((p, sq), mk_prio_sq_co prio_co)))
  |> Co.coroutine

fun enum_prio_sq_co next p =
  let
    val prio_co = Co.enum next (A.K p)
    fun mk_co prio_co = (fn _ => Co.resume prio_co () >>= A.second (arr mk_co)) |> Co.coroutine
  in mk_prio_sq_co (mk_co prio_co) end
end
end
