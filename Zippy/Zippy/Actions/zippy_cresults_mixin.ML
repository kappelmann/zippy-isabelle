(*  Title:      Zippy/zippy_cresults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_CRESULTS_MIXIN =
sig
  include ZIPPY_CRESULTS_MIXIN_BASE

  val empty_cresults : @{ParaT_args encl: "(" ")"} Co.ME.exn -> @{AllT_args} cresults

  val run_cresults : @{AllT_args} cresults -> (@{ParaT_args} @{AllT_args} zipper,
    cost * (@{ParaT_args} @{AllT_args} zipper, result, cost) Co.Co.acoroutine) morph

  val gen_cresults_from_resultsq :
    (*acoroutine in case of an empty sequence*)
    (@{ParaT_args} @{AllT_args} zipper, result, cost) Co.Co.acoroutine ->
    @{AllT_args} cresultsq -> result Seq.seq -> @{AllT_args} cresults

  val cresults_from_resultsq : @{ParaT_args encl: "(" ")"} Co.ME.exn -> @{AllT_args} cresultsq ->
    result Seq.seq -> @{AllT_args} cresults

  val pure_cresultsq : (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, cost) Co.Co.coroutine ->
    @{AllT_args} cresultsq
  val enum_cresultsq : (@{ParaT_args} cost) emorph -> cost -> @{AllT_args} cresultsq
end

functor Zippy_CResults_Mixin(
    CResults : ZIPPY_CRESULTS_MIXIN_BASE
  ) : ZIPPY_CRESULTS_MIXIN =
struct

open CResults
structure MU = Zippy_Monad_Util(M); open MU

local open Mo SC A Co
in
fun empty_cresults exn = cresults (Co.throw exn)

fun run_cresults cresults = dest_cresults cresults |> Co.resume

fun gen_aco_from_sq aco_empty_sq cresultsq sq =
  let
    fun update pure_cresultsq sq =
      arr (fn z => Seq.pull sq |> Either.of_opt |> Either.map_left (Library.K z))
      >>> AC.merge (Co.resume aco_empty_sq)
        (second (arr (gen_aco_from_sq aco_empty_sq pure_cresultsq)))
      |> Co.acoroutine
  in
    arr (rpair sq)
    >>> Co.resume cresultsq
    >>> arr (fn ((cost, sq), pure_cresultsq) => (cost, update pure_cresultsq sq))
    |> Co.acoroutine
  end

fun gen_cresults_from_resultsq aco_empty_sq cresultsq = gen_aco_from_sq aco_empty_sq cresultsq
  #> cresults

fun cresults_from_resultsq exn = gen_cresults_from_resultsq (Co.throw exn)

fun pure_cresultsq cost_co = (fn (z, sq) => Co.resume cost_co (z, sq)
  >>= arr (fn (p, cost_co) => ((p, sq), pure_cresultsq cost_co)))
  |> Co.coroutine

fun enum_cresultsq next c =
  let
    val cost_co = Co.enum next (A.K c)
    fun mk_co cost_co = (fn _ => Co.resume cost_co () >>= A.second (arr mk_co)) |> Co.coroutine
  in pure_cresultsq (mk_co cost_co) end
end
end
