(*  Title:      Zippy/zippy_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PRESULTS_MIXIN =
sig
  include ZIPPY_PRESULTS_MIXIN_BASE

  val gen_presults_from_sq :
    (*coroutine in case of an empty sequence*)
    (@{ParaT_args} @{AllT_args} zipper, result, prio) CO.acoroutine ->
    (*create next priority while (optionally) updating the sequence*)
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine ->
    result Seq.seq -> @{AllT_args} presults

  val presults_from_sq : @{ParaT_args encl = "(" ")"} CO.AE.exn ->
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine ->
    result Seq.seq -> @{AllT_args} presults

  (** create priorities **)
  val update_prio_co : (@{ParaT_args} @{AllT_args} zipper * prio, prio) CO.coroutine ->
    prio -> (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine
end

functor Zippy_Presults_Mixin(
    PRESULTS : ZIPPY_PRESULTS_MIXIN_BASE
  ) : ZIPPY_PRESULTS_MIXIN =
struct

open PRESULTS
structure U = Zippy_Monad_Util(L.K.M); open U

local open SC MO A
in
fun gen_presults_from_sq aco_empty_sq mk_prio_sq_c sq =
  let
    fun update mk_prio_sq_c sq =
      arr (fn z => Seq.pull sq |> Either.of_opt |> Either.map_left (Library.K z))
      >>> AC.merge (CO.resume aco_empty_sq)
        (second (arr (gen_presults_from_sq aco_empty_sq mk_prio_sq_c #> dest_presults)))
      |> CO.acoroutine
  in
    arr (rpair sq)
    >>> CO.resume mk_prio_sq_c
    >>> arr (fn ((prio, sq), mk_prio_sq_c) => (prio, update mk_prio_sq_c sq))
    |> CO.acoroutine |> presults
  end

fun presults_from_sq e = gen_presults_from_sq (CO.throw e)

fun update_prio_co prio_co p =
  (fn (z, sq) => CO.resume prio_co (z, p)
    >>= arr (fn (p, prio_co) => ((p, sq), update_prio_co prio_co p)))
  |> CO.coroutine
end

end
