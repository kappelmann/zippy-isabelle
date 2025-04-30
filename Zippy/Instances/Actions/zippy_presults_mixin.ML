(*  Title:      Zippy/zippy_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PRESULTS_MIXIN =
sig
  include ZIPPY_PRESULTS_MIXIN_BASE
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
  sharing type AE.K.M.t = M.t

  (* presults *)
  val gen_presults_from_sq :
    (*coroutine in case of an empty sequence*)
    (@{ParaT_args} @{AllT_args} zipper, result, prio) CO.acoroutine ->
    (*create next priority while (optionally) updating the sequence*)
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine ->
    result Seq.seq -> @{AllT_args} presults

  val presults_from_sq : @{ParaT_args encl = "(" ")"} AE.exn ->
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine ->
    result Seq.seq -> @{AllT_args} presults

  (** create priorities **)
  val update_prio_co : (@{ParaT_args} @{AllT_args} zipper * prio, prio) CO.coroutine ->
    prio -> (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine
end

functor Zippy_Presults_Mixin(
    structure Z : ZIPPY_BASE
    structure PRESULTS : ZIPPY_PRESULTS_MIXIN_BASE
    sharing type PRESULTS.zipper = Z.Z4.zipper
    sharing type PRESULTS.M.t = Z.M.t
    sharing type PRESULTS.L.lens = Z.L.lens
    sharing type PRESULTS.CO.acoroutine = Z.CO.acoroutine
    sharing type PRESULTS.CO.AE.exn = Z.CO.AE.exn
  ) : ZIPPY_PRESULTS_MIXIN =
struct

open Z PRESULTS

local open SC MO A
in
(* presults *)
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

fun presults_from_sq e = gen_presults_from_sq (empty_aco e)

fun update_prio_co prio_co p =
  (fn (z, sq) => CO.resume prio_co (z, p)
    >>= arr (fn (p, prio_co) => ((p, sq), update_prio_co prio_co p)))
  |> CO.coroutine
end

end

