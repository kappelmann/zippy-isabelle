(*  Title:      Zippy/zippy_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_COPY_MIXIN =
sig
  include ZIPPY_COPY_MIXIN_BASE

  val get_run_copy : copy_update_data -> @{AllT_args} zipper_from ->
    (@{ParaT_args} @{AllT_args} zipper_to) hom_move

  val get_run_copy_safe : copy_update_data -> @{AllT_args} zipper_from ->
    (@{ParaT_args} @{AllT_args} zipper_to) hom_move
end

functor Zippy_Copy_Mixin(
    structure Copy : ZIPPY_COPY_MIXIN_BASE
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Copy.M.t
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = Copy.M.t
  ) : ZIPPY_COPY_MIXIN =
struct

open Copy
structure MU = Zippy_Monad_Util(M); open MU

local open Mo
in
fun get_run_copy cud z3 z1 = Ctxt.MS.get () >>= (fn ctxt =>
  let val _ = @{log Logger.ERR} ctxt (fn _ => "Copying")
  in L.getter z3 |> (run_copy #> (fn copy => copy cud z3 z1))
  end)
fun get_run_copy_safe cud z3 = Exn.AE.try (get_run_copy cud z3)
end

end

