(*  Title:      Zippy/zippy_enum_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ENUM_COPY_MIXIN =
sig
  include ZIPPY_COPY_MIXIN_BASE
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t

  val copy_parents : (unit -> @{ParaT_args encl = "" ""} Co.ME.exn) ->
    copy_update_data -> (@{ParaT_args} @{AllT_args} zipper_to) hom_move
end

functor Zippy_Enum_Copy_Mixin(
    structure Z : ZIPPY_ENUM_MIXIN
    structure Copy : ZIPPY_COPY_MIXIN_BASE
    sharing type Copy.zipper_from = Z.Z3.zipper
    sharing type Copy.zipper_to = Z.Z1.zipper
    sharing type Copy.M.t = Z.M.t
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
  ) : ZIPPY_ENUM_COPY_MIXIN =
struct

open Z Copy
structure MU = Zippy_Monad_Util(M); open MU
structure Co = Co
structure Exn = Zippy_Exception_Mixin(Co)
structure Copy = Zippy_Copy_Mixin(structure Copy = Copy; structure Ctxt = Ctxt; structure Exn = Exn)

local open SC Mo Co
in
fun copy_parents mk_exn cud z1 =
  (Up1.move >>> Up5.move >>> Up4.move >>> Z3.ZM.Unzip.move >>> Z3.ZM.Zip.move) z1
  >>= (fn z3 => Co.repeat_step_res (arr fst)
    (AA.uncurry (Copy.get_run_copy_safe cud) >>> arr Co.continue) (DF_Post3.enum_zipper mk_exn)
    (z3, z1))
  >>= arr (Co.dest_res #> snd)
end

end

