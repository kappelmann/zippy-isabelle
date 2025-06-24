(*  Title:      Zippy/zippy_enum_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ENUM_COPY_MIXIN =
sig
  include ZIPPY_COPY_MIXIN_BASE
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close>
  sharing type AE.K.M.t = M.t

  val copy_parents : (unit -> @{ParaT_args encl = "" ""} AE.exn) ->
    copy_update_data -> (@{ParaT_args} @{AllT_args} zipper_to) hom_move
end

functor Zippy_Enum_Copy_Mixin(
    structure Z : ZIPPY_BASE_ENUM
    structure Copy : ZIPPY_COPY_MIXIN_BASE
    sharing type Copy.zipper_from = Z.Z3.zipper
    sharing type Copy.zipper_to = Z.Z1.zipper
    sharing type Copy.M.t = Z.M.t
  ) : ZIPPY_ENUM_COPY_MIXIN =
struct

open Z Copy
structure MU = Zippy_Monad_Util(M); open MU
structure ZC = Zippy_Copy_Mixin(structure Copy = Copy; structure AE = AE)

local open SC Mo
in
fun copy_parents mk_exn cud z1 =
  (Up1.move >>> Up5.move >>> Up4.move >>> Z3.ZM.Unzip.move >>> Z3.ZM.Zip.move) z1
  >>= (fn z3 => Co.repeat_step_res (arr fst)
    (AA.uncurry (ZC.get_run_copy_safe cud) >>> arr Co.continue) (DF_Post3.enum_zipper mk_exn)
    (z3, z1))
  >>= arr (Co.dest_res #> snd)
end

end

