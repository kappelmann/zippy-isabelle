(*  Title:      Zippy/zippy_paction_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_MIXIN =
sig
  include ZIPPY_PACTION_MIXIN_BASE
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
  sharing type AE.K.M.t = M.t
  structure AF : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_FOLD"\<close>
  sharing type AF.K.M.t = M.t

  val no_action : @{ParaT_args encl = "(" ")"} AE.exn -> @{AllT_args} action
  val no_paction : @{ParaT_args encl = "(" ")"} AE.exn -> @{AllT_args} paction
  val disable_paction : @{ParaT_args encl = "(" ")"} AE.exn ->
    (@{ParaT_args} @{AllT_args} zipper) hom_move

  val get_run_paction : (@{ParaT_args} @{AllT_args} zipper, prio * @{AllT_args} action) cat
  val run_action : prio * @{AllT_args} action -> (@{ParaT_args} @{AllT_args} zipper) hom_move

  (*find action candidates*)
  val gen_fold_pactions :
    (*next zipper*)
    (@{ParaT_args} @{AllT_args} zipper) hom_move ->
    (*update result*)
    (@{ParaT_args} ((prio * @{AllT_args} action) * @{AllT_args} zipper) * 'r, 'r AF.res) cat ->
    (*initialise result*)
    (@{ParaT_args} @{AllT_args} zipper, 'r AF.res) cat ->
    (@{ParaT_args} @{AllT_args} zipper, 'r AF.res) cat

  val fold_pactions_init_continue : (@{ParaT_args} @{AllT_args} zipper,
    ((prio * @{AllT_args} action) * @{AllT_args} zipper) AF.res) cat

  val fold_pactions_run_single_res : (@{ParaT_args}
    ((prio * @{AllT_args} action) * @{AllT_args} zipper) AF.res, @{AllT_args} zipper) cat

  val fold_pactions_prio_ord : prio ord -> ((prio * @{AllT_args} action) * @{AllT_args} zipper) ord

  val fold_pactions_max : prio ord ->
    (@{ParaT_args} ((prio * @{AllT_args} action) * @{AllT_args} zipper)) hom_move ->
    (@{ParaT_args} @{AllT_args} zipper) hom_move ->
    (@{ParaT_args} @{AllT_args} zipper,
      ((prio * @{AllT_args} action) * @{AllT_args} zipper) AF.res) cat
end

functor Zippy_PAction_Mixin(
    structure PACTION : ZIPPY_PACTION_MIXIN_BASE
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
    sharing type AE.K.M.t = PACTION.M.t
  ) : ZIPPY_PACTION_MIXIN =
struct

open PACTION
structure U = Zippy_Monad_Util(M); open U
structure AE = AE
structure AF = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Fold_Exception_Rec"\<close>(AE)

fun no_action e _ = AE.throw' e
fun no_paction e = AE.throw' e |> PACTION.paction

fun set_paction x = x |> (L.lens () |> L.set |> curry)
fun disable_paction e = set_paction (no_paction e)

local open SC MO A
in
fun get_run_paction x = L.getter x
  >>= (fn paction => PACTION.run_paction paction x)
fun run_action (p, action) = action p

fun gen_fold_pactions_mk_res x = x |> (get_run_paction &&& id ())

fun gen_fold_pactions next update = AF.fold_init next
  (AE.catch' (first gen_fold_pactions_mk_res >>> update) (arr snd >>> arr AF.continue))

fun fold_pactions_init_continue x = x |> (gen_fold_pactions_mk_res >>> arr AF.continue)
fun fold_pactions_run_single_res x = x |> (arr AF.dest_res >>> AA.uncurry run_action)

fun fold_pactions_prio_ord prio_ord = Order_Util.fst_ord (Order_Util.fst_ord prio_ord)

fun fold_pactions_max prio_ord update_res next = gen_fold_pactions next
  (first update_res >>> arr (Order_Util.max_ord snd (fold_pactions_prio_ord prio_ord) #> AF.continue))
  (gen_fold_pactions_mk_res >>> update_res >>> arr AF.continue)
end

end
