(*  Title:      Zippy/zippy_caction_queue_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_CACTION_QUEUE_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_CACTION_QUEUE_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  sharing type M.t = CAction.M.t
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t

  val mk_entry : (@{ParaT_args} @{AllT_args} CAction.zipper, @{AllT_args} entry) morph
  val run_entry : @{AllT_args} entry -> (@{ParaT_args} @{AllT_args} CAction.zipper,
    @{AllT_args} CAction.action_result) morph

  val mk_prio : (@{ParaT_args} @{AllT_args} entry, Queue.prio) morph

  val fold_cactions :
    (*update result*)
    (@{ParaT_args} @{AllT_args} entry * 'r, 'r Co.Co.res) morph ->
    (*initialise result*)
    (@{ParaT_args} @{AllT_args} CAction.zipper, 'r Co.Co.res) morph ->
    (*zipper enumeration*)
    (@{ParaT_args} @{AllT_args} CAction.zipper, @{AllT_args} CAction.zipper) Co.Co.coroutine ->
    (*zipper to start the enumeration*)
    (@{ParaT_args} @{AllT_args} CAction.zipper, (@{AllT_args} CAction.zipper * 'r) Co.Co.res) morph

  val mk_entry_insert : @{AllT_args} CAction.zipper -> (@{ParaT_args} @{AllT_args} queue) emorph

  val insert_cactions_queue :
    (@{ParaT_args} @{AllT_args} CAction.zipper, @{AllT_args} CAction.zipper) Co.Co.coroutine ->
    @{AllT_args} CAction.zipper -> (@{ParaT_args} @{AllT_args} queue) emorph

  type @{AllT_args} container1
  val insert_descendant_cactions_queue : @{AllT_args} container1 ->
    (@{ParaT_args} @{AllT_args} queue) emorph
  val init_cactions_queue : (@{ParaT_args} @{AllT_args} container1, @{AllT_args} queue) morph

  val update_unchanged : @{AllT_args} CAction.zipper -> (@{ParaT_args} @{AllT_args} queue) emorph
  val update_expanded :
    (@{AllT_args} CAction.zipper_expanded -> (@{ParaT_args} @{AllT_args} queue) emorph) ->
    @{AllT_args} CAction.zipper_expanded -> (@{ParaT_args} @{AllT_args} queue) emorph
  val update_changed : @{AllT_args} CAction.zipper_changed ->
    (@{ParaT_args} @{AllT_args} queue) emorph
end

functor Zippy_CAction_Queue_Mixin(
    structure Z : ZIPPY_ENUM_MIXIN
    structure CAction_Queue : ZIPPY_CACTION_QUEUE_MIXIN_BASE
    sharing type CAction_Queue.CAction.zipper_changed = Z.Z1.zipper
    sharing type CAction_Queue.CAction.zipper = Z.Z4.zipper
    sharing type CAction_Queue.CAction.zipper_expanded = Z.Z5.zipper
    sharing type CAction_Queue.CAction.M.t = Z.M.t
    val mk_prio : (@{ParaT_args} @{AllT_args} CAction_Queue.entry, CAction_Queue.Queue.prio) Z.morph
    val mk_exn : (unit -> @{ParaT_args encl: "(" ")"} Z.Co.ME.exn)
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t =Z.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure Show_Container1 : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show_Container1.t = Z.Z1.ZM.container
    structure Show4 : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show4.t = Z.Z4.zipper
  ) : ZIPPY_CACTION_QUEUE_MIXIN =
struct

open Z CAction_Queue Log
structure MU = Zippy_Monad_Util(CAction.M); open MU

local open SC Mo A Co CAction.Exn
in
fun mk_entry zipper = CAction.get_run_caction zipper
  >>= arr (fn (cost, action) => {cost = cost, action = action, zipper = zipper})
fun run_entry entry = CAction.run_action (#cost entry, #action entry)

val mk_prio = mk_prio

fun fold_cactions update = Co.repeat_step_res_init (arr fst)
  (AE.catch' (first mk_entry >>> update) (arr (snd #> Co.continue))) (AE.id ())

fun mk_entry_insert z queue = Ctxt.get_ctxt () >>= (fn ctxt =>
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
        Pretty.str "Inserting caction of",
        Show4.pretty ctxt z,
        Pretty.str "to queue."
      ] |> Pretty.block |> Pretty.string_of);
    mk_entry z
    >>= (fn entry => mk_prio entry
    >>= arr (fn prio => Queue.insert (prio, entry) queue))))

fun insert_cactions_queue co z = AE.try (fn queue =>
  fold_cactions
    (fn (entry, queue) => mk_prio entry
      >>= arr (fn prio => Queue.insert (prio, entry) queue |> Co.continue))
    (fn z => mk_entry_insert z queue >>= arr Co.continue) co z
  >>= arr (Co.dest_res #> snd))

type @{AllT_args} container1 = @{AllT_args} Z1.ZM.container
(*FIXME: could be made more efficient: only add cactions of goals that may take more results*)
fun insert_descendant_cactions_queue c queue = Ctxt.get_ctxt () >>= (fn ctxt =>
  (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Inserting descendant cactions of",
      Show_Container1.pretty ctxt c,
      Pretty.str "to queue."
    ] |> Pretty.block |> Pretty.string_of);
  AE.catch'
    (Z1.ZM.Zip.morph >>> ADF_Post4.enum_zipper3 mk_exn
      >>> (fn (z, co) => insert_cactions_queue (Co.cons (id ()) co) z queue))
    (A.K queue) c))
fun init_cactions_queue c = insert_descendant_cactions_queue c Queue.empty

local fun mk_entry_insert_safe z = AE.try (mk_entry_insert z)
in
fun update_unchanged z = mk_entry_insert_safe z
fun update_expanded insert_descendant_cactions_queue z = insert_descendant_cactions_queue z
  >>> (fn queue => Z.Up5.morph z >>= (fn z => mk_entry_insert_safe z queue))
end
(*paths of entries in the queue might have changed; we hence re-initialise the queue*)
fun update_changed z _ = Z1.ZM.Unzip.morph z >>= init_cactions_queue
end

end
