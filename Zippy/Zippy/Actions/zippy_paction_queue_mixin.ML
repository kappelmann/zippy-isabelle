(*  Title:      Zippy/zippy_paction_queue_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_QUEUE_MIXIN =
sig
  include ZIPPY_PACTION_QUEUE_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) cat

  val mk_entry : (@{ParaT_args} @{AllT_args} PAction.zipper, @{AllT_args} entry) cat
  val run_entry : @{AllT_args} entry -> (@{ParaT_args} @{AllT_args} PAction.zipper,
    @{AllT_args} PAction.action_result) move

  val fold_pactions :
    (*update result*)
    (@{ParaT_args} @{AllT_args} entry * 'r, 'r Co.res) cat ->
    (*initialise result*)
    (@{ParaT_args} @{AllT_args} PAction.zipper, 'r Co.res) cat ->
    (*zipper enumeration*)
    (@{ParaT_args} @{AllT_args} PAction.zipper, @{AllT_args} PAction.zipper) Co.coroutine ->
    (*zipper to start the enumeration*)
    (@{ParaT_args} @{AllT_args} PAction.zipper, (@{AllT_args} PAction.zipper * 'r) Co.res) cat

  val insert : @{AllT_args} entry -> @{AllT_args} queue -> @{AllT_args}queue
  val mk_entry_insert : @{AllT_args} PAction.zipper -> (@{ParaT_args} @{AllT_args} queue) hom_move

  val fold_pactions_queue :
    (@{ParaT_args} @{AllT_args} PAction.zipper, @{AllT_args} PAction.zipper) Co.coroutine ->
    @{AllT_args} PAction.zipper -> (@{ParaT_args} @{AllT_args} queue) hom_move

  type @{AllT_args} container1
  val fold_children_pactions_queue : @{AllT_args} container1 ->
    (@{ParaT_args} @{AllT_args} queue) hom_move
  val init_pactions_queue : (@{ParaT_args} @{AllT_args} container1, @{AllT_args} queue) cat

  val update_stagnate : @{AllT_args} PAction.zipper -> (@{ParaT_args} @{AllT_args} queue) hom_move
  val update_expand :
    (@{AllT_args} PAction.zipper_expand -> (@{ParaT_args} @{AllT_args} queue) hom_move) ->
    @{AllT_args} PAction.zipper_expand -> (@{ParaT_args} @{AllT_args} queue) hom_move
  val update_trim : @{AllT_args} PAction.zipper_trim -> (@{ParaT_args} @{AllT_args} queue) hom_move
end

functor Zippy_PAction_Queue_Mixin(
    structure Z : ZIPPY_BASE_ENUM
    structure PAction_Queue : ZIPPY_PACTION_QUEUE_MIXIN_BASE
    sharing type PAction_Queue.PAction.zipper_trim = Z.Z1.zipper
    sharing type PAction_Queue.PAction.zipper = Z.Z4.zipper
    sharing type PAction_Queue.PAction.zipper_expand = Z.Z5.zipper
    sharing type PAction_Queue.PAction.M.t = Z.M.t
    val mk_exn : (unit -> @{ParaT_args encl = "" ""} Z.AE.exn)
  ) : ZIPPY_PACTION_QUEUE_MIXIN =
struct

open Z PAction_Queue
structure AE = struct open PAction Co.AE end
structure MU = Zippy_Monad_Util(PAction.M); open MU MU.MB
structure PAction = Zippy_PAction_Mixin(structure PAction = PAction; structure AE = AE)

local open SC Mo A PAction
in
fun mk_entry zipper = get_run_paction zipper
  >>= arr (fn (prio, action) => {prio = prio, action = action, zipper = zipper})
fun run_entry entry = run_action (#prio entry, #action entry)

fun fold_pactions update = Co.repeat_step_res_init (arr fst)
  (AE.catch' (first mk_entry >>> update) (arr (snd #> Co.continue))) (AE.id ())

fun insert entry = Queue.insert (#prio entry, entry)
fun mk_entry_insert z queue = mk_entry z >>= arr (fn entry => insert entry queue)

fun fold_pactions_queue co z = AE.try (fn queue =>
  fold_pactions (arr (Library.uncurry insert #> Co.continue))
    (fn z => mk_entry_insert z queue >>= arr Co.continue) co z
  >>= arr (Co.dest_res #> snd))

type @{AllT_args} container1 = @{AllT_args} Z1.ZM.container
fun fold_children_pactions_queue c queue = AE.catch'
  (Z1.ZM.Zip.move >>> ADF_Post4.enum_zipper3 mk_exn
    >>> (fn (z, co) => fold_pactions_queue (Co.cons (id ()) co) z queue))
  (A.K queue) c
fun init_pactions_queue c = fold_children_pactions_queue c Queue.empty

fun update_stagnate z = AE.try (mk_entry_insert z)
fun update_expand fold_pactions_queue z = fold_pactions_queue z
  >>> (fn queue => Z.Up5.move z >>= (fn z => update_stagnate z queue))
(*trimming may invalidate entries in the queue; we hence re-initialise it*)
fun update_trim z _ = Z1.ZM.Unzip.move z >>= init_pactions_queue
end

end
