(*  Title:      Zippy/zippy_paction_queue_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_QUEUE_MIXIN_BASE =
sig
  type prio
  structure PAction : ZIPPY_PACTION_MIXIN_BASE
  sharing type PAction.prio = prio
  structure Queue : PRIORITY_QUEUE
  sharing type Queue.prio = prio

  type @{AllT_args} entry = {prio : prio,
    action : @{AllT_args} PAction.action,
    zipper : @{AllT_args} PAction.zipper}
  type @{AllT_args} queue = @{AllT_args} entry Queue.t
end

functor Zippy_PAction_Queue_Mixin_Base(A :
  sig
    structure PAction : ZIPPY_PACTION_MIXIN_BASE
    structure Queue : PRIORITY_QUEUE
    sharing type Queue.prio = PAction.prio
  end
  ) : ZIPPY_PACTION_QUEUE_MIXIN_BASE
  =
struct
open A
type prio = PAction.prio

type @{AllT_args} entry = {prio : prio,
  action : @{AllT_args} PAction.action,
  zipper : @{AllT_args} PAction.zipper}
type @{AllT_args} queue = @{AllT_args} entry Queue.t
end
