(*  Title:      Zippy/zippy_caction_queue_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_CACTION_QUEUE_MIXIN_BASE =
sig
  type cost
  structure CAction : ZIPPY_CACTION_MIXIN
  sharing type CAction.cost = cost
  structure Queue : PRIORITY_QUEUE
  sharing type Queue.prio = cost

  type @{AllT_args} entry = {cost : cost,
    action : @{AllT_args} CAction.action,
    zipper : @{AllT_args} CAction.zipper}
  type @{AllT_args} queue = @{AllT_args} entry Queue.t
end

functor Zippy_CAction_Queue_Mixin_Base(A :
  sig
    structure CAction : ZIPPY_CACTION_MIXIN
    structure Queue : PRIORITY_QUEUE
    sharing type Queue.prio = CAction.cost
  end
  ) : ZIPPY_CACTION_QUEUE_MIXIN_BASE
  =
struct
open A
type cost = CAction.cost

type @{AllT_args} entry = {cost : cost,
  action : @{AllT_args} CAction.action,
  zipper : @{AllT_args} CAction.zipper}
type @{AllT_args} queue = @{AllT_args} entry Queue.t
end
