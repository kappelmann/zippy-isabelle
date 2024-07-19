(*  Title:      HOCLP/move_util.ML
    Author:     Kevin Kappelmann
*)
signature MOVE_UTIL =
sig
  include MOVE_BASE
  structure ME : IMONAD_EXCEPTION_BASE
  sharing type ME.t = K.M.t
  structure C : ICATEGORY
  structure AE : IARROW_EXCEPTION

  type 'a res
  val stop : 'a -> 'a res
  val continue : 'a -> 'a res
  val dest_res : 'a res -> 'a
  val fold : ('a -> ('i, 'j, 'a) ME.t) -> ('a -> 'b -> ('j, 'i, 'b res) ME.t) ->
    ('i, 'j, 'a) ME.t -> 'b -> ('i, 'i, 'b) ME.t
end

functor Move_Util(ME : IMONAD_EXCEPTION_BASE) : MOVE_UTIL =
struct

structure MB = Move_Base(IKleisli(ME))
open MB

structure ME = ME
structure M = IMonad(ME)
structure AE = IArrow_Exception(IKleisli_Arrow_Exception(ME))
structure C = ICategory(AE)
structure A = IArrow(AE)

datatype 'a res = Stop of 'a | Continue of 'a

val stop = Stop
val continue = Continue
fun dest_res (Stop x) = x
  | dest_res (Continue x) = x

local open M in
fun fold move f m acc = m
  >>= (fn x => f x acc
  >>= (fn Stop acc => M.pure acc
    | Continue acc => ME.catch (fold move f (move x) acc) (A.K acc)))
end

end
