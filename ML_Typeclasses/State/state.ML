(*  Title:  state.ML
    Author: Kevin Kappelmann

Indexed state monad transformer.
*)

signature STATE_TRANS =
sig

structure SR : STATE_RESULT_BASE

type 'a mt
type ('si, 'so, 'a) state = 'si -> ('so, 'a) SR.result mt

include IMONAD_TRANS
where type ('si, 'so, 'a) t = ('si, 'so, 'a) state
sharing type M.t = mt

val state : ('si -> ('so, 'a) SR.result) -> ('si, 'so, 'a) state

val eval : ('si, 'so, 'a) state -> 'si -> 'a M.t
val exec : ('si, 'so, 'a) state -> 'si -> 'so M.t
val get : unit -> ('s, 's, 's) state
val put : 'so -> ('si, 'so, unit) state

val map_state : ('sj -> 'so) -> ('si, 'sj, 'a) state -> ('si, 'so, 'a) state
val map_result : ('a -> 'sj -> ('so, 'b) SR.result) -> ('si, 'sj, 'a) state -> ('si, 'so, 'b) state

val kleisli : ('a -> 'b) -> 'a -> ('s, 's, 'b) state
val kleisli_state : ('a -> 's -> 'b) -> 'a -> ('s, 's, 'b) state
val kleisli_state_monad : ('a -> 's -> 'b M.t) -> 'a -> ('s, 's, 'b) state

end

functor State_Trans(structure M : MONAD_BASE; structure SR : STATE_RESULT_BASE) : STATE_TRANS =
struct

structure M = M
structure SR = State_Result(SR)

type 'a mt = 'a M.t
type ('si, 'so, 'a) state = 'si -> ('so, 'a) SR.result M.t

fun state fs = M.pure o fs

fun eval st s = st s |> M.map SR.value
fun exec st s = st s |> M.map SR.state
fun get () = state (fn s => SR.result s s)
fun put s = state (fn _ => SR.result s ())

fun map_base f st = M.map f o st

structure IMT : IMONAD_TRANS =
struct
structure M = M
type ('si, 'so, 'a) t = ('si, 'so, 'a) state

fun lift x s = M.bind x (SR.result s #> M.pure)

fun map f = map_base (SR.map_value f)
fun pure x = M.pure o (fn s => SR.result s x)
fun <*> stf stx = (fn s => M.bind (stf s)
  (fn r => M.bind (stx (SR.state r))
  (fn r' => SR.result (SR.state r') (SR.value r (SR.value r')) |> M.pure)))
fun bind st f_st = (fn s => M.bind (st s) (fn r => (f_st (SR.value r)) (SR.state r)))
end
open IMT

fun map_state f = map_base (SR.map_state f)
fun map_result f = map_base (SR.map f)

structure IK = IKleisli_IArrow_Apply(IMT)
fun kleisli f = IK.arr f

fun kleisli_state f x = get () |> map (f x)
fun kleisli_state_monad f x = (fn s => M.map (SR.result s) (f x s))

end

signature STATE_STACK =
sig

structure S : STATE_TRANS
structure SRS : STATE_RESULT_STACK

val push_state_monad : ('a -> 'sc) -> ('a -> ('si, ('sa, 'sb) SRS.entry, 'b) S.state) ->
  'a -> ('si, ('sa, ('sb, 'sc) SRS.entry) SRS.entry, 'b) S.state
val lift_push_state_monad : ('a -> 'sk) -> ('a -> ('si, 'sj) SRS.entry -> 'b S.M.t) ->
  'a -> (('si, 'sj) SRS.entry, ('si, ('sj, 'sk) SRS.entry) SRS.entry, 'b) S.state

end

functor State_Stack(S : STATE_TRANS) : STATE_STACK =
struct

structure S = S
structure SR = State_Result(S.SR)
structure SRS = State_Result_Stack(S.SR)

fun push_state_monad lense f x = S.M.map (SR.map_state (SRS.push (lense x))) o f x
fun lift_push_state_monad lense = push_state_monad lense o S.kleisli_state_monad

end