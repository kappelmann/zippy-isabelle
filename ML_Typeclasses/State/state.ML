(*  Title:  state.ML
    Author: Kevin Kappelmann

State monads adapted from Haskells mtl package.
*)
signature MONAD_STATE_BASE =
sig
  structure SR : STATE_RESULT_BASE
  type s
  include MONAD_BASE
  val state : (s -> (s, 'a) SR.result) -> ('p1, 'a) t
  val get : unit -> ('p1, s) t
  val put : s -> ('p1, unit) t
end

signature MONAD_STATE =
sig
  include MONAD_STATE_BASE
  val map_state : (s -> s) -> ('p1, 'a) t -> ('p1, 'a) t
  val map_result : ('a -> s -> (s, 'b) SR.result) -> ('p1, 'a) t -> ('p1, 'b) t
end

functor Monad_State(M : MONAD_STATE_BASE) : MONAD_STATE =
struct
open M
structure SR = State_Result(SR)
fun map_base f st = M.bind st (M.state o f)
fun map_state f = map_base (fn x => fn s => SR.result (f s) x)
fun map_result f = map_base f
end

signature STATE_TRANS =
sig
  structure SR : STATE_RESULT_BASE

  type ('p1, 'a) mt
  type s
  type ('p1, 'a) state = s -> ('p1, (s, 'a) SR.result) mt

  include MONAD_TRANS
  where type ('p1, 'a) t = ('p1, 'a) state
  sharing type M.t = mt

  (*MONAD_STATE_BASE*)
  val state : (s -> (s, 'a) SR.result) -> ('p1, 'a) state
  val get : unit -> ('p1, s) state
  val put : s -> ('p1, unit) state

  val eval : s -> ('p1, 'a) state -> ('p1, 'a) M.t
  val exec : s -> ('p1, 'a) state -> ('p1, s) M.t
end

functor State_Trans(structure M : MONAD_BASE; structure SR : STATE_RESULT_BASE; type s) : STATE_TRANS =
struct

type ('p1, 'a) mt = ('p1, 'a) M.t
type ('p1, 'a) state = s -> ('p1, (s, 'a) SR.result) mt

structure MT : MONAD_TRANS =
struct
structure M = Monad(M) open M
type ('p1, 'a) t = ('p1, 'a) state

fun lift x s = x >>= (SR.result s #> M.pure)

structure SR = State_Result(SR)
fun map f st = M.map (SR.map_value f) o st
fun pure x = M.pure o (fn s => SR.result s x)
fun stf <*> stx = (fn s => stf s
  >>= (fn r => stx (SR.state r)
  >>= (fn r' => SR.result (SR.state r') (SR.value r (SR.value r')) |> M.pure)))
fun bind st f_st = (fn s => st s >>= (fn r => (f_st (SR.value r)) (SR.state r)))
end
open MT

structure MS : MONAD_STATE_BASE =
struct
open MT
structure SR = SR
type s = s
fun state fs = M.pure o fs
fun get () = state (fn s => SR.result s s)
fun put s = state (fn _ => SR.result s ())
end
open MS

fun eval s st = st s |> M.map SR.value
fun exec s st = st s |> M.map SR.state

end

functor Monad_Zero_State_Trans(
    structure M : MONAD_ZERO_BASE
    structure S : STATE_TRANS
    sharing type S.M.t = M.t
  ) : MONAD_ZERO_BASE where type ('p1, 'a) t = ('p1, 'a) S.t
  =
struct
fun zero _ = S.lift (M.zero ())
open S
end

functor Monad_Exception_State_Trans(
    structure M : MONAD_EXCEPTION_BASE
    structure S : STATE_TRANS
    sharing type S.M.t = M.t
  ) : MONAD_EXCEPTION_BASE where type ('p1, 'a) t = ('p1, 'a) S.t
  =
struct

open M
fun throw e = S.lift (M.throw e)
fun catch m f s = M.catch (m s) (fn e => f e s)
open S

end

signature ARROW_STATE_BASE =
sig
  include ARROW_BASE
  type s
  val get : unit -> ('p1, 'a, s) cat
  val put : unit -> ('p1, s, unit) cat
end

signature ARROW_STATE =
sig
  include ARROW_STATE_BASE
  val change : ('p1, 'a * s, s) cat -> ('p1, 'a, 'a) cat
  val access : ('p1, 'a * s, 'b) cat -> ('p1, 'a, 'b) cat
end

functor Arrow_State(
    structure AS : ARROW_STATE_BASE
    structure A : ARROW
    sharing type A.cat = AS.cat
  ) : ARROW_STATE =
struct
open AS
open A

local structure SC = Semi_Category(A) open SC
in
fun get_state _ = id () &&& get ()
fun access f = get_state () >>> f
fun change f = access f &&& id ()
  >>> first (put ())
  >>> arr snd
end

end

signature KLEISLI_ARROW_STATE =
sig
  structure K : KLEISLI
  include ARROW_STATE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_State(structure MS : MONAD_STATE_BASE) : KLEISLI_ARROW_STATE =
struct
structure KA = Kleisli_Arrow_Apply_Base(MS)
open KA
type s = MS.s
local structure M = Monad(MS) open M
in
fun get _ _ = MS.get ()
fun put _ x = MS.put x
fun access f x = get () x >>= (pair x #> f)
fun change f x = access f x >>= put () >>= arr (fn _ => x)
end
end

