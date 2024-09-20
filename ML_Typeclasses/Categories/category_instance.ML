(*  Title:  category_instance.ML
    Author: Kevin Kappelmann

Instances of categories.
*)
structure SArrow_Apply : ARROW_APPLY_BASE =
struct

(*standard function space*)
type ('a, 'b) cat = 'a -> 'b
fun id _ = I
fun comp f g x = f (g x)
fun comp_lazy f g x = f () (g x)
val arr = I
fun (f *** g) (x, y) = (f x, g y)
fun app (f, x) = f x

end

(*Kleisli category*)

signature KLEISLI =
sig
  structure M : MONAD_BASE
  type ('a, 'b) kleisli = 'a -> 'b M.t
end

functor Kleisli(M : MONAD_BASE) : KLEISLI =
struct
structure M = M
type ('a, 'b) kleisli = 'a -> 'b M.t
end

(*Kleisli category*)
functor Kleisli_Arrow_Apply_Choice(M : MONAD_BASE) :
  sig
    include KLEISLI
    include ARROW_APPLY_BASE
    where type ('a, 'b) cat = ('a, 'b) kleisli
    val cases : ('a, 'c) cat -> ('b, 'd) cat -> (('a, 'b) Either.either, ('c, 'd) Either.either) cat
    val merge : ('a, 'c) cat -> ('b, 'c) cat -> (('a, 'b) Either.either, 'c) cat
  end =
struct

structure K = Kleisli(M)
open K
structure M = Monad(M) open M

type ('a, 'b) cat = ('a, 'b) kleisli
fun id _ = pure
fun comp k1 k2 x = k2 x >>= k1
fun comp_lazy k1 k2 = comp (fn x => k1 () x) k2
fun arr f = pure o f
fun k1 *** k2 = (fn (x, y) => k1 x
  >>= (fn x' => k2 y
  >>= (fn y' => pure (x', y'))))
fun app (f, x) = f x
fun cases f _ (Either.Left x) = M.map Either.Left (f x)
  | cases _ g (Either.Right y) = M.map Either.Right (g y)
fun merge f _ (Either.Left x) = f x
  | merge _ g (Either.Right y) = g y

end

functor Kleisli_Arrow_Zero(MZ : MONAD_ZERO_BASE) : sig
    include KLEISLI
    include ARROW_ZERO_BASE
    where type ('a, 'b) cat = ('a, 'b) kleisli
  end =
struct

structure KAA = Kleisli_Arrow_Apply_Choice(MZ)
open KAA

fun zero _ _ = MZ.zero ()

end

functor Kleisli_Arrow_Plus(MP : MONAD_PLUS_BASE) : sig
    include KLEISLI
    include ARROW_PLUS_BASE
    where type ('a, 'b) cat = ('a, 'b) kleisli
  end =
struct

structure KAZ = Kleisli_Arrow_Zero(MP)
open KAZ

fun plus f g x = MP.plus_lazy (f x) (fn _ => g x)

end

functor Kleisli_Arrow_Or(MO : MONAD_OR_BASE) : sig
    include KLEISLI
    include ARROW_OR_BASE
    where type ('a, 'b) cat = ('a, 'b) kleisli
  end =
struct

structure KAZ = Kleisli_Arrow_Zero(MO)
open KAZ

fun or f g x = MO.or_lazy (f x) (fn _ => g x)

end

functor Kleisli_Arrow_Exception(ME : MONAD_EXCEPTION_BASE) : sig
    include KLEISLI
    include ARROW_EXCEPTION_BASE
    where type ('a, 'b) cat = ('a, 'b) kleisli
  end =
struct

structure KA = Kleisli_Arrow_Apply_Choice(ME)
open KA

type exn = ME.exn

val throw = ME.throw
fun catch f g x = ME.catch (f x) (g o pair x)

end

