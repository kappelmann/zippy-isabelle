(*  Title:  category_instance.ML
    Author: Kevin Kappelmann

Instances of categories.
*)
(*standard function space*)
structure SArrow_Apply : ARROW_APPLY_BASE =
struct

type ('p1, 'a, 'b) cat = 'a -> 'b
fun id _ = I
fun comp f g x = f (g x)
val arr = I
fun (f *** g) (x, y) = (f x, g y)
fun app (f, x) = f x

end

structure SLazy_Comp : LAZY_COMP =
struct

open SArrow_Apply
fun comp_lazy f g x = f () (g x)

end

(*Kleisli category*)
signature KLEISLI =
sig
  structure M : MONAD_BASE
  type ('p1, 'a, 'b) kleisli = 'a -> ('p1, 'b) M.t
end

functor Kleisli(M : MONAD_BASE) : KLEISLI =
struct
structure M = M
type ('p1, 'a, 'b) kleisli = 'a -> ('p1, 'b) M.t
end

functor Kleisli_Arrow_Apply_Choice(M : MONAD_BASE) :
  sig
    include KLEISLI
    include ARROW_APPLY_BASE
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) kleisli
    val cases : ('p1, 'a, 'c) cat -> ('p1, 'b, 'd) cat ->
      ('p1, ('a, 'b) Either.either, ('c, 'd) Either.either) cat
    val merge : ('p1, 'a, 'c) cat -> ('p1, 'b, 'c) cat ->
      ('p1, ('a, 'b) Either.either, 'c) cat
    val comp_lazy : (unit -> ('p1, 'b, 'c) cat) -> ('p1, 'a, 'b) cat -> ('p1, 'a, 'c) cat
  end =
struct

structure K = Kleisli(M)
open K
structure M = Monad(M) open M

type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) kleisli
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
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) kleisli
  end =
struct

structure KAA = Kleisli_Arrow_Apply_Choice(MZ)
open KAA

fun zero _ _ = MZ.zero ()

end

functor Kleisli_Arrow_Plus(MP : MONAD_PLUS_BASE) : sig
    include KLEISLI
    include ARROW_PLUS_BASE
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) kleisli
  end =
struct

structure KAZ = Kleisli_Arrow_Zero(MP)
open KAZ

fun plus f g x = MP.plus_lazy (f x) (fn _ => g x)

end

functor Kleisli_Arrow_Or(MO : MONAD_OR_BASE) : sig
    include KLEISLI
    include ARROW_OR_BASE
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) kleisli
  end =
struct

structure KAZ = Kleisli_Arrow_Zero(MO)
open KAZ

fun or f g x = MO.or_lazy (f x) (fn _ => g x)

end

functor Kleisli_Arrow_Exception(ME : MONAD_EXCEPTION_BASE) : sig
    include KLEISLI
    include ARROW_EXCEPTION_BASE
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) kleisli
  end =
struct

structure KA = Kleisli_Arrow_Apply_Choice(ME)
open KA

type exn = ME.exn

val throw = ME.throw
fun catch f g x = ME.catch (f x) (g o pair x)

end
