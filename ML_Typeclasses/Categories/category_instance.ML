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
val arr = I
fun *** f g (x, y) = (f x, g y)
fun app (f, x) = f x

end

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
functor Kleisli_Arrow_Apply(M : MONAD_BASE) : sig
    include KLEISLI
    include ARROW_APPLY_BASE
    where type ('a, 'b) cat = ('a, 'b) kleisli
  end =
struct

structure K = Kleisli(M)
open K

type ('a, 'b) cat = ('a, 'b) kleisli
fun id _ = M.pure
fun comp k1 k2 = (fn x => M.bind (k2 x) k1)
fun arr f = M.pure o f
fun *** k1 k2 = (fn (x, y) => M.bind (k1 x)
  (fn x' => M.bind (k2 y)
  (fn y' => M.pure (x', y'))))
fun app (f, x) = f x

end

functor Kleisli_Arrow_Plus(MP : MONAD_PLUS_BASE) : sig
    include KLEISLI
    include ARROW_PLUS_BASE
    where type ('a, 'b) cat = ('a, 'b) kleisli
  end =
struct

structure KAA = Kleisli_Arrow_Apply(MP)
open KAA

fun zero _ _ = MP.zero ()
fun plus f g x = MP.plus (f x) (g x)

end
