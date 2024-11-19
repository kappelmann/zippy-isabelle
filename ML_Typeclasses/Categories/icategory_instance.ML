(*  Title:  icategory_instance.ML
    Author: Kevin Kappelmann

Instances of indexed categories.
*)

(*Indexed Kleisli category*)
signature IKLEISLI =
sig
  structure M : IMONAD_BASE
  type ('p1, 'i, 'o, 'a, 'b) kleisli = 'a -> ('p1, 'i, 'o, 'b) M.t
end

functor IKleisli(M : IMONAD_BASE) : IKLEISLI =
struct
structure M = M
type ('p1, 'i, 'o, 'a, 'b) kleisli = 'a -> ('p1, 'i, 'o, 'b) M.t
end

functor IKleisli_Arrow_Apply_Choice(M : IMONAD_BASE) :
  sig
    include IKLEISLI
    include IARROW_APPLY_BASE
    where type ('p1, 'i, 'o, 'a, 'b) cat = ('p1, 'i, 'o, 'a, 'b) kleisli
    val cases : ('p1, 'i, 'j, 'a, 'c) cat -> ('p1, 'i, 'j, 'b, 'd) cat ->
      ('p1, 'i, 'j, ('a, 'b) Either.either, ('c, 'd) Either.either) cat
    val merge : ('p1, 'i, 'j, 'a, 'c) cat -> ('p1, 'i, 'j, 'b, 'c) cat ->
      ('p1, 'i, 'j, ('a, 'b) Either.either, 'c) cat
    val comp_lazy : (unit -> ('p1, 'j, 'k, 'b, 'c) cat) -> ('p1, 'i, 'j, 'a, 'b) cat ->
      ('p1, 'i, 'k, 'a, 'c) cat
  end =
struct

structure M = M
structure K = IKleisli(M)
open K

structure M = IMonad(M) open M
type ('p1, 'i, 'o, 'a, 'b) cat = ('p1, 'i, 'o, 'a, 'b) kleisli
fun id _ = pure
fun comp k1 k2 = (fn x => k2 x >>= k1)
fun comp_lazy k1 k2 = comp (fn x => k1 () x) k2
fun arr f = (pure o f)
fun k1 *** k2 = (fn (x, y) => k1 x
  >>= (fn x' => k2 y
  >>= (fn y' => pure (x', y'))))
fun app (f, x) = f x
fun cases f _ (Either.Left x) = M.map Either.Left (f x)
  | cases _ g (Either.Right y) = M.map Either.Right (g y)
fun merge f _ (Either.Left x) = f x
  | merge _ g (Either.Right y) = g y

end

functor IKleisli_Arrow_Zero(MZ : IMONAD_ZERO_BASE) : sig
    include IKLEISLI
    include IARROW_ZERO_BASE
    where type ('p1, 'i, 'o, 'a, 'b) cat = ('p1, 'i, 'o, 'a, 'b) kleisli
  end =
struct

structure IKAA = IKleisli_Arrow_Apply_Choice(MZ)
open IKAA
fun zero _ _ = MZ.zero ()
end

functor IKleisli_Arrow_Plus(MP : IMONAD_PLUS_BASE) : sig
    include IKLEISLI
    include IARROW_PLUS_BASE
    where type ('p1, 'i, 'o, 'a, 'b) cat = ('p1, 'i, 'o, 'a, 'b) kleisli
  end =
struct
structure KAZ = IKleisli_Arrow_Zero(MP)
open KAZ
fun plus f g x = MP.plus_lazy (f x) (fn _ => g x)
end

functor IKleisli_Arrow_Or(MO : IMONAD_OR_BASE) : sig
    include IKLEISLI
    include IARROW_OR_BASE
    where type ('p1, 'i, 'o, 'a, 'b) cat = ('p1, 'i, 'o, 'a, 'b) kleisli
  end =
struct
structure KAZ = IKleisli_Arrow_Zero(MO)
open KAZ
fun or f g x = MO.or_lazy (f x) (fn _ => g x)
end

functor IKleisli_Arrow_Exception(ME : IMONAD_EXCEPTION_BASE) :
  sig
    include IKLEISLI
    include IARROW_EXCEPTION_BASE
    where type ('p1, 'i, 'o, 'a, 'b) cat = ('p1, 'i, 'o, 'a, 'b) kleisli
  end =
struct

structure KA = IKleisli_Arrow_Apply_Choice(ME)
open KA
type exn = ME.exn

val throw = ME.throw
fun catch f g x = ME.catch (f x) (g o pair x)
end
