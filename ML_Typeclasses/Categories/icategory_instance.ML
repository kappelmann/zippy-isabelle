(*  Title:  icategory_instance.ML
    Author: Kevin Kappelmann

Instances of indexed categories.
*)
signature IKLEISLI =
sig

structure IM : IMONAD_BASE
type ('i, 'o, 'a, 'b) kleisli = 'a -> ('i, 'o, 'b) IM.t

end

functor Kleisli_IKleisli(structure IK : IKLEISLI; structure T : GROUND_TYPE) : KLEISLI =
struct

structure M = Monad_IMonad(structure IM = IK.IM; structure T = T)
type ('a, 'b) kleisli = (T.t, T.t, 'a, 'b) IK.kleisli

end

(*Indexed Kleisli category*)
functor IKleisli_IArrow_Apply(IM : IMONAD_BASE) : sig
    include IKLEISLI
    include IARROW_APPLY_BASE
    where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) kleisli
  end =
struct

structure IM = IM
type ('i, 'o, 'a, 'b) kleisli = 'a -> ('i, 'o, 'b) IM.t

type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) kleisli
fun id _ = IM.pure
fun comp k1 k2 = (fn x => IM.bind (k2 x) (k1))
fun arr f = (IM.pure o f)
fun *** k1 k2 = (fn (x, y) => IM.bind (k1 x)
  (fn x' => IM.bind (k2 y)
  (fn y' => IM.pure (x', y'))))
fun app (f, x) = f x

end

functor IKleisli_IArrow_Plus(IMP : IMONAD_PLUS_BASE) : sig
    include IKLEISLI
    include IARROW_PLUS_BASE
    where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) kleisli
  end =
struct

structure IKAA = IKleisli_IArrow_Apply(IMP)
open IKAA

fun zero _ _ = IMP.zero ()
fun plus f g x = IMP.plus (f x) (g x)

end

