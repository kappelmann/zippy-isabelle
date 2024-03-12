(*  Title:  itypeclass_base.ML
    Author: Kevin Kappelmann

Basic indexed typeclasses (in Atkey-style),
inspired by the Haskell Prelude and "Parameterised Notions of Computation" by Robert Atkey.
*)
signature IFUNCTOR_BASE =
sig

type ('i, 'o, 'a) t
(*TODO: should we also require contravariant in first and covariance in second parameter?
cf. paper by Atkey*)
val map : ('a -> 'b) -> ('i, 'o, 'a) t -> ('i, 'o, 'b) t

end

(*In general, we would like to get a Functor from an IFunctor for arbitrary index types;
but the best we can do in SML is to create an instance for an arbitrary but fixed ground index type.*)
signature GROUND_TYPE = sig type t end

functor Functor_IFunctor(structure IF : IFUNCTOR_BASE; structure T : GROUND_TYPE) : FUNCTOR_BASE =
struct

type 'a t = (T.t, T.t, 'a) IF.t
fun map f = IF.map f

end

signature IAPPLICATIVE_BASE =
sig

include IFUNCTOR_BASE
val pure : 'a -> ('i, 'i, 'a) t
val <*> : ('i, 'j, 'a -> 'b) t -> ('j, 'k, 'a) t -> ('i, 'k, 'b) t

end

functor Applicative_IApplicative(
    structure IA : IAPPLICATIVE_BASE;
    structure T : GROUND_TYPE
  ) : APPLICATIVE_BASE =
struct

structure F = Functor_IFunctor(structure IF = IA; structure T = T)
open F
val pure = IA.pure
val <*> = IA.<*>

end

signature IMONAD_BASE =
sig

include IAPPLICATIVE_BASE
val bind : ('i, 'j, 'a) t -> ('a -> ('j, 'k, 'b) t) -> ('i, 'k, 'b) t

end

functor Monad_IMonad(structure IM : IMONAD_BASE; structure T : GROUND_TYPE) : MONAD_BASE =
struct

structure A = Applicative_IApplicative(structure IA = IM; structure T = T)
open A
val bind = IM.bind

end

signature IMONAD =
sig

include IMONAD_BASE
val join : ('i, 'j, ('j, 'k, 'a) t) t -> ('i, 'k, 'a) t
val >=> : ('a -> ('i, 'j, 'b) t) -> ('b -> ('j, 'k, 'c) t) -> 'a -> ('i, 'k, 'c) t

end

functor IMonad(M : IMONAD_BASE) : IMONAD =
struct

open M
fun join x = bind x I
fun >=> fm gm x = bind (fm x) gm

end

signature IMONAD_TRANS =
sig

(*the base monad to transform*)
structure M : MONAD_BASE
include IMONAD_BASE

val lift : 'a M.t -> ('i, 'i, 'a) t

end

functor Monad_Trans_IMonad_Trans(structure IMT : IMONAD_TRANS; structure T : GROUND_TYPE) : MONAD_TRANS =
struct

structure M = IMT.M
structure M' = Monad_IMonad(structure IM = IMT; structure T = T)
open M'

val lift = IMT.lift

end

signature IMONAD_PLUS_BASE =
sig

include IMONAD_BASE
val zero : unit -> ('i, 'i, 'a) t
val plus : ('i, 'j, 'a) t -> ('i, 'j, 'a) t -> ('i, 'j, 'a) t

end

functor Monad_Plus_IMonad_Plus(structure IMP : IMONAD_PLUS_BASE; structure T : GROUND_TYPE) :
  MONAD_PLUS_BASE =
struct

structure M = Monad_IMonad(structure IM = IMP; structure T = T)
open M
val zero = IMP.zero
val plus = IMP.plus

end