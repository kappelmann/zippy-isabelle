(*  Title:  itypeclass_base.ML
    Author: Kevin Kappelmann

Basic indexed typeclasses (in Atkey-style),
inspired by the Haskell Prelude and "Parameterised Notions of Computation" by Robert Atkey.
*)
signature IFUNCTOR_BASE =
sig

type ('i, 'o, 'a) t
(*TODO: should we also require contravariance in first and covariance in second parameter?
cf. paper by Atkey*)
val map : ('a -> 'b) -> ('i, 'o, 'a) t -> ('i, 'o, 'b) t

end

functor IFunctor_Functor(F : FUNCTOR_BASE) : IFUNCTOR_BASE =
struct
open F
type ('i, 'o, 'a) t = 'a t
end

(*In general, we would like to get a Functor from an IFunctor for an arbitrary (polymorphic) index type;
but the best we can do in SML is to create an instance for an arbitrary but fixed ground index type.*)
signature GROUND_TYPE = sig type t end

functor Functor_IFunctor(structure F : IFUNCTOR_BASE; structure T : GROUND_TYPE) : FUNCTOR_BASE =
struct
open F
type 'a t = (T.t, T.t, 'a) F.t
end

signature IFUNCTOR =
sig
  include IFUNCTOR_BASE
  val <&> : ('i, 'o, 'a) t * ('a -> 'b) -> ('i, 'o, 'b) t
end

functor IFunctor(F : IFUNCTOR_BASE) : IFUNCTOR =
struct

open F
fun x <&> f = map f x

end

signature IFUNCTOR_TRANS =
sig
  (*the base functor to transform*)
  structure F : FUNCTOR_BASE
  include IFUNCTOR_BASE
  val lift : 'a F.t -> ('i, 'i, 'a) t
end

functor IFunctor_Trans_Functor_Trans(FT : FUNCTOR_TRANS) : IFUNCTOR_TRANS =
struct
open FT
structure F' = IFunctor_Functor(FT)
open F'
end

functor Functor_Trans_IFunctor_Trans(structure FT : IFUNCTOR_TRANS; structure T : GROUND_TYPE)
  : FUNCTOR_TRANS =
struct
open FT
structure F' = Functor_IFunctor(structure F = FT; structure T = T)
open F'
end

signature IAPPLICATIVE_BASE =
sig

include IFUNCTOR_BASE
val pure : 'a -> ('i, 'i, 'a) t
val <*> : ('i, 'j, 'a -> 'b) t * ('j, 'k, 'a) t -> ('i, 'k, 'b) t

end

functor IApplicative_Applicative(A : APPLICATIVE_BASE) : IAPPLICATIVE_BASE =
struct
open A
structure F = IFunctor_Functor(A)
open F
end

functor Applicative_IApplicative(
    structure A : IAPPLICATIVE_BASE
    structure T : GROUND_TYPE
  ) : APPLICATIVE_BASE =
struct
open A
structure F = Functor_IFunctor(structure F = A; structure T = T)
open F
end

signature IMONAD_BASE =
sig

include IAPPLICATIVE_BASE
val bind : ('i, 'j, 'a) t -> ('a -> ('j, 'k, 'b) t) -> ('i, 'k, 'b) t

end

functor IMonad_Monad(M : MONAD_BASE) : IMONAD_BASE =
struct
open M
structure A = IApplicative_Applicative(M)
open A
end

functor Monad_IMonad(structure M : IMONAD_BASE; structure T : GROUND_TYPE) : MONAD_BASE =
struct
open M
structure A = Applicative_IApplicative(structure A = M; structure T = T)
open A
end

signature IMONAD =
sig

include IMONAD_BASE
val >>= : ('i, 'j, 'a) t * ('a -> ('j, 'k, 'b) t) -> ('i, 'k, 'b) t
val join : ('i, 'j, ('j, 'k, 'a) t) t -> ('i, 'k, 'a) t
val >=> : ('a -> ('i, 'j, 'b) t) * ('b -> ('j, 'k, 'c) t) -> 'a -> ('i, 'k, 'c) t

end

functor IMonad(M : IMONAD_BASE) : IMONAD =
struct

open M
fun m >>= f = bind m f
fun join x = bind x I
fun (fm >=> gm) x = fm x >>= gm

end

signature IMONAD_TRANS =
sig

(*the base monad to transform*)
structure M : MONAD_BASE
include IMONAD_BASE

val lift : 'a M.t -> ('i, 'i, 'a) t

end

functor IMonad_Trans_Monad_Trans(MT : MONAD_TRANS) : IMONAD_TRANS =
struct
open MT
structure M' = IMonad_Monad(MT)
open M'
end

functor Monad_Trans_IMonad_Trans(structure MT : IMONAD_TRANS; structure T : GROUND_TYPE) : MONAD_TRANS =
struct
open MT
structure M' = Monad_IMonad(structure M = MT; structure T = T)
open M'
end

signature IMONAD_ZERO_BASE =
sig
include IMONAD_BASE
val zero : unit -> ('i, 'i, 'a) t
end

functor IMonad_Zero_Monad_Zero(MO : MONAD_ZERO_BASE) : IMONAD_ZERO_BASE =
struct
open MO
structure M = IMonad_Monad(MO)
open M
end

functor Monad_Zero_IMonad_Zero(structure MO : IMONAD_ZERO_BASE; structure T : GROUND_TYPE)
  : MONAD_ZERO_BASE =
struct
open MO
structure M = Monad_IMonad(structure M = MO; structure T = T)
open M
end

signature IMONAD_PLUS_BASE =
sig
include IMONAD_ZERO_BASE
(*satisfies left distribution law: "plus x y >>= f = plus (x >>= f) (y >>= f)"*)
val plus_lazy : ('i, 'j, 'a) t -> (unit -> ('i, 'j, 'a) t) -> ('i, 'j, 'a) t
end

functor IMonad_Plus_Monad_Plus(MP : MONAD_PLUS_BASE) : IMONAD_PLUS_BASE =
struct
open MP
structure MZ = IMonad_Zero_Monad_Zero(MP)
open MZ
end

functor Monad_Plus_IMonad_Plus(structure MP : IMONAD_PLUS_BASE; structure T : GROUND_TYPE)
  : MONAD_PLUS_BASE =
struct
open MP
structure MZ = Monad_Zero_IMonad_Zero(structure MO = MP; structure T = T)
open MZ
end

signature IMONAD_OR_BASE =
sig
include IMONAD_ZERO_BASE
(*satisfies left catch law: "or (pure x) y = pure x"*)
val or_lazy : ('i, 'j, 'a) t -> (unit -> ('i, 'j, 'a) t) -> ('i, 'j, 'a) t
end

functor IMonad_Or_Monad_Or(MO : MONAD_OR_BASE) : IMONAD_OR_BASE =
struct
open MO
structure MZ = IMonad_Zero_Monad_Zero(MO)
open MZ
end

functor Monad_Or_IMonad_Or(structure MO : IMONAD_OR_BASE; structure T : GROUND_TYPE) :
  MONAD_OR_BASE =
struct
open MO
structure MZ = Monad_IMonad(structure M = MO; structure T = T)
open MZ
end

signature IMONAD_EXCEPTION_BASE =
sig
  include IMONAD_BASE
  type exn
  val throw : exn -> ('i, 'i, 'a) t
  val catch : ('i, 'j, 'a) t -> (exn -> ('i, 'j, 'a) t) -> ('i, 'j, 'a) t
end

functor IMonad_Exception_Monad_Exception(ME : MONAD_EXCEPTION_BASE)
  : IMONAD_EXCEPTION_BASE =
struct
open ME
structure M = IMonad_Monad(ME)
open M
end

functor Monad_Exception_IMonad_Exception(structure ME : IMONAD_EXCEPTION_BASE; structure T : GROUND_TYPE)
  : MONAD_EXCEPTION_BASE =
struct
open ME
structure M = Monad_IMonad(structure M = ME; structure T = T)
open M
end
