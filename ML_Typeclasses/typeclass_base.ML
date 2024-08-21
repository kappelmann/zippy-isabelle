(*  Title:  typeclass_base.ML
    Author: Kevin Kappelmann

Basic typeclasses inspired by the Haskell Prelude, monad-transformers, and the mtl package.
*)
infix 1 <*>
infix 1 >>=
infix 1 >=>
infix 1 <&>

signature FUNCTOR_BASE =
sig
  type 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
end

signature FUNCTOR =
sig
  include FUNCTOR_BASE
  val <&> : 'a t * ('a -> 'b) -> 'b t
end

functor Functor(F : FUNCTOR_BASE) : FUNCTOR =
struct

open F
fun x <&> f = map f x

end

signature FUNCTOR_TRANS =
sig
  (*the base functor to transform*)
  structure F : FUNCTOR_BASE
  include FUNCTOR_BASE
  val lift : 'a F.t -> 'a t
end

signature APPLICATIVE_BASE =
sig
  include FUNCTOR_BASE
  val pure : 'a -> 'a t
  val <*> : ('a -> 'b) t * 'a t -> 'b t
end

signature APPLICATIVE =
sig
  include APPLICATIVE_BASE
  val liftA2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
end

functor Applicative(A : APPLICATIVE_BASE) : APPLICATIVE =
struct

open A
fun liftA2 f x = curry (op <*>) (A.map f x)

end

signature APPLICATIVE_TRANS =
sig
  (*the base applicative to transform*)
  structure A : APPLICATIVE_BASE
  include APPLICATIVE_BASE
  val lift : 'a A.t -> 'a t
end

signature MONAD_BASE =
sig
  include APPLICATIVE_BASE
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

signature MONAD =
sig
  include MONAD_BASE
  val >>= : 'a t * ('a -> 'b t) -> 'b t
  val join : ('a t) t -> 'a t
  val >=> : ('a -> 'b t) * ('b -> 'c t) -> 'a -> 'c t
  val flat1 : ('a -> 'b t) t -> 'a -> 'b t
  val flat2 : ('a -> 'b -> 'c t) t -> 'a -> 'b -> 'c t
end

functor Monad(M : MONAD_BASE) : MONAD =
struct

open M
fun x >>= f = bind x f
fun join x = x >>= I
fun (fm >=> gm) x = fm x >>= gm
fun flat1 fm x = fm >>= (fn f => f x)
fun flat2 fm x = M.map (fn f => f x) fm |> flat1

end

signature MONAD_TRANS =
sig
  (*the base monad to transform*)
  structure M : MONAD_BASE
  include MONAD_BASE

  val lift : 'a M.t -> 'a t
end

signature ALTERNATIVE_BASE =
sig
  include APPLICATIVE_BASE
  (*laws: (empty, <|>) forms a monoid on 'a t*)
  val empty : unit -> 'a t
  val <|> : 'a t -> 'a t -> 'a t
end

signature ALTERNATIVE =
sig
  include ALTERNATIVE_BASE
  val optional : 'a t -> 'a option t
end

functor Alternative(A : ALTERNATIVE_BASE) : ALTERNATIVE =
struct

open A
fun optional x = A.<|> (A.map SOME x) (A.pure NONE)

end

signature MONAD_ZERO_BASE =
sig
  include MONAD_BASE
  val zero : unit -> 'a t
end

signature MONAD_PLUS_BASE =
sig
  include MONAD_ZERO_BASE
  (*satisfies left distribution law: "plus x y >>= f = plus (x >>= f) (y >>= f)"*)
  val plus_lazy : 'a t -> (unit -> 'a t) -> 'a t
end

signature MONAD_PLUS =
sig
  include MONAD_PLUS_BASE
  val plus : 'a t -> 'a t -> 'a t
end

functor Monad_Plus(M : MONAD_PLUS_BASE) : MONAD_PLUS =
struct
  open M
  fun plus x y = M.plus_lazy x (K y)
end

signature MONAD_OR_BASE =
sig
  include MONAD_ZERO_BASE
  (*satisfies left catch law: "or (pure x) y = pure x"*)
  val or_lazy : 'a t -> (unit -> 'a t) -> 'a t
end

signature MONAD_OR =
sig
  include MONAD_OR_BASE
  val or : 'a t -> 'a t -> 'a t
end

functor Monad_Or(M : MONAD_OR_BASE) : MONAD_OR =
struct
  open M
  fun or x y = M.or_lazy x (K y)
end

signature MONAD_EXCEPTION_BASE =
sig
  include MONAD_BASE
  type exn
  val throw : exn -> 'a t
  val catch : 'a t -> (exn -> 'a t) -> 'a t
end

signature FOLDABLE_BASE =
sig
  type 'a f
  val foldl : ('a -> 'b -> 'b) -> 'a f -> 'b -> 'b
  val foldr : ('a -> 'b -> 'b) -> 'a f -> 'b -> 'b
end

signature TRAVERSABLE_BASE =
sig
  include FUNCTOR_BASE
  include FOLDABLE_BASE
  sharing type t = f

  structure A : APPLICATIVE_BASE

  val traverse : ('a -> 'b A.t) -> 'a t -> 'b t A.t
end

signature TRAVERSABLE =
sig
  include TRAVERSABLE_BASE
  val sequence : ('a A.t) t -> ('a t) A.t
end

functor Traversable(T : TRAVERSABLE_BASE) : TRAVERSABLE =
struct

open T
fun sequence x = traverse I x

end

signature TRAVERSABLE_TRANS =
sig
  (*the base traversable to transform*)
  structure T : TRAVERSABLE_BASE
  include TRAVERSABLE_BASE
  val lift : 'a T.t -> 'a t
end

