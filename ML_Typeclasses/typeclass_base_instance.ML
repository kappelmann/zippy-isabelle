(*  Title: typeclass_base_instance.ML
    Author: Kevin Kappelmann

Instances of basic typeclasses.
*)
structure Identity_Monad : MONAD_BASE =
struct

type 'a t = 'a
fun map f x = f x
fun pure x = x
fun <*> f x = f x
fun bind x f = f x

end

structure Identity_Foldable : FOLDABLE_BASE =
struct

type 'a f = 'a
fun foldl f x acc = f x acc
fun foldr f x acc = f x acc

end

functor Identity_Traversable(A : APPLICATIVE_BASE) : TRAVERSABLE_BASE =
struct

open Identity_Monad
open Identity_Foldable

structure A = A
fun traverse f x = f x

end

functor Seq_Functor_Trans(F : FUNCTOR_BASE) : FUNCTOR_TRANS =
struct

structure F = F

type 'a t = 'a Seq.seq F.t
fun lift x = F.map Seq.single x
fun map f = F.map (Seq.map f)

end

functor Seq_Foldable_Trans(F : FOLDABLE_BASE) : FOLDABLE_BASE =
struct

type 'a f = 'a Seq.seq F.f

fun fold_base step sq acc = case Seq.pull sq of
    SOME (x, sq) => step (fold_base step sq) x acc
  | NONE => acc

fun foldl f = F.foldl (fold_base (fn frec => frec oo f))
fun foldr f = F.foldr (fold_base (fn frec => fn x => f x o frec))

end

functor Seq_Traversable_Trans(T : TRAVERSABLE_BASE) : TRAVERSABLE_TRANS =
struct

structure T = T
structure F = Seq_Functor_Trans(T)
open F
structure F = Seq_Foldable_Trans(T)
open F
structure F = Seq_Foldable_Trans(Identity_Foldable)

structure A = Applicative(T.A)
fun traverse f = T.traverse (fn sq => F.foldr (A.liftA2 Seq.cons o f) sq (A.pure Seq.empty))

end

(*Note: this does not yield a monad unless the argument monad is commutative.*)
functor Seq_Monad_Trans(M : MONAD_BASE) : MONAD_TRANS =
struct

structure M = M
structure F = Seq_Functor_Trans(M)
open F

structure F = Seq_Functor_Trans(Identity_Monad)
structure T = Seq_Traversable_Trans(Identity_Traversable(M))

fun pure x = M.pure (Seq.single x)
fun <*> f x = M.bind x (fn x => M.bind f (Seq.maps (fn f => F.map f x) #> M.pure))

fun bind x f = M.bind x (fn x => M.bind (T.traverse f x) (Seq.flat #> M.pure))

end

functor List_Functor_Trans(F : FUNCTOR_BASE) : FUNCTOR_TRANS =
struct

structure F = F

type 'a t = 'a list F.t
fun lift x = F.map single x
fun map f = F.map (List.map f)

end

functor List_Foldable_Trans(F : FOLDABLE_BASE) : FOLDABLE_BASE =
struct

type 'a f = 'a list F.f

fun fold_base step [] = I
  | fold_base step (x :: xs) = step (fold_base step xs) x

fun foldl f = F.foldl (fold_base (fn frec => frec oo f))
fun foldr f = F.foldr (fold_base (fn frec => fn x => f x o frec))

end

functor List_Traversable_Trans(T : TRAVERSABLE_BASE) : TRAVERSABLE_TRANS =
struct

structure T = T
structure F = List_Functor_Trans(T)
open F
structure F = List_Foldable_Trans(T)
open F
structure F = List_Foldable_Trans(Identity_Foldable)

structure A = Applicative(T.A)
fun traverse f = T.traverse (fn sq => F.foldr (A.liftA2 cons o f) sq (A.pure []))

end

(*Note: this does not yield a monad unless the argument monad is commutative;
cf https://wiki.haskell.org/ListT_done_right*)
functor List_Monad_Trans(M : MONAD_BASE) : MONAD_TRANS =
struct

structure M = M
structure F = List_Functor_Trans(M)
open F

structure F = List_Functor_Trans(Identity_Monad)
structure T = List_Traversable_Trans(Identity_Traversable(M))

fun pure x = M.pure (single x)
fun <*> f x = M.bind x (fn x => M.bind f (maps (fn f => F.map f x) #> M.pure))

fun bind x f = M.bind x (fn x => M.bind (T.traverse f x) (flat #> M.pure))

end

functor Option_Functor_Trans(F : FUNCTOR_BASE) : FUNCTOR_TRANS =
struct

structure F = F

type 'a t = 'a option F.t
fun lift x = F.map SOME x
fun map f = F.map (Option.map f)

end

functor Option_Monad_Trans(M : MONAD_BASE) : MONAD_TRANS =
struct

structure M = M
structure F = Option_Functor_Trans(M)
open F

fun pure x = M.pure (SOME x)
fun <*> f x = M.bind f (fn NONE => M.pure NONE | SOME f => map f x)
fun bind x f = M.bind x (fn NONE => M.pure NONE | SOME x => f x)

end

functor Option_Monad_Plus(M : MONAD_BASE) : MONAD_PLUS_BASE =
struct

structure OM = Option_Monad_Trans(M)
open OM

fun zero _ = M.pure NONE
fun plus x y = OM.M.bind x (fn NONE => y | x => M.pure x)

end

functor Option_Foldable_Trans(F : FOLDABLE_BASE) : FOLDABLE_BASE =
struct

type 'a f = 'a option F.f

fun fold_base _ NONE = I
  | fold_base f (SOME x) = f x
fun foldl f = F.foldl (fold_base f)
fun foldr f = F.foldr (fold_base f)

end

functor Option_Traversable_Trans(T : TRAVERSABLE_BASE) : TRAVERSABLE_TRANS =
struct

structure T = T
structure F = Option_Functor_Trans(T)
open F
structure F = Option_Foldable_Trans(T)
open F

structure A = Applicative(T.A)
fun traverse f = T.traverse (fn NONE => A.pure NONE | SOME x => A.map SOME (f x))

end

