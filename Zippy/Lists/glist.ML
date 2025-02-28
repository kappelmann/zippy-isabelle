(*  Title:      HOCLP/glist.ML
    Author:     Kevin Kappelmann

Generalised lists.
*)
signature GLIST =
sig
  structure M : MONAD_EXCEPTION_BASE

  type 'a t
  val empty : 'a t
  val cons : 'a -> 'a t -> 'a t
  val from_list : 'a list -> 'a t

  val is_empty : 'a t -> bool
  val dest : 'a t -> ('p1, 'a * 'a t) M.t
  val foldl : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val nth : 'a t -> int -> ('p1, 'a) M.t
  val length : 'a t -> int
end

functor GList(M : MONAD_EXCEPTION_BASE where type 'p1 exn = unit) : GLIST where type 'a t = 'a list =
struct
  structure M = M
  type 'a t = 'a list
  val empty = []
  val is_empty = null
  val foldl = fold
  val cons = cons
  fun dest [] = M.throw ()
    | dest (x :: xs) = M.pure (x, xs)
  val from_list = I
  fun nth xs n = nth xs n handle Subscript => M.throw ()
  val length =length
end