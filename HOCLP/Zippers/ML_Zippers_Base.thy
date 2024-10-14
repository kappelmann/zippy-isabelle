\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Zippers\<close>
theory ML_Zippers_Base
  imports
    ML_Typeclasses.ML_Lenses
begin

(*TODO: move*)
ML\<open>
signature GLIST =
sig

structure A : IARROW_EXCEPTION_BASE

type 'a t
val empty : 'a t
val cons : 'a -> 'a t -> 'a t
val from_list : 'a list -> 'a t

val is_empty : 'a t -> bool
val dest : ('i, 'i, 'a t, 'a * 'a t) A.cat
val foldl : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
end

functor GList(M : IMONAD_EXCEPTION_BASE where type exn = unit) : GLIST =
struct
  structure A = IKleisli_Arrow_Exception(M)
  type 'a t = 'a list
  val empty = []
  val is_empty = null
  val foldl = fold
  val cons = cons
  fun dest [] = M.throw ()
    | dest (x :: xs) = M.pure (x, xs)
  val from_list : 'a list -> 'a t = I
end
\<close>

ML_file\<open>zipper_direction.ML\<close>

ML_file\<open>zipper_data.ML\<close>

end