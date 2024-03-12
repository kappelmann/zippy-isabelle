\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Zippers\<close>
theory ML_Zippers
  imports
    ML_Typeclasses.ML_Lenses
begin

(*TODO: list type*)
ML\<open>
structure List =
struct
  type 'a t = 'a list
  val empty = []
  val is_empty = null
  val fold = fold
  val cons = cons
  fun dest [] = NONE
    | dest (x :: xs) = SOME (x, xs)
  val from_list : 'a list -> 'a t = I
end
\<close>

ML_file\<open>zipper_base.ML\<close>
ML_file\<open>zipper_data.ML\<close>
ML_file\<open>bi_zipper.ML\<close>
ML_file\<open>bi_zipper_extend.ML\<close>
ML_file\<open>zipper.ML\<close>
ML_file\<open>zipper_enumerable.ML\<close>

end