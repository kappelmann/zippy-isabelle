(*  Title:      Zippy/df_preorder_enumerate_zipper.ML
    Author:     Kevin Kappelmann
*)
(*preconditions:
1) Down.move moves to leftmost, topmost child*)
functor \<^eval>\<open>sfx_T_nargs "DF_Preorder_Enumerate_Zipper"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) Z.cat
  ) : \<^eval>\<open>sfx_T_nargs "ENUMERATE_ZIPPER"\<close>
  =
struct
structure Z = Z; open Z
structure Co = Co
local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Co.AE); open SC Co.AE
in
fun enum_zipper mk_exn =
  let
    fun make n = arr (fn z => (z, next n)) |> Co.coroutine
    and next n = catch' (down n) (catch' (right n) (up_right n)) |> Co.coroutine
    and down n z = z |> (Down.move >>> Co.resume (make (n + 1)))
    and right n z = z |> (Right.move >>> Co.resume (make n))
    and up_right n z = z |> (if n <= 0
      then Co.AE.throw' (mk_exn ())
      else Up.move >>> catch' (right (n - 1)) (up_right (n - 1)))
  in make 0 end
fun enum_zipper_down mk_exn =
  Co.cons (id ()) (Down.move >>> Co.resume (enum_zipper mk_exn) |> Co.coroutine)
end
end