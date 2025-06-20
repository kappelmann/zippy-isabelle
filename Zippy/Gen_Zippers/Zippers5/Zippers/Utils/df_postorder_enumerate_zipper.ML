(*  Title:      Zippy/df_postorder_enumerate_zipper.ML
    Author:     Kevin Kappelmann
*)
(*preconditions:
1) Down.move moves to leftmost, topmost child*)
functor \<^eval>\<open>sfx_T_nargs "DF_Postorder_Enumerate_Zipper"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) Z.cat
  ) : \<^eval>\<open>sfx_T_nargs "ENUMERATE_ZIPPER"\<close>
  =
struct
structure Z = Z; open Z
structure Co = Co
local
  open Co.AE
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Co.AE); open SC
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(Z.K.M); open M
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Arrow"\<close>(Co.AE)
in
fun snoc mk_exn c1 f = Co.append c1 (Co.cons f (Co.throw (mk_exn ())))
fun enum_zipper mk_exn = Co.append
  (enum_zipper_down mk_exn)
  ((fn z => z |> (Right.move >>> Co.resume (enum_zipper mk_exn))) |> Co.coroutine)
and enum_zipper_down mk_exn =
  (fn z => z |> catch'
    (Down.move >>> Co.resume (enum_zipper mk_exn) >>> A.second (arr (fn c => snoc mk_exn c Up.move)))
    (arr (fn z => (z, Co.throw (mk_exn ())))))
  |> Co.coroutine
end
end

