(*  Title:      Zippy/zippy_base.ML
    Author:     Kevin Kappelmann
*)
infix 3 \>
infix 3 \\>

signature ZIPPY_BASE =
sig
  include ZIPPY_BASE_BASE

  (* misc *)
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
  sharing type AE.K.M.t = M.t
  structure AF : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_FOLD"\<close>
  sharing type AF.K.M.t = M.t
  structure LE : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI_EXCEPTION"\<close>
  sharing type LE.K.M.t = M.t
  sharing type LE.lens = L.lens

  val seq_snoc : 'a Seq.seq -> 'a -> 'a Seq.seq

  (* lenses *)
  val lcomp : (unit -> (@{ParaT_args} 'b, 'c) L.slens) -> (@{ParaT_args} 'a, 'b) L.slens ->
    (@{ParaT_args} 'a, 'c) L.slens
  val \> : (@{ParaT_args} 'a, 'b) L.slens * (unit -> (@{ParaT_args} 'b, 'c) L.slens) ->
    (@{ParaT_args} 'a, 'c) L.slens
  val \\> : (@{ParaT_args} 'a, 'b) L.smodifier * (@{ParaT_args} 'b, 'c) L.smodifier ->
    (@{ParaT_args} 'a, 'c) L.smodifier

  val set_safe : (@{ParaT_args} 's, (@{ParaT_args} 'i) M.t) L.smodifier -> 'i ->
    (@{ParaT_args} 's) hom_move

  (* movements *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val top{i} : (@{ParaT_args} @{AllT_args} Z{i}.zipper, @{AllT_args} Z1.zipper) move\<close>\<close>
end

functor Zippy_Base(
    structure Z : ZIPPY_BASE_BASE
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
    sharing type AE.K.M.t = Z.M.t
  ) : ZIPPY_BASE =
struct

open Z

(* misc *)
structure AE = AE
structure AF = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Fold_Exception_Rec"\<close>(AE)
structure LE = \<^eval>\<open>sfx_ParaT_nargs "Lens_Kleisli_Exception"\<close>(
  structure AE = AE; structure L = L)
structure U = Zippy_Monad_Util(M); open U

fun seq_snoc sq x = Seq.append sq (Seq.single x)

local open SC MO
in
(* lenses *)
fun lcomp l1 l2 = L.comp (l1 ()) l2
fun l1 \> l2 = lcomp l2 l1
fun l1 \\> l2 = L.comp_modify l2 l1

fun set_safe l i s = LE.set_safe l (pure i, s)

(* movements *)
fun top1 x = x |>
  (AE.repeat (Up1.move >>> Up5.move >>> Up4.move >>> Up3.move >>> Up2.move))
fun top2 x = x |>
  (AE.repeat (Up2.move >>> Up1.move >>> Up5.move >>> Up4.move >>> Up3.move)
  >>> Up2.move)
fun top3 x = x |>
  (AE.repeat (Up3.move >>> Up2.move >>> Up1.move >>> Up5.move >>> Up4.move)
  >>> Up3.move >>> Up2.move)
fun top4 x = x |>
  (AE.repeat (Up4.move >>> Up3.move >>> Up2.move >>> Up1.move >>> Up5.move)
  >>> Up4.move >>> Up3.move >>> Up2.move)
fun top5 x = x |> (AE.repeat (Up5.move >>> Up4.move >>> Up3.move >>> Up2.move >>> Up1.move)
  >>> Up5.move >>> Up4.move >>> Up3.move >>> Up2.move)
end

end
