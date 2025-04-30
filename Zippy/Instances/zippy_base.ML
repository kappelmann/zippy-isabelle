(*  Title:      Zippy/zippy_base.ML
    Author:     Kevin Kappelmann
*)
infix 3 \>
infix 3 \\>

signature ZIPPY_BASE =
sig
  include ZIPPY_BASE_BASE

  (* misc *)
  structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) cat
  structure SC : \<^eval>\<open>sfx_ParaT_nargs "SEMI_CATEGORY"\<close>
  where type (@{ParaT_args} 'a, 'b) cat = (@{ParaT_args} 'a, 'b) cat
  structure MO : \<^eval>\<open>sfx_ParaT_nargs "MONAD"\<close>
  sharing type MO.t = M.t
  structure C : \<^eval>\<open>sfx_ParaT_nargs "CATEGORY"\<close>
  where type (@{ParaT_args} 'a, 'b) cat = (@{ParaT_args} 'a, 'b) cat
  structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW"\<close>
  sharing type A.K.M.t = M.t
  structure AA : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_APPLY"\<close>
  sharing type AA.K.M.t = M.t
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
  sharing type AE.K.M.t = M.t
  sharing type AE.exn = CO.AE.exn
  structure AF : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_FOLD"\<close>
  sharing type AF.K.M.t = M.t
  structure AC : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_CHOICE"\<close>
  sharing type AC.K.M.t = M.t
  structure LE : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI_EXCEPTION"\<close>
  sharing type LE.K.M.t = M.t
  sharing type LE.lens = L.lens

  val empty_aco : @{ParaT_args encl = "(" ")"} AE.exn -> (@{ParaT_args} 'a, 'b, 'c) CO.acoroutine
  val no_parent : (@{ParaT_args} @{ParaT_args encl = "(" ")"} AE.exn, 'p) cat
  val no_next : (@{ParaT_args} @{ParaT_args encl = "(" ")"} AE.exn, 'n) cat

  (* lenses *)
  val lcomp : (unit -> (@{ParaT_args} 'b, 'c) L.slens) -> (@{ParaT_args} 'a, 'b) L.slens ->
    (@{ParaT_args} 'a, 'c) L.slens
  val \> : (@{ParaT_args} 'a, 'b) L.slens * (unit -> (@{ParaT_args} 'b, 'c) L.slens) ->
    (@{ParaT_args} 'a, 'c) L.slens
  val \\> : (@{ParaT_args} 'a, 'b) L.smodifier * (@{ParaT_args} 'b, 'c) L.smodifier ->
    (@{ParaT_args} 'a, 'c) L.smodifier

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure NODE{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type NODE{i}.container = Z{i}.zipper
  sharing type NODE{i}.data = ZCORE.N{i}.node
  sharing type NODE{i}.K.M.t = M.t
  sharing type NODE{i}.lens = L.lens

  structure NODE_CO{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type NODE_CO{i}.container = Z{i}.zipper
  sharing type NODE_CO{i}.data = ZCORE.N{i}.content
  sharing type NODE_CO{i}.K.M.t = M.t
  sharing type NODE_CO{i}.lens = L.lens

  structure NODE_NEXT{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZCORE.N{i}.next
  sharing type NODE_NEXT{i}.container = Z{i}.zipper
  sharing type NODE_NEXT{i}.K.M.t = M.t
  sharing type NODE_NEXT{i}.lens = L.lens\<close>\<close>

  val set_safe : (@{ParaT_args} 's, (@{ParaT_args} 'i) M.t) L.smodifier -> 'i ->
    (@{ParaT_args} 's) hom_move
  val set_no_next : @{ParaT_args encl = "(" ")"} AE.exn ->
    (@{ParaT_args} 's, (@{ParaT_args} 'i) M.t) L.smodifier -> (@{ParaT_args} 's) hom_move

  (* movements *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val top{i} : (@{ParaT_args} @{AllT_args} Z{i}.zipper, @{AllT_args} Z1.zipper) move\<close>\<close>
end

functor Zippy_Base(
    structure Z : ZIPPY_BASE_BASE
    structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) Z.cat
  ) : ZIPPY_BASE =
struct

open Z

(* misc *)
structure CO = CO
structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Z)
structure MO = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M)
structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M)
structure C = \<^eval>\<open>sfx_ParaT_nargs "Category"\<close>(A)
structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply"\<close>(M)
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Rec"\<close>(
  struct open CO.AE; structure K = K end)
structure AF = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Fold_Exception_Rec"\<close>(AE)
structure AC = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Choice"\<close>(M)
structure LE = \<^eval>\<open>sfx_ParaT_nargs "Lens_Kleisli_Exception"\<close>(
  structure AE = AE; structure L = L)

val empty_aco = CO.throw
val no_parent = AE.throw
val no_next = AE.throw

local open SC MO
in
(* lenses *)
fun lcomp l1 l2 = L.comp (l1 ()) l2
fun l1 \> l2 = lcomp l2 l1
fun l1 \\> l2 = L.comp_modify l2 l1

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure NODE{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.CO
  structure L2 = ZCORE_CO{i})

structure NODE_CO{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = NODE{i}
  structure L2 = ZCORE.N{i}.CO)

structure NODE_NEXT{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = NODE{i}
  structure L2 = ZCORE.N{i}.NEXT)\<close>\<close>

fun set_safe l i s = LE.set_safe l (pure i, s)
fun set_no_next exn nextl z = L.set_modify nextl (no_next exn, z)

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
