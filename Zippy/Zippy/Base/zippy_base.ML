(*  Title:      Zippy/zippy_base.ML
    Author:     Kevin Kappelmann
*)
infix 3 \>
infix 3 \\>

signature ZIPPY_BASE =
sig
  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_UTIL"\<close>

  (* misc *)
  structure LT : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close>
  where type (@{ParaT_args} 'a) t = 'a list
  sharing type LT.A.t = M.t
  structure LF : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_MONAD"\<close>
  where type (@{ParaT_args} 'a) f = 'a list
  sharing type LF.M.t = M.t

  (* lenses *)
  val lcomp : (unit -> (@{ParaT_args} 'b, 'c) L.slens) -> (@{ParaT_args} 'a, 'b) L.slens ->
    (@{ParaT_args} 'a, 'c) L.slens
  val \> : (@{ParaT_args} 'a, 'b) L.slens * (unit -> (@{ParaT_args} 'b, 'c) L.slens) ->
    (@{ParaT_args} 'a, 'c) L.slens
  val \\> : (@{ParaT_args} 'a, 'b) L.smodifier * (@{ParaT_args} 'b, 'c) L.smodifier ->
    (@{ParaT_args} 'a, 'c) L.smodifier
end

functor Zippy_Base(
    structure Z : ZIPPY_BASE_BASE
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = Z.M.t
  ) : ZIPPY_BASE =
struct

open Z
structure AZU = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Util"\<close>(
  structure Z = Z; structure AE = Exn.AE); open AZU

(* misc *)
structure LT = \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(M))
structure LF = \<^eval>\<open>sfx_ParaT_nargs "Foldable_Monad"\<close>(
  structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Foldable_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close>)
  structure M = M)

(* lenses *)
fun lcomp l1 l2 = L.comp (l1 ()) l2
fun l1 \> l2 = lcomp l2 l1
fun l1 \\> l2 = L.comp_modify l2 l1
end
