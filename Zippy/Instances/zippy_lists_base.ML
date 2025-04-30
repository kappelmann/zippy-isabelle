(*  Title:      Zippy/zippy_lists_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_BASE =
sig
  include ZIPPY_LISTS_BASE_BASE

  (* misc *)
  structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) cat
  structure LT : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close>
  where type (@{ParaT_args} 'a) t = 'a list
  sharing type LT.A.t = M.t
  structure LF : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_MONAD"\<close>
  where type (@{ParaT_args} 'a) f = 'a list
  sharing type LF.M.t = M.t

  (* lenses *)
  val modify_cons_safe : (@{ParaT_args} 's, (@{ParaT_args} 'i list) M.t) L.smodifier -> 'i ->
    (@{ParaT_args} 's) hom_move

  (* movements *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val first{i} : (@{ParaT_args} @{AllT_args} Z{i}.ZM.container, @{AllT_args} Z{i}.zipper) cat
  val next{i} : (@{ParaT_args} @{AllT_args} Z{i}.zipper) hom_move\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val cons_node_move_safe{i} : @{AllT_args} ZCORE.N\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>node ->
    (@{ParaT_args} @{AllT_args} Z{i}.zipper,
      @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper) cat\<close>
  where stop = 4\<close>

  (* containers *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val list_container_zippers{i} :
    (@{ParaT_args} @{AllT_args} Z{i}.zipper, @{AllT_args} Z{i}.zipper list) cat\<close>\<close>
end

functor Zippy_Lists_Base(
    structure Z : ZIPPY_LISTS_BASE_BASE
    structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) Z.cat
  ) : ZIPPY_LISTS_BASE =
struct

open Z
structure Z = Zippy_Base(structure Z = Z; structure CO = CO)
open Z

(* misc *)
structure LT = \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(M))
structure LF = \<^eval>\<open>sfx_ParaT_nargs "Foldable_Monad"\<close>(
  structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Foldable_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close>)
  structure M = M)

local open SC MO
in
(* lenses *)
fun modify_cons_safe modify x =
  AE.catch' (curry (LE.modify_monad modify) (arr (cons x))) (curry (L.set_modify modify) (pure [x]))
fun cons_node_move_safe modify down n = modify_cons_safe modify n >>> down

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun cons_node_move_safe{i} x = cons_node_move_safe NODE_NEXT{i}.modifier Down{i}.move x\<close>
where stop = 4\<close>

(* movements *)
\<^imap>\<open>\<open>{i}\<close> => \<open>
val first{i} = Z{i}.ZM.Zip.move
val next{i} = Z{i}.ZM.Down.move\<close>\<close>

(* containers *)
local structure EU = \<^eval>\<open>sfx_ParaT_nargs "Enumerable_Util"\<close>(structure CO = CO)
in
fun list_container_zippers unzip first next = unzip >>> EU.list first next
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun list_container_zippers{i} x = list_container_zippers Z{i}.ZM.Unzip.move first{i} next{i} x\<close>\<close>
end

end
