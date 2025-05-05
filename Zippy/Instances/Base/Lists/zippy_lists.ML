(*  Title:      Zippy/zippy_lists.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS =
sig
  include ZIPPY_LISTS_BASE

  (* misc *)
  structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) cat
  sharing type CO.AE.exn = ZCOREAZ2.LI.M.exn
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
  sharing type AE.K.M.t = M.t
  sharing type AE.exn = ZCOREAZ2.LI.M.exn
  structure LT : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close>
  where type (@{ParaT_args} 'a) t = 'a list
  sharing type LT.A.t = M.t
  structure LF : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_MONAD"\<close>
  where type (@{ParaT_args} 'a) f = 'a list
  sharing type LF.M.t = M.t

  val empty_aco : @{ParaT_args encl = "(" ")"} AE.exn -> (@{ParaT_args} 'a, 'b, 'c) CO.acoroutine

  (* lenses *)
  val modify_cons_safe : (@{ParaT_args} 's, (@{ParaT_args} 'i list) M.t) L.smodifier -> 'i ->
    (@{ParaT_args} 's) hom_move

  (* movements *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val cons_node_move_safe{i} : @{AllT_args} ZCORE.N\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>node ->
    (@{ParaT_args} @{AllT_args} Z{i}.zipper,
      @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper) cat\<close>
  where stop = 4\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val first{i} : (@{ParaT_args} @{AllT_args} Z{i}.ZM.container, @{AllT_args} Z{i}.zipper) cat
  val next{i} : (@{ParaT_args} @{AllT_args} Z{i}.zipper) hom_move\<close>\<close>

  (* containers *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val list_container_zippers{i} :
    (@{ParaT_args} @{AllT_args} Z{i}.zipper, @{AllT_args} Z{i}.zipper list) cat\<close>\<close>

  val fold_newest_first : ('a -> (@{ParaT_args} 'b) hom_move) -> 'a list ->
    (@{ParaT_args} 'b) hom_move
  val fold_oldest_first : ('a -> (@{ParaT_args} 'b) hom_move) -> 'a list ->
    (@{ParaT_args} 'b) hom_move
end

functor Zippy_Lists(
    structure Z : ZIPPY_LISTS_BASE
    structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) Z.cat
    sharing type CO.AE.exn = Z.ZCOREAZ2.LI.M.exn
  ) : ZIPPY_LISTS =
struct

open Z
structure U = Zippy_Monad_Util(M); open U
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Rec"\<close>(
  open CO.AE; structure K = \<^eval>\<open>sfx_ParaT_nargs "Kleisli"\<close>(M))
structure ZB = Zippy_Base(structure Z = Z; structure AE = AE); open ZB
structure ZN = Zippy_Node(structure Z = Z; structure AE = AE)

(* misc *)
structure CO = CO
structure LT = \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(M))
structure LF = \<^eval>\<open>sfx_ParaT_nargs "Foldable_Monad"\<close>(
  structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Foldable_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close>)
  structure M = M)

val empty_aco = CO.throw

local open SC MO
in
(* lenses *)
fun modify_cons_safe modify x =
  AE.catch' (curry (LE.modify_monad modify) (arr (cons x))) (curry (L.set_modify modify) (pure [x]))

(* movements *)
fun cons_node_move_safe modify down n = modify_cons_safe modify n >>> down

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun cons_node_move_safe{i} x = cons_node_move_safe ZN.NODE_NEXT{i}.modifier Down{i}.move x\<close>
where stop = 4\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
val first{i} = Z{i}.ZM.Zip.move
val next{i} = Z{i}.ZM.Down.move\<close>\<close>

(* containers *)
local structure EU = \<^eval>\<open>sfx_ParaT_nargs "Enumerable_Util"\<close>(CO)
in
fun list_container_zippers unzip first next = unzip >>> EU.list first next
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun list_container_zippers{i} x = list_container_zippers Z{i}.ZM.Unzip.move first{i} next{i} x\<close>\<close>

(*invariant: operations add new node to the front of the lists*)
val fold_newest_first = LF.foldlM
val fold_oldest_first = LF.foldrM

end

end
