(*  Title:      Zippy/zippy_lists.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS =
sig
  include ZIPPY_LISTS_BASE

  (* misc *)
  structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) cat
  sharing type Co.AE.exn = ZN_AZ2.L.M.exn
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REPEAT"\<close>
  sharing type AE.K.M.t = M.t
  sharing type AE.exn = ZN_AZ2.L.M.exn

  (* lenses *)
  val modify_cons_safe : (@{ParaT_args} 's, (@{ParaT_args} 'i list) M.t) L.slens -> 'i ->
    (@{ParaT_args} 's) hom_move

  (* movements *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val cons_node_move_safe{i} : @{AllT_args} ZN.N\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>node ->
    (@{ParaT_args} @{AllT_args} Z{i}.zipper,
      @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper) cat
  val cons_content_move_safe{i} : @{ParaT_args encl = "(" ")"} Co.AE.exn ->
    @{AllT_args} ZN.N\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>content ->
    (@{ParaT_args} @{AllT_args} Z{i}.zipper,
      @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper) cat\<close>
  where stop = 4\<close>

  (* enumerations *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  (*returns first zipper and remaining enumeration, respecting the order of goal clusters for Z2*)
  val enum_zipper{i} : (@{ParaT_args} @{AllT_args} Z{i}.ZM.container, @{AllT_args} Z{i}.zipper *
    (@{ParaT_args} @{AllT_args} Z{i}.zipper, @{AllT_args} Z{i}.zipper) Co.coroutine) cat\<close>\<close>

  (* containers *)
  (*respects the order of goal clusters for Z2*)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val list_container_zippers{i} :
    (@{ParaT_args} @{AllT_args} Z{i}.zipper, @{AllT_args} Z{i}.zipper list) cat\<close>\<close>
end

functor Zippy_Lists(
    structure Z : ZIPPY_LISTS_BASE
    structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) Z.cat
    sharing type Co.AE.exn = Z.ZN_AZ2.L.M.exn
  ) : ZIPPY_LISTS =
struct

open Z
structure MU = Zippy_Monad_Util(M); open MU
structure Co = Co
structure AE = struct open Z Co.AE end
structure ZNU = Zippy_Node(structure Z = Z; structure AE = AE)
structure ZB = Zippy_Base(structure Z = Z; structure AE = AE)

(* misc *)
local open SC Mo
in
(* lenses *)
fun modify_cons_safe l x s = L.get l s
  |> (AE.catch' (M.map (cons x)) (fn _ => pure [x])
  >>> arr (fn xs => L.set l (pure xs, s)))

(* movements *)
fun cons_node_move_safe l down n = modify_cons_safe l n >>> down

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun cons_node_move_safe{i} x = cons_node_move_safe (ZNU.Node_Next{i}.lens ()) Down{i}.move x
fun cons_content_move_safe{i} exn n = ZNU.node_no_next\<^eval>\<open>succ_mod_nzippers {i}\<close> exn n
  |> cons_node_move_safe{i}\<close>
where stop = 4\<close>

(* enumerations *)
\<^imap>\<open>\<open>{i}\<close> => \<open>
val first{i} = Z{i}.ZM.Zip.move
val next{i} = Z{i}.ZM.Down.move
fun enum_zipper{i} x = x |> (first{i} >>> arr (rpair (Co.enum' next{i})))
\<close>\<close>

(* containers *)
local
  fun list_container_zippers unzip first next =
    let fun build acc = AE.catch' (fn z => next z >>= build acc >>= arr (cons z)) (arr single)
    in unzip >>> first >>> build [] end
in
\<^imap>\<open>\<open>{i}\<close> => \<open>
fun list_container_zippers{i} x = list_container_zippers Z{i}.ZM.Unzip.move first{i} next{i} x\<close>\<close>
end
end

end
