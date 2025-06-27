(*  Title:      Zippy/zippy_lists.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS =
sig
  include ZIPPY_LISTS_BASE
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t

  (* lenses *)
  val modify_cons_safe : (@{ParaT_args} 's, (@{ParaT_args} 'i list) M.t) L.slens -> 'i ->
    (@{ParaT_args} 's) emorph

  (* movements *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val cons_node_move_safe{i} : @{AllT_args} ZN.N\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>node ->
    (@{ParaT_args} @{AllT_args} Z{i}.zipper,
      @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper) morph
  val cons_content_move_safe{i} : @{ParaT_args encl = "(" ")"} Co.Co.AE.exn ->
    @{AllT_args} ZN.N\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>content ->
    (@{ParaT_args} @{AllT_args} Z{i}.zipper,
      @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper) morph\<close>
  where stop = 4\<close>

  (* enumerations *)
  (*in order of container list*)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val enum_zipper{i} : (@{ParaT_args} @{AllT_args} Z{i}.ZM.container, @{AllT_args} Z{i}.zipper *
    (@{ParaT_args} @{AllT_args} Z{i}.zipper, @{AllT_args} Z{i}.zipper) Co.Co.coroutine) morph\<close>\<close>

  (* containers *)
  (*in order of container list*)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val list_container_zippers{i} :
    (@{ParaT_args} @{AllT_args} Z{i}.zipper, @{AllT_args} Z{i}.zipper list) morph\<close>\<close>
end

functor Zippy_Lists(
    structure Z : ZIPPY_LISTS_BASE
    structure Co : ZIPPY_COROUTINE_MIXIN_BASE
    sharing type Co.M.t = Z.M.t
  ) : ZIPPY_LISTS =
struct

open Z
structure Co = Co
structure MU = Zippy_Monad_Util(M); open MU
structure Exn = Zippy_Exception_Mixin(Co)
structure ZNU = Zippy_Node(structure Z = Z; structure Exn = Exn)

local open SC Mo Exn
in
(* lenses *)
fun modify_cons_safe l x s = L.get l s
  |> (AE.catch' (M.map (cons x)) (fn _ => pure [x])
  >>> K.arr (fn xs => L.set l (pure xs, s)))

(* movements *)
fun cons_node_move_safe l down n = modify_cons_safe l n >>> down

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun cons_node_move_safe{i} x = cons_node_move_safe (ZNU.Node_Next{i}.lens ()) Down{i}.morph x
fun cons_content_move_safe{i} exn n = ZNU.node_no_next\<^eval>\<open>succ_mod_nzippers {i}\<close> exn n
  |> cons_node_move_safe{i}\<close>
where stop = 4\<close>

(* enumerations *)
\<^imap>\<open>\<open>{i}\<close> => \<open>
val first{i} = Z{i}.ZM.Zip.morph
val next{i} = Z{i}.ZM.Down.morph
fun enum_zipper{i} x = x |> (first{i} >>> K.arr (rpair (Co.Co.enum' next{i})))
\<close>\<close>

(* containers *)
local
  fun list_container_zippers unzip first next =
    let fun build acc = AE.catch' (fn z => next z >>= build acc >>= K.arr (cons z)) (K.arr single)
    in unzip >>> first >>> build [] end
in
\<^imap>\<open>\<open>{i}\<close> => \<open>
fun list_container_zippers{i} x = list_container_zippers Z{i}.ZM.Unzip.morph first{i} next{i} x\<close>\<close>
end
end
end

