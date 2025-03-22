(*  Title:      Zippy/zippy_with_paction.ML
    Author:     Kevin Kappelmann
*)
infix 3 \>

signature ZIPPY_WITH_PACTION =
sig
  include ZIPPY_WITH_PACTION_BASE

  (* misc *)
  structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) cat
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
  where type (@{ParaT_args} 'a) K.M.t = (@{ParaT_args} 'a) M.t
  sharing type AE.exn = CO.AE.exn
  structure AF : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_FOLD"\<close>
  where type (@{ParaT_args} 'a) K.M.t = (@{ParaT_args} 'a) M.t

  val empty_aco : @{ParaT_args encl = "(" ")"} AE.exn -> (@{ParaT_args} 'a, 'b, 'c) CO.acoroutine
  val no_parent : (@{ParaT_args} @{ParaT_args encl = "(" ")"} AE.exn, 'p) cat
  val no_next : (@{ParaT_args} @{ParaT_args encl = "(" ")"} AE.exn, 'n) cat

  (* lenses *)
  val lcomp : (unit -> (@{ParaT_args} 'j, 'k, 'b, 'c) L.lens) ->
    (@{ParaT_args} 'i, 'j, 'a, 'b) L.lens -> (@{ParaT_args} 'i, 'k, 'a, 'c) L.lens
  val \> : (@{ParaT_args} 'i, 'j, 'a, 'b) L.lens * (unit -> (@{ParaT_args} 'j, 'k, 'b, 'c) L.lens) ->
    (@{ParaT_args} 'i, 'k, 'a, 'c) L.lens

  (** Z3 (action cluster) **)
  val actionc_node : unit -> (@{ParaT_args} @{AllT_args} Z3.zipper, @{AllT_args} ZCORE.N3.node) L.slens

  val node_copy : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N3.node, @{AllT_args} copy) L.slens
  val node_cd_more : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N3.node, @{AllT_args} cd_more) L.slens

  val copy : unit -> (@{ParaT_args} @{AllT_args} Z3.zipper, @{AllT_args} copy) L.slens
  val cd_more : unit -> (@{ParaT_args} @{AllT_args} Z3.zipper, @{AllT_args} cd_more) L.slens
  val actionc_next : unit -> (@{ParaT_args} @{AllT_args} Z3.zipper, @{AllT_args} ZCORE.N3.next) L.slens

  (** Z4 (action) **)
  val action_node : unit -> (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} ZCORE.N4.node) L.slens

  val node_paction : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N4.node, @{AllT_args} paction) L.slens
  val node_pad_more : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N4.node, @{AllT_args} pad_more) L.slens

  val paction : unit -> (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} paction) L.slens
  val pad_more : unit -> (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} pad_more) L.slens
  val action_next : unit -> (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} ZCORE.N4.next) L.slens

  (** Z5 (action application) **)
  val actiona_node : unit -> (@{ParaT_args} @{AllT_args} Z5.zipper, @{AllT_args} ZCORE.N5.node) L.slens

  val node_prio : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N5.node, prio) L.slens
  val node_pd_more : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N5.node, @{AllT_args} pd_more) L.slens
  val actiona_next : unit -> (@{ParaT_args} @{AllT_args} Z5.zipper, @{AllT_args} ZCORE.N5.next) L.slens

  val prio : unit -> (@{ParaT_args} @{AllT_args} Z5.zipper, prio) L.slens
  val pd_more : unit -> (@{ParaT_args} @{AllT_args} Z5.zipper, @{AllT_args} pd_more) L.slens

  (* movements *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val top{i} : (@{ParaT_args} @{AllT_args} Z{i}.zipper, @{AllT_args} Z1.zipper) move\<close>\<close>

  (* copy *)
  (** run copies **)
  val get_run_copy : copy_update_data -> @{AllT_args} Z3.zipper ->
    (@{ParaT_args} @{AllT_args} Z1.zipper) hom_move

  val gen_copy_parent_actions :
    (*foldM*)
    (('pa -> (@{ParaT_args} 'z) hom_move) -> 'pas -> (@{ParaT_args} 'z) hom_move) ->
    (*copy parent action*)
    ('cud -> 'pa -> (@{ParaT_args} 'z) hom_move) ->
    'cud -> 'pas -> (@{ParaT_args} 'z) hom_move

  val copy_parent_actions :
    ((@{AllT_args} Z3.zipper -> (@{ParaT_args} @{AllT_args} Z1.zipper) hom_move) ->
      'zs -> (@{ParaT_args} 'z) hom_move) ->
    copy_update_data -> 'zs -> (@{ParaT_args} 'z) hom_move

  (* actions *)
  val no_action : @{ParaT_args encl = "(" ")"} AE.exn -> @{AllT_args} action
  val no_paction : @{ParaT_args encl = "(" ")"} AE.exn -> @{AllT_args} paction
  val disable_paction : @{ParaT_args encl = "(" ")"} AE.exn -> (@{ParaT_args} @{AllT_args} Z4.zipper) hom_move

  val get_run_paction : (@{ParaT_args} @{AllT_args} Z4.zipper, prio * @{AllT_args} action) move
  val run_action : prio * @{AllT_args} action -> (@{ParaT_args} @{AllT_args} Z4.zipper) hom_move

  (** find action candidates **)
  val gen_fold_pactions :
    (*next zipper*)
    (@{ParaT_args} @{AllT_args} Z4.zipper) hom_move ->
    (*update result*)
    (@{ParaT_args} ((prio * @{AllT_args} action) * @{AllT_args} Z4.zipper) * 'r, 'r AF.res) cat ->
    (*init result*)
    (@{ParaT_args} @{AllT_args} Z4.zipper, 'r AF.res) cat ->
    (@{ParaT_args} @{AllT_args} Z4.zipper, 'r AF.res) cat

  val fold_pactions_init_continue : (@{ParaT_args} @{AllT_args} Z4.zipper,
    ((prio * @{AllT_args} action) * @{AllT_args} Z4.zipper) AF.res) cat

  val fold_pactions_run_single_res : (@{ParaT_args}
    ((prio * @{AllT_args} action) * @{AllT_args} Z4.zipper) AF.res, @{AllT_args} Z4.zipper) cat

  val fold_pactions_prio_ord : prio ord -> ((prio * @{AllT_args} action) * @{AllT_args} Z4.zipper) ord

  val fold_pactions_max : prio ord ->
    (@{ParaT_args} ((prio * @{AllT_args} action) * @{AllT_args} Z4.zipper)) hom_move ->
    (@{ParaT_args} @{AllT_args} Z4.zipper) hom_move ->
    (@{ParaT_args} @{AllT_args} Z4.zipper,
      ((prio * @{AllT_args} action) * @{AllT_args} Z4.zipper) AF.res) cat

end

functor Zippy_With_PAction(
    structure Z : ZIPPY_WITH_PACTION_BASE
    structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) Z.cat
  ) : ZIPPY_WITH_PACTION =
struct

open Z.ZCORE Z

(* misc *)
structure CO = CO
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Rec"\<close>(
  struct open CO.AE; structure K = K end)
structure AF = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Fold_Exception_Rec"\<close>(AE)

val empty_aco = CO.throw
val no_parent = AE.throw
val no_next = AE.throw

(* lenses *)
fun lcomp l1 l2 = L.comp (l1 ()) l2
fun l1 \> l2 = lcomp l2 l1

(** Z3 **)
fun actionc_node _ = Z3.ZO.content () \> zcore_content3

val node_cd = N3.content
fun node_copy _ = node_cd () \> CD.copy
fun node_cd_more _ = node_cd () \> CD.more

fun copy _ = actionc_node () \> node_copy
fun cd_more _ = actionc_node () \> node_cd_more
fun actionc_next _ = actionc_node () \> N3.next

fun get_copy x = x |> (copy () |> L.get)

(** Z4 **)
fun action_node _ = Z4.ZO.content () \> zcore_content4

val node_pad = N4.content
fun node_paction _ = node_pad () \> PAD.paction
fun node_pad_more _ = node_pad () \> PAD.more

fun paction _ = action_node () \> node_paction
fun pad_more _ = action_node () \> node_pad_more
fun action_next _ = action_node () \> N4.next

fun get_paction x = x |> (paction () |> L.get)
fun set_paction x = x |> (paction () |> L.set |> curry)

(** Z5 **)
fun actiona_node _ = Z5.ZO.content () \> zcore_content5

val node_pd = N5.content
fun node_prio _ = node_pd () \> PD.prio
fun node_pd_more _ = node_pd () \> PD.more

fun prio _ = actiona_node () \> node_prio
fun pd_more _ = actiona_node () \> node_pd_more
fun actiona_next _ = actiona_node () \> N5.next

local
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Z)
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(K.M);
  structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Arrow_Apply"\<close>(M)
  open SC M AA AA.A
in

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

(* copy *)
(** run copies **)
fun get_run_copy cud z3 z1 = get_copy z3
  >>= arr (dest_copy #> (fn copy => (copy cud z3, z1))) >>= AA.app

fun gen_copy_parent_actions foldM copy_parent_action cud =
  foldM (fn ac => AE.try (copy_parent_action cud ac))

fun copy_parent_actions foldM = gen_copy_parent_actions foldM get_run_copy

(* actions *)
fun no_action e _ = AE.throw' e
fun no_paction e = AE.throw' e |> Z.mk_paction
fun disable_paction e = set_paction (no_paction e)

fun get_run_paction x = get_paction x
  >>= (fn paction => dest_paction paction x)
fun run_action (p, action) = action p

(** find action candidates **)
fun gen_fold_pactions_mk_res x = x |> (get_run_paction &&& id ())

fun gen_fold_pactions next update = AF.fold_init next
  (AE.catch' (first gen_fold_pactions_mk_res >>> update) (arr snd >>> arr AF.continue))

fun fold_pactions_init_continue x = x |> (gen_fold_pactions_mk_res >>> arr AF.continue)
fun fold_pactions_run_single_res x = x |> (arr AF.dest_res >>> AA.uncurry run_action)

fun fold_pactions_prio_ord prio_ord = Order_Util.fst_ord (Order_Util.fst_ord prio_ord)

fun fold_pactions_max prio_ord update_res next = gen_fold_pactions next
  (first update_res >>> arr (Order_Util.max_ord snd (fold_pactions_prio_ord prio_ord) #> AF.continue))
  (gen_fold_pactions_mk_res >>> update_res >>> arr AF.continue)

end

end

functor Instantiate_Zippy_With_PAction(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_WITH_PACTION
  ) :
    ZIPPY_WITH_PACTION
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCORE.A.Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZM.container
    where type @{AllT_args} ZCORE.A.Z{i}.ZO.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZO.content
    where type @{AllT_args} ZCORE.A.Z{i}.ZO.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZO.zcontext
    where type @{AllT_args} ZCORE.A.Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.zipper\<close>\<close>
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCORE.A.N{i}.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.N{i}.content\<close>
    where stop = 2\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCORE.zcontext{i} = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.zcontext{i}
    where type @{AllT_args} ZCORE.pzipper{i} = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.pzipper{i}\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZM.container
    where type @{AllT_args} Z{i}.ZO.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.content
    where type @{AllT_args} Z{i}.ZO.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.zipper\<close>\<close>
    where type @{AllT_args} cd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.cd_more
    where type @{AllT_args} pad_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.pad_more
    where type @{AllT_args} pd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.pd_more
    where type @{AllT_args} paction = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{AllT_args} copy = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.copy =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i} = @{AllT_args} inst{i}\<close>\<close> end
structure Z = Instantiate_Zippy_With_PAction_Base(open Base; structure Z = Z)
open Z
end
