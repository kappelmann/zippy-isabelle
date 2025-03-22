(*  Title:      HOCLP/zippy_with_presults.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_WITH_PRESULTS =
sig
  include ZIPPY_WITH_PRESULTS_BASE

  (* lenses *)
  (** Z4 **)
  val node_presults : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N4.node, @{AllT_args} presults) L.slens
  val action_node_actiona_num : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N4.node, actiona_num) L.slens
  val node_action_and_more : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N4.node,
    @{AllT_args} action_and_more) L.slens

  val presults : unit -> (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} presults) L.slens
  val action_actiona_num : unit -> (@{ParaT_args} @{AllT_args} Z4.zipper, actiona_num) L.slens
  val action_and_more : unit -> (@{ParaT_args} @{AllT_args} Z4.zipper,
    @{AllT_args} action_and_more) L.slens

  (** Z5 **)
  val actiona_node_actiona_num : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N5.node, actiona_num) L.slens
  val node_actiona_and_more : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N5.node,
    @{AllT_args} actiona_and_more) L.slens

  val actiona_actiona_num : unit -> (@{ParaT_args} @{AllT_args} Z5.zipper, actiona_num) L.slens
  val actiona_and_more : unit -> (@{ParaT_args} @{AllT_args} Z5.zipper,
    @{AllT_args} actiona_and_more) L.slens

  (* actions *)
  val gen_inc_actiona_num : (@{ParaT_args} 'z, actiona_num) L.smodifier ->
    (@{ParaT_args} 'z) hom_move

  (** paction from presult **)
  val gen_paction_from_presults :
    (*get presults*)
    (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} presults) cat ->
    (*action when results are empty*)
    @{AllT_args} action ->
    (*update zipper with pulled result and the remaining presults*)
    (result * @{AllT_args} presults -> @{AllT_args} action) ->
    @{AllT_args} paction

  val paction_from_presults : @{ParaT_args encl = "(" ")"} AE.exn ->
    (result * @{AllT_args} presults -> @{AllT_args} action) ->
    @{AllT_args} paction

  val gen_update_result_tail_presults :
    (*update with pulled result*)
    (prio -> result -> (@{ParaT_args} @{AllT_args} Z4.zipper, 'z) cat) ->
    (*update with remaining presults*)
    (prio -> @{AllT_args} presults -> (@{ParaT_args} 'z, @{AllT_args} Z4.zipper) cat) ->
    result * @{AllT_args} presults -> @{AllT_args} action

  val gen_update_result :
    (*init child node*)
    (prio -> 'res -> (@{ParaT_args} @{AllT_args} Z4.zipper, 'cud * 'ch) cat) ->
    (*get parent actions*)
    (@{ParaT_args} 'ch, 'pas) cat ->
    (*copy parent actions*)
    ('cud -> 'pas -> (@{ParaT_args} 'ch, 'z) cat) ->
    prio -> 'res -> (@{ParaT_args} @{AllT_args} Z4.zipper, 'z) cat

  val update_tail_presults : @{AllT_args} presults -> (@{ParaT_args} @{AllT_args} Z4.zipper) hom_move

  (* presults *)
  val gen_presults_from_sq :
    (*coroutine in case of an empty sequence*)
    (@{ParaT_args} @{AllT_args} Z4.zipper, result, prio) CO.acoroutine ->
    (*create next priority while (optionally) updating the sequence*)
    (@{ParaT_args} @{AllT_args} Z4.zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine ->
    result Seq.seq -> @{AllT_args} presults

  val presults_from_sq : @{ParaT_args encl = "(" ")"} AE.exn ->
    (*create next priority while (optionally) updating the sequence*)
    (@{ParaT_args} @{AllT_args} Z4.zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine ->
    result Seq.seq -> @{AllT_args} presults

  val presults_from_tac_state : @{ParaT_args encl = "(" ")"} AE.exn ->
    (*create next priority while (optionally) updating the sequence*)
    (@{ParaT_args} @{AllT_args} Z4.zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine ->
    ('st -> result Seq.seq) -> 'st -> @{AllT_args} presults

end

functor Zippy_With_PResults(
    structure Z : ZIPPY_WITH_PRESULTS_BASE
  ) : ZIPPY_WITH_PRESULTS =
struct

open Z

(* lenses *)
(** Z4 **)
fun node_presults _ = node_pad_more () \> PRD.presults
fun node_presults_data_more _ = node_pad_more () \> PRD.more
fun action_node_actiona_num _ = node_presults_data_more () \> AND.actiona_num
fun node_action_and_more _ = node_presults_data_more () \> AND.more

fun presults _ = action_node () \> node_presults
fun action_actiona_num _ = action_node () \> action_node_actiona_num
fun action_and_more _ = action_node () \> node_action_and_more

(** Z5 **)
fun actiona_node_actiona_num _ = node_pd_more () \> AND.actiona_num
fun node_actiona_and_more _ = node_pd_more () \> AND.more

fun actiona_actiona_num _ = actiona_node () \> actiona_node_actiona_num
fun actiona_and_more _ = actiona_node () \> node_actiona_and_more

local
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Z)
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(K.M)
  structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Arrow_Apply"\<close>(M)
  structure AC = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Choice"\<close>(M)
  open SC M AA AA.A
in

(* actions *)
fun gen_inc_actiona_num modify_actiona_num = (modify_actiona_num |> curry) (arr inc_actiona_num)

fun gen_paction_from_presults get_presults empty_action update_result_tail_presults =
  let fun update_action rp_aco prio = AE.catch'
    (fn z => CO.resume rp_aco z
      >>= (apsnd mk_presults #> (fn rpresults => update_result_tail_presults rpresults prio z)))
    (empty_action prio)
  in
    (get_presults >>> arr (dest_presults #> CO.resume)) &&& id ()
    >>> AA.app
    >>> second (arr update_action)
    |> Z.mk_paction
  end

fun paction_from_presults e = gen_paction_from_presults (L.get (presults ()))
  (Library.K (disable_paction e))

fun gen_update_result_tail_presults update_result update_tail_presults (x, aco) prio =
  update_result prio x >>> update_tail_presults prio aco

fun gen_update_result init_child get_parent_actions copy_parent_actions prio x = init_child prio x
  >>> second (get_parent_actions &&& id ())
  >>> arr (fn (cud, (pas, d)) => (copy_parent_actions cud pas, d))
  >>> AA.app

fun update_tail_presults prs = (presults () |> L.set |> curry) prs
  >>> gen_inc_actiona_num (action_actiona_num () |> L.modify)

(* presults *)
fun gen_presults_from_sq aco_empty_sq mk_prio_sq_c sq =
  let
    fun update mk_prio_sq_c sq =
      arr (fn z => Seq.pull sq |> Either.of_opt |> Either.map_left (Library.K z))
      >>> AC.merge (CO.resume aco_empty_sq)
        (second (arr (gen_presults_from_sq aco_empty_sq mk_prio_sq_c #> dest_presults)))
      |> CO.acoroutine
  in
    arr (rpair sq)
    >>> CO.resume mk_prio_sq_c
    >>> arr (fn ((prio, sq), mk_prio_sq_c) => (prio, update mk_prio_sq_c sq))
    |> CO.acoroutine |> mk_presults
  end

fun presults_from_sq e = gen_presults_from_sq (empty_aco e)
fun presults_from_tac_state e mk_prio_sq_c tac = tac #> presults_from_sq e mk_prio_sq_c

end

end

functor Instantiate_Zippy_With_PResults(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_WITH_PRESULTS
  ) :
    ZIPPY_WITH_PRESULTS
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
    where type @{AllT_args} action_and_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.action_and_more
    where type @{AllT_args} actiona_and_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.actiona_and_more
    where type @{AllT_args} paction = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{AllT_args} copy = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.copy
    where type @{AllT_args} presults = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.presults =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i} = @{AllT_args} inst{i}\<close>\<close> end
structure Z = Instantiate_Zippy_With_PResults_Base(open Base; structure Z = Z)
open Z
end
