\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy
  imports
    Zippy_Base
    ML_Alternating_Zippers4
begin

ML_file\<open>zippy.ML\<close>


ML\<open>
  @{functor_instance struct_name = Standard_Zippy_Goal_Clusters
    and functor_name = Zippy_Goal_Clusters
    and id = \<open>""\<close>
    and more_args = \<open>structure UF = Imperative_Union_Find\<close>}
  structure GCS = Standard_Zippy_Goal_Clusters
  structure GC = Zippy_Goal_Cluster(GCS)
  structure AC = Zippy_Action_Cluster
  structure A = Zippy_Action
  structure FP = Zippy_Focus_Pos(GCS)
\<close>

ML\<open>
(* fun throw_mk_action mk_action e = AE.throw' e |> mk_action
fun set_throw_mk_action e set_mk_action = throw_mk_action e |> set_mk_action

fun update_aco_disable_mk_action e set_mk_action update_aco = update_aco
  >>> set_throw_mk_action e set_mk_action *)
\<close>

ML_file\<open>result_update_info.ML\<close>

(* lemma test: "A \<Longrightarrow> B \<Longrightarrow> G \<Longrightarrow> B \<Longrightarrow> (A \<Longrightarrow> A) \<Longrightarrow> E \<Longrightarrow> A &&& B &&& C &&& D &&& E &&& F &&& G"
  sorry *)

ML\<open>
datatype 'i pos_update_info = Skip | Move of 'i

datatype ('r, 'ui) result = Result of {
    result : 'r,
    update_info : 'ui
  }
\<close>

ML\<open>
datatype 'i pos_update_info = Skip | Move of 'i
datatype ('i, 'r) result = Result of {
    result : 'r,
    pos_update_info : 'i -> 'i pos_update_info
  }

val state = @{thm test} |> `Thm.nprems_of |> uncurry Goal.protect
val gclusterss = GCS.init state
val gclusters = GC.init (apsnd (map snd) gclusterss)

val DETERM_SUCCEED = the oo SINGLE
val cheat = Skip_Proof.cheat_tac @{context} |> ALLGOALS |> DETERM_SUCCEED

val solved_gclusterss = map (GC.get_state #> cheat #> GCS.init) gclusters
val solved_gclusters = solved_gclusterss |> map (apsnd (map snd) #> GC.init)

val finisheds = map (fst #> GCS.is_finished) solved_gclusterss
val test = GCS.finish_gclusters @{context} (map fst solved_gclusterss) (fst gclusterss)

(* val update = fold_index (fn (i, j) => General_Util.fun_update (equal j) i) indices (K (~1,~1)) *)
(* val test = GCS.mk_gpos_index (gclusterss |> snd |> map fst) *)
\<close>

end
