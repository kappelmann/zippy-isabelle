(*  Title:      HOCLP/hoclp.ML
    Author:     Kevin Kappelmann
*)
signature HOCLP_SIG =
sig
  include HAS_LOGGER

  (* HOCLP tactics *)
  type binding = Binding.binding

end

functor HOCLP(A : sig
    structure FIA : FUNCTOR_INSTANCE_ARGS
    structure TI : TERM_INDEX
  end)
  (* : HOCLP_SIG = *)
  =
struct

structure TI = A.TI
structure FIU = Functor_Instance_Util(A.FIA)

structure Util = HOCLP_Util
structure Show = SpecCheck_Show
structure MLCU = ML_Code_Util

val logger = Logger.setup_new_logger Logger.root_logger FIU.FIA.full_name

(* HOCLP tactics *)
type binding = Binding.binding

val eq_binding = Binding.eq_name
val pretty_binding = Binding.pretty

type metadata = binding

val eq_metadata = eq_binding
val pretty_metadata = pretty_binding

type tactic = context_tactic

datatype data = Data of tactic * metadata

fun data tac meta = Data (tac, meta)
fun dest_data (Data data) = data
fun data_tactic (Data (tac, _)) = tac
fun data_metadata (Data (_, meta)) = meta

val eq_data = eq_metadata o apply2 data_metadata
val pretty_data = pretty_metadata o data_metadata

(*HOCLP rules*)
type rule = data list * thm

fun eq_rule ((datas1, thm1), (datas2, thm2)) =
  Thm.eq_thm (thm1, thm2) andalso List.all eq_data (datas1 ~~ datas2)
  handle ListPair.UnequalLengths => false

fun pretty_rule ctxt (datas, thm) =
  let
    val pretty_term = Show.term ctxt
    val pretty_term_data = Show.zip pretty_term pretty_data
    val pretty_prem_datas = map2 (curry pretty_term_data) (Thm.prems_of thm) datas
    val pretty_subgoals = Pretty.list "\<lbrakk>" "\<rbrakk>" pretty_prem_datas
  in
    Pretty.block [
      pretty_subgoals,
      Pretty.str " \<Longrightarrow> ",
      pretty_term (Thm.concl_of thm)
    ]
  end

datatype rules = Rules of {rules : rule TI.term_index}

val empty_rules = Rules {rules = TI.empty}
fun dest_rules (Rules data) = data

fun merge_rules (rs1, rs2) =
  if pointer_eq (rs1, rs2) then rs1
  else
    let
      val Rules {rules = rules1} = rs1
      val Rules {rules = rules2} = rs2
      val merged_rules = TI.merge eq_rule rules1 rules2
    in Rules {rules = merged_rules} end

structure rules_data = Generic_Data(
  type T = rules
  val empty = empty_rules
  val merge = merge_rules
)

val term_index_key_of_term = Logic.strip_imp_concl #> TI.norm_term
val term_index_key_of_thm = term_index_key_of_term o Thm.prop_of

fun add_rule (rule as (datas, thm)) context =
  let
    val ctxt = Context.proof_of context
    val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Adding HOCLP rule ",
        pretty_rule ctxt rule
      ] |> Pretty.string_of)
    val thm' = Thm.trim_context thm
    val key = term_index_key_of_thm thm'
    val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.block [
        Pretty.str "Computed term key: ",
        Show.term ctxt key
      ] |> Pretty.string_of)
    fun update (hoclprs as Rules {rules}) =
      Rules {rules = TI.insert (curry eq_rule (datas, thm')) (key, (datas, thm')) rules}
      handle Term_Index_Base.INSERT =>
        (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
            Pretty.str "HOCLP rule for key ",
            Show.term ctxt key,
            Pretty.str " already added."
          ] |> Pretty.string_of);
        hoclprs)
    val context = rules_data.map update context
  in context end

fun delete_rule (rule as (_, thm)) context =
  let
    val ctxt = Context.proof_of context
    val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Deleting HOCLP rule ",
        pretty_rule ctxt rule
      ] |> Pretty.string_of)
    val key = term_index_key_of_thm thm
    val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.block [
        Pretty.str "Computed term key: ",
        Show.term ctxt key
      ] |> Pretty.string_of)
    fun update (hoclprs as Rules {rules}) =
      Rules {rules = TI.delete (curry eq_rule rule) key rules}
      handle Term_Index_Base.DELETE =>
        (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
            Pretty.str "HOCLP rule for key ",
            Show.term ctxt key,
            Pretty.str " not found."
          ] |> Pretty.string_of);
        hoclprs)
    val context = rules_data.map update context
  in context end

fun get_unifiable_rules goal context =
  let
    val ctxt = Context.proof_of context
    val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Retrieving HOCLP rule for ",
        Show.term ctxt goal
      ] |> Pretty.string_of)
    val key = term_index_key_of_term goal
    val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.block [
        Pretty.str "Computed term key: ",
        Show.term ctxt key
      ] |> Pretty.string_of)
    val (Rules {rules : rule TI.term_index}) = rules_data.get context
    val rules = TI.unifiables rules key
  in rules end

fun hoclp_attr operation (datas, pos) =
  let val code = MLCU.read "curry" @ FIU.code_struct_op (ML_Syntax_Util.atomic operation) @
    MLCU.list datas
  in ML_Attribute.run_declaration_attribute (code, pos) end

fun is_valid_rule num_datas nprems = num_datas = nprems

fun invalid_rule_msg num_datas nprems = implode [
    "Number of passed HOCLP tactics (",
    string_of_int num_datas,
    ") not equal to number of theorem premises (",
    string_of_int nprems,
    ")."
  ]

fun add_hoclp_attr (datas, pos) (context, thm) =
  let
    val num_datas = length datas
    val nprems = Thm.nprems_of thm
  in
    if is_valid_rule num_datas nprems
    then hoclp_attr "add_rule" (datas, pos) (context, thm)
    else error (invalid_rule_msg num_datas nprems)
  end

fun delete_hoclp_attr (datas, pos) (context, thm) =
  let
    val num_datas = length datas
    val nprems = Thm.nprems_of thm
    val _ = if is_valid_rule num_datas nprems then ()
      else @{log Logger.WARN} (Context.proof_of context)
        (fn _ => invalid_rule_msg num_datas nprems)
  in hoclp_attr "delete_rule" (datas, pos) (context, thm) end

val print_tac_binding = @{binding "print"}

val print_tactic =
  (fn (ctxt, thm) => TACTIC_CONTEXT ctxt (print_tac ctxt "printtac" thm))
  |> General_Util.flip data print_tac_binding

fun add_print_rule thm =
  Thm.prems_of thm
  |> map (K print_tactic)
  |> rpair thm
  |> add_rule

fun delete_print_rule thm =
  Thm.prems_of thm
  |> map (K print_tactic)
  |> rpair thm
  |> delete_rule



fun select get_ptac combine_ptac get_ptac_goal_cluster state =
  get_ptac combine_ptac get_ptac_goal_cluster state
(* fun select find_best get_ptac state = find_best get_ptac state *)

fun update apply insert selected =
  let
    val result = apply selected
    val updated = insert selected result
  in updated end

fun bfs_step select update state =
  let
    val selected = select state
    val updated = update selected
  in updated end

fun bfs step continue state =
  let val updated = step state
  in continue updated end

structure List =
struct
  type 'a t = 'a list
  val empty = []
  val is_empty = null
  val fold = fold
  val cons = cons
  fun dest [] = NONE
    | dest (x :: xs) = SOME (x, xs)
  val from_list = I
end

(* structure Set =
struct
  type 'a t = 'a list
  val empty = []
  val is_empty = null
  val fold = fold
end *)

structure Goal_Cluster_State =
struct
  type t = thm
  val subgoals = Thm.cprems_of
end

datatype 's goal_cluster_state_base = Goal_Cluster_State of 's
type goal_cluster_state_content = {state : Goal_Cluster_State.t}
type goal_cluster_state = goal_cluster_state_content goal_cluster_state_base

datatype 'g goal_cluster_base = Goal_Cluster of 'g
type 'ptac_ret goal_cluster_content = {state : goal_cluster_state, ptac_ret : 'ptac_ret}
type 'ptac_ret goal_cluster = ('ptac_ret goal_cluster_content) goal_cluster_base

type ('co, 'ch) node_base = {content : 'co, children : 'ch}

type ('ptac_ret, 'tns) goal_node = ('ptac_ret goal_cluster, 'tns) node_base
type ('ptac_ret, 'tns) goal_nodes = ('ptac_ret, 'tns) goal_node List.t

datatype 't tac_app_base = Tac_App of 't
type 'mr tac_app_content = {mkres : 'mr}
type 'mr tac_app = ('mr tac_app_content) tac_app_base

type ('mr, 'gns) tac_node = ('mr tac_app, 'gns) node_base
type ('mr, 'gns) tac_nodes = ('mr, 'gns) tac_node List.t

val init_goal_cluster_state : goal_cluster_state =
  let
    val init_goal = @{cprop "\<And>x. x \<equiv> x"}
    val state = Goal.init init_goal
  in Goal_Cluster_State {state = state} end

structure ETA = struct
  type ('c, 'ch) tree_content = ('c, 'ch) goal_nodes
  type ('ac, 'ach) app_tree_content  = ('ac, 'ach) tac_nodes
end
@{functor_instance struct_name = ET
  and functor_name = Exploration_Tree
  and accessor = FIU.accessor
  and id = FIU.FIA.id
  and more_args = \<open>structure ETA = ETA\<close>}

(*TODO: type of tactic*)
type tac = Tactical.tactic
type prio = int
type ptac = prio * tac
(*test instantiation*)
type ptac_ret = goal_cluster_state -> ptac option
(*TODO: type of mkres*)
type mr = int

type ('ptac_ret, 'mr) tree_node = ('ptac_ret, ('ptac_ret, 'mr) ET.app_tree) goal_node
type ('ptac_ret, 'mr) tac_tree_node = ('mr, ('ptac_ret, 'mr) ET.tree) tac_node

val prio_ord = int_ord
fun ptac_ord ((prio1, _), (prio2, _)) = prio_ord (prio1, prio2)
fun opt_ptac_ord optp = option_ord ptac_ord optp

fun ord_max ord (x, y) = case ord (x, y) of LESS => y | _ => x

fun combine_ptac opt_ptac1 opt_ptac2 = ord_max opt_ptac_ord (opt_ptac1, opt_ptac2)

val init_goal_cluster : ptac_ret goal_cluster =
  let
    val state = init_goal_cluster_state
    val prio = 0
    val tac = all_tac
    val ptac = (prio, tac)
    fun ptac_ret _ = SOME ptac
  in Goal_Cluster {state = state, ptac_ret = ptac_ret} end

val init_tac_tree_internal : (ptac_ret, mr) ET.app_tree_internal = List.empty
val init_tac_tree : (ptac_ret, mr) ET.app_tree = ET.App_Tree init_tac_tree_internal

val init_tree_node : (ptac_ret, mr) tree_node =
  let
    val content = init_goal_cluster
    val children = init_tac_tree
  in {content = content, children = children} end
val init_tree_internal : (ptac_ret, mr) ET.tree_internal = List.from_list [init_tree_node]
val init_tree : (ptac_ret, mr) ET.tree = ET.Tree init_tree_internal

type ('c, 'ctxt) zipper_base = {
  content : 'c,
  context : 'ctxt
}

fun map_zipper_base_context f {content, context} = {content = content, context = f context}

type ('c, 'pz) zipper_context_base = {
  prev : 'c List.t,
  next : 'c List.t,
  parent_zipper: 'pz
}

type ('mr, 'ctxt) tree_parent_zipper_base = ('mr tac_app, 'ctxt) zipper_base
type ('ptac_ret, 'mr, 'pz) tree_zipper_context_base =
  (('ptac_ret, 'mr) tree_node, 'pz) zipper_context_base

type ('ptac_ret, 'ctxt) tac_tree_parent_zipper_base = ('ptac_ret goal_cluster, 'ctxt) zipper_base
type ('ptac_ret, 'mr, 'pz) tac_tree_zipper_context_base =
  (('ptac_ret, 'mr) tac_tree_node, 'pz) zipper_context_base

datatype ('ptac_ret, 'mr) tree_zipper_context =
  Tree_Zipper_Context of
    ('ptac_ret, 'mr,
    ('mr, ('ptac_ret, 'mr) tac_tree_zipper_context) tree_parent_zipper_base option)
    tree_zipper_context_base
and ('ptac_ret, 'mr) tac_tree_zipper_context =
  Tac_Tree_Zipper_Context of
    ('ptac_ret, 'mr,
    ('ptac_ret, ('ptac_ret, 'mr) tree_zipper_context) tac_tree_parent_zipper_base)
    tac_tree_zipper_context_base

type ('ptac_ret, 'mr) tree_zipper =
  (('ptac_ret, 'mr) tree_node, ('ptac_ret, 'mr) tree_zipper_context) zipper_base

type ('ptac_ret, 'mr) tac_tree_zipper =
  (('ptac_ret, 'mr) tac_tree_node, ('ptac_ret, 'mr) tac_tree_zipper_context) zipper_base

fun dest_tree_zipper_context (Tree_Zipper_Context context) = context
fun dest_tac_tree_zipper_context (Tac_Tree_Zipper_Context context) = context

fun init_zipper_base parent_zipper = List.dest
  #> Option.map (fn (first, rest) =>
    {content = first, context = {
      prev = List.empty,
      next = rest,
      parent_zipper = parent_zipper
    }})

fun init_tree_zipper parent_zipper (ET.Tree gns) =
  init_zipper_base parent_zipper gns
  |> Option.map (map_zipper_base_context Tree_Zipper_Context)

fun init_tac_node_zipper parent_zipper (ET.App_Tree tns) =
  init_zipper_base parent_zipper tns
  |> Option.map (map_zipper_base_context Tac_Tree_Zipper_Context)

type ('a, 'b) move = 'a -> 'b option
(* datatype ('a, 'b) moves = Moves of 'a -> ('a, 'b) moves * 'b option *)
(* type 'a moves = 'a Seq.seq *)
(* fun keep_move f = Moves (fn x => (keep_move f, f x)) *)

fun move_right_zipper_base {content, context = {prev, next, parent_zipper}} =
  List.dest next
  |> Option.map (fn (first, rest) =>
    {content = first, context = {
      prev = List.cons content prev,
      next = rest,
      parent_zipper = parent_zipper
    }})

fun lift_zipper_base_fun_context dest_context mk_context f =
  map_zipper_base_context dest_context
  #> f
  #> Option.map (map_zipper_base_context mk_context)

fun lift_zipper_base_fun_tree_zipper f =
  lift_zipper_base_fun_context dest_tree_zipper_context Tree_Zipper_Context f

fun lift_zipper_base_fun_tac_tree_zipper f =
  lift_zipper_base_fun_context dest_tac_tree_zipper_context Tac_Tree_Zipper_Context f

fun move_right_tree_zipper zip = lift_zipper_base_fun_tree_zipper move_right_zipper_base zip
fun move_right_tac_tree_zipper zip =
  lift_zipper_base_fun_tac_tree_zipper move_right_zipper_base zip

fun move_left_zipper_base {content, context = {prev, next, parent_zipper}} =
  List.dest prev
  |> Option.map (fn (first, rest) =>
    {content = first, context = {
      prev = rest,
      next = List.cons content next,
      parent_zipper = parent_zipper
    }})

fun move_left_tree_zipper zip = lift_zipper_base_fun_tree_zipper move_left_zipper_base zip
fun move_left_tac_tree_zipper zip =
  lift_zipper_base_fun_tac_tree_zipper move_left_zipper_base zip

fun move_down_zipper_base f {content = {content, children}, context} =
  f {content = content, context = context} children

fun test {content = {content, children}, context} =
  init_tac_node_zipper {content = content, context = context} children
fun move_down_tree_zipper zip = move_down_zipper_base init_tac_node_zipper zip
fun move_down_tac_tree_zipper zip = move_down_zipper_base (init_tree_zipper o SOME) zip

fun move_up_zipper_base dest_context dest_parent_zipper mk_children {content, context} =
  dest_context context
  |> (fn {prev, next, parent_zipper} => dest_parent_zipper parent_zipper
    |> (fn {content = pcontent, context = pcontext} => {
      content = {content = pcontent, children = mk_children (prev @ [content] @ next)},
      context = pcontext
    }))

fun move_up_tree_zipper zip =
  try (move_up_zipper_base dest_tree_zipper_context the ET.Tree) zip
fun move_up_tac_tree_zipper zip =
  move_up_zipper_base dest_tac_tree_zipper_context I ET.App_Tree zip

(* fun fold_moves moves f =
  let fun fold (_, NONE) acc = acc
        | fold (Moves moves, SOME x) acc = fold (moves x) (f x acc)
  in fold o pair moves end *)

fun seq_fold f sq acc = case Seq.pull sq of
    SOME (x, sq) => seq_fold f sq (f x acc)
  | NONE => acc

fun get_ptac_goal_cluster (Goal_Cluster {state, ptac_ret}) = ptac_ret state
fun get_ptac_tree_node {content,...} = get_ptac_goal_cluster content

fun select_tree_zipper tree =
  let
    val seq_of_opt = the_default Seq.empty
    fun bfs zip contsq =
      let
        val contsq = move_down_tree_zipper zip
          |> Option.mapPartial move_down_tac_tree_zipper
          |> Option.map (Seq.single #> Seq.append contsq)
          |> the_default contsq
        val nextsq = (case move_right_tree_zipper zip of
            SOME zip => SOME (zip, contsq)
          | NONE => Seq.pull contsq)
          |> Option.map (uncurry bfs)
          |> seq_of_opt
      in Seq.cons zip nextsq end
    fun dfs zip =
      let
        val downsq = move_down_tree_zipper zip
          |> Option.mapPartial move_down_tac_tree_zipper
          |> Option.map dfs
          |> seq_of_opt
        val rightsq = move_right_tree_zipper zip
          |> Option.map dfs
          |> seq_of_opt
      in Seq.cons zip (Seq.append downsq rightsq) end
    fun step_tree_node (zip as {content,...}) =
      SOME (zip, get_ptac_tree_node content)
      |> General_Util.flip (curry (ord_max (option_ord (apply2 snd #> opt_ptac_ord))))
  in
    init_tree_zipper NONE tree
    |> Option.mapPartial (fn zip => seq_fold step_tree_node (bfs zip Seq.empty) NONE)
  end

fun apply_goal_cluster_state (Goal_Cluster_State {state}, (prio, tac)) = tac state

fun goal_cluster_get_state (Goal_Cluster {state,...} : 'a goal_cluster) = state

fun node_content ({content,...} : ('co, 'ch) node_base) = content
fun zipper_content ({content,...} : ('c, 'ctxt) zipper_base) = content

fun apply_goal_cluster p = apfst goal_cluster_get_state p |> apply_goal_cluster_state
fun apply_goal_node p = apfst node_content p |> apply_goal_cluster

fun apply_tree_zipper p = apfst zipper_content p |> apply_goal_node

fun update apply insert selected =
  let
    val result = apply selected
    val updated = insert selected result
  in updated end

(*
datatype ('state, 'gact, 'ract) goal_node = Goal_Node of {
    gc : ('state, 'gact) goal_cluster,
    rn : ('state, 'gact, 'ract) rule_node
  } List.t
and ('state, 'gact, 'ract) rule_node = Rule_Node of {
    act : 'ract,
    gn : ('state, 'gact, 'ract) goal_node
  } List.t *)

(* datatype ('state, 'gact, 'ract) node = Goal of  ('state, 'gact, 'ract) goal_node
  | Rule of ('state, 'gact, 'ract) rule_node *)

(* datatype path = Path of int List.t

fun walk (Path []) n = n
  | walk (Path (i :: is)) (Goal (Goal_Node gns)) = walk (Path is) (List.nth gns i |> #rn |> Rule)
  | walk (Path (i :: is)) (Rule (Rule_Node rns)) = walk (Path is) (List.nth rns i |> #gn |> Goal) *)

(* val test =
  let
    val default = Prio.Table.empty
    val combine = Prio.Table.merge
  in
    act default combine init_node
    |> @{print}
  end *)

(*
fun update apply insert selected =
  let
    val result = apply selected
    val updated = insert selected result
  in updated end

fun bfs_step select update state =
  let
    val selected = select state
    val updated = update selected
  in updated end

fun bfs step continue state =
  let val updated = step state
  in continue updated end*)

end
