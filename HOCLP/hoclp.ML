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
structure GU = General_Util

val logger = Logger.setup_new_logger Logger.root FIU.FIA.full_name

(* HOCLP tactics *)
(* type binding = Binding.binding

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

fun is_valid_rule num_datas nprems = num_datas = nprems

fun invalid_rule_msg num_datas nprems = implode [
    "Number of passed HOCLP tactics (",
    string_of_int num_datas,
    ") not equal to number of theorem premises (",
    string_of_int nprems,
    ")."
  ]


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
val term_index_key_of_thm = Thm.prop_of #> term_index_key_of_term

fun add_rule (rule as (datas, thm)) context =
  let
    val ctxt = Context.proof_of context
    val num_datas = length datas
    val nprems = Thm.nprems_of thm
    val _ = if is_valid_rule num_datas nprems
      then @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
          Pretty.str "Adding HOCLP rule ",
          pretty_rule ctxt rule
        ] |> Pretty.string_of)
      else error (invalid_rule_msg num_datas nprems)
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

fun delete_rule (rule as (datas, thm)) context =
  let
    val num_datas = length datas
    val nprems = Thm.nprems_of thm
    val ctxt = Context.proof_of context
    val _ = if is_valid_rule num_datas nprems
      then @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
          Pretty.str "Deleting HOCLP rule ",
          pretty_rule ctxt rule
        ] |> Pretty.string_of)
      else @{log Logger.WARN} (Context.proof_of context)
        (fn _ => invalid_rule_msg num_datas nprems)
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

fun add_hoclp_attr (datas, pos) (context, thm) =
  hoclp_attr "add_rule" (datas, pos) (context, thm)

fun delete_hoclp_attr (datas, pos) (context, thm) =
  hoclp_attr "delete_rule" (datas, pos) (context, thm)

val print_tac_binding = @{binding "print"}

val print_tactic =
  (fn (ctxt, thm) => TACTIC_CONTEXT ctxt (print_tac ctxt "printtac" thm))
  |> GU.flip data print_tac_binding

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

structure List =
struct
  type 'a t = 'a list
  val empty = []
  val is_empty = null
  val fold = fold
  val cons = cons
  fun dest [] = NONE
    | dest (x :: xs) = SOME (x, xs)
  val from_list : 'a list -> 'a t = I
end *)

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

fun goal_cluster_state state = Goal_Cluster_State {state = state}
fun get_goal_cluster_state_state (Goal_Cluster_State {state}) = state
fun map_goal_cluster_state_state f (Goal_Cluster_State {state}) =
  Goal_Cluster_State {state = f state}

datatype 'g goal_cluster_base = Goal_Cluster of 'g
type 'prio_tac_ret goal_cluster_content = {state : goal_cluster_state, prio_tac_ret : 'prio_tac_ret}
type 'prio_tac_ret goal_cluster = ('prio_tac_ret goal_cluster_content) goal_cluster_base

fun goal_cluster state prio_tac_ret = Goal_Cluster {state = state, prio_tac_ret = prio_tac_ret}
fun dest_goal_cluster (Goal_Cluster goal_cluster) = goal_cluster
fun get_goal_cluster_state (Goal_Cluster {state, ...} : 'prio_tac_ret goal_cluster) = state
fun get_goal_cluster_prio_tac_ret (Goal_Cluster {prio_tac_ret, ...}) = prio_tac_ret
fun map_goal_cluster_state f (Goal_Cluster {state, prio_tac_ret}) =
  Goal_Cluster {state = f state, prio_tac_ret = prio_tac_ret}
fun map_goal_cluster_prio_tac_ret f (Goal_Cluster {state, prio_tac_ret}) =
  Goal_Cluster {state = state, prio_tac_ret = f prio_tac_ret}

type ('co, 'ch) node_base = {content : 'co, children : 'ch}

fun get_node_content {content, children} = content
fun get_node_children {children, content} = children
fun map_node_content f {content, children} = {content = f content, children = children}
fun map_node_children f {content, children} = {content = content, children = f children}

type ('prio_tac_ret, 'tns) goal_node = ('prio_tac_ret goal_cluster, 'tns) node_base
type ('prio_tac_ret, 'tns) goal_nodes = ('prio_tac_ret, 'tns) goal_node List.t

datatype 't tac_app_base = Tac_App of 't
type 'mr tac_app_content = {mkres : 'mr}
type 'mr tac_app = ('mr tac_app_content) tac_app_base

fun tac_app mkres = Tac_App {mkres = mkres}
fun dest_tac_app (Tac_App tac_app) = tac_app
fun get_tac_app_mkres (Tac_App {mkres}) = mkres
fun map_tac_app_mkres f (Tac_App {mkres}) = Tac_App {mkres = f mkres}

type ('mr, 'gns) tac_node = ('mr tac_app, 'gns) node_base
type ('mr, 'gns) tac_nodes = ('mr, 'gns) tac_node List.t

structure ETA = struct
  type ('c, 'ch) tree_content = ('c, 'ch) goal_nodes
  type ('ac, 'ach) app_tree_content  = ('ac, 'ach) tac_nodes
end
@{functor_instance struct_name = ET
  and functor_name = Exploration_Tree
  and accessor = FIU.accessor
  and id = FIU.FIA.id
  and more_args = \<open>structure ETA = ETA\<close>}

type ('prio_tac_ret, 'mr) tree_node = ('prio_tac_ret, ('prio_tac_ret, 'mr) ET.app_tree) goal_node
type ('prio_tac_ret, 'mr) tac_tree_node = ('mr, ('prio_tac_ret, 'mr) ET.tree) tac_node

type ('prio_tac_ret, 'mr) tree_nodes = ('prio_tac_ret, 'mr) ET.tree_internal
type ('prio_tac_ret, 'mr) tac_tree_nodes = ('prio_tac_ret, 'mr) ET.app_tree_internal
type ('prio_tac_ret, 'mr) tree = ('prio_tac_ret, 'mr) ET.tree
type ('prio_tac_ret, 'mr) tac_tree = ('prio_tac_ret, 'mr) ET.app_tree

(* zippers *)
type ('c, 'ctxt) zipper_base = {
  content : 'c,
  context : 'ctxt
}

fun map_zipper_content f {content, context} = {content = f content, context = context}
fun map_zipper_context f {content, context} = {content = content, context = f context}

type ('c, 'pz) zipper_context_base = {
  prev : 'c List.t,
  next : 'c List.t,
  parent_zipper: 'pz
}

type ('mr, 'ctxt) tree_parent_zipper_base = ('mr tac_app, 'ctxt) zipper_base
type ('prio_tac_ret, 'mr, 'pz) tree_zipper_context_base =
  (('prio_tac_ret, 'mr) tree_node, 'pz) zipper_context_base

type ('prio_tac_ret, 'ctxt) tac_tree_parent_zipper_base = ('prio_tac_ret goal_cluster, 'ctxt) zipper_base
type ('prio_tac_ret, 'mr, 'pz) tac_tree_zipper_context_base =
  (('prio_tac_ret, 'mr) tac_tree_node, 'pz) zipper_context_base

datatype ('prio_tac_ret, 'mr) tree_zipper_context =
  Tree_Zipper_Context of
    ('prio_tac_ret, 'mr,
    ('mr, ('prio_tac_ret, 'mr) tac_tree_zipper_context) tree_parent_zipper_base option)
    tree_zipper_context_base
and ('prio_tac_ret, 'mr) tac_tree_zipper_context =
  Tac_Tree_Zipper_Context of
    ('prio_tac_ret, 'mr,
    ('prio_tac_ret, ('prio_tac_ret, 'mr) tree_zipper_context) tac_tree_parent_zipper_base)
    tac_tree_zipper_context_base

type ('prio_tac_ret, 'mr) tree_zipper =
  (('prio_tac_ret, 'mr) tree_node, ('prio_tac_ret, 'mr) tree_zipper_context) zipper_base

type ('prio_tac_ret, 'mr) tac_tree_zipper =
  (('prio_tac_ret, 'mr) tac_tree_node, ('prio_tac_ret, 'mr) tac_tree_zipper_context) zipper_base

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
  |> Option.map (map_zipper_context Tree_Zipper_Context)

fun init_tac_tree_zipper parent_zipper (ET.App_Tree tns) =
  init_zipper_base parent_zipper tns
  |> Option.map (map_zipper_context Tac_Tree_Zipper_Context)

type ('a, 'b) move = 'a -> 'b option

fun move_right_zipper_base {content, context = {prev, next, parent_zipper}} =
  List.dest next
  |> Option.map (fn (first, rest) =>
    {content = first, context = {
      prev = List.cons content prev,
      next = rest,
      parent_zipper = parent_zipper
    }})

fun lift_zipper_base_fun_context dest_context mk_context f =
  map_zipper_context dest_context
  #> f
  #> Option.map (map_zipper_context mk_context)

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

fun move_down_tree_zipper zip = move_down_zipper_base init_tac_tree_zipper zip
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

(* paths *)

structure Pos =
struct
type pos = int
val init = 0
fun right p = p + 1
fun left p = p - 1
end

structure Path =
struct
type path = Pos.pos List.t
val empty = List.empty
val init = List.cons Pos.init
val move_right = List.dest #> Option.map (fn (first, rest) => List.cons (Pos.right first) rest)
val move_left = List.dest #> Option.map (fn (first, rest) => List.cons (Pos.left first) rest)
val move_down = init
val move_up : path -> path option = List.dest #> Option.map snd
end

(* path zippers *)

type 'z path_zipper_base = {
  path : Path.path,
  zipper: 'z
}

fun map_path_zipper_path f {path, zipper} = {path = f path, zipper = zipper}
fun map_path_zipper_zipper f {path, zipper} = {path = path, zipper = f zipper}

fun empty_path_zipper_base zipper = {path = Path.empty, zipper = zipper}

type ('prio_tac_ret, 'mr) path_tree_zipper = (('prio_tac_ret, 'mr) tree_zipper) path_zipper_base
type ('prio_tac_ret, 'mr) path_tac_tree_zipper = (('prio_tac_ret, 'mr) tac_tree_zipper) path_zipper_base

fun map_option_zipper_base fpath fzipper {path, zipper} =
  fzipper zipper
  |> Option.mapPartial (fn zipper => fpath path
  |> Option.map (fn path => {path = path, zipper = zipper}))

val move_path_zipper_base = map_option_zipper_base

fun init_path_zipper_base init_zipper parent_path_zipper tree =
  map_option_zipper_base (SOME o Path.init) (GU.flip init_zipper tree) parent_path_zipper

fun init_path_tree_zipper parent_path_zipper =
  init_path_zipper_base init_tree_zipper parent_path_zipper
fun init_path_tac_tree_zipper parent_path_zipper =
  init_path_zipper_base init_tac_tree_zipper parent_path_zipper

fun move_right_path_zipper_base move_right_zipper =
  move_path_zipper_base Path.move_right move_right_zipper

fun move_right_path_tree_zipper path_zipper =
  move_right_path_zipper_base move_right_tree_zipper path_zipper
fun move_right_path_tac_tree_zipper path_zipper =
  move_right_path_zipper_base move_right_tac_tree_zipper path_zipper

fun move_left_path_zipper_base move_left_zipper =
  move_path_zipper_base Path.move_left move_left_zipper

fun move_left_path_tree_zipper path_zipper =
  move_left_path_zipper_base move_left_tree_zipper path_zipper
fun move_left_path_tac_tree_zipper path_zipper =
  move_left_path_zipper_base move_left_tac_tree_zipper path_zipper

fun move_down_path_zipper_base move_down_zipper =
  move_path_zipper_base (SOME o Path.move_down) move_down_zipper

fun move_down_path_tree_zipper path_zipper =
  move_down_path_zipper_base move_down_tree_zipper path_zipper
fun move_down_path_tac_tree_zipper path_zipper =
  move_down_path_zipper_base move_down_tac_tree_zipper path_zipper

fun move_up_path_zipper_base move_up_zipper = move_path_zipper_base Path.move_up move_up_zipper

fun move_up_path_tree_zipper path_zipper =
  move_up_path_zipper_base move_up_tree_zipper path_zipper
fun move_up_path_tac_tree_zipper path_zipper =
  move_up_path_zipper_base (SOME o move_up_tac_tree_zipper) path_zipper

type ('prio, 'c) prio_content = {prio: 'prio, content: 'c}
fun prio_content prio content = {prio = prio, content = content}
fun get_prio_content_prio {prio, ...} = prio
fun get_prio_content_content {content, ...} = content

(*TODO: type of tactic (return more information about changes)*)
type ('prio, 'c) tac = ('prio, 'c) prio_content -> 'c option
type ('prio, 'prio_tac_ret, 'mr) prio_tac = ('prio, ('prio, ('prio_tac_ret, 'mr) path_tree_zipper) tac) prio_content
datatype ('prio, 'mr) prio_tac_ret = Prio_Tac_Ret of
  (('prio, 'mr) prio_tac_ret, 'mr) path_tree_zipper -> ('prio, ('prio, 'mr) prio_tac_ret, 'mr) prio_tac option
(*test instantiation*)
(*TODO: type of mkres*)
datatype ('prio, 'res) mr = Make_Tac_App_Result of
  (('prio, ('prio, 'res) mr) prio_tac_ret, ('prio, 'res) mr) path_tac_tree_zipper -> 'res -> 'res
type prio = int
type res = Goal_Cluster_State.t
type mr = (prio, res) mr
type prio_tac_ret = (prio, mr) prio_tac_ret

val empty_tree : ('prio_tac_ret, 'mr) tree = ET.Tree List.empty
val empty_tac_tree : ('prio_tac_ret, 'mr) tac_tree = ET.App_Tree List.empty

val prio_tac_ret = Prio_Tac_Ret
fun dest_prio_tac_ret (Prio_Tac_Ret prio_tac_ret) = prio_tac_ret
fun map_prio_tac_ret f (Prio_Tac_Ret prio_tac_ret) = Prio_Tac_Ret (f prio_tac_ret)

val prio_ord = int_ord
val prio_content_ord = apply2 get_prio_content_prio #> prio_ord
fun opt_prio_content_ord optp = option_ord prio_content_ord optp

fun ord_max ord (x, y) = case ord (x, y) of LESS => y | _ => x

fun combine_prio_tac opt_prio_tac1 opt_prio_tac2 = ord_max opt_prio_content_ord (opt_prio_tac1, opt_prio_tac2)

val init_prio_tac_ret : prio_tac_ret =
  let
    val prio = 0
    val tac = SOME o get_prio_content_content
    val prio_tac = prio_content prio tac
    fun ptret _ = SOME prio_tac
  in prio_tac_ret ptret end

fun tree_node goal_cluster tac_tree : ('prio_tac_ret, 'mr) tree_node =
  {content = goal_cluster, children = tac_tree}
fun tac_tree_node tac_app tree : ('prio_tac_ret, 'mr) tac_tree_node =
  {content = tac_app, children = tree}

val tree_nodes = List.from_list
val insert_tree_node = List.cons
val tac_tree_nodes = List.from_list
val insert_tac_tree_node = List.cons

val tree = ET.Tree
val map_tree = ET.map_tree
fun tree_insert_tree_node tree_node = map_tree (insert_tree_node tree_node)

val tac_tree = ET.App_Tree
val map_tac_tree = ET.map_app_tree
fun tac_tree_insert_tac_tree_node tac_tree_node = map_tac_tree (insert_tac_tree_node tac_tree_node)

fun goal_node_insert_tac_tree_node tac_tree_node =
  map_node_children (tac_tree_insert_tac_tree_node tac_tree_node)

fun leaf_tree_node goal_cluster = tree_node goal_cluster empty_tac_tree

val init_tree_node : (prio_tac_ret, mr) tree_node =
  let
    val init_goal = @{cprop "\<And>P. P \<equiv> P"} |> Goal.init
    val goal_cluster = goal_cluster (goal_cluster_state init_goal) init_prio_tac_ret
  in leaf_tree_node goal_cluster end
val init_tree_nodes : (prio_tac_ret, mr) tree_nodes = tree_nodes [init_tree_node]
val init_tree : (prio_tac_ret, mr) tree = ET.Tree init_tree_nodes


fun seq_fold f sq acc = case Seq.pull sq of
    SOME (x, sq) => seq_fold f sq (f x acc)
  | NONE => acc

fun get_tree_node_prio_tac_ret {content,...} = get_goal_cluster_prio_tac_ret content

fun seq_of_opt opt = Option.map Seq.single opt |> the_default Seq.empty

fun dfs_base finish_node dfs_children move_down move_right node =
  let
    val downsq = Seq.make (fn () => move_down node |> seq_of_opt
      |> Seq.maps dfs_children
      |> Seq.pull)
    val rightsq = Seq.make (fn () => move_right node |> seq_of_opt
      |> Seq.maps (dfs_base finish_node dfs_children move_down move_right)
      |> Seq.pull)
  in finish_node node (Seq.append downsq rightsq) end

fun dfs_tac_tree path_tac_tree_zipper = dfs_base (K I) dfs_tree
  move_down_path_tac_tree_zipper move_right_path_tac_tree_zipper path_tac_tree_zipper
and dfs_tree path_tree_zipper = dfs_base Seq.cons dfs_tac_tree
  move_down_path_tree_zipper move_right_path_tree_zipper path_tree_zipper

fun bfs_base finish_node bfs_children move_down move_right node contsq childrensq =
  let
    val childrensq =
      Seq.make (fn () => move_down node |> seq_of_opt |> Seq.append childrensq |> Seq.pull)
    val bfs = bfs_base finish_node bfs_children move_down move_right
    val nextsq = Seq.make (fn () => (case move_right node of
        SOME node => bfs node contsq childrensq
      | NONE => case Seq.pull contsq of
          SOME (node, contsq) => bfs node contsq childrensq
        | NONE => case Seq.pull childrensq of
            SOME (child, childrensq) => bfs_children child childrensq Seq.empty
          | NONE => Seq.empty)
      |> Seq.pull)
  in finish_node node nextsq end

fun bfs_tac_tree path_tac_tree_zipper = bfs_base (K I) bfs_tree
  move_down_path_tac_tree_zipper move_right_path_tac_tree_zipper path_tac_tree_zipper
and bfs_tree path_tree_zipper = bfs_base Seq.cons bfs_tac_tree
  move_down_path_tree_zipper move_right_path_tree_zipper path_tree_zipper

fun select_tree_zipper (tree : (prio_tac_ret, mr) tree) =
  let
    fun traverse path_zipper = dfs_tree path_zipper
    (* fun traverse path_zipper = bfs_tree path_zipper Seq.empty Seq.empty *)
    (* fun step_tree_node (path_zipper as {zipper = {content,...},...}) =
      get_prio_tac_tree_node content
      |> Option.map (pair path_zipper)
      |> List.cons
    val init_select = [] *)
    fun step_tree_node (path_zipper as {zipper = {content,...},...}) =
      dest_prio_tac_ret (get_tree_node_prio_tac_ret content) path_zipper
      |> Option.map (fn {prio, content} => prio_content prio path_zipper |> pair content)
      |> GU.flip (curry (ord_max (option_ord (apply2 snd #> prio_content_ord))))
    val init_select = NONE
  in
    init_path_tree_zipper (empty_path_zipper_base NONE) tree
    |> Option.mapPartial (fn path_zipper => seq_fold step_tree_node (traverse path_zipper) init_select)
    (* |> Option.map (fn path_zipper => seq_fold step_tree_node (traverse path_zipper) init_select) *)
  end

fun get_zipper_content ({content,...} : ('c, 'ctxt) zipper_base) = content
fun get_path_zipper_zipper ({zipper,...} : 'z path_zipper_base) = zipper

fun apply_tac (tac, args) = tac args

fun apply_make_tac_app_result (Make_Tac_App_Result mk_tac_app_res) path_zipper res_children =
  mk_tac_app_res path_zipper res_children

fun update apply insert selected =
  let
    val result = apply selected
    val updated = insert selected result
  in updated end

fun zipper_insert_tac_tree_node tac_tree_node =
  map_zipper_content (goal_node_insert_tac_tree_node tac_tree_node)

fun path_zipper_insert_tac_tree_node tac_tree_node =
  map_path_zipper_zipper (zipper_insert_tac_tree_node tac_tree_node)


fun get_path_zipper_state path_zipper = get_path_zipper_zipper path_zipper
  |> get_zipper_content |> get_node_content |> get_goal_cluster_state
  |> get_goal_cluster_state_state

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
