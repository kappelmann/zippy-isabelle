(*  Title:      HOCLP/hoclp_rule.ML
    Author:     Kevin Kappelmann
*)
functor HOCLP_Rules(A : sig
    structure FIA : FUNCTOR_INSTANCE_ARGS
    structure TI : TERM_INDEX
    type tac
    val eq_tac : tac * tac -> bool
    val pretty_tac : Proof.context -> tac -> Pretty.T
  end) =
struct

open A
structure FIU = Functor_Instance_Util(A.FIA)
structure MLCU = ML_Code_Util
structure Show = SpecCheck_Show

val logger = Logger.setup_new_logger hoclp_logger FIU.FIA.full_name

type rule = tac list * thm

fun eq_rule ((tacs1, thm1), (tacs2, thm2)) =
  Thm.eq_thm (thm1, thm2) andalso List.all eq_tac (tacs1 ~~ tacs2)
  handle ListPair.UnequalLengths => false

fun pretty_rule ctxt (tacs, thm) =
  let
    val pretty_term = Show.term ctxt
    val pretty_term_tac = Show.zip pretty_term (pretty_tac ctxt)
    val pretty_prem_datas = map2 (curry pretty_term_tac) (Thm.prems_of thm) tacs
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
    "Number of passed tactics (",
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

val term_index_key_of_subgoal = Term_Util.strip_subgoal #> snd #> snd #> TI.norm_term
val term_index_key_of_thm = Thm.prop_of #> term_index_key_of_subgoal

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

fun get_unifiable_rules subgoal context =
  let
    val ctxt = Context.proof_of context
    val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Retrieving HOCLP rule for ",
        Show.term ctxt subgoal
      ] |> Pretty.string_of)
    val key = term_index_key_of_subgoal subgoal
    val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.block [
        Pretty.str "Computed term key: ",
        Show.term ctxt key
      ] |> Pretty.string_of)
    val (Rules {rules : rule TI.term_index}) = rules_data.get context
    val rules = TI.unifiables rules key
  in rules end

fun attr operation (datas, pos) =
  let val code = MLCU.read "curry" @ FIU.code_struct_op (ML_Syntax_Util.atomic operation) @
    MLCU.list datas
  in ML_Attribute.run_declaration_attribute (code, pos) end

val add_attr = attr "add_rule"
val delete_attr = attr "delete_rule"

end
