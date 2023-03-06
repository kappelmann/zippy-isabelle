(*  Title:      Constraint_Logic_Programming/clp.ML
    Author:     Kevin Kappelmann
*)

signature CONSTRAINT_LOGIC_PROGRAMMING =
sig
  structure Logger : LOGGER
end

functor Constraint_Logic_Programming (TI : TERM_INDEX)
  (* : CONSTRAINT_LOGIC_PROGRAMMING = *)
  =
struct

structure Logger = @{new_logger "clp"}

type clp_rule = thm

val pretty_clp_rule = Thm.pretty_thm

val eq_clp_rule = Thm.eq_thm_prop

datatype clp_rules = CLP_Rules of {rules : thm TI.ti}

fun dest_clp_rules (CLP_Rules data) = data

val empty_clp_rules = CLP_Rules {rules = TI.empty}

val eq_rules = Thm.eq_thm_prop

fun merge_clp_rules (clprs1, clprs2) =
  if pointer_eq (clprs1, clprs2) then clprs1
  else
    let
      val CLP_Rules {rules = rules1} = clprs2
      val CLP_Rules {rules = rules2} = clprs2
      val merged_rules = TI.merge eq_rules rules1 rules2
    in CLP_Rules {rules = merged_rules} end

structure CLP_Rules_Data = Generic_Data(
  type T = clp_rules
  val empty = empty_clp_rules
  val merge = merge_clp_rules
)

fun add_clp_rule thm context =
  let
    val ctxt = Context.proof_of context
    val _ = @{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "Adding clp rule ",
        pretty_clp_rule ctxt thm
      ]
      |> Pretty.string_of)
    val thm' = Thm.trim_context thm
    val t = Thm.full_prop_of thm' |> TI.norm_term
    val _ = @{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "Normalised clp rule ",
        Syntax.pretty_term ctxt t
      ]
      |> Pretty.string_of)
    fun update (clprs as CLP_Rules {rules}) =
      CLP_Rules {rules = TI.insert eq_clp_rule (t, thm) rules}
      handle Term_Index_Base.INSERT =>
        (@{log Logger.WARN} ctxt (fn _ =>
          Pretty.block [
            Pretty.str "Clp rule ",
            Syntax.pretty_term ctxt t,
            Pretty.str " already added"
          ]
          |> Pretty.string_of);
        clprs)
    val context' = CLP_Rules_Data.map update context
  in context' end
  (* Thm.trim_context #> (fn thm => Data.map
    (map_transfer_raw (Item_Net.update thm) o
     map_compound_lhs
       (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
          Const (\<^const_name>\<open>Rel\<close>, _) $ _ $ (lhs as (_ $ _)) $ _ =>
            Item_Net.update (lhs, thm)
        | _ => I) o
     map_compound_rhs
       (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
          Const (\<^const_name>\<open>Rel\<close>, _) $ _ $ _ $ (rhs as (_ $ _)) =>
            Item_Net.update (rhs, thm)
        | _ => I) o
     map_known_frees (Term.add_frees (Thm.concl_of thm)))) *)

(* val b = Thm.declaration_attribute (fn thm => fn ctxt => *)
    (* (add_transfer_thm o prep_rule (Context.proof_of ctxt)) thm ctxt) *)

(* val transfer_attribute =
  Attrib.add_del transfer_add transfer_del *)

(* fun attrib f = Thm.declaration_attribute (map_ss o f); *)
(* val unif_hint_add = attrib undefined *)
(* val unif_hint_del = attrib undefined *)

(* val _ = Theory.setup (
  Attrib.setup @{binding unif_hint} (Attrib.add_del unif_hint_add unif_hint_del)
    "declaration of unification hint") *)

  (* Attrib.setup @{binding unif_hint} (Attrib.add_del unif_hint_add unif_hint_del) *)

(* val a : attribute = c *)
(* val a : int Token.context_parser = a *)
(* val a : int Token.parser = a *)
(* type 'a parser = 'a Token.parser; *)
(* type 'a context_parser = 'a Token.context_parser; *)


end
