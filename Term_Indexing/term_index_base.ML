(*  Title: Term_Indexing/term_index_base.ML
    Author: Kevin Kappelmann

Basic signature for term indexes.
*)

signature TERM_INDEX_BASE =
sig
  exception INSERT
  exception DELETE
end

structure Term_Index_Base : TERM_INDEX_BASE =
struct
  exception INSERT
  exception DELETE
end

signature TERM_INDEX =
sig
  type 'a term_index
  val empty : 'a term_index
  val is_empty : 'a term_index -> bool
  val content : 'a term_index -> 'a list

  (*puts a term into normal form as required by the index structure*)
  val norm_term : term -> term
  (*first argument is the equality test for values;
  raises Term_Index_Base.INSERT if the term, value pair is already inserted*)
  val insert : (('a * 'a) -> bool) -> (term * 'a) -> 'a term_index -> 'a term_index
  val insert_safe : (('a * 'a) -> bool) -> (term * 'a) -> 'a term_index -> 'a term_index

  (*first argument selects which values for the given term should be removed;
  raises Term_Index_Base.DELETE if no value is deleted*)
  val delete : ('a -> bool) -> term -> 'a term_index -> 'a term_index
  val delete_safe : ('a -> bool) -> term -> 'a term_index -> 'a term_index

  val variants : 'a term_index -> term -> 'a list
  val generalisations : 'a term_index -> term -> 'a list
  val instances : 'a term_index -> term -> 'a list
  val unifiables : 'a term_index -> term -> 'a list

  (*first argument is the equality test for values*)
  val merge : (('a * 'a) -> bool) -> 'a term_index -> 'a term_index -> 'a term_index
end