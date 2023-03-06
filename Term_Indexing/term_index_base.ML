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
  type 'a ti
  val empty : 'a ti
  val is_empty : 'a ti -> bool
  val content : 'a ti -> 'a list

  (*puts a term into normal form as required by the index structure*)
  val norm_term : term -> term
  (*first argument is the equality test for values;
  raises Term_Index_Base.INSERT if the term, value pair is already inserted*)
  val insert : (('a * 'a) -> bool) -> (term * 'a) -> 'a ti -> 'a ti
  val insert_safe : (('a * 'a) -> bool) -> (term * 'a) -> 'a ti -> 'a ti

  (*first argument selects which values for the given term should be removed;
  raises Term_Index_Base.DELETE if no value is deleted*)
  val delete : ('a -> bool) -> term -> 'a ti -> 'a ti
  val delete_safe : ('a -> bool) -> term -> 'a ti -> 'a ti

  val variants : 'a ti -> term -> 'a list
  val generalisations : 'a ti -> term -> 'a list
  val instances : 'a ti -> term -> 'a list
  val unifiables : 'a ti -> term -> 'a list

  (*first argument is the equality test for values*)
  val merge : (('a * 'a) -> bool) -> 'a ti -> 'a ti -> 'a ti
end