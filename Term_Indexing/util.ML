(*  Title: Term_Indexing/util.ML
    Author: Kevin Kappelmann

Utilities for term indexes.
*)
signature TERM_INDEXING_UTIL =
sig
  val norm_term_beta_eta_short : term -> term
end

structure Term_Indexing_Util : TERM_INDEXING_UTIL =
struct

val norm_term_beta_eta_short = Envir.beta_eta_contract

end

