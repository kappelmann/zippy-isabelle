(*  Title:      HOCLP/util.ML
    Author:     Kevin Kappelmann
Utilities used for HOCLP.
*)
signature HOCLP_UTIL =
sig
end

structure HOCLP_Util  =
(* : HOCLP_UTIL = *)
struct

fun min_ord ord x y = if is_less_equal (ord (x, y)) then x else y
fun max_ord ord x y = if is_greater_equal (ord (x, y)) then x else y

fun eq_ord _ = EQUAL
fun fst_ord ord = prod_ord ord eq_ord

end
