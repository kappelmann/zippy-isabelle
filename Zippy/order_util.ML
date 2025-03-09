(*  Title:      ML_Utils/order_util.ML
    Author:     Kevin Kappelmann

Order utilities.
*)
signature ORDER_UTIL =
sig
  val max_ord : ('a * 'a -> 'a) -> 'a ord -> 'a * 'a -> 'a
  val min_ord : ('a * 'a -> 'a) -> 'a ord -> 'a * 'a -> 'a
  val fst_ord : 'a ord -> ('a * 'b) ord
  val snd_ord : 'b ord -> ('a * 'b) ord
  val update_eq_ord : 'a ord -> 'a ord -> 'a ord
end

structure Order_Util : ORDER_UTIL =
struct

fun max_ord eq_sel ord (x, y) = case ord (x, y) of
    GREATER => x
  | LESS => y
  | EQUAL => eq_sel (x, y)
fun min_ord eq_sel ord (x, y) = case ord (x, y) of
    GREATER => y
  | LESS => x
  | EQUAL => eq_sel (x, y)

fun fst_ord ord ((x, _), (x', _)) = ord (x, x')
fun snd_ord ord ((_, y), (_, y')) = ord (y, y')
fun update_eq_ord ord_eq ord p = case ord p of
    EQUAL => ord_eq p
  | ord => ord

end
