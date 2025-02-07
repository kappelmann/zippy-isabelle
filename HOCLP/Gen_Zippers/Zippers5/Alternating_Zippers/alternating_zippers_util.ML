(*  Title:    HOCLP/alternating_zippers_util.ML
    Auor:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_UTIL"\<close> =
sig
  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
  structure CO : COROUTINE_UTIL_APPLY
  where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) cat

  val enum_zippers : ('p1, 'zs, 'z) cat -> ('p1, 'z, 'z) cat ->
    ('p1, 'zs, ('p1, 'a, 'z) CO.coroutine) cat
  val list_zippers : ('p1, 'zs, 'z) cat -> ('p1, 'z, 'z) cat -> ('p1, 'zs, 'z list) cat
  val list_container_zippers : ('a, 'z, 'c) cat -> ('a, 'c, 'z) cat -> ('a, 'z, 'z) cat ->
    ('a, 'z, 'z list) cat
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Zippers" ^ "_Util"\<close>(
    structure A : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
    structure CO : COROUTINE_UTIL_APPLY
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_UTIL"\<close> =
struct

open A
structure CO = CO

local
  structure SC = Semi_Category(A); structure M = Monad(K.M); structure A = Kleisli_Arrow(M)
  structure AA = Kleisli_Arrow_Apply(M)
  open SC A M
in

fun enum_zippers first next = first >>> arr (fn x => CO.cons (K x) (CO.enum next x))
fun list_zippers first next = enum_zippers first next >>> arr CO.list_of >>> AA.app' ()
fun list_container_zippers unzip first next = unzip >>> list_zippers first next

end

end