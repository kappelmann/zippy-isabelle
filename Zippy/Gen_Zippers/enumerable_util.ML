(*  Title:    HOCLP/enumerable_util.ML
    Auor:     Kevin Kappelmann
*)
signature ENUMERABLE_UTIL =
sig
  structure CO : COROUTINE_UTIL_APPLY

  val enum : ('p1, 'zs, 'z) CO.C.cat -> ('p1, 'z, 'z) CO.C.cat ->
    ('p1, 'zs, ('p1, 'a, 'z) CO.coroutine) CO.C.cat
  val list : ('p1, 'zs, 'z) CO.C.cat -> ('p1, 'z, 'z) CO.C.cat -> ('p1, 'zs, 'z list) CO.C.cat
end

functor Enumerable_Util(structure CO : COROUTINE_UTIL_APPLY) : ENUMERABLE_UTIL =
struct

structure CO = CO

local structure SC = Semi_Category(CO.C); structure A = Arrow(CO.AA) open SC A
in
fun enum first next = first >>> arr (fn x => CO.cons (K x) (CO.enum next x))
fun list first next = enum first next >>> arr CO.list_of >>> CO.AA.app' ()
end

end