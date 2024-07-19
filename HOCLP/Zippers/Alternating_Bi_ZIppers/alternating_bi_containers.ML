(*  Title:      HOCLP/alternating_bi_containers.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_BI_CONTAINERS =
sig
  type ('i, 'a, 'b) container1
  type ('i, 'a, 'b) container2

  type ('i, 'a, 'b) acontainer1
  type ('i, 'a, 'b) acontainer2

  val acontainer1 : ('i, 'a, ('i, 'b, 'a) acontainer2) container1 -> ('i, 'a, 'b) acontainer1
  val dest_acontainer1 : ('i, 'a, 'b) acontainer1 -> ('i, 'a, ('i, 'b, 'a) acontainer2) container1

  val acontainer2 : ('i, 'a, ('i, 'b, 'a) acontainer1) container2 -> ('i, 'a, 'b) acontainer2
  val dest_acontainer2 : ('i, 'a, 'b) acontainer2 -> ('i, 'a, ('i, 'b, 'a) acontainer1) container2
end

functor Alternating_Bi_Containers(type ('i, 'a, 'b) container1; type ('i, 'a, 'b) container2)
  : ALTERNATING_BI_CONTAINERS =
struct

type ('i, 'a, 'b) container1 = ('i, 'a, 'b) container1
type ('i, 'a, 'b) container2 = ('i, 'a, 'b) container2

datatype ('i, 'a, 'b) acontainer1 = Acontainer1 of ('i, 'a, ('i, 'b, 'a) acontainer2) container1
and ('i, 'a, 'b) acontainer2 = Acontainer2 of ('i, 'a, ('i, 'b, 'a) acontainer1) container2

val acontainer1 = Acontainer1
fun dest_acontainer1 (Acontainer1 n) = n

val acontainer2 = Acontainer2
fun dest_acontainer2 (Acontainer2 n) = n

end