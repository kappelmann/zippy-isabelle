(*  Title:      HOCLP/alternating_qcontainers.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_QCONTAINERS =
sig
  type ('i, 'a, 'b, 'c, 'd) container1
  type ('i, 'a, 'b, 'c, 'd) container2
  type ('i, 'a, 'b, 'c, 'd) container3
  type ('i, 'a, 'b, 'c, 'd) container4

  type ('i, 'a, 'b, 'c, 'd) acontainer1
  type ('i, 'a, 'b, 'c, 'd) acontainer2
  type ('i, 'a, 'b, 'c, 'd) acontainer3
  type ('i, 'a, 'b, 'c, 'd) acontainer4

  val acontainer1 : ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer2, 'c, 'd) container1 ->
    ('i, 'a, 'b, 'c, 'd) acontainer1
  val dest_acontainer1 : ('i, 'a, 'b, 'c, 'd) acontainer1 ->
    ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer2, 'c, 'd) container1

  val acontainer2 : ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer3, 'c, 'd) container2 ->
    ('i, 'a, 'b, 'c, 'd) acontainer2
  val dest_acontainer2 : ('i, 'a, 'b, 'c, 'd) acontainer2 ->
    ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer3, 'c, 'd) container2

  val acontainer3 : ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer4, 'c, 'd) container3 ->
    ('i, 'a, 'b, 'c, 'd) acontainer3
  val dest_acontainer3 : ('i, 'a, 'b, 'c, 'd) acontainer3 ->
    ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer4, 'c, 'd) container3

  val acontainer4 : ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer1, 'c, 'd) container4 ->
    ('i, 'a, 'b, 'c, 'd) acontainer4
  val dest_acontainer4 : ('i, 'a, 'b, 'c, 'd) acontainer4 ->
    ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer1, 'c, 'd) container4

end

functor Alternating_QContainers(
    type ('i, 'a, 'b, 'c, 'd) container1
    type ('i, 'a, 'b, 'c, 'd) container2
    type ('i, 'a, 'b, 'c, 'd) container3
    type ('i, 'a, 'b, 'c, 'd) container4
  ) : ALTERNATING_QCONTAINERS =
struct

type ('i, 'a, 'b, 'c, 'd) container1 = ('i, 'a, 'b, 'c, 'd) container1
type ('i, 'a, 'b, 'c, 'd) container2 = ('i, 'a, 'b, 'c, 'd) container2
type ('i, 'a, 'b, 'c, 'd) container3 = ('i, 'a, 'b, 'c, 'd) container3
type ('i, 'a, 'b, 'c, 'd) container4 = ('i, 'a, 'b, 'c, 'd) container4

datatype ('i, 'a, 'b, 'c, 'd) acontainer1 = Acontainer1 of
  ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer2, 'c, 'd) container1
and ('i, 'a, 'b, 'c, 'd) acontainer2 = Acontainer2 of
  ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer3, 'c, 'd) container2
and ('i, 'a, 'b, 'c, 'd) acontainer3 = Acontainer3 of
  ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer4, 'c, 'd) container3
and ('i, 'a, 'b, 'c, 'd) acontainer4 = Acontainer4 of
  ('i, 'a, ('i, 'b, 'c, 'd, 'a) acontainer1, 'c, 'd) container4

val acontainer1 = Acontainer1
fun dest_acontainer1 (Acontainer1 x) = x

val acontainer2 = Acontainer2
fun dest_acontainer2 (Acontainer2 x) = x

val acontainer3 = Acontainer3
fun dest_acontainer3 (Acontainer3 x) = x

val acontainer4 = Acontainer4
fun dest_acontainer4 (Acontainer4 x) = x

end