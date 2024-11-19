(*  Title:      HOCLP/modify_node5.ML
    Author:     Kevin Kappelmann
*)
functor Node4_Node5(
    structure N : NODE5
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst1
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst2
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst3
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst4
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst5
  ) :
    NODE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst1, ('p1, 'a1, 'a2, 'a3, 'a4) inst2,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst3, ('p1, 'a1, 'a2, 'a3, 'a4) inst4,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst5) N.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst1, ('p1, 'a1, 'a2, 'a3, 'a4) inst2,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst3, ('p1, 'a1, 'a2, 'a3, 'a4) inst4,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst5) N.next
    where type ('p1, 'a1, 'a2, 'a3, 'a4) node = ('p1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst1, ('p1, 'a1, 'a2, 'a3, 'a4) inst2,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst3, ('p1, 'a1, 'a2, 'a3, 'a4) inst4,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst5) N.node
  =
struct
open N
type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1,
  ('p1, 'a1, 'a2, 'a3, 'a4) inst1, ('p1, 'a1, 'a2, 'a3, 'a4) inst2,
  ('p1, 'a1, 'a2, 'a3, 'a4) inst3, ('p1, 'a1, 'a2, 'a3, 'a4) inst4,
  ('p1, 'a1, 'a2, 'a3, 'a4) inst5) content
type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1,
  ('p1, 'a1, 'a2, 'a3, 'a4) inst1, ('p1, 'a1, 'a2, 'a3, 'a4) inst2,
  ('p1, 'a1, 'a2, 'a3, 'a4) inst3, ('p1, 'a1, 'a2, 'a3, 'a4) inst4,
  ('p1, 'a1, 'a2, 'a3, 'a4) inst5) next
type ('p1, 'a1, 'a2, 'a3, 'a4) node = ('p1,
  ('p1, 'a1, 'a2, 'a3, 'a4) inst1, ('p1, 'a1, 'a2, 'a3, 'a4) inst2,
  ('p1, 'a1, 'a2, 'a3, 'a4) inst3, ('p1, 'a1, 'a2, 'a3, 'a4) inst4,
  ('p1, 'a1, 'a2, 'a3, 'a4) inst5) node
end