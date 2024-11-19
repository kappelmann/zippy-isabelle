(*  Title:      HOCLP/zipper4.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER4 =
sig
  include MOVE_BASE
  type ('p1, 'a1, 'a2, 'a3, 'a4) zipper
  structure ZM : ZIPPER4_MOVES
  structure ZO : ZIPPER4_OPTICS
  sharing type ZM.zipper = zipper
  sharing type ZO.zipper = zipper
  sharing type ZM.cat = cat
  sharing type ZO.L.C.cat = cat
end

functor Zipper4(
    structure ZM : ZIPPER4_MOVES
    structure ZO : ZIPPER4_OPTICS
    sharing type ZO.zipper = ZM.zipper
    sharing type ZO.L.C.cat = ZM.cat
  ) : ZIPPER4 =
struct

structure ZM = ZM
structure ZO = ZO
open ZM

end

functor Instantiate_Zipper4(
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst1
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst2
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst3
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst4
    structure Z : ZIPPER4
  ) :
    ZIPPER4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst2, ('p1, 'a1, 'a2, 'a3, 'a4) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst4) Z.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst2, ('p1, 'a1, 'a2, 'a3, 'a4) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst4) Z.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst2, ('p1, 'a1, 'a2, 'a3, 'a4) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst4) Z.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst2, ('p1, 'a1, 'a2, 'a3, 'a4) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst4) Z.zipper
  = Z

