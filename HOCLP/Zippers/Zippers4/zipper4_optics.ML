(*  Title:      HOCLP/zipper4_optics.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER4_OPTICS =
sig
  structure L : LENS
  type ('p1, 'a1, 'a2, 'a3, 'a4) zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) content
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext

  val zipper : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) content * ('p1, 'a1, 'a2, 'a3, 'a4) zcontext,
    ('p1, 'a1, 'a2, 'a3, 'a4) zipper) L.C.cat

  val content : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper, ('p1, 'a1, 'a2, 'a3, 'a4) content) L.slens
  val zcontext : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext) L.slens
  val get_content :
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper, ('p1, 'a1, 'a2, 'a3, 'a4) content) L.getter
  val get_zcontext :
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext) L.getter
  val map_content :
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper, ('p1, 'a1, 'a2, 'a3, 'a4) content) L.smodifier
  val map_zcontext :
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext) L.smodifier
end

functor Instantiate_Zipper4_Optics(
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst1
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst2
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst3
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst4
    structure Z : ZIPPER4_OPTICS
  ) :
    ZIPPER4_OPTICS
    where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst2, ('p1, 'a1, 'a2, 'a3, 'a4) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst4) Z.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst2, ('p1, 'a1, 'a2, 'a3, 'a4) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst4) Z.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst2, ('p1, 'a1, 'a2, 'a3, 'a4) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst4) Z.zipper
  = Z
