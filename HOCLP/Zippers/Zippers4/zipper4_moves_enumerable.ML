(*  Title:      HOCLP/zipper4_enumerable..ML
    Author:     Kevin Kappelmann
*)
functor Zipper_Moves4_Enumerable(
    structure A : LAZY_ARROW
    structure L : GLIST
    sharing type L.A.cat = A.T.cat
    structure E : ENUMERABLE4
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) A.cat
    val init_data :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) E.data L.t, ('p1, 'a1, 'a2, 'a3, 'a4) E.init_data) E.move
  ) :
    ZIPPER4_MOVES
    where type ('p1, 'a1, 'a2, 'a3, 'a4) container = ('p1, 'a1, 'a2, 'a3, 'a4) E.init_data
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) E.data L.t
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) E.cat
  =
Zipper4_Moves(
  structure M = E
  type ('p1, 'a1, 'a2, 'a3, 'a4) container = ('p1, 'a1, 'a2, 'a3, 'a4) E.init_data
  type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) E.data L.t

  local structure SC = Semi_Category(E) open SC A
  in
  fun zip _ = E.First.move >>> arr (fn pos => L.cons pos L.empty)
    |> Lazy_Cat_Util.unlift
  val unzip = init_data

  fun lazy_Ldest _ = L.dest

  fun horizontal_move pos_move _ = lazy_Ldest >>> first pos_move >>> arr (uncurry L.cons)
    |> Lazy_Cat_Util.unlift

  fun right _ = horizontal_move E.Next.move
    |> Lazy_Cat_Util.unlift
  fun left _ = horizontal_move E.Prev.move
    |> Lazy_Cat_Util.unlift

  fun down _ = (E.First.move o init_data) &&& id ()
    >>> arr (uncurry L.cons)
    |> Lazy_Cat_Util.unlift

  fun up _ = arr snd o lazy_Ldest
    |> Lazy_Cat_Util.unlift
  end
)