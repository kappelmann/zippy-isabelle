(*  Title:      HOCLP/zipper4_moves_enumerable..ML
    Author:     Kevin Kappelmann
*)
functor Zipper_Moves4_Enumerable(
    structure L : GLIST
    structure E : ENUMERABLE4
    sharing type E.M.t = L.M.t
    val init_data :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) E.data L.t, ('p1, 'a1, 'a2, 'a3, 'a4) E.init_data) E.move
  ) :
    ZIPPER4_MOVES
    where type ('p1, 'a1, 'a2, 'a3, 'a4) container = ('p1, 'a1, 'a2, 'a3, 'a4) E.init_data
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) E.data L.t
    where type ('p1, 'a) M.t = ('p1, 'a) E.M.t
  =
Zipper4_Moves(
  structure M = E
  type ('p1, 'a1, 'a2, 'a3, 'a4) container = ('p1, 'a1, 'a2, 'a3, 'a4) E.init_data
  type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) E.data L.t

  local structure SC = Semi_Category(E); structure A = Kleisli_Arrow(E.M) open SC A
  in
  fun zip x = x |> (E.First.move >>> arr (fn pos => L.cons pos L.empty))
  val unzip = init_data

  fun horizontal_move pos_move x = x |> (L.dest >>> first pos_move >>> arr (uncurry L.cons))

  fun right x = x |> horizontal_move E.Next.move
  fun left x = x |> horizontal_move E.Prev.move
  fun down x = x |> ((init_data >>> E.First.move) &&& id ()
    >>> arr (uncurry L.cons))
  fun up x = x |> (L.dest >>> arr snd)
  end
)