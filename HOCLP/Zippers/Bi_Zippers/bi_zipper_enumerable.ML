(*  Title:      HOCLP/bi_zipper_enumerable..ML
    Author:     Kevin Kappelmann
*)
functor Bi_Zipper_Moves_Bi_Enumerable(
    structure L : GLIST
    structure E : BI_ENUMERABLE
    sharing type E.K.M.t = L.M.t
    val init_data : ('i, ('i, 'a, 'b) E.data L.t, ('i, 'a, 'b) E.init_data) E.move
  ) :
    HOM_BI_ZIPPER_MOVES
    where type ('i, 'a, 'b) init_from = ('i, 'a, 'b) E.init_data
    where type ('i, 'a, 'b) data = ('i, 'a, 'b) E.data L.t
    where type ('i, 'j, 'a) K.M.t = ('i, 'j, 'a) E.K.M.t
  =
Hom_Bi_Zipper_Moves(
  structure M = E
  type ('i, 'a, 'b) init_from = ('i, 'a, 'b) E.init_data
  type ('i, 'a, 'b) data = ('i, 'a, 'b) E.data L.t

  structure A = IArrow(IKleisli_IArrow_Apply(E.K.M))

  fun init x = x |>
    (E.First.move
    |> A.comp (A.arr (fn pos => L.cons pos L.empty)))

  fun horizontal_move pos_move = L.dest
    |> A.comp (A.first pos_move)
    |> A.comp (A.arr (uncurry L.cons))

  fun right p = p |> horizontal_move E.Next.move
  fun left p = p |>horizontal_move E.Prev.move

  fun down p = p |>
    (A.&&& (A.comp E.First.move init_data, A.id ())
    |> A.comp (A.arr (uncurry L.cons)))

  fun up p = p |> (L.dest |> A.comp (A.arr snd))
)

functor Bi_Zipper_Bi_Enumerable(
    structure L : GLIST
    structure E : BI_ENUMERABLE
    sharing type E.K.M.t = L.M.t
    val init_data : ('i, ('i, 'a, 'b) E.data L.t, ('i, 'a, 'b) E.init_data) E.move
    val unzip : ('i, 'a, 'b) E.data L.t -> ('i, 'a, 'b) E.init_data
  ) :
    BI_ZIPPER
    where type ('i, 'a, 'b) content = ('i, 'a, 'b) E.data L.t
    where type ('i, 'a, 'b) zcontext = unit
    where type ('i, 'a, 'b) zipper = ('i, 'a, 'b) E.data L.t
    where type ('i, 'a, 'b) container = ('i, 'a, 'b) E.init_data
    where type ('i, 'j, 'a) K.M.t = ('i, 'j, 'a) E.K.M.t
  =
Content_Bi_Zipper(
  structure M = Bi_Zipper_Moves_Bi_Enumerable(
    structure L = L; structure E = E; val init_data = init_data)
  val unzip = unzip
)