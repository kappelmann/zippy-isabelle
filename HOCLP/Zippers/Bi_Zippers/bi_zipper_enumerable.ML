(*  Title:      HOCLP/bi_zipper_enumerable..ML
    Author:     Kevin Kappelmann
*)
functor Bi_Zipper_Moves_Bi_Enumerable(
    structure A : IARROW
    structure L : GLIST
    sharing type L.A.cat = A.cat
    structure E : BI_ENUMERABLE
    sharing type E.C.cat = L.A.cat
    val init_data : ('i, ('i, 'a, 'b) E.data L.t, ('i, 'a, 'b) E.init_data) E.move
  ) :
    HOM_BI_ZIPPER_MOVES
    where type ('i, 'a, 'b) init_from = ('i, 'a, 'b) E.init_data
    where type ('i, 'a, 'b) data = ('i, 'a, 'b) E.data L.t
    where type ('i, 'j, 'a, 'b) C.cat = ('i, 'j, 'a, 'b) E.C.cat
  =
Hom_Bi_Zipper_Moves(
  structure M = E
  type ('i, 'a, 'b) init_from = ('i, 'a, 'b) E.init_data
  type ('i, 'a, 'b) data = ('i, 'a, 'b) E.data L.t

  local structure SC = ISemi_Category(E.C) open SC
  in
  fun init _ = E.First.move () >>> A.arr (fn pos => L.cons pos L.empty)

  fun horizontal_move pos_move _ = L.dest
    >>> A.first (pos_move ())
    >>> A.arr (uncurry L.cons)

  fun right _ = horizontal_move E.Next.move ()
  fun left _ = horizontal_move E.Prev.move ()

  fun down _ =
    A.&&& (A.comp_lazy E.First.move (init_data ()), A.id ())
    >>> A.arr (uncurry L.cons)

  fun up _ = A.comp (A.arr snd) L.dest
  end
)

functor Bi_Zipper_Bi_Enumerable(
    structure A : IARROW
    structure L : GLIST
    sharing type L.A.cat = A.cat
    structure E : BI_ENUMERABLE
    sharing type E.C.cat = L.A.cat
    val init_data : ('i, ('i, 'a, 'b) E.data L.t, ('i, 'a, 'b) E.init_data) E.move
    val unzip : ('i, 'a, 'b) E.data L.t -> ('i, 'a, 'b) E.init_data
  ) :
    BI_ZIPPER
    where type ('i, 'a, 'b) content = ('i, 'a, 'b) E.data L.t
    where type ('i, 'a, 'b) zcontext = unit
    where type ('i, 'a, 'b) zipper = ('i, 'a, 'b) E.data L.t
    where type ('i, 'a, 'b) container = ('i, 'a, 'b) E.init_data
    where type ('i, 'j, 'a, 'b) C.cat = ('i, 'j, 'a, 'b) E.C.cat
  =
Content_Bi_Zipper(
  structure M = Bi_Zipper_Moves_Bi_Enumerable(
    structure A = A; structure L = L; structure E = E; val init_data = init_data)
  val unzip = unzip
)