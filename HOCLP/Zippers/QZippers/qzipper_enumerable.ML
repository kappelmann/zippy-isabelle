(*  Title:      HOCLP/qzipper_enumerable..ML
    Author:     Kevin Kappelmann
*)
functor QZipper_Moves_QEnumerable(
    structure A : LAZY_IARROW
    structure L : GLIST
    sharing type L.A.cat = A.T.cat
    structure E : QENUMERABLE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.T.lcat
    val init_data : ('i, ('i, 'a, 'b, 'c, 'd) E.data L.t, ('i, 'a, 'b, 'c, 'd) E.init_data) E.move
  ) :
    HOM_QZIPPER_MOVES
    where type ('i, 'a, 'b, 'c, 'd) init_from = ('i, 'a, 'b, 'c, 'd) E.init_data
    where type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) E.data L.t
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) E.cat
  =
Hom_QZipper_Moves(
  structure M = E
  type ('i, 'a, 'b, 'c, 'd) init_from = ('i, 'a, 'b, 'c, 'd) E.init_data
  type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) E.data L.t

  local structure SC = ISemi_Category(E) open SC
  in
  fun init _ = (E.First.move >>> A.arr (fn pos => L.cons pos L.empty)) ()

  fun lazy_Ldest _ = L.dest

  fun horizontal_move pos_move _ = (lazy_Ldest >>> A.first pos_move >>> A.arr (uncurry L.cons)) ()

  fun right _ = horizontal_move E.Next.move ()
  fun left _ = horizontal_move E.Prev.move ()

  fun down _ = (A.&&& (E.First.move o init_data, A.id ())
    >>> A.arr (uncurry L.cons))
    ()

  fun up _ = (A.arr snd o lazy_Ldest) ()
  end
)

functor QZipper_QEnumerable(
    structure A : LAZY_IARROW
    structure L : GLIST
    sharing type L.A.cat = A.T.cat
    structure E : QENUMERABLE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.T.lcat
    val init_data : ('i, ('i, 'a, 'b, 'c, 'd) E.data L.t, ('i, 'a, 'b, 'c, 'd) E.init_data) E.move
    val unzip : ('i, 'a, 'b, 'c, 'd) E.data L.t -> ('i, 'a, 'b, 'c, 'd) E.init_data
  ) :
    QZIPPER
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) E.data L.t
    where type ('i, 'a, 'b, 'c, 'd) zcontext = unit
    where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) E.data L.t
    where type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) E.init_data
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) E.cat
  =
Content_QZipper(
  structure M = QZipper_Moves_QEnumerable(
    structure A = A; structure L = L; structure E = E; val init_data = init_data)
  val unzip = unzip
)