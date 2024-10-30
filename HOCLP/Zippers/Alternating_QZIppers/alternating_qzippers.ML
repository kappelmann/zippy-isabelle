(*  Title:      HOCLP/alternating_qzippers.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_QZIPPERS =
sig
  structure Z1 : QZIPPER
  structure Z2 : QZIPPER
  structure Z3 : QZIPPER
  structure Z4 : QZIPPER

  structure Down1 : QMOVE
  where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z1.zipper
  where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'b, 'c, 'd, 'a) Z2.zipper

  structure Down2 : QMOVE
  where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z2.zipper
  where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'b, 'c, 'd, 'a) Z3.zipper

  structure Down3 : QMOVE
  where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z3.zipper
  where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'b, 'c, 'd, 'a) Z4.zipper

  structure Down4 : QMOVE
  where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z4.zipper
  where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'b, 'c, 'd, 'a) Z1.zipper

  structure Up1 : QMOVE
  where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z1.zipper
  where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'd, 'a, 'b, 'c) Z4.zipper

  structure Up2 : QMOVE
  where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z2.zipper
  where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'd, 'a, 'b, 'c) Z1.zipper

  structure Up3 : QMOVE
  where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z3.zipper
  where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'd, 'a, 'b, 'c) Z2.zipper

  structure Up4 : QMOVE
  where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z4.zipper
  where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'd, 'a, 'b, 'c) Z3.zipper
end
