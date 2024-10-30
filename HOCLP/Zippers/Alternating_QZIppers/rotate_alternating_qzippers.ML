(*  Title:      HOCLP/rotate_alternating_qzippers.ML
    Author:     Kevin Kappelmann
*)
functor Rotate_Alternating_QZippers(AZ : ALTERNATING_QZIPPERS) :
    ALTERNATING_QZIPPERS
    where type ('i, 'a, 'b, 'c, 'd) Z1.content = ('i, 'a, 'b, 'c, 'd) AZ.Z2.content
    where type ('i, 'a, 'b, 'c, 'd) Z1.zcontext = ('i, 'a, 'b, 'c, 'd) AZ.Z2.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z1.zipper = ('i, 'a, 'b, 'c, 'd) AZ.Z2.zipper
    where type ('i, 'a, 'b, 'c, 'd) Z1.container = ('i, 'a, 'b, 'c, 'd) AZ.Z2.container
    where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) AZ.Z2.cat

    where type ('i, 'a, 'b, 'c, 'd) Z2.content = ('i, 'a, 'b, 'c, 'd) AZ.Z3.content
    where type ('i, 'a, 'b, 'c, 'd) Z2.zcontext = ('i, 'a, 'b, 'c, 'd) AZ.Z3.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z2.zipper = ('i, 'a, 'b, 'c, 'd) AZ.Z3.zipper
    where type ('i, 'a, 'b, 'c, 'd) Z2.container = ('i, 'a, 'b, 'c, 'd) AZ.Z3.container
    where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) AZ.Z3.cat

    where type ('i, 'a, 'b, 'c, 'd) Z3.content = ('i, 'a, 'b, 'c, 'd) AZ.Z4.content
    where type ('i, 'a, 'b, 'c, 'd) Z3.zcontext = ('i, 'a, 'b, 'c, 'd) AZ.Z4.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z3.zipper = ('i, 'a, 'b, 'c, 'd) AZ.Z4.zipper
    where type ('i, 'a, 'b, 'c, 'd) Z3.container = ('i, 'a, 'b, 'c, 'd) AZ.Z4.container
    where type ('i, 'j, 'a, 'b) Z3.cat = ('i, 'j, 'a, 'b) AZ.Z4.cat

    where type ('i, 'a, 'b, 'c, 'd) Z4.content = ('i, 'a, 'b, 'c, 'd) AZ.Z1.content
    where type ('i, 'a, 'b, 'c, 'd) Z4.zcontext = ('i, 'a, 'b, 'c, 'd) AZ.Z1.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z4.zipper = ('i, 'a, 'b, 'c, 'd) AZ.Z1.zipper
    where type ('i, 'a, 'b, 'c, 'd) Z4.container = ('i, 'a, 'b, 'c, 'd) AZ.Z1.container
    where type ('i, 'j, 'a, 'b) Z4.cat = ('i, 'j, 'a, 'b) AZ.Z1.cat

    where type ('i, 'j, 'a, 'b) Down1.cat = ('i, 'j, 'a, 'b) AZ.Down2.cat
    where type ('i, 'j, 'a, 'b) Down2.cat = ('i, 'j, 'a, 'b) AZ.Down3.cat
    where type ('i, 'j, 'a, 'b) Down3.cat = ('i, 'j, 'a, 'b) AZ.Down4.cat
    where type ('i, 'j, 'a, 'b) Down4.cat = ('i, 'j, 'a, 'b) AZ.Down1.cat

    where type ('i, 'j, 'a, 'b) Up1.cat = ('i, 'j, 'a, 'b) AZ.Up2.cat
    where type ('i, 'j, 'a, 'b) Up2.cat = ('i, 'j, 'a, 'b) AZ.Up3.cat
    where type ('i, 'j, 'a, 'b) Up3.cat = ('i, 'j, 'a, 'b) AZ.Up4.cat
    where type ('i, 'j, 'a, 'b) Up4.cat = ('i, 'j, 'a, 'b) AZ.Up1.cat
  =
struct
structure Z1 = AZ.Z2
structure Z2 = AZ.Z3
structure Z3 = AZ.Z4
structure Z4 = AZ.Z1
structure Down1 = AZ.Down2
structure Down2 = AZ.Down3
structure Down3 = AZ.Down4
structure Down4 = AZ.Down1
structure Up1 = AZ.Up2
structure Up2 = AZ.Up3
structure Up3 = AZ.Up4
structure Up4 = AZ.Up1
end
