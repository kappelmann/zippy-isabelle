(*  Title:      HOCLP/zippy_with_goals.ML
    Author:     Kevin Kappelmann

Zippy with goals.
*)
signature ZIPPY_WITH_GOALS =
sig
  type gclusters
  type gcluster
  type focus

  structure GCSD : KLEISLI_ZIPPY_GCLUSTERS_DATA
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcsd_more
  structure GCD : ZIPPY_GCLUSTER_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) GCSD.L.C.cat
  sharing type GCD.L.lens = GCSD.L.lens
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcd_more
  structure FD : ZIPPY_FOCUS_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) GCSD.L.C.cat
  sharing type FD.L.lens = GCSD.L.lens
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_fd_more
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_fd_more

  include ZIPPY_WITH_PRESULTS
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) N1.content =
    (gclusters, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcsd_more) GCSD.gclusters_data
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) N2.content =
    (gcluster, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcd_more) GCD.gcluster_data
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_and_more = (focus,
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_fd_more) FD.focus_data
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_and_more = (focus,
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_fd_more) FD.focus_data
  where type ('p1, 'a) M.t = ('p1, 'a) GCSD.K.M.t
  where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) GCSD.L.lens

end

functor Zippy_With_Goals(
    type gclusters
    type gcluster
    type focus

    structure GCSD : KLEISLI_ZIPPY_GCLUSTERS_DATA
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcsd_more
    structure GCD : ZIPPY_GCLUSTER_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) GCSD.L.C.cat
    sharing type GCD.L.lens = GCSD.L.lens
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcd_more
    structure FD : ZIPPY_FOCUS_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) GCSD.L.C.cat
    sharing type FD.L.lens = GCSD.L.lens
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_fd_more
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_fd_more

    structure Z : ZIPPY_WITH_PRESULTS
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) N1.content = 'a1
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) N2.content = 'a2
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_and_more = 'a4
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_and_more = 'a5
    where type ('p1, 'a) M.t = ('p1, 'a) GCSD.K.M.t
    where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) GCSD.L.lens
  ) : ZIPPY_WITH_GOALS =
struct

type gclusters = gclusters
type gcluster = gcluster
type focus = focus

structure GCSD = GCSD
type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcsd_more = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcsd_more
structure GCD = GCD
type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcd_more = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcd_more
structure FD = FD
type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_fd_more = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_fd_more
type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_fd_more = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_fd_more

structure Z = Instantiate_Zippy_With_PResults(
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1 =
    (gclusters, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcsd_more) GCSD.gclusters_data
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2 =
    (gcluster, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcd_more) GCD.gcluster_data
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3 = 'a3
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4 =
    (focus, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_fd_more) FD.focus_data
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5 =
    (focus, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_fd_more) FD.focus_data
  structure Z = Z
)
open Z

end

functor Instantiate_Zippy_With_Goals(
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5
    structure Z : ZIPPY_WITH_GOALS
  ) :
    ZIPPY_WITH_GOALS
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.zipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext1 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext1
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext2 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext2
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext3 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext3
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext4 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext4
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext5 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext5
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper1 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper1
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper2 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper2
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper3 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper3
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper4 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper4
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper5 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper5
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcsd_more = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.gcsd_more
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) gcd_more = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.gcd_more
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.cd_more
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_fd_more = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.action_fd_more
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_fd_more = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.aaction_fd_more
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.paction
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) copy = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.copy
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.presults =
struct
open Z
structure Base =
struct
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5
end
structure Z = Instantiate_Zippy_With_PResults(open Base; structure Z = Z)
open Z
end
