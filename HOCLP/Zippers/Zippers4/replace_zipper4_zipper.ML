(*  Title:      HOCLP/replace_zipper4_zipper.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Zipper4_Zipper(
    structure Z : ZIPPER4
    type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper
    val nzipper :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) nzipper) Z.cat
    val dest_nzipper :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nzipper, ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper) Z.cat
  ) :
    ZIPPER4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) Z.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.content = ('p1, 'a1, 'a2, 'a3, 'a4) Z.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) Z.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  =
Zipper4(
  structure Base =
  struct
    type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper
    val nzipper = nzipper
    val dest_nzipper = dest_nzipper
  end
  structure ZM = Replace_Zipper4_Moves_Zipper(open Base; structure Z = Z.ZM)
  structure ZO = Replace_Zipper4_Optics_Zipper(open Base;
    structure A = Kleisli_Arrow(Z.M); structure Z = Z.ZO)
)
