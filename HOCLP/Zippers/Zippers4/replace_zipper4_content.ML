(*  Title:      HOCLP/replace_zipper4_content.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Zipper4_Content(
    structure Z : ZIPPER4
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent
    val ncontent :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z.ZO.content, ('p1, 'a1, 'a2, 'a3, 'a4) ncontent) Z.cat
    val dest_ncontent :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) ncontent, ('p1, 'a1, 'a2, 'a3, 'a4) Z.ZO.content) Z.cat
  ) :
    ZIPPER4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) Z.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) Z.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  =
Zipper4(
  structure ZM = Z.ZM
  structure ZO = Replace_Zipper4_Optics_Content(
    structure A = Kleisli_Arrow(Z.M)
    structure Z = Z.ZO
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent
    val ncontent = ncontent
    val dest_ncontent = dest_ncontent
  )
)
