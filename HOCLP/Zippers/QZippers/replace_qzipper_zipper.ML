(*  Title:      HOCLP/replace_qzipper_zipper.ML
    Author:     Kevin Kappelmann
*)
functor Replace_QZipper_Base_Zipper(
    structure Z : QZIPPER_BASE
    type ('i, 'a, 'b, 'c, 'd) nzipper
    val nzipper : ('i, 'a, 'b, 'c, 'd) Z.zipper -> ('i, 'a, 'b, 'c, 'd) nzipper
    val dest_nzipper : ('i, 'a, 'b, 'c, 'd) nzipper -> ('i, 'a, 'b, 'c, 'd) Z.zipper
  ) :
    QZIPPER_BASE
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) Z.content
    where type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) Z.zcontext
    where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) nzipper
    where type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) Z.container
  =
struct

open Z
type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) nzipper

fun zipper x zctxt = Z.zipper x zctxt |> nzipper
fun get_content x = x |> dest_nzipper |> Z.get_content
fun get_zcontext x = x |> dest_nzipper |> Z.get_zcontext

fun map_content f z = dest_nzipper z |> Z.map_content f |> nzipper
fun map_zcontext f z = dest_nzipper z |> Z.map_zcontext f |> nzipper

fun unzip z = dest_nzipper z |> Z.unzip
end

functor Replace_QZipper_Zipper(
    structure A : LAZY_IARROW_BASE
    structure Z : QZIPPER
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.T.lcat
    type ('i, 'a, 'b, 'c, 'd) nzipper
    val nzipper : ('i, 'a, 'b, 'c, 'd) Z.zipper -> ('i, 'a, 'b, 'c, 'd) nzipper
    val dest_nzipper : ('i, 'a, 'b, 'c, 'd) nzipper -> ('i, 'a, 'b, 'c, 'd) Z.zipper
  ) :
    QZIPPER
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) Z.content
    where type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) Z.zcontext
    where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) nzipper
    where type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) Z.container
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) Z.cat
  =
QZipper_QZipper_Moves(
  structure M = Replace_Hom_QZipper_Moves_Data(
    structure C = A
    structure M = Z
    type ('i, 'a, 'b, 'c, 'd) ndata = ('i, 'a, 'b, 'c, 'd) nzipper
    fun ndata _ = A.arr nzipper ()
    fun dest_ndata _ = A.arr dest_nzipper ()
  )
  structure Z = Replace_QZipper_Base_Zipper(
    structure Z = Z; type ('i, 'a, 'b, 'c, 'd) nzipper = ('i, 'a, 'b, 'c, 'd) nzipper;
    val nzipper = nzipper; val dest_nzipper = dest_nzipper)
)
