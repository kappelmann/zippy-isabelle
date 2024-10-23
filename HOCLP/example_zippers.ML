(* structure List = GList(M) *)
signature LIST_ZIPPER_BASE =
sig
  structure L : GLIST
  include ZIPPER_BASE
  where type ('i, 'c) content = 'c
  where type ('i, 'c) zcontext = 'c L.t * 'c L.t
  where type ('i, 'c) container = 'c L.t
end

functor List_Zipper_Base(L : GLIST where type 'a t = 'a list) : LIST_ZIPPER_BASE =
struct
structure L = L
structure ZD = Zipper_Data
type ('i, 'c) content = 'c
type ('i, 'c) zcontext = 'c L.t * 'c L.t
type ('i, 'c) zipper = (('i, 'c) content, ('i, 'c) zcontext) ZD.zipper
val zipper = ZD.zipper

val get_content = ZD.get_content
val get_zcontext = ZD.get_zcontext

val map_content = ZD.map_content
val map_zcontext = ZD.map_zcontext

type ('i, 'c) container = 'c L.t
fun unzip zipper = let val (rev_pref, suff) = get_zcontext zipper
  in rev rev_pref @ [get_content zipper] @ suff end
end

functor List_Zipper(
    structure Z : LIST_ZIPPER_BASE
    where type 'a L.t = 'a list
    val mk_exn_horizontal : unit -> ('i, 'i, ('i, 'c) Z.zipper, Z.L.A.exn) Z.L.A.cat
  ) =
struct
structure Z = Zipper(
  structure Z = Z
  structure L = Z.L
  structure A = IArrow(L.A)
  structure M = Move_Base(Lazy_ICategory_Base(Z.L.A))
  structure SC = ISemi_Category(A) open SC
  fun init _ = L.dest >>> A.arr (fn (x, xs) => Z.zipper x (L.empty, xs))
  fun dest_zipper zipper =
    let
      val c = Z.get_content zipper
      val (hs, ts) = Z.get_zcontext zipper
    in (hs, (c, ts)) end
  fun up _ = A.arr dest_zipper
    >>> A.first L.dest
    >>> A.arr (fn ((h, hs), (c, ts)) => Z.zipper h (hs, L.cons c ts))
  fun down _ = A.arr dest_zipper
    >>> A.second (A.second L.dest)
    >>> A.arr (fn (hs, (c, (t, ts))) => Z.zipper t (L.cons c hs, ts))
  fun left _ = mk_exn_horizontal () >>> L.A.throw
  fun right _ = mk_exn_horizontal () >>> L.A.throw
)
open Z
fun append_zcontext content = apsnd (fn ts => ts @ [content])
end

signature ROSE_ZIPPER_BASE =
sig
  structure L : GLIST
  type 'a rose
  val dest_rose : 'a rose -> ('a * 'a rose) L.t
  val rose : ('a * 'a rose) L.t -> 'a rose
  include ZIPPER_BASE
  where type ('i, 'c) content = 'c
  where type ('i, 'c) zcontext = 'c rose * ((('c * 'c rose) L.t * ('c * 'c rose) L.t * 'c option) L.t)
  where type ('i, 'c) container = 'c rose
end

functor Rose_Zipper_Base(L : GLIST where type 'a t = 'a list) : ROSE_ZIPPER_BASE =
struct
  structure L = L
  datatype 'a rose = Rose of ('a * 'a rose) L.t
  fun dest_rose (Rose xs) = xs
  fun rose xs = Rose xs

  structure ZD = Zipper_Data
  type ('i, 'c) content = 'c
  type ('i, 'c) zcontext = 'c rose * ((('c * 'c rose) L.t * ('c * 'c rose) L.t * 'c option) L.t)
  type ('i, 'c) zipper = (('i, 'c) content, ('i, 'c) zcontext) ZD.zipper
  val zipper = ZD.zipper

  val get_content = ZD.get_content
  val get_zcontext = ZD.get_zcontext

  val map_content = ZD.map_content
  val map_zcontext = ZD.map_zcontext

  type ('i, 'c) container = 'c rose
  fun unzip zipper =
    let
      val (children, xs) = get_zcontext zipper
      fun mk [(rev_pref, suff, _)] children v = Rose (rev rev_pref @ [(v, children)] @ suff)
        | mk ((rev_pref, suff, SOME c) :: xs) children v = mk xs (Rose (rev rev_pref @ [(v, children)] @ suff)) c
    in mk xs children (get_content zipper) end
end

functor Rose_Zipper(
    structure Z : ROSE_ZIPPER_BASE
    where type L.A.exn = unit
    where type 'a L.t = 'a list
    structure AC : IARROW_CHOICE
    sharing type AC.cat = Z.L.A.cat
  ) =
struct
open Z
structure Z = Zipper(
  structure Z = Z
  structure L = Z.L
  structure A = IArrow(L.A)
  structure M = Move_Base(Lazy_ICategory_Base(Z.L.A))
  structure SC = ISemi_Category(A) open SC
  fun init _ =
    A.arr Z.dest_rose >>> L.dest >>> A.arr (fn ((x, cs), xs) => Z.zipper x (cs, [([], xs, NONE)]))
  fun dest_zipper zipper =
    let
      val c = Z.get_content zipper
      val (ch, xs) = Z.get_zcontext zipper
    in (ch, (c, xs)) end
  fun dest_zipper_flip zipper = dest_zipper zipper |> (fn (ch, (c, xs)) => (xs, (c, ch)))
  fun up _ =
    A.arr dest_zipper_flip
    >>> A.first L.dest
    >>> A.arr (fn (((rev_pref, suff, p), xs), (c, ch)) =>
      Option.map (fn p => Z.zipper p (Z.rose (rev rev_pref @ [(c, ch)] @ suff), xs)) p)
    >>> AC.opt L.A.throw (A.id ())
  fun down _ = A.arr (dest_zipper #> apfst Z.dest_rose)
    >>> A.first L.dest
    >>> A.arr (fn (((c, ch), cs), (p, xs)) => Z.zipper c (ch, (L.cons (L.empty, cs, SOME p) xs)))
  fun left _ = A.arr dest_zipper_flip
    >>> A.first L.dest
    >>> A.first (A.arr (fn ((rev_pref, suff, p), xs) => (rev_pref, (suff, p, xs))))
    >>> A.first (A.first L.dest)
    >>> A.arr (fn ((((r, rch), rs), (suff, p, xs)), (c, ch)) =>
      Z.zipper r (rch, L.cons (rs, L.cons (c, ch) suff , p) xs))
  fun right _ = A.arr dest_zipper_flip
    >>> A.first L.dest
    >>> A.first (A.arr (fn ((rev_pref, suff, p), xs) => (suff, (rev_pref, p, xs))))
    >>> A.first (A.first L.dest)
    >>> A.arr (fn ((((s, sch), ss), (rev_pref, p, xs)), (c, ch)) =>
      Z.zipper s (sch, L.cons (L.cons (c, ch) rev_pref, ss, p) xs))
)
open Z
end
