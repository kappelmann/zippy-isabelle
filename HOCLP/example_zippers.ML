signature LIST_ZIPPER4 =
sig
  structure LI : GLIST
  include ZIPPER4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.content = 'a1
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext = 'a1 LI.t * 'a1 LI.t
  where type ('p1, 'a1, 'a2) ZO.L.C.cat = ('p1, 'a1, 'a2) LI.A.cat
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZM.container = 'a1 LI.t
  val append_zcontext : 'a1 -> ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext ->
    ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext
end

functor List_Zipper(
    structure A : LAZY_ARROW
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
    structure LI : GLIST
    where type 'a t = 'a list
    where type ('p1, 'a, 'b) A.cat = ('p1, 'a, 'b) A.cat
    val mk_exn_horizontal : ('p1, unit, LI.A.exn) LI.A.cat
  ) : LIST_ZIPPER4 =
struct

structure LI = LI
structure ZO = Zipper4_Optics_Zipper_Data(
struct
  structure ZD = Zipper_Data
  structure A = A
  structure L = L
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = 'a1
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = 'a1 LI.t * 'a1 LI.t
end
)
structure ZM = Zipper4_Moves(
  structure M = Move_Base(A)
  structure SC = Semi_Category(A) open SC ZO A
  type ('p1, 'a1, 'a2, 'a3, 'a4) container = 'a1 LI.t
  fun zip _ = LI.dest >>> second (arr (pair LI.empty)) >>> zipper
    |> Lazy_Cat_Util.unlift
  fun unzip _ = get_content &&& get_zcontext
    >>> arr (fn (c, (rev_pref, suff)) => rev rev_pref @ [c] @ suff)
    |> Lazy_Cat_Util.unlift
  fun dest_zipper _ = get_content &&& get_zcontext
    >>> arr (fn (c, (hs, ts)) => (hs, (c, ts)))
    |> Lazy_Cat_Util.unlift
  fun up _ = dest_zipper
    >>> first LI.dest
    >>> arr (fn ((h, hs), (c, ts)) => (h, (hs, LI.cons c ts)))
    >>> zipper
    |> Lazy_Cat_Util.unlift
  fun down _ = dest_zipper
    >>> second (second LI.dest)
    >>> arr (fn (hs, (c, (t, ts))) => (t, (LI.cons c hs, ts)))
    >>> zipper
    |> Lazy_Cat_Util.unlift
  fun left _ = K () >>> mk_exn_horizontal >>> LI.A.throw
    |> Lazy_Cat_Util.unlift
  fun right _ = K () >>> mk_exn_horizontal >>> LI.A.throw
    |> Lazy_Cat_Util.unlift
)

structure Z = Zipper4(structure ZO = ZO; structure ZM = ZM)
open Z

fun append_zcontext content = apsnd (fn ts => ts @ [content])

end

signature ROSE_ZIPPER =
sig
  structure LI : GLIST
  type 'a rose
  val dest_rose : 'a rose -> ('a * 'a rose) LI.t
  val rose : ('a * 'a rose) LI.t -> 'a rose
  include ZIPPER4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.content = 'a1
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext =
    'a1 rose * ((('a1 * 'a1 rose) LI.t * ('a1 * 'a1 rose) LI.t * 'a1 option) LI.t)
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZM.container = 'a1 rose
end

functor Rose_Zipper(
    structure A : LAZY_ARROW
    structure AC : ARROW_CHOICE
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) A.cat
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
    structure LI : GLIST
    where type 'a t = 'a list
    where type A.exn = unit
    where type ('p1, 'a, 'b) A.cat = ('p1, 'a, 'b) A.cat
  ) : ROSE_ZIPPER =
struct

structure LI = LI

datatype 'a rose = Rose of ('a * 'a rose) LI.t
fun dest_rose (Rose xs) = xs
fun rose xs = Rose xs

structure ZO = Zipper4_Optics_Zipper_Data(
struct
  structure ZD = Zipper_Data
  structure A = A
  structure L = L
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = 'a1
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext =
    'a1 rose * (('a1 * 'a1 rose) LI.t * ('a1 * 'a1 rose) LI.t * 'a1 option) LI.t
end
)

structure ZM = Zipper4_Moves(
  structure M = Move_Base(A)
  structure SC = Semi_Category(A) open SC A ZO
  type ('p1, 'a1, 'a2, 'a3, 'a4) container = 'a1 rose
  fun zip _ = arr dest_rose
    >>> LI.dest
    >>> arr (fn ((x, cs), xs) => pair x (cs, [([], xs, NONE)]))
    >>> zipper
    |> Lazy_Cat_Util.unlift
  fun unzip _ =
    let
      fun mk [(rev_pref, suff, _)] children v = Rose (rev rev_pref @ [(v, children)] @ suff)
        | mk ((rev_pref, suff, SOME c) :: xs) children v =
            mk xs (Rose (rev rev_pref @ [(v, children)] @ suff)) c
    in
      get_content &&& get_zcontext
      >>> arr (fn (c, (children, xs)) => mk xs children c)
      |> Lazy_Cat_Util.unlift
    end
  fun dest_zipper _ = get_content &&& get_zcontext
    >>> arr (fn (c, (ch, xs)) => (ch, (c, xs)))
    |> Lazy_Cat_Util.unlift
  fun dest_zipper_flip _ = dest_zipper >>> arr (fn (ch, (c, xs)) => (xs, (c, ch)))
    |> Lazy_Cat_Util.unlift
  fun up _ = dest_zipper_flip
    >>> first LI.dest
    >>> arr (fn (((rev_pref, suff, p), xs), (c, ch)) =>
      Option.map (rpair (rose (rev rev_pref @ [(c, ch)] @ suff), xs)) p)
    >>> AC.opt LI.A.throw zipper
    |> Lazy_Cat_Util.unlift
  fun down _ = dest_zipper
    >>> first (arr dest_rose >>> LI.dest)
    >>> arr (fn (((c, ch), cs), (p, xs)) => pair c (ch, (LI.cons (LI.empty, cs, SOME p) xs)))
    >>> zipper
    |> Lazy_Cat_Util.unlift
  fun left _ = dest_zipper_flip
    >>> first LI.dest
    >>> first (arr (fn ((rev_pref, suff, p), xs) => (rev_pref, (suff, p, xs))))
    >>> first (first LI.dest)
    >>> arr (fn ((((r, rch), rs), (suff, p, xs)), (c, ch)) =>
      pair r (rch, LI.cons (rs, LI.cons (c, ch) suff , p) xs))
    >>> zipper
    |> Lazy_Cat_Util.unlift
  fun right _ = dest_zipper_flip
    >>> first LI.dest
    >>> first (arr (fn ((rev_pref, suff, p), xs) => (suff, (rev_pref, p, xs))))
    >>> first (first LI.dest)
    >>> arr (fn ((((s, sch), ss), (rev_pref, p, xs)), (c, ch)) =>
      pair s (sch, LI.cons (LI.cons (c, ch) rev_pref, ss, p) xs))
    >>> zipper
    |> Lazy_Cat_Util.unlift
)

structure Z = Zipper4(structure ZO = ZO; structure ZM = ZM)
open Z

end
