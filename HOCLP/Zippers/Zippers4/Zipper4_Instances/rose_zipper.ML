(*  Title:      HOCLP/rose_zipper.ML
    Author:     Kevin Kappelmann
*)
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
    structure A : KLEISLI_ARROW
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
    structure LI : GLIST
    where type 'a t = 'a list
    where type 'p1 M.exn = unit
    sharing type LI.M.t = A.K.M.t
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
  structure M = Move_Base(A.K.M)
  structure AC = Kleisli_Arrow_Choice(M.M)
  structure SC = Semi_Category(A) open SC A ZO
  type ('p1, 'a1, 'a2, 'a3, 'a4) container = 'a1 rose
  fun zip x = x |> (arr dest_rose
    >>> LI.dest
    >>> arr (fn ((x, cs), xs) => pair x (cs, [([], xs, NONE)]))
    >>> zipper)
  fun unzip x = x |> (
    let
      fun mk [(rev_pref, suff, _)] children v = Rose (rev rev_pref @ [(v, children)] @ suff)
        | mk ((rev_pref, suff, SOME c) :: xs) children v =
            mk xs (Rose (rev rev_pref @ [(v, children)] @ suff)) c
    in
      get_content &&& get_zcontext
      >>> arr (fn (c, (children, xs)) => mk xs children c)
    end)
  fun dest_zipper x = x |> (get_content &&& get_zcontext
    >>> arr (fn (c, (ch, xs)) => (ch, (c, xs))))
  fun dest_zipper_flip x = x |> (dest_zipper >>> arr (fn (ch, (c, xs)) => (xs, (c, ch))))
  fun up x = x |> (dest_zipper_flip
    >>> first LI.dest
    >>> arr (fn (((rev_pref, suff, p), xs), (c, ch)) =>
      Option.map (rpair (rose (rev rev_pref @ [(c, ch)] @ suff), xs)) p)
    >>> AC.opt LI.M.throw zipper)
  fun down x = x |> (dest_zipper
    >>> first (arr dest_rose >>> LI.dest)
    >>> arr (fn (((c, ch), cs), (p, xs)) => pair c (ch, (LI.cons (LI.empty, cs, SOME p) xs)))
    >>> zipper)
  fun left x = x |> (dest_zipper_flip
    >>> first LI.dest
    >>> first (arr (fn ((rev_pref, suff, p), xs) => (rev_pref, (suff, p, xs))))
    >>> first (first LI.dest)
    >>> arr (fn ((((r, rch), rs), (suff, p, xs)), (c, ch)) =>
      pair r (rch, LI.cons (rs, LI.cons (c, ch) suff , p) xs))
    >>> zipper)
  fun right x = x |> (dest_zipper_flip
    >>> first LI.dest
    >>> first (arr (fn ((rev_pref, suff, p), xs) => (suff, (rev_pref, p, xs))))
    >>> first (first LI.dest)
    >>> arr (fn ((((s, sch), ss), (rev_pref, p, xs)), (c, ch)) =>
      pair s (sch, LI.cons (LI.cons (c, ch) rev_pref, ss, p) xs))
    >>> zipper)
)

structure Z = Zipper4(structure ZO = ZO; structure ZM = ZM)
open Z

end
