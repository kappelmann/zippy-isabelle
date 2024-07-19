structure Example_Zippers =
struct

structure List = GList(M)

structure List_Zipper_Base : ZIPPER_BASE =
struct
  structure ZD = Zipper_Data
  type ('i, 'c) content = 'c
  type ('i, 'c) zcontext = 'c List.t * 'c List.t
  type ('i, 'c) zipper = (('i, 'c) content, ('i, 'c) zcontext) ZD.zipper
  val zipper = ZD.zipper

  val get_content = ZD.get_content
  val get_zcontext = ZD.get_zcontext

  val map_content = ZD.map_content
  val map_zcontext = ZD.map_zcontext

  type ('i, 'c) container = 'c List.t
  fun unzip zipper = let val (rev_pref, suff) = get_zcontext zipper
    in rev rev_pref @ [get_content zipper] @ suff end
end

structure List_Zipper = Zipper(
  structure Z = List_Zipper_Base
  fun init xs = List.dest xs |> M.map (fn (x, xs) => Z.zipper x ([], xs))
  fun up zipper =
    let
      val c = Z.get_content zipper
      val (hs, ts) = Z.get_zcontext zipper
    in List.dest hs |> M.map (fn (h, hs) => Z.zipper h (hs, c :: ts)) end
  fun down zipper =
    let
      val c = Z.get_content zipper
      val (hs, ts) = Z.get_zcontext zipper
    in List.dest ts |> ME.map (fn (t, ts) => Z.zipper t (c :: hs, ts)) end
  fun left _ = MZ.zero ()
  fun right _ = MZ.zero ()
  structure M = MB
)

datatype 'a rose = Rose of ('a * 'a rose) List.t

structure Rose_Zipper_Base : ZIPPER_BASE =
struct
  structure ZD = Zipper_Data
  type ('i, 'c) content = 'c
  type ('i, 'c) zcontext = 'c rose * ((('c * 'c rose) List.t * ('c * 'c rose) List.t * 'c option) List.t)
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

structure Rose_Zipper = Zipper(
  structure Z = Rose_Zipper_Base
  fun init (Rose xs) = List.dest xs |> M.map (fn ((x, cs), xs) => Z.zipper x (cs, [([], xs, NONE)]))
  fun up zipper =
    let
      val c = Z.get_content zipper
      val (ch, xs) = Z.get_zcontext zipper
    in
      M.bind (List.dest xs)
      (fn ((rev_pref, suff, p), xs) => p |>
        Option.map (fn p => Z.zipper p (Rose (rev rev_pref @ [(c, ch)] @ suff), xs))
        |> MS.lift)
    end
  fun down zipper =
    let
      val p = Z.get_content zipper
      val (Rose ch, xs) = Z.get_zcontext zipper
    in List.dest ch |> M.map (fn ((c, ch), cs) => Z.zipper c (ch, (([], cs, SOME p) :: xs))) end
  fun left zipper =
    let
      val c = Z.get_content zipper
      val (ch, xs) = Z.get_zcontext zipper
    in M.bind (List.dest xs) (fn ((rev_pref, suff, p), xs) =>
      M.map (fn ((r, rch), rs) => Z.zipper r (rch, (rs, (c, ch) :: suff , p) :: xs)) (List.dest rev_pref)) end
  fun right zipper =
    let
      val c = Z.get_content zipper
      val (ch, xs) = Z.get_zcontext zipper
    in M.bind (List.dest xs) (fn ((rev_pref, suff, p), xs) =>
      M.map (fn ((s, sch), ss) => Z.zipper s (sch, ((c, ch) :: rev_pref, ss, p) :: xs)) (List.dest suff)) end
  structure M = MB
)

end