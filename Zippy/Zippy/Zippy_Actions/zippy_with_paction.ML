(*  Title:      HOCLP/zippy_with_paction.ML
    Author:     Kevin Kappelmann

Zippy with prioritised actions.
*)
signature ZIPPY_WITH_PACTION =
sig
  type copy_update_data
  type prio

  structure CD : KLEISLI_ZIPPY_COPY_DATA
  type @{T_args} cd_more
  structure PAD : ZIPPY_PACTION_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) CD.L.C.cat
  sharing type PAD.L.lens = CD.L.lens
  type @{T_args} pad_more
  structure PD : ZIPPY_PRIO_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) CD.L.C.cat
  sharing type PD.L.lens = CD.L.lens
  type @{T_args} pd_more

  type @{T_args} paction
  type @{T_args} copy

  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES"\<close>
  where type @{T_args} N3.content = (@{T_args} copy, @{T_args} cd_more) CD.copy_data
  where type @{T_args} N4.content = (@{T_args} paction, @{T_args} pad_more) PAD.paction_data
  where type @{T_args} N5.content = (prio, @{T_args} pd_more) PD.prio_data
  where type ('p1, 'a) M.t = ('p1, 'a) CD.K.M.t
  where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) CD.L.lens

  val mk_copy : (copy_update_data -> @{T_args} Z3.zipper ->
    (@{ParaT_args}, @{T_args} Z1.zipper) hom_move) -> @{T_args} copy
  val dest_copy : @{T_args} copy -> copy_update_data ->
    @{T_args} Z3.zipper -> (@{ParaT_args}, @{T_args} Z1.zipper) hom_move

  type @{T_args} action = prio -> (@{ParaT_args}, @{T_args} Z4.zipper) hom_move

  val mk_paction : (@{ParaT_args}, @{T_args} Z4.zipper, prio * @{T_args} action) cat ->
    @{T_args} paction
  val dest_paction : @{T_args} paction ->
    (@{ParaT_args}, @{T_args} Z4.zipper, prio * @{T_args} action) cat
end

functor Zippy_With_PAction(
    type copy_update_data
    type prio
    structure CD : KLEISLI_ZIPPY_COPY_DATA
    type @{T_args} cd_more
    structure PAD : ZIPPY_PACTION_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) CD.L.C.cat
    sharing type PAD.L.lens = CD.L.lens
    type @{T_args} pad_more
    structure PD : ZIPPY_PRIO_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) CD.L.C.cat
    sharing type PD.L.lens = CD.L.lens
    type @{T_args} pd_more

    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES"\<close>
    where type @{T_args} N3.content = @{PolyT_arg 2}
    where type @{T_args} N4.content = @{PolyT_arg 3}
    where type @{T_args} N5.content = @{PolyT_arg 4}
    where type ('p1, 'a) M.t = ('p1, 'a) CD.K.M.t
    sharing type Z.L.lens = PAD.L.lens
  ) : ZIPPY_WITH_PACTION =
struct

type copy_update_data = copy_update_data
type prio = prio
structure CD = CD
type @{T_args} cd_more = @{T_args} cd_more
structure PAD = PAD
type @{T_args} pad_more = @{T_args} pad_more
structure PD = PD
type @{T_args} pd_more = @{T_args} pd_more

open Z

(* paction *)
datatype (@{T_args encl = "" ""}, 'padm) paction = PAction of
  (@{ParaT_args}, (@{T_args encl = "" ""}, 'padm) zipper4, prio *
    (prio -> (@{ParaT_args}, (@{T_args encl = "" ""}, 'padm) zipper4) hom_move)) cat
withtype \<^imap>\<open>\<open>{i}\<close> => \<open>
(@{T_args encl = "" ""}, 'padm) zipper{i} = (@{ParaT_args}, @{PolyT_args stop = 2},
  ((@{T_args encl = "" ""}, 'padm) paction, 'padm) PAD.paction_data, @{PolyT_arg 4}) Z{i}.zipper\<close>
where sep = "and"\<close>

fun mk_paction paction = PAction paction
fun dest_paction (PAction paction) = paction

(* copy *)
datatype (@{T_args encl = "" ""}, 'padm, 'cdm) copy = Copy of copy_update_data ->
  (@{T_args encl = "" ""}, 'padm, 'cdm) zipper3 -> (@{ParaT_args},
    (@{T_args encl = "" ""}, 'padm, 'cdm) zipper1) hom_move
withtype
\<^imap>\<open>\<open>{i}\<close> => \<open>
(@{T_args encl = "" ""}, 'padm, 'cdm) zipper{i} = (@{ParaT_args}, @{PolyT_args stop = 1},
  ((@{T_args encl = "" ""}, 'padm, 'cdm) copy, 'cdm) CD.copy_data,
  @{PolyT_args start = 3 and stop = 4}, 'padm) zipper{i}\<close>
where sep = "and"\<close>
and (@{T_args encl = "" ""}, 'padm, 'cdm) paction = (@{ParaT_args}, @{PolyT_args stop = 1},
  ((@{T_args encl = "" ""}, 'padm, 'cdm) copy, 'cdm) CD.copy_data,
  @{PolyT_args start = 3 and stop = 4}, 'padm) paction

fun mk_copy copy = Copy copy
fun dest_copy (Copy copy) = copy

type \<^imap>\<open>\<open>{i}\<close> => \<open>
(@{T_args encl = "" ""}, 'padm, 'cdm, 'pdm) zipper{i} =
  (@{ParaT_args}, @{PolyT_args stop = 3}, (prio, 'pdm) PD.prio_data, 'padm, 'cdm) zipper{i}\<close>
where sep = "and"\<close>
and (@{T_args encl = "" ""}, 'padm, 'cdm, 'pdm) paction =
  (@{ParaT_args}, @{PolyT_args stop = 3}, (prio, 'pdm) PD.prio_data, 'padm, 'cdm) paction
and (@{T_args encl = "" ""}, 'padm, 'cdm, 'pdm) copy =
  (@{ParaT_args}, @{PolyT_args stop = 3}, (prio, 'pdm) PD.prio_data, 'padm, 'cdm) copy

type \<^imap>\<open>\<open>{i}\<close> => \<open>
@{T_args} zipper{i} = (@{T_args encl = "" ""},
  @{T_args} pad_more, @{T_args} cd_more, @{T_args} pd_more) zipper{i}\<close>
where sep = "and"\<close>
and @{T_args} paction = (@{T_args encl = "" ""},
  @{T_args} pad_more, @{T_args} cd_more, @{T_args} pd_more) paction
and @{T_args} copy = (@{T_args encl = "" ""},
  @{T_args} pad_more, @{T_args} cd_more, @{T_args} pd_more) copy

type @{T_args} action = prio -> (@{ParaT_args}, @{T_args} zipper4) hom_move

structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Alternating_Zippers" ^ "_Nodes"\<close>(
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{T_args} inst{i} = @{PolyT_arg \<open>{i} - 1\<close>}\<close>\<close>
  type @{T_args} inst3 = (@{T_args} copy, @{T_args} cd_more) CD.copy_data
  type @{T_args} inst4 = (@{T_args} paction, @{T_args} pad_more) PAD.paction_data
  type @{T_args} inst5 = (prio, @{T_args} pd_more) PD.prio_data
  structure Z = Z
)
open Z

end

functor Instantiate_Zippy_With_PAction(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_WITH_PACTION
  ) :
    ZIPPY_WITH_PACTION
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} A.Z{i}.ZM.container = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZM.container
    where type @{T_args} A.Z{i}.ZO.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZO.content
    where type @{T_args} A.Z{i}.ZO.zcontext = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZO.zcontext
    where type @{T_args} A.Z{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.zipper\<close>\<close>
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} A.N{i}.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.N{i}.content\<close>
    where stop = 2\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} zcontext{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.zcontext{i}
    where type @{T_args} pzipper{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.pzipper{i}\<close>\<close>
    where type @{T_args} cd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.cd_more
    where type @{T_args} pad_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.pad_more
    where type @{T_args} pd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.pd_more
    where type @{T_args} paction = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{T_args} copy = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.copy =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i} = @{T_args} inst{i}\<close>\<close> end
structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Alternating_Zippers"\<close>(
  open Base; structure Z = Z)
open Z
end
