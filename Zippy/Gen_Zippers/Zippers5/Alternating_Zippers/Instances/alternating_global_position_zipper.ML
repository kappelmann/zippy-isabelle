(*  Title:      Zippy/alternating_global_position_zipper.ML
    Author:     Kevin Kappelmann
*)
(*TODO: generalise to arbitrary list types*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_GLOBAL_POSITION_ZIPPER"\<close> =
sig
  type path = int list list
  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZM.container = path
  where type @{AllT_args} Z{i}.ZD.zcontext = unit
  where type @{AllT_args} Z{i}.ZD.content = path
  where type @{AllT_args} Z{i}.zipper = path\<close>\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Global_Position_Zipper"\<close>(
    L : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_GLOBAL_POSITION_ZIPPER"\<close> =
struct

type path = int list list

structure L = L
structure MB = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(L.K.M)
open MB

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZM = \<^eval>\<open>sfx_T_nargs "Zipper_Moves"\<close>(
    structure M = MB
    open M.M
    type @{AllT_args} container = path
    type @{AllT_args} zipper = path
    fun zip pss = pure ([0] :: pss)
    fun unzip (_ :: pss) = pure pss
    fun down (ps :: pss) = pure ((0 :: ps) :: pss)
    fun up ((p :: ps) :: pss) = pure (ps :: pss)
    fun left ((p :: ps) :: pss) = pure ((p + 1 :: ps) :: pss)
    fun right ((p :: ps) :: pss) = pure ((p - 1 :: ps) :: pss))
  structure ZD = \<^eval>\<open>sfx_T_nargs "Content_Zipper_Data"\<close>(
    structure L = L
    type @{AllT_args} content = path))\<close>\<close>

structure Base =
struct
  open MB
  type @{AllT_args} from = path
  type @{AllT_args} to = path
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} = struct open Base; fun move pss = M.pure ([0] :: pss) end\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Up{i} = struct open Base; fun move (_ :: pss) = M.pure pss end\<close>\<close>

end
