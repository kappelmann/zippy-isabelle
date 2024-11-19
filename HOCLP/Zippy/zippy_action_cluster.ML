(*  Title:      HOCLP/zippy_action_cluster.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_CLUSTER =
sig
  type ('c, 'd) acluster
end

structure Zippy_Action_Cluster : ZIPPY_ACTION_CLUSTER =
struct

datatype ('c, 'd) acluster = ACluster of {
    copy : 'c,
    data : 'd
  }

end
