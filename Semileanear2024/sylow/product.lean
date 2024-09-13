import Semileanear2024.sylow.basic


namespace Semileanear


section sectionProduct

variable (G : Type u) [Group G]

def ProductOfSubgroups (H K : Subgroup G) := {g : G | ∃ h k, h ∈ H.carrier ∧ k ∈ K.carrier ∧ g = h ~ k}


end sectionProduct

end Semileanear
