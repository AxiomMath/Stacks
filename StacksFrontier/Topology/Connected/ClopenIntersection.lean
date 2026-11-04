module

public import StacksFrontier.Topology.Spectral.ComponentSpace

/-!
# Connected components as intersections of clopens

## Main results

* `connectedComponent_eq_iInter_isClopen_of_compactSpace`: in a quasi-compact space with a
  basis of quasi-compact opens whose pairwise intersections are quasi-compact, the connected
  component of a point is the intersection of all clopen subsets containing that point.
-/

@[expose] public section

universe u

open Set TopologicalSpace

/-- Let `X` be a topological space that is quasi-compact, admits a basis of quasi-compact open
sets, and is such that the intersection of any two quasi-compact open sets is quasi-compact. Then
for every `x : X` the connected component of `x` equals the intersection of all clopen subsets of
`X` containing `x`. -/
@[stacks 005F]
theorem connectedComponent_eq_iInter_isClopen_of_compactSpace
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {B : Set (Set X)} (hB : IsTopologicalBasis B)
    (hBqc : ∀ U ∈ B, IsCompact U)
    (hqcInter :
      ∀ ⦃U V : Set X⦄, IsOpen U → IsCompact U → IsOpen V → IsCompact V → IsCompact (U ∩ V))
    (x : X) :
    connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, (Z : Set X) := by
  have : PrespectralSpace X := .of_isTopologicalBasis hB hBqc
  have : QuasiSeparatedSpace X := ⟨fun U V => @hqcInter U V⟩
  rw [show (⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, (Z : Set X))
      = ⋂ Z ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z by ext z; simp]
  exact Subset.antisymm (connectedComponent_subset_iInter_isClopen_set X x)
    ((spectral_iInter_isClopen_isPreconnected X x).subset_connectedComponent
      (mem_iInter_isClopen_self x))

end
