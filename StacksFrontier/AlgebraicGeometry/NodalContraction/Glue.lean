module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalOnSource
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality
public import StacksFrontier.AlgebraicGeometry.F6Rank136.SmoothIsNodal

/-!
# Gluing the nodal property over a point and its complement

A morphism of schemes which is at-worst-nodal of relative dimension one on the complement of a
closed point, and smooth of relative dimension one on an open neighbourhood of that point, is
at-worst-nodal of relative dimension one.

## Main results

* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_of_compl_and_nbhd`: the statement
  above.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism which is at-worst-nodal of relative dimension one away from a closed point and
smooth of relative dimension one on a neighbourhood of that point is at-worst-nodal of relative
dimension one. -/
public theorem isAtWorstNodalOfRelativeDimensionOne_of_compl_and_nbhd
    {X S : Scheme.{u}} (f : X ⟶ S) (z : X) (hz : IsClosed ({z} : Set X))
    (hW : IsAtWorstNodalOfRelativeDimensionOne
      (Scheme.Opens.ι (⟨({z} : Set X)ᶜ, hz.isOpen_compl⟩ : X.Opens) ≫ f))
    (V : X.Opens) (hzV : z ∈ V)
    (hV : SmoothOfRelativeDimension 1 (V.ι ≫ f)) :
    IsAtWorstNodalOfRelativeDimensionOne f := by
  let W : X.Opens := ⟨({z} : Set X)ᶜ, hz.isOpen_compl⟩
  let C : Bool → X.Opens := fun t => if t then V else W
  have hcov : Presieve.ofArrows (fun t : Bool => (C t).toScheme) (fun t => (C t).ι) ∈
      Scheme.etalePrecoverage X := by
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr ⟨fun x => ?_, fun t => ?_⟩
    · by_cases hx : x = z
      · exact ⟨true, ⟨⟨x, hx ▸ hzV⟩, rfl⟩⟩
      · exact ⟨false, ⟨⟨x, hx⟩, rfl⟩⟩
    · cases t <;> infer_instance
  refine (isAtWorstNodalOfRelativeDimensionOne_iff_of_etaleCovering f
    (fun t : Bool => (C t).ι) hcov).mpr fun t => ?_
  cases t
  · exact hW
  · let := hV
    exact isAtWorstNodalOfRelativeDimensionOne_of_smoothOfRelativeDimension (V.ι ≫ f)

end AlgebraicGeometry

end
