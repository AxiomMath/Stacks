module

public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.DiagonalPositivity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.TransversalCycleMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkDimension

/-!
# Positivity of the intersection multiplicity at the local ideals of two points

Tag 0B0V, read for the reduced closures of two points `x` and `y` of a nonsingular variety, at a
point `z` of both closures: if the closure of `z` is an irreducible component of
`closure {x} ∩ closure {y}` and the two closures intersect properly along it, then the Tor-formula
multiplicity `e(X, closure {x} · closure {y}, closure {z})` of the local ideals is positive.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

/-- **Tag 0B0V at the local ideals of two points.** -/
theorem localIntersectionMultiplicity_localIdealAt_pos {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsVariety k f] (hX : IsRegular X) {x y z : X}
    (hzx : z ∈ closure ({x} : Set X)) (hzy : z ∈ closure ({y} : Set X))
    (h0 : ringKrullDim (X.presheaf.stalk z ⧸ (localIdealAt x z ⊔ localIdealAt y z)) = 0)
    (hproper : ringKrullDim (X.presheaf.stalk z) ≤
      ringKrullDim (X.presheaf.stalk z ⧸ localIdealAt x z) +
        ringKrullDim (X.presheaf.stalk z ⧸ localIdealAt y z)) :
    0 < (localIdealAt x z).localIntersectionMultiplicity
      (X.presheaf.stalk z ⧸ localIdealAt y z) := by
  have hmem : ∀ a : X, z ∈ closure ({a} : Set X) →
      z ∈ Set.range (Stacks.Chow.integralComponentAt a).subschemeι.base := fun a h => by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact mem_support_integralComponentAt h
  set I := Stacks.Chow.integralComponentAt x with hI
  set J := Stacks.Chow.integralComponentAt y with hJ
  obtain ⟨v, hv⟩ := hmem x hzx
  obtain ⟨w, hw⟩ := hmem y hzy
  obtain ⟨ζ, hζv, hζw⟩ := Scheme.Pullback.exists_preimage_pullback (f := I.subschemeι)
    (g := J.subschemeι) v w (hv.trans hw.symm)
  have hξ : I.subschemeι (pullback.fst I.subschemeι J.subschemeι ζ) = z := by rw [hζv, hv]
  have hpos := Stacks.Intersection.Diagonal.intersectionMultiplicity_pos_of_isRegular f hX
    I.subschemeι J.subschemeι ζ ?_ ?_
  · rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι, hξ,
      Stacks.Intersection.intersectionMultiplicity_eq] at hpos
    exact hpos
  · rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι, hξ,
      AlgebraicGeometry.IdealSheafData.stalk_sup]
    exact h0
  · rw [hξ, ← Stacks.Chow.ringKrullDim_quotient_idealStalk_eq I,
      ← Stacks.Chow.ringKrullDim_quotient_idealStalk_eq J, hξ, hζw, hw]
    exact hproper

end Stacks.Intersection.RationalEquivalenceProduct

end
