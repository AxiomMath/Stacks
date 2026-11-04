module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionConstruction

/-!
# The exceptional divisor of a blown-up regular surface is an exceptional curve of the first kind

Let `(A, 𝔪, κ)` be a regular local ring of dimension two and let `X ⟶ Spec A` be the blowing up
of `A` in `𝔪`, with exceptional divisor `E`. Then `E` is an exceptional curve of the first kind:
it is an effective Cartier divisor, and there is an isomorphism `𝐏¹_κ ≅ E` along which the normal
sheaf of `E` in `X` pulls back to `𝒪(-1)`.

## Main results

* `Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdealData`.

## References

* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing RingedSpaceModuleAdjunction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Blowup

/-- **The exceptional divisor of the blowup of a regular local surface is an exceptional curve of
the first kind.** For `(A, 𝔪, κ)` regular local of dimension two, the exceptional divisor `E` of
the blowing up of `A` in `𝔪` admits an isomorphism `𝐏¹_κ ≅ E` under which the normal sheaf of `E`
pulls back to `𝒪(-1)`. -/
theorem exists_isExceptionalCurveOfFirstKind_exceptionalIdealData
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    ∃ e : projectiveLineProj (ResidueField A) ≅
        (exceptionalIdealData (maximalIdeal A)).subscheme,
      (exceptionalIdealData (maximalIdeal A)).IsExceptionalCurveOfFirstKind
        (ResidueField A) e := by
  obtain ⟨_, -, -, ρ, -, -, -, -, ⟨hN⟩⟩ :=
    exists_isClosedImmersion_blowUpSpec_maximalIdeal_exceptional_projectiveLine A hdim
  exact ⟨ρ.symm, inferInstance, ⟨Scheme.Modules.pullbackInvObjIso ρ hN.symm⟩⟩

end Stacks.Blowup

end
