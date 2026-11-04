module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CommutingAfterBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProduct

/-!
# The class of the blowup construction commutes with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `Z ⊆ X` be a closed subscheme with a virtual normal sheaf `𝒩` of
arbitrary rank. Stacks 0FBP asserts that the class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of Stacks 0FBK
commutes (Stacks 0FA2) with every bivariant class `c ∈ A^*(Y ⟶ X)`, for `Y ⟶ X` locally of finite
type. Stacks 0FBP itself, for the class `Stacks.Chow.VirtualNormalBundle.completedClass` of
Stacks 0FBK, is `Stacks.Chow.VirtualNormalBundle.completedClass_bivariantCommute`.

This file proves the same commutation for `Stacks.Chow.completedVirtualNormalGysinClass`, the
completed class built from the blowup `W` of `𝐏¹_X` in `∞(Z)` and its class at infinity
(`Stacks.Chow.virtualNormalConeClass`), which is used by the Gysin maps of local complete
intersection morphisms in this directory. On the completed group (Stacks 0FE0) commuting is read
degree by degree (`Stacks.Chow.completedCommutesWithEveryClass`): every homogeneous part commutes
with every homogeneous class over `X`, and so, by linearity, with every element of the graded
group `A^*(Y ⟶ X)`. The homogeneous parts even commute with every class after every base change
(`Stacks.Chow.completedCommutesAfterBaseChange_completedVirtualNormalGysinClass`).

## Main results

* `Stacks.Chow.completedCommutesWithEveryClass_completedVirtualNormalGysinClass` — the class of
  the blowup construction commutes with every class.
* `Stacks.Chow.completedCommutesWithEveryClass_completedVirtualNormalGysinClassOfOpen` — its
  counterpart for immersions (Stacks 0FBQ).

## References

* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsLocallyNoetherian Z] [IsLocallyNoetherian X]

/-- **The class of the blowup construction commutes with every bivariant class.** Let `X` be
locally of finite type over `S`, let `Z ⊆ X` be a closed subscheme with a virtual normal sheaf `𝒩`
of arbitrary rank. Then every homogeneous part of `Stacks.Chow.completedVirtualNormalGysinClass`
commutes with every homogeneous class over `X` (Stacks 0FA2); each part commutes with every class
after every base change
(`Stacks.Chow.completedCommutesAfterBaseChange_completedVirtualNormalGysinClass`), in particular
after the identity base change. For the class of Stacks 0FBK this is Stacks 0FBP,
`Stacks.Chow.VirtualNormalBundle.completedClass_bivariantCommute`. -/
theorem completedCommutesWithEveryClass_completedVirtualNormalGysinClass (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : i ≫ sX = sZ) (𝒩 : VirtualNormalBundle i) :
    completedCommutesWithEveryClass C sZ sX i hi
      (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) := fun n ↦
  (completedCommutesAfterBaseChange_completedVirtualNormalGysinClass C sZ sX i hi 𝒩
    n).commutesWithEveryClass

/-- **The counterpart of Stacks 0FBP for immersions** (Stacks 0FBQ). For an immersion
`i : Z ⟶ X` with a virtual normal bundle `𝒩` of arbitrary rank, the class
`c(Z ⟶ X, 𝒩) = c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^* ∈ A^*(Z ⟶ X)^∧` commutes with every bivariant class over
`X`, degree by degree. -/
@[stacks 0FBQ "(3), counterparts: the counterpart of Lemma 0FBP, c(Z → X, 𝒩) ∈ A^*(Z → X)^∧ \
commutes with every c ∈ A^*(Y → X), for an immersion Z → X and 𝒩 of arbitrary rank"]
theorem completedCommutesWithEveryClass_completedVirtualNormalGysinClassOfOpen (i : Z ⟶ X)
    [IsImmersion i] (hi : i ≫ sX = sZ) (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hU : i' ≫ U.ι = i) (𝒩 : VirtualNormalBundle i) :
    completedCommutesWithEveryClass C sZ sX i hi
      (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩) := fun n ↦
  (completedCommutesAfterBaseChange_completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩
    n).commutesWithEveryClass

end Stacks.Chow

end
