module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.ModelTransport
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.SituationBoxPairing

/-!
# The complex of [Stacks, Tag 0G0A] in Situation [Stacks, Tag 0G08], from the standard model

`AlgebraicGeometry.exists_kunnethComplex_of_imagePairing` of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.SituationBoxPairing` states the
conclusion of [Stacks, Tag 0G0A] at the hypotheses of Situation [Stacks, Tag 0G08] from one Künneth
input, `himage`, about Hom groups of the locally small model of `D(𝒪_{X ×_k Y})`.
`AlgebraicGeometry.DiagonalResolution.isTensorPairing_transformedImagePairing_iff_std` of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.ModelTransport` says that
input is equivalent to the same statement with every derived category read at
`CategoryTheory.HasDerivedCategory.standard`, the model at which [Stacks, Tag 0FXZ],
[Stacks, Tag 08DK] and [Stacks, Tag 0FLQ] are stated.

This file composes the two: `AlgebraicGeometry.exists_kunnethComplex_of_imagePairingStd` is the
conclusion of [Stacks, Tag 0G0A] in Situation [Stacks, Tag 0G08] from the standard-model Künneth
input on `X ×_k Y`. It registers no tag, since it still takes that input as an argument.

## Main results

* `AlgebraicGeometry.exists_kunnethComplex_of_imagePairingStd`: the complex of [Stacks, Tag 0G0A]
  from the Künneth identification on `X ×_k Y` at the standard model.

## References

* [Stacks Project, Tag 0G08](https://stacks.math.columbia.edu/tag/0G08)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.PerfectComplexes

universe u

namespace AlgebraicGeometry

attribute [local instance] CategoryTheory.Linear.fullSubcategory
attribute [local instance] isTriangulated_isPerfect_locallySmall

open DiagonalResolution in
/-- **The complex of [Stacks, Tag 0G0A] in Situation [Stacks, Tag 0G08], from the Künneth input on
`X ×_k Y` at the standard model.** For every `k`-linear, exact, fully faithful
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` and every resolution `R` of the diagonal of `X`, if the pairing
`(a, c) ↦ a ⊠ c` exhibits each Hom group
`Hom(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))` of the standard model of `D(𝒪_{X ×_k Y})` as
`Hom(ℰᵢ, ℰⱼ) ⊗_k Hom(F(𝒢ᵢ), F(𝒢ⱼ))`, then there is a complex
`… ⟶ ℰ₂ ⊠ F(𝒢₂) ⟶ ℰ₁ ⊠ F(𝒢₁) ⟶ ℰ₀ ⊠ F(𝒢₀)` on `X ×_k Y` whose term of index `i` is `ℰᵢ ⊠ F(𝒢ᵢ)`
and whose differentials are those of `R`, read through an identification of Hom groups carrying
each pure map `a ⊠ b` to `a ⊠ F(b)`.

This is `AlgebraicGeometry.exists_kunnethComplex_of_imagePairing` with its input moved to the
standard model by
`AlgebraicGeometry.DiagonalResolution.isTensorPairing_transformedImagePairing_iff_std`. -/
theorem exists_kunnethComplex_of_imagePairingStd (k : Type u) [Field k]
    (X Y : Over (Spec (.of k))) [Smooth X.hom] [Smooth Y.hom]
    [IsProper X.hom] [IsProper Y.hom] :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    (∀ (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] [F.IsTriangulated],
      F.Linear k → Nonempty F.FullyFaithful → ∀ (R : DiagonalResolution X.hom) (i j : ℕ),
        IsTensorPairing k (R.left i ⟶ R.left j)
          (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j)
          (R.transformedImagePairingStd Y.hom F i j)) →
    ∀ (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] [F.IsTriangulated],
      F.Linear k → Nonempty F.FullyFaithful →
      ∀ (R : DiagonalResolution X.hom),
        ∃ T : ImageHomTransport R Y.hom F,
          (∀ i, T.complex.X i = R.imageTerm Y.hom F i) ∧
          (∀ i, T.complex.d (i + 1) i = T.hom (i + 1) i (R.boxDifferential i)) ∧
          ∀ (i j : ℕ) (a : R.left i ⟶ R.left j) (b : R.right i ⟶ R.right j),
            T.hom i j (externalTensorProductMap X.hom X.hom a b) =
              R.transformedMap Y.hom F a b := by
  let _ : Linear k X.left.Modules := modulesLinear k X
  let _ : Linear k Y.left.Modules := modulesLinear k Y
  intro hstd F _ _ hlin hff R
  exact exists_kunnethComplex_of_imagePairing k X Y F hlin hff R fun i j =>
    (R.isTensorPairing_transformedImagePairing_iff_std Y.hom F i j).2 (hstd F hlin hff R i j)

end AlgebraicGeometry

end
