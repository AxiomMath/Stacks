module

public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.LocalizationData
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.FiniteCohomologicalDimension

/-!
# Cohomology on the complement of a zero locus in degrees above one

Let `I` be a finitely generated ideal of a commutative ring `A` and let `U = Spec A \ V(I)`.
The affine localization triangle of Stacks 0DWR is
`RΓ_{V(I)}(M) ⟶ M ⟶ RΓ(U, M̃|U) ⟶ RΓ_{V(I)}(M)[1]`.
This file reads off its long exact homology sequence in every degree above zero. For `p ≥ 1`
both `H^p(M[0])` and `H^{p+1}(M[0])` vanish, so the connecting map of the triangle is
simultaneously a monomorphism and an epimorphism, hence an isomorphism
`H^p(RΓ(U, M̃|U)) ≅ H^{p+1}_{V(I)}(M)`. Local cohomology in degrees above one is therefore
cohomology on the complement, shifted by one — the content of Stacks 0DWR in positive degrees.

## Main definitions

* `Stacks.LocalCohomology.homologyComplementIsoLocalCohomologyModule` — **the comparison of
  Stacks 0DWR in degrees above one**: for `p ≥ 1` the degree-`p` cohomology of derived sections
  on `U` is the degree-`p+1` local cohomology of `M`.

## Main results

* `Stacks.LocalCohomology.isIso_homologySequenceδ_of_isZero` — the connecting map of a
  distinguished triangle is an isomorphism when the middle term has no cohomology in either of
  the two degrees the map connects.
* `Stacks.LocalCohomology.isIso_localizationTriangleδ` — the connecting map of the localization
  triangle is an isomorphism in every degree above zero.
* `Stacks.LocalCohomology.nonempty_localizationTriangleData_higherComparison` — the comparison
  holds for a localization triangle data chosen functorially in the module, with no hypothesis
  beyond finite generation of `I`.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- The connecting map of a distinguished triangle is an isomorphism as soon as the middle term
has no cohomology in either of the two degrees the map connects. -/
theorem isIso_homologySequenceδ_of_isZero {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor C n₀).obj T.obj₂))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor C n₁).obj T.obj₂)) :
    IsIso (DerivedCategory.HomologySequence.δ T n₀ n₁ h) :=
  have : Mono (DerivedCategory.HomologySequence.δ T n₀ n₁ h) :=
    (DerivedCategory.HomologySequence.exact₃ T hT n₀ n₁ h).mono_g (h₀.eq_of_src _ _)
  have : Epi (DerivedCategory.HomologySequence.δ T n₀ n₁ h) :=
    (DerivedCategory.HomologySequence.exact₁ T hT n₀ n₁ h).epi_f (h₁.eq_of_tgt _ _)
  isIso_of_mono_of_epi _

variable {A : Type u} [CommRing A] {I : Ideal A} {hI : I.FG}

/-- In every degree above zero the connecting map of the localization triangle is an
isomorphism. -/
theorem isIso_localizationTriangleδ (D : LocalizationTriangleData.{u, v} A I hI)
    (M : ModuleCat.{v} A) (p : ℕ) (hp : 1 ≤ p) :
    IsIso (DerivedCategory.HomologySequence.δ (D.triangle M) (p : ℤ) ((p : ℤ) + 1) rfl) :=
  isIso_homologySequenceδ_of_isZero (D.triangle M) (D.distinguished M) (p : ℤ) ((p : ℤ) + 1) rfl
    (isZero_homology_singleFunctor_obj M (p : ℤ) (by lia))
    (isZero_homology_singleFunctor_obj M ((p : ℤ) + 1) (by lia))

/-- **Stacks 0DWR in degrees above one.** For `p ≥ 1` the degree-`p` cohomology of derived
sections on `U = Spec A \ V(I)` is the degree-`p+1` local cohomology of `M` with support in
`V(I)`, the isomorphism being the connecting map of the localization triangle. -/
def homologyComplementIsoLocalCohomologyModule (D : LocalizationTriangleData.{u, v} A I hI)
    (M : ModuleCat.{v} A) (p : ℕ) (hp : 1 ≤ p) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} A) (p : ℤ)).obj
        (D.complement.obj M) ≅
      localCohomologyModule A I hI M ((p : ℤ) + 1) :=
  @asIso _ _ _ _
    (DerivedCategory.HomologySequence.δ (D.triangle M) (p : ℤ) ((p : ℤ) + 1) rfl)
    (isIso_localizationTriangleδ D M p hp)

variable (A I) in
/-- **Stacks 0DWR in degrees above one, with no choice left to the consumer.** For a finitely
generated ideal the affine localization triangle can be chosen functorially in the module, and in
every degree above zero its connecting map identifies the cohomology of derived sections on
`U = Spec A \ V(I)` with local cohomology shifted by one. -/
theorem nonempty_localizationTriangleData_higherComparison (hI : I.FG) :
    ∃ D : LocalizationTriangleData.{u, v} A I hI,
      ∀ (M : ModuleCat.{v} A) (p : ℕ), 1 ≤ p →
        Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) (p : ℤ)).obj
            (D.complement.obj M) ≅
          localCohomologyModule A I hI M ((p : ℤ) + 1)) :=
  let ⟨D⟩ := nonempty_localizationTriangleData.{v} A I hI
  ⟨D, fun M p hp ↦ ⟨homologyComplementIsoLocalCohomologyModule D M p hp⟩⟩

end Stacks.LocalCohomology

end
