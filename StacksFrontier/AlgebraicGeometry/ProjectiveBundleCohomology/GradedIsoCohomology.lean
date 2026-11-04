module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.GradedIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Iso
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementSheafCohomology

/-!
# Cohomology of the twisting sheaves across a graded ring isomorphism

Let `ψ : 𝒜 →+*ᵍ ℬ` be an isomorphism of nonnegatively graded rings, with inverse `χ`. Then
`Proj.map ψ : Proj ℬ ⟶ Proj 𝒜` is an isomorphism of schemes, the canonical comparison
`θ : (Proj.map ψ)^* 𝒪_{Proj 𝒜}(d) ⟶ 𝒪_{Proj ℬ}(d)` is an isomorphism of modules, and therefore
the cohomology of `𝒪_{Proj 𝒜}(d)` and of `𝒪_{Proj ℬ}(d)` vanish in the same degrees.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isAwayDegreewise_one`: a graded ring
  isomorphism is, degreewise, the localization away from `1`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isIso_twistMap_of_inverse`: the twist
  comparison of a graded ring isomorphism is an isomorphism.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isZero_Hgroup_twistingSheaf_iff_of_inverse`:
  `Hᵠ(Proj ℬ, 𝒪(d)) = 0` if and only if `Hᵠ(Proj 𝒜, 𝒪(d)) = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- **A graded ring isomorphism is, degreewise, the localization away from `1`.** -/
public theorem isAwayDegreewise_one (ψ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜)
    (hψχ : ∀ b, ψ (χ b) = b) (hχψ : ∀ a, χ (ψ a) = a) :
    Stacks.GradedLocalization.IsAwayDegreewise ψ 1 where
  isUnit_map := by rw [map_one]; exact isUnit_one
  surj n y hy := ⟨0, χ y, χ.map_mem hy, by rw [hψχ, pow_zero, one_mul]⟩
  torsion n x _ h := ⟨0, by rw [pow_zero, one_mul, ← hχψ x, h, map_zero]⟩

/-- The irrelevant-ideal inclusion attached to a graded ring isomorphism. -/
public theorem irrelevant_le_map_of_inverse (ψ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜)
    (hψχ : ∀ b, ψ (χ b) = b) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ :=
  ProjPolynomialSections.irrelevant_le_map_of_graded_section 𝒜 ℬ ψ χ hψχ

/-- **`Proj` of a graded ring isomorphism is an isomorphism of schemes.** -/
public theorem isIso_projMap_of_inverse (ψ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜)
    (hψχ : ∀ b, ψ (χ b) = b) (hχψ : ∀ a, χ (ψ a) = a) :
    IsIso (AlgebraicGeometry.Proj.map ψ (irrelevant_le_map_of_inverse ψ χ hψχ)) :=
  AlgebraicGeometry.Proj.isIso_map _ (irrelevant_le_map_of_inverse χ ψ hχψ)
    (GradedRingHom.ext fun a => hχψ a) (GradedRingHom.ext fun b => hψχ b)

/-- **The twist comparison of a graded ring isomorphism is an isomorphism**, in every degree. -/
public theorem isIso_twistMap_of_inverse (ψ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜)
    (hψχ : ∀ b, ψ (χ b) = b) (hχψ : ∀ a, χ (ψ a) = a) (d : ℤ) :
    IsIso (Stacks.ProjTwistComparison.twistMap ψ (irrelevant_le_map_of_inverse ψ χ hψχ) d) :=
  Stacks.ProjTwistComparison.isIso_twistMap ψ _ d (isAwayDegreewise_one ψ χ hψχ hχψ)
    (SetLike.one_mem_graded 𝒜)

/-- **Cohomology of the twisting sheaves across a graded ring isomorphism.** For mutually
inverse graded ring homomorphisms between `𝒜` and `ℬ`, `Hᵠ(Proj ℬ, 𝒪(d))` vanishes exactly when
`Hᵠ(Proj 𝒜, 𝒪(d))` does. -/
public theorem isZero_Hgroup_twistingSheaf_iff_of_inverse (ψ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜)
    (hψχ : ∀ b, ψ (χ b) = b) (hχψ : ∀ a, χ (ψ a) = a) (d : ℤ) (q : ℕ) :
    IsZero (Hgroup (AlgebraicGeometry.Proj ℬ).ringCatSheaf ⊤ q (twistingSheaf ℬ d)) ↔
      IsZero (Hgroup (AlgebraicGeometry.Proj 𝒜).ringCatSheaf ⊤ q (twistingSheaf 𝒜 d)) := by
  have htw := isIso_twistMap_of_inverse ψ χ hψχ hχψ d
  have := isIso_projMap_of_inverse ψ χ hψχ hχψ
  let e := asIso (AlgebraicGeometry.Proj.map ψ (irrelevant_le_map_of_inverse ψ χ hψχ))
  refine Iff.trans ?_ (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff e
    (twistingSheaf 𝒜 d) q)
  exact Iso.isZero_iff ((Hfunctor (AlgebraicGeometry.Proj ℬ).ringCatSheaf ⊤ q).mapIso
    (@asIso _ _ _ _ (Stacks.ProjTwistComparison.twistMap ψ (irrelevant_le_map_of_inverse ψ χ hψχ) d)
      htw)).symm

/-- **Cohomology over the image of an open immersion.** For an open immersion `j : X ⟶ Y` and a
module `G` on `Y`, `Hᵠ(j(X), G)` vanishes exactly when `Hᵠ(X, j^* G)` does. -/
public theorem isZero_Hgroup_image_top_iff {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (G : Y.Modules) (q : ℕ) :
    IsZero (Hgroup Y.ringCatSheaf (j ''ᵁ ⊤) q G) ↔
      IsZero (Hgroup X.ringCatSheaf ⊤ q ((Scheme.Modules.restrictFunctor j).obj G)) := by
  rw [j.image_top_eq_opensRange]
  let e := j.isoOpensRange
  refine (Iso.isZero_iff (Stacks.LocalCohomology.hgroupRestrictIso Y j.opensRange q G)).trans ?_
  refine (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff e _ q).symm.trans ?_
  refine Iso.isZero_iff ((Hfunctor X.ringCatSheaf ⊤ q).mapIso ?_)
  exact ((Scheme.Modules.restrictFunctorIsoPullback e.hom).app _).symm ≪≫
    ((Scheme.Modules.restrictFunctorComp e.hom j.opensRange.ι).app G).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr j.isoOpensRange_hom_ι).app G

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
