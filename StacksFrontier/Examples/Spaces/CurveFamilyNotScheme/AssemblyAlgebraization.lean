module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.Instance.FormalNeighborhood
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveFormalNeighborhoodCofinal
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraizationAmple
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraizationSections
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal

/-!
# The algebraization of the formal neighbourhood of the strict transform

In the construction of [Stacks, Tag 0D5E], `Z` is the blowup of the cubic surface
`Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` at the chosen point `y` of the central fibre and
`C ⊆ Z` the strict transform of the central fibre, a curve of genus one with conormal sheaf
`𝒪_C(p)`. Let `A = lim Γ(Cₙ, 𝒪)`, a complete Noetherian local domain of dimension two
(`Stacks.Examples.CurveFamilyNotScheme.formalNeighborhoodRing_strictTransformCentralFibre`).
This file algebraizes the `𝔪`-adic tower `Zₙ = C_{2n+1} ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)` of the
formal neighbourhood of `C` (Stacks 089A, in the form
`AlgebraicGeometry.Scheme.IdealSheafData.exists_isProper_algebraization`): there is a proper
`f : Z~ ⟶ Spec A` with compatible morphisms `kₙ : Zₙ ⟶ Z~` exhibiting `Zₙ` as
`Z~ ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)`, and `A ⟶ Γ(Z~, 𝒪)` is bijective.

The cofinality input of the algebraization theorem is checked on a cover of `Z` by affine opens
on which `C` is cut out by a nonzerodivisor (`C` is an effective Cartier divisor), by
`AlgebraicGeometry.Scheme.IdealSheafData.pow_le_comap_map_maximalIdeal_pow_of_genusOne_of_iso`.

## Main definitions

* `Stacks.Examples.CurveFamilyNotScheme.cubicFormalRing`: `A`.
* `Stacks.Examples.CurveFamilyNotScheme.cubicTowerIndex`: `n ↦ 2 n + 1`.
* `Stacks.Examples.CurveFamilyNotScheme.cubicToLine`: `Z ⟶ A¹`.
* `Stacks.Examples.CurveFamilyNotScheme.cubicAlgebraization`,
  `Stacks.Examples.CurveFamilyNotScheme.cubicAlgebraizationHom`,
  `Stacks.Examples.CurveFamilyNotScheme.cubicAlgebraizationTower`: `Z~`, `f`, `kₙ`.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.maximalIdeal_cubicFormalRing_eq`: `𝔪 = F₁`.
* `Stacks.Examples.CurveFamilyNotScheme.exists_cubicAlgebraization`: the algebraization.
* `Stacks.Examples.CurveFamilyNotScheme.bijective_appTop_cubicAlgebraizationHom`:
  `A ≅ Γ(Z~, 𝒪)`.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.GenusOne
open Stacks.Divisors (IsEffectiveCartierDivisor negativeTwist)

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

variable (k : Type u) [Field k] [IsAlgClosed k] [Uncountable k] (h3 : ringChar k ≠ 3)

/-! ### The ring of formal functions along `C` -/

/-- The ring `A = lim Γ(Cₙ, 𝒪)` of formal functions along the strict transform `C` of the
central fibre. -/
abbrev cubicFormalRing : Type u :=
  (strictTransformCentralFibre k h3).formalNeighborhoodRing

/-- `A` is local. -/
instance isLocalRing_cubicFormalRing : IsLocalRing (cubicFormalRing k h3) :=
  (formalNeighborhoodRing_strictTransformCentralFibre k h3).1.isLocal

/-- `A` is Noetherian. -/
instance isNoetherianRing_cubicFormalRing : IsNoetherianRing (cubicFormalRing k h3) :=
  (formalNeighborhoodRing_strictTransformCentralFibre k h3).1.isNoetherian

/-- `A` is `𝔪`-adically complete. -/
instance isAdicComplete_cubicFormalRing :
    IsAdicComplete (maximalIdeal (cubicFormalRing k h3)) (cubicFormalRing k h3) :=
  (formalNeighborhoodRing_strictTransformCentralFibre k h3).1.isComplete

/-- `A` is a domain. -/
instance isDomain_cubicFormalRing : IsDomain (cubicFormalRing k h3) :=
  (formalNeighborhoodRing_strictTransformCentralFibre k h3).2.2

/-- `A` has Krull dimension two. -/
theorem ringKrullDim_cubicFormalRing : ringKrullDim (cubicFormalRing k h3) = 2 :=
  (formalNeighborhoodRing_strictTransformCentralFibre k h3).2.1

/-- The data of a curve of genus one with conormal sheaf `𝒪_C(p)` for the strict transform:
a `k`-point `p` of `C`, the effective Cartier divisor `p` on `C`, and `𝒪_Z(-C)|_C ≅ 𝒪_C(p)`. -/
theorem exists_point_conormal_iso :
    ∃ (p : Spec (.of k) ⟶ (strictTransformCentralFibre k h3).subscheme)
      (hp : p ≫ ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) = 𝟙 _),
      IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
        (⟨{GenusOne.point p}, GenusOne.isClosed_point _ p hp⟩ :
          Closeds (strictTransformCentralFibre k h3).subscheme) ^ 1) ∧
      Nonempty ((Scheme.Modules.pullback (strictTransformCentralFibre k h3).subschemeι).obj
          (negativeTwist (strictTransformCentralFibre k h3)) ≅
        GenusOne.pointDivisorSheaf p hp 1) := by
  obtain ⟨p, hp, -, ⟨ψ⟩⟩ := exists_section_conormal_iso k h3
  have := isCurve_fermatCurveToSpec k h3
  have : IsCurve k ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) :=
    GenusOne.isCurve _ (finrank_structureSheafCohomology_zero_strictTransformCentralFibre k h3)
  have : Smooth ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) :=
    SmoothOfRelativeDimension.smooth 1 ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k))
  refine ⟨p, hp, ?_, ⟨ψ⟩⟩
  rw [pow_one]
  have hcl : (⟨{GenusOne.point p}, GenusOne.isClosed_point _ p hp⟩ :
      Closeds (strictTransformCentralFibre k h3).subscheme) =
      Closeds.closure {GenusOne.point p} :=
    Closeds.ext (GenusOne.isClosed_point _ p hp).closure_eq.symm
  rw [hcl]
  exact IsCurve.isEffectiveCartierDivisor_vanishingIdeal_closure_singleton k
    ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) (GenusOne.isClosed_point _ p hp)

/-- **The maximal ideal of `A` is the first step of the filtration**: the compatible functions
vanishing on `C`. -/
theorem maximalIdeal_cubicFormalRing_eq :
    maximalIdeal (cubicFormalRing k h3) =
      formalNeighborhoodFiltration (strictTransformCentralFibre k h3) 1 := by
  obtain ⟨p, hp, _, ⟨ψ⟩⟩ := exists_point_conormal_iso k h3
  have h0 := finrank_structureSheafCohomology_zero_strictTransformCentralFibre k h3
  have hg := genus_strictTransformCentralFibre k h3
  have hsurj := surjective_thickeningRestriction_of_isZero (strictTransformCentralFibre k h3)
    (isZero_H1_conormalPow_of_genusOne h0 hg p hp
      (fun n => (nonempty_pullback_negativeTwist_pow_iso _ _ ψ n).some))
  have hA := isField_quotient_formalNeighborhoodFiltration_one_of_isField
    (strictTransformCentralFibre k h3)
    (surjective_formalNeighborhoodProjection _ hsurj 0)
    (isField_sections_of_genusOne (D := strictTransformCentralFibre k h3) h0)
  exact (IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ hA)).symm

/-- `𝔪ⁿ⁺¹` vanishes on the `n`-th thickening `Cₙ`. -/
theorem maximalIdeal_pow_le_ker_cubicFormalRing (n : ℕ) :
    maximalIdeal (cubicFormalRing k h3) ^ (n + 1) ≤
      RingHom.ker (formalNeighborhoodProjection (strictTransformCentralFibre k h3) n) :=
  (isCompleteFiltration_formalNeighborhoodFiltration _).pow_le _
    (maximalIdeal_cubicFormalRing_eq k h3).le (n + 1)

/-! ### A cover of `Z` by principal charts of `C` -/

/-- An affine open neighbourhood of `z` on which `C` is cut out by one regular function. -/
def principalChart (z : cubicBlowup k h3) : (cubicBlowup k h3).affineOpens :=
  ⟨_, (Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
    (strictTransformCentralFibre k h3)
    (isEffectiveCartierDivisor_strictTransformCentralFibre k h3) z).choose_spec.choose⟩

/-- `z` lies in its principal chart. -/
theorem mem_principalChart (z : cubicBlowup k h3) : z ∈ ((principalChart k h3 z).1 : Set _) :=
  (Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
    (strictTransformCentralFibre k h3)
    (isEffectiveCartierDivisor_strictTransformCentralFibre k h3) z).choose_spec.choose_spec.1

/-- On a principal chart, `C` is cut out by a nonzerodivisor. -/
theorem exists_ideal_principalChart_eq_span (z : cubicBlowup k h3) :
    ∃ t : Γ(cubicBlowup k h3, (principalChart k h3 z).1),
      t ∈ nonZeroDivisors _ ∧
        (strictTransformCentralFibre k h3).ideal (principalChart k h3 z) = Ideal.span {t} := by
  obtain ⟨t, ht, he⟩ :=
    (Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
    (strictTransformCentralFibre k h3)
    (isEffectiveCartierDivisor_strictTransformCentralFibre k h3) z).choose_spec.choose_spec.2
  exact ⟨t, ht.mem_nonZeroDivisors, he⟩

/-- The principal charts cover `Z`. -/
theorem iSup_principalChart : ⨆ z, (principalChart k h3 z).1 = ⊤ :=
  eq_top_iff.mpr fun z _ => Opens.mem_iSup.mpr ⟨z, mem_principalChart k h3 z⟩

/-! ### The adic tower and its algebraization -/

/-- The index function `n ↦ 2 n + 1` of the adic tower
`Zₙ = C_{2n+1} ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)`. -/
def cubicTowerIndex (n : ℕ) : ℕ := 2 * n + 1

/-- The index function of the tower is monotone. -/
theorem monotone_cubicTowerIndex : Monotone cubicTowerIndex := fun _ _ h => by
  simp only [cubicTowerIndex]
  omega

/-- The index function of the tower dominates the identity. -/
theorem le_cubicTowerIndex (n : ℕ) : n ≤ cubicTowerIndex n := by
  simp only [cubicTowerIndex]
  omega

/-- **The cofinality input of the algebraization on the principal charts**:
`I(V)^{2n+2} ⊆ 𝔪ⁿ⁺¹ · Γ(V, 𝒪) / I(V)^{2n+4}`. -/
theorem pow_le_comap_map_principalChart (n : ℕ) (z : cubicBlowup k h3) :
    (strictTransformCentralFibre k h3).ideal (principalChart k h3 z) ^ (cubicTowerIndex n + 1) ≤
      Ideal.comap (Ideal.Quotient.mk ((strictTransformCentralFibre k h3).ideal
          (principalChart k h3 z) ^ (cubicTowerIndex (n + 1) + 1)))
        (Ideal.map (formalNeighborhoodChart (strictTransformCentralFibre k h3)
            (principalChart k h3 z) (cubicTowerIndex (n + 1)))
          (maximalIdeal (cubicFormalRing k h3) ^ (n + 1))) := by
  obtain ⟨p, hp, _, ⟨ψ⟩⟩ := exists_point_conormal_iso k h3
  obtain ⟨t, ht, hVt⟩ := exists_ideal_principalChart_eq_span k h3 z
  have h := pow_le_comap_map_maximalIdeal_pow_of_genusOne_of_iso
    (finrank_structureSheafCohomology_zero_strictTransformCentralFibre k h3)
    (genus_strictTransformCentralFibre k h3) p hp ψ ht hVt (cubicTowerIndex (n + 1)) (n + 1)
  have he : cubicTowerIndex n + 1 = 2 * (n + 1) := by
    simp only [cubicTowerIndex]
    ring
  rw [he]
  exact h

/-- The structure morphism `Z ⟶ Y ⟶ A¹` of the blown-up cubic surface. -/
def cubicToLine : cubicBlowup k h3 ⟶ affineLine k :=
  pointBlowupToBase (chosenPoint k h3) (isClosed_chosenPoint k h3) ≫ cubicSurfaceToLine k

/-- `Z` is proper over `A¹`. -/
instance isProper_cubicToLine : IsProper (cubicToLine k h3) := by
  unfold cubicToLine
  infer_instance

/-- **The conormal sheaf of `C` is ample.** -/
theorem isAmple_conormalModule_strictTransformCentralFibre :
    Stacks.Ample.IsAmple (strictTransformCentralFibre k h3).subscheme
      (conormalModule (strictTransformCentralFibre k h3)) := by
  obtain ⟨p, hp, _, ⟨ψ⟩⟩ := exists_point_conormal_iso k h3
  exact isAmple_conormalModule_of_iso_pointDivisorSheaf _
    (finrank_structureSheafCohomology_zero_strictTransformCentralFibre k h3) p hp ψ

/-- **Algebraization of the formal neighbourhood of `C`** (Stacks 089A): a proper
`f : Z~ ⟶ Spec A` with compatible `kₙ : Zₙ ⟶ Z~` exhibiting the adic tower `Zₙ` as
`Z~ ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)`. -/
theorem exists_cubicAlgebraization :
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of (cubicFormalRing k h3))), IsProper fY ∧
      ∃ kk : ∀ n, adicTower (strictTransformCentralFibre k h3) (maximalIdeal _) cubicTowerIndex n ⟶
          Y,
        (∀ n, adicTowerSucc (strictTransformCentralFibre k h3) (maximalIdeal _)
          monotone_cubicTowerIndex n ≫ kk (n + 1) = kk n) ∧
        ∀ n, IsPullback (kk n)
          (adicTowerToThickening (strictTransformCentralFibre k h3) (maximalIdeal _)
            cubicTowerIndex n)
          fY (adicThickeningι (cubicFormalRing k h3) (maximalIdeal _) n) := by
  obtain ⟨Y, fY, hfY, -, -, -, kk, hk, hpb, -⟩ :=
    exists_isProper_algebraization (strictTransformCentralFibre k h3) (maximalIdeal _)
      cubicTowerIndex (cubicToLine k h3) (maximalIdeal_cubicFormalRing_eq k h3).le
      monotone_cubicTowerIndex (principalChart k h3) (iSup_principalChart k h3)
      (fun n z => pow_le_comap_map_principalChart k h3 n z)
      (isAmple_conormalModule_strictTransformCentralFibre k h3)
  exact ⟨Y, fY, hfY, kk, hk, hpb⟩

/-- The algebraization `Z~` of the formal neighbourhood of `C`. -/
def cubicAlgebraization : Scheme.{u} := (exists_cubicAlgebraization k h3).choose

/-- The proper morphism `f : Z~ ⟶ Spec A`. -/
def cubicAlgebraizationHom : cubicAlgebraization k h3 ⟶ Spec (.of (cubicFormalRing k h3)) :=
  (exists_cubicAlgebraization k h3).choose_spec.choose

/-- `f : Z~ ⟶ Spec A` is proper. -/
instance isProper_cubicAlgebraizationHom : IsProper (cubicAlgebraizationHom k h3) :=
  (exists_cubicAlgebraization k h3).choose_spec.choose_spec.1

/-- The morphisms `kₙ : Zₙ ⟶ Z~` from the adic tower. -/
def cubicAlgebraizationTower (n : ℕ) :
    adicTower (strictTransformCentralFibre k h3) (maximalIdeal _) cubicTowerIndex n ⟶
      cubicAlgebraization k h3 :=
  (exists_cubicAlgebraization k h3).choose_spec.choose_spec.2.choose n

/-- The morphisms `kₙ` are compatible with the transition maps of the tower. -/
theorem adicTowerSucc_comp_cubicAlgebraizationTower (n : ℕ) :
    adicTowerSucc (strictTransformCentralFibre k h3) (maximalIdeal _) monotone_cubicTowerIndex n ≫
      cubicAlgebraizationTower k h3 (n + 1) = cubicAlgebraizationTower k h3 n :=
  (exists_cubicAlgebraization k h3).choose_spec.choose_spec.2.choose_spec.1 n

/-- The morphisms `kₙ` exhibit `Zₙ` as `Z~ ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)`. -/
theorem isPullback_cubicAlgebraizationTower (n : ℕ) :
    IsPullback (cubicAlgebraizationTower k h3 n)
      (adicTowerToThickening (strictTransformCentralFibre k h3) (maximalIdeal _) cubicTowerIndex n)
      (cubicAlgebraizationHom k h3) (adicThickeningι (cubicFormalRing k h3) (maximalIdeal _) n) :=
  (exists_cubicAlgebraization k h3).choose_spec.choose_spec.2.choose_spec.2 n

/-- **`A ⟶ Γ(Z~, 𝒪)` is bijective.** -/
theorem bijective_appTop_cubicAlgebraizationHom :
    Function.Bijective
      ((Scheme.ΓSpecIso (.of (cubicFormalRing k h3))).inv ≫
        (cubicAlgebraizationHom k h3).appTop).hom :=
  bijective_appTop_of_isPullback (strictTransformCentralFibre k h3) (maximalIdeal _)
    monotone_cubicTowerIndex le_rfl (maximalIdeal_pow_le_ker_cubicFormalRing k h3)
    le_cubicTowerIndex (cubicAlgebraizationHom k h3) (cubicAlgebraizationTower k h3)
    (adicTowerSucc_comp_cubicAlgebraizationTower k h3) (isPullback_cubicAlgebraizationTower k h3)

end Stacks.Examples.CurveFamilyNotScheme

end
