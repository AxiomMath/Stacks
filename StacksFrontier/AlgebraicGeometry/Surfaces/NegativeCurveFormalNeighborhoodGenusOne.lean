module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.PointDivisorData
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.FibreDims
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveFormalNeighborhoodStalk

/-!
# The formal neighbourhood of a curve of genus one with conormal bundle `𝒪(p)`

Let `D` be an effective Cartier divisor on a scheme `X` whose subscheme `C = V(D)` is a proper
smooth curve of genus one over a field `k` with `H⁰(C, 𝒪_C) = k`, let `p` be a `k`-point of `C`,
and suppose the powers of the conormal sheaf are the powers of `𝒪_C(p)`:

`φₙ : 𝒪_X(-D ^ (n + 1))|_C ≅ 𝒪_C(p) ^⊗ (n + 1)`  for every `n`.

This is the situation of the strict transform `C` of a smooth fibre of a family of surfaces,
blown up at a point `y` of the fibre: `C · C = -1`, and the conormal bundle of `C` is `𝒪_C(p)` for
`p = C ∩ E`.

Then the ring `A = lim Γ(Cₙ, 𝒪)` of compatible functions on the thickenings of `C` is a complete
Noetherian local domain of Krull dimension two
(`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing_of_genusOne`).

The hypotheses of
`AlgebraicGeometry.Scheme.IdealSheafData.isNoetherianCompleteLocalRing_of_chartPointValue` are
read off the section ring of `𝒪_C(p)`, `AlgebraicGeometry.GenusOne.pointDivisorData`:

* `H¹(C, 𝒪(p)^⊗ m) = 0` and `dim H⁰(C, 𝒪(p)^⊗ m) = m` for `m ≥ 1` (Riemann–Roch);
* the sections of `𝒪(p)` vanish at `p`, and `𝒪(p)^⊗ 2`, `𝒪(p)^⊗ 3` have sections of order `0` at
  `p` (the orders attained in degree `m` are `[0, m] \ {m - 1}`);

and the values at `p` of the formal neighbourhood are the vanishing of these sections, by
`AlgebraicGeometry.Scheme.IdealSheafData.germ_mem_maximalSmul_iff_chartPointValue_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Divisors
open AlgebraicGeometry.GenusOne
open Stacks.GradedSections (powSections sectionRing)
open Stacks.TensorPowers (natTensorPow)
open Stacks.SectionProduct (globalSection)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (baseRingHom)
open Stacks.StalkOrder

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

attribute [local instance] Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.sectionAlgebra
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-! ### Orders of sections and vanishing -/

section Order

variable {Y : Scheme.{u}} (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] (y : Y)
  [IsDomain (Y.presheaf.stalk y)] [IsDiscreteValuationRing (Y.presheaf.stalk y)]

/-- **A germ of an invertible module has order `0` exactly when it does not vanish.** -/
public theorem stalkOrd_eq_zero_iff_notMem_maximalSmul
    (z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf y) :
    stalkOrd M y z = 0 ↔ z ∉ Stacks.ModuleStalk.maximalSmul M y := by
  obtain ⟨g, hg, hfree⟩ := exists_generator M y
  have hgm : g ∉ Stacks.ModuleStalk.maximalSmul M y := by
    intro hgm
    have htop : (⊤ : Submodule (Y.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf y)) = Submodule.span _ {g} := by
      refine (eq_top_iff.2 fun m _ => ?_).symm
      obtain ⟨r, rfl⟩ := hg m
      exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self g)
    rw [Stacks.ModuleStalk.maximalSmul, htop, Submodule.mem_smul_span_singleton] at hgm
    obtain ⟨μ, hμ, hμg⟩ := hgm
    have h1 : (1 - μ) • g = 0 := by rw [sub_smul, one_smul, hμg, sub_self]
    have h2 := hfree _ h1
    rw [sub_eq_zero] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      ((Ideal.eq_top_iff_one _).2 (h2 ▸ hμ))
  obtain ⟨r, rfl⟩ := hg z
  rw [stalkOrd_smul_generator hg hfree, IsDiscreteValuationRing.addVal_eq_zero_iff,
    Stacks.ModuleStalk.smul_mem_maximalSmul_iff]
  tauto

end Order

/-! ### The genus-one data -/

section GenusOneData

variable {k : Type u} [Field k] {X : Scheme.{u}} {D : X.IdealSheafData}
  [D.subscheme.Over (Spec (.of k))]
  [IsProper (D.subscheme ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (D.subscheme ↘ Spec (.of k))]
  (h0 : Module.finrank k (structureSheafCohomology (D.subscheme ↘ Spec (.of k)) 0) = 1)
  (hg : genus (D.subscheme ↘ Spec (.of k)) = 1) (p : Spec (.of k) ⟶ D.subscheme)
  (hp : p ≫ (D.subscheme ↘ Spec (.of k)) = 𝟙 _)
  [IsEffectiveCartierDivisor (vanishingIdeal
    (⟨{point p}, isClosed_point (D.subscheme ↘ Spec (.of k)) p hp⟩ : Closeds D.subscheme) ^ 1)]
  (φ : ∀ n : ℕ, (Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))) ≅
    natTensorPow (pointDivisorSheaf p hp 1) (n + 1))

omit [IsProper (D.subscheme ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 1 (D.subscheme ↘ Spec (.of k))] in
include h0 in
/-- `Γ(C, 𝒪_C) = k` is a field. -/
public theorem isField_sections_of_genusOne : IsField Γ(D.subscheme, ⊤) :=
  MulEquiv.isField (Field.toIsField k)
    (RingEquiv.ofBijective _ (bijective_globalSectionsHom _ h0)).symm.toMulEquiv

/-- The additive equivalence of global sections induced by an isomorphism of modules. -/
private def sectionsAddEquivOfIso {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N) :
    Γ(M, ⊤) ≃+ Γ(N, ⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  left_inv m := by
    change (e.hom ≫ e.inv).app ⊤ m = m
    rw [e.hom_inv_id]; rfl
  right_inv m := by
    change (e.inv ≫ e.hom).app ⊤ m = m
    rw [e.inv_hom_id]; rfl
  map_add' a b := map_add _ a b

include h0 hg φ in
/-- **`dim H⁰(C, Lⁿ⁺¹) = n + 1`**, from Riemann–Roch for `𝒪(p)^⊗ (n + 1)`. -/
public theorem finrank_conormalPowSections_of_genusOne (n : ℕ) :
    Module.finrank Γ(D.subscheme, ⊤) (conormalPowSections D n) = n + 1 := by
  have h := finrank_cohomologyOverField_zero_pointDivisor h0 hg p hp 1 one_pos
    (m := n + 1) (by omega)
  rw [← finrank_gradingK, (gradingKEquivSections (pointDivisorSheaf p hp 1) k (n + 1)).finrank_eq,
    one_mul] at h
  have hr := rank_eq_of_equiv_equiv (baseRingHom k D.subscheme)
    (sectionsAddEquivOfIso (φ n)).symm (bijective_globalSectionsHom _ h0)
    fun c m => Scheme.Modules.Hom.app_smul _ _ _
  have hf := congrArg Cardinal.toNat hr
  change Module.finrank k _ = Module.finrank Γ(D.subscheme, ⊤) (conormalPowSections D n) at hf
  rw [← hf, h]

include h0 hg φ in
/-- **`H¹(C, Lⁿ⁺¹) = 0`**, from the vanishing of `H¹(C, 𝒪(p)^⊗ (n + 1))`. -/
public theorem isZero_H1_conormalPow_of_genusOne (n : ℕ) :
    IsZero (((Stacks.Cohomology.sectionsFunctor D.subscheme ⊤).rightDerived 1).obj
      ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))))) := by
  have h := isZero_cohomologyOverField_pointDivisor h0 hg p hp 1 one_pos (m := n + 1)
    (by omega) (i := 1) one_pos
  have h' := IsZero.of_iso h (Stacks.FibreCohomology.cohomologyOverFieldMapIso k _ (φ n) 1)
  rw [ModuleCat.isZero_iff_subsingleton] at h' ⊢
  exact h'

include h0 hg in
/-- **Every section of `𝒪(p)` vanishes at `p`**: the orders attained in degree one are `{1}`. -/
private theorem germ_mem_maximalSmul_natTensorPow_one
    (τ : Γ(natTensorPow (pointDivisorSheaf p hp 1) 1, ⊤)) :
    ((natTensorPow (pointDivisorSheaf p hp 1) 1).presheaf.Γgerm (point p)).hom τ ∈
      Stacks.ModuleStalk.maximalSmul (natTensorPow (pointDivisorSheaf p hp 1) 1) (point p) := by
  have := isIntegral (D.subscheme ↘ Spec (.of k)) h0
  have := isDiscreteValuationRing_stalk (D.subscheme ↘ Spec (.of k)) h0 p hp
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := D.subscheme)
    (pointDivisorSheaf p hp 1) 1
  have := nontrivial_sectionRing h0 (pointDivisorSheaf p hp 1)
  by_contra hτ
  have hord0 := (stalkOrd_eq_zero_iff_notMem_maximalSmul _ _ _).2 hτ
  set s := (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv D.subscheme _).symm τ
  have hs : globalSection D.subscheme _ s = τ :=
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv D.subscheme _).apply_symm_apply τ
  have hne : DirectSum.of (powSections (pointDivisorSheaf p hp 1)) 1 s ≠ 0 := by
    intro h
    have hs0 : s = 0 := DirectSum.of_injective 1 (h.trans (map_zero _).symm)
    apply hτ
    rw [← hs, hs0, show globalSection D.subscheme _ (0 : powSections _ 1) = 0 from
      map_zero (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv D.subscheme _), map_zero]
    exact zero_mem _
  have hord : (pointDivisorData h0 hg p hp 1 one_pos).ord
      (DirectSum.of (powSections (pointDivisorSheaf p hp 1)) 1 s) = ((0 : ℕ) : ℕ∞) := by
    change ringOrd (pointDivisorSheaf p hp 1) (point p) _ = _
    rw [ringOrd_of]
    change stalkOrd _ _ (((natTensorPow (pointDivisorSheaf p hp 1) 1).presheaf.Γgerm (point p)).hom
      (globalSection D.subscheme _ s)) = _
    rw [hs, hord0]
    rfl
  have h := (Stacks.GenusOneSectionRing.exists_ord_eq_iff (pointDivisorData h0 hg p hp 1 one_pos)
    le_rfl le_rfl 0).1 ⟨_, ⟨s, rfl⟩, hne, hord⟩
  omega

include h0 hg in
/-- **`𝒪(p)^⊗ m` has a section not vanishing at `p`** for `m ≥ 2`: order `0` is attained in
degree `m`. -/
private theorem exists_germ_notMem_maximalSmul_natTensorPow {m : ℕ} (hm : 2 ≤ m) :
    ∃ τ : Γ(natTensorPow (pointDivisorSheaf p hp 1) m, ⊤),
      ((natTensorPow (pointDivisorSheaf p hp 1) m).presheaf.Γgerm (point p)).hom τ ∉
        Stacks.ModuleStalk.maximalSmul (natTensorPow (pointDivisorSheaf p hp 1) m) (point p) := by
  have := isIntegral (D.subscheme ↘ Spec (.of k)) h0
  have := isDiscreteValuationRing_stalk (D.subscheme ↘ Spec (.of k)) h0 p hp
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := D.subscheme)
    (pointDivisorSheaf p hp 1) m
  have := nontrivial_sectionRing h0 (pointDivisorSheaf p hp 1)
  obtain ⟨a, ⟨s, rfl⟩, -, hord⟩ := (Stacks.GenusOneSectionRing.exists_ord_eq_iff
    (pointDivisorData h0 hg p hp 1 one_pos) le_rfl (by omega : 1 ≤ m) 0).2 ⟨by omega, by omega⟩
  refine ⟨globalSection D.subscheme _ s, (stalkOrd_eq_zero_iff_notMem_maximalSmul _ _ _).1 ?_⟩
  have h : ringOrd (pointDivisorSheaf p hp 1) (point p)
      (DirectSum.of (powSections (pointDivisorSheaf p hp 1)) m s) = ((0 : ℕ) : ℕ∞) := hord
  rw [ringOrd_of] at h
  exact h

include h0 hg φ in
/-- **Every section of `L` vanishes at `p`.** -/
public theorem germ_mem_maximalSmul_conormal (σ : conormalPowSections D 0) :
    (((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (0 + 1)))).presheaf.Γgerm
        (point p)).hom σ ∈ Stacks.ModuleStalk.maximalSmul
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (0 + 1)))) (point p) := by
  rw [← Stacks.ModuleStalk.mem_maximalSmul_mapFun_iff (φ 0), Stacks.ModuleStalk.mapFun_Γgerm]
  exact germ_mem_maximalSmul_natTensorPow_one h0 hg p hp _

include h0 hg φ in
/-- **`Lⁿ⁺¹` has a section not vanishing at `p`** for `n ≥ 1`. -/
public theorem exists_germ_notMem_maximalSmul_conormal {n : ℕ} (hn : 1 ≤ n) :
    ∃ σ : conormalPowSections D n,
      (((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1)))).presheaf.Γgerm
        (point p)).hom σ ∉ Stacks.ModuleStalk.maximalSmul
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1)))) (point p) := by
  obtain ⟨τ, hτ⟩ := exists_germ_notMem_maximalSmul_natTensorPow h0 hg p hp (m := n + 1) (by omega)
  refine ⟨(φ n).inv.app ⊤ τ, ?_⟩
  rw [← Stacks.ModuleStalk.mem_maximalSmul_mapFun_iff (φ n), Stacks.ModuleStalk.mapFun_Γgerm]
  change ((natTensorPow (pointDivisorSheaf p hp 1) (n + 1)).presheaf.Γgerm (point p)).hom
    (((φ n).inv ≫ (φ n).hom).app ⊤ τ) ∉ _
  rw [(φ n).inv_hom_id]
  exact hτ

include h0 hg φ in
/-- **The formal neighbourhood of a curve of genus one with conormal bundle `𝒪(p)`.** Let `D` be
an effective Cartier divisor on a scheme `X` whose subscheme `C` is a proper smooth curve of genus
one over `k` with `H⁰(C, 𝒪_C) = k`, let `p` be a `k`-point of `C`, and let
`φₙ : 𝒪_X(-D ^ (n + 1))|_C ≅ 𝒪_C(p) ^⊗ (n + 1)`. Then the ring `lim Γ(Cₙ, 𝒪)` of compatible
functions on the thickenings of `C` is a complete Noetherian local domain of Krull dimension `2`. -/
public theorem formalNeighborhoodRing_of_genusOne [IsEffectiveCartierDivisor D] :
    IsNoetherianCompleteLocalRing (formalNeighborhoodRing D) ∧
      ringKrullDim (formalNeighborhoodRing D) = 2 ∧ IsDomain (formalNeighborhoodRing D) := by
  have := isIntegral (D.subscheme ↘ Spec (.of k)) h0
  obtain ⟨V, hxV, t, ht, hVt⟩ := Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor D
    inferInstance (D.subschemeι.base (point p))
  have hP := ideal_le_chartPrime D V hxV (subschemeι_mem_support (point p))
  have hsurj := surjective_thickeningRestriction_of_isZero D
    (isZero_H1_conormalPow_of_genusOne h0 hg p hp φ)
  have hfield := isField_sections_of_genusOne (D := D) h0
  have hdim := finrank_conormalPowSections_of_genusOne h0 hg p hp φ
  have h1 : ∀ a ∈ formalNeighborhoodFiltration D 1, chartPointValue D V t hP 1 a = 0 := by
    intro a ha
    exact (germ_mem_maximalSmul_iff_chartPointValue_eq_zero ht hVt (point p) hxV 0 _
      (gradedSectionsHom_gradedSymbol D 0 ⟨a, ha⟩)).1
      (germ_mem_maximalSmul_conormal h0 hg p hp φ _)
  have hlift : ∀ n, 1 ≤ n → ∃ z ∈ formalNeighborhoodFiltration D (n + 1),
      chartPointValue D V t hP (n + 1) z ≠ 0 := by
    intro n hn
    obtain ⟨σ, hσ⟩ := exists_germ_notMem_maximalSmul_conormal h0 hg p hp φ hn
    obtain ⟨z, hz, hzσ⟩ := exists_projection_eq_of_thickeningRestriction_eq_zero D n hsurj
      ((gradedSectionsHom_eq_iff D n _).2 ⟨σ, rfl⟩)
    exact ⟨z, hz, fun h => hσ ((germ_mem_maximalSmul_iff_chartPointValue_eq_zero ht hVt (point p)
      hxV n σ hzσ.symm).2 h)⟩
  obtain ⟨x, hx, hx0⟩ := hlift 1 le_rfl
  obtain ⟨y, hy, hy0⟩ := hlift 2 (by omega)
  exact ⟨isNoetherianCompleteLocalRing_of_chartPointValue hP hsurj hfield hdim ht hVt h1 hx hx0
      hy hy0,
    ringKrullDim_formalNeighborhoodRing_eq_two_of_chartPointValue hP hsurj hfield hdim ht hVt h1 hx
      hx0 hy hy0,
    isDomain_formalNeighborhoodRing⟩

end GenusOneData

end AlgebraicGeometry.Scheme.IdealSheafData

end
