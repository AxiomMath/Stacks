module

public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.StabilizationGenericFibre
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.PrestableMinimalModel

/-!
# A curve with semistable reduction is the generic fibre of the stabilization of its minimal model

Let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth projective curve over
`K` with `H⁰(C, 𝒪_C) = K` of genus `g ≥ 2` which has semistable reduction. Its minimal model is a
prestable family of curves over `Spec R` of genus `g` with generic fibre `C`
(`Stacks.Models.exists_isPrestableCurveFamily_of_hasSemistableReduction`). Any contraction of it
to a stable family of curves over `Spec R` whose fibres are contractions to stable curves
(conditions of [Stacks, Tag 0E8A]) has generic fibre `C`
(`AlgebraicGeometry.CurveFamily.exists_hom_of_stableContractionFibres`). This is the proof of the
implication (1) ⟹ (2) of [Stacks, Tag 0E8D], from the stabilization of [Stacks, Tag 0E8A].

## Main results

* `Stacks.Models.exists_isStableCurveFamily_of_stabilization`: if the prestable family of the
  minimal model has a stabilization in the sense of Stacks 0E8A, then `C` is the generic fibre of
  a stable family of curves over `R`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **(1) ⟹ (2) of [Stacks, Tag 0E8D], from a stabilization.** For a prestable family of curves
`X` over `Spec R` with generic fibre `C` (smooth, proper, `H⁰ = K`, genus `≥ 2`) and a morphism
`c : X ⟶ Y` over `Spec R` to a stable family whose fibres over field-valued points are contractions
to stable curves (Stacks 0E7Q), `C` is the generic fibre of the stable family `Y`. -/
theorem exists_isStableCurveFamily_of_stabilization (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] [IsProper c]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (hg : 2 ≤ genus c)
    {X : CurveFamily B hZ} (ψ : X.base ≅ integerSiteObject B hZ hR)
    (φ : @curveFamilyOfScheme K _ (Over.mk c) ‹IsProper c› B hZ
      (contains_spec_of_isFractionRing hR)
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := c)).le ⟶ X)
    (hφ : φ.baseMap ≫ ψ.hom = integerSiteMap B hZ (contains_spec_of_isFractionRing hR) hR
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    {Y : CurveFamily B hZ} (hb : Y.base = X.base) (c' : X.total ⟶ Y.total)
    (hc' : c' ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase)
    (hY : IsStableCurveFamily B hZ Y)
    (h2 : ∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
      (VX VY : BigFppfOver B integerBase hZ) (vX : VX ⟶ p.siteObject) (vY : VY ⟶ p.siteObject)
      (qX : yoneda.obj VX ⟶ X.total.obj) (qY : yoneda.obj VY ⟶ Y.total.obj) (a : VX ⟶ VY),
      IsPullback qX (yoneda.map vX) X.toBase.hom (yonedaEquiv.symm p.value) →
      IsPullback qY (yoneda.map vY) (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom
        (yonedaEquiv.symm p.value) →
      a ≫ vY = vX → qX ≫ c'.hom = yoneda.map a ≫ qY →
      Stacks.Curves.StableModel.IsStableContraction
        ((BigFppfOver.toScheme B integerBase hZ).map vX)
        ((BigFppfOver.toScheme B integerBase hZ).map vY)
        ((BigFppfOver.toScheme B integerBase hZ).map a)) :
    ∃ (F : CurveFamily B hZ) (ψ' : F.base ≅ integerSiteObject B hZ hR)
      (φ' : @curveFamilyOfScheme K _ (Over.mk c) ‹IsProper c› B hZ
        (contains_spec_of_isFractionRing hR)
        (IsCurve.topologicalKrullDim_eq_one (k := K) (f := c)).le ⟶ F),
      IsStableCurveFamily B hZ F ∧
        φ'.baseMap ≫ ψ'.hom = integerSiteMap B hZ (contains_spec_of_isFractionRing hR) hR
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨φ', hφ'⟩ := CurveFamily.exists_hom_of_stableContractionFibres
    (contains_spec_of_isFractionRing hR) c
    (IsCurve.topologicalKrullDim_eq_one (k := K) (f := c)) hg hb c' hc' hY h2 φ
  refine ⟨Y, eqToIso hb ≪≫ ψ, φ', hY, ?_⟩
  rw [hφ', Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, hφ]

end Stacks.Models

end
