module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenusRank
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOverField

/-!
# The fibre genus of the family of a proper scheme over a field

For a proper scheme `X` of dimension at most one over a field `k`, the family of curves
`X → Spec k` (`AlgebraicGeometry.curveFamilyOfScheme`) has every fibre over a field-valued point
of genus `g` (`AlgebraicGeometry.CurveFamily.HasFieldPointFibreGenus`) exactly when `X` has genus
`g`: a fibre over `Spec K → Spec k` is the base change of `X` along `K/k`, which does not change
the genus (Stacks 0BY9), and the fibre over the identity point is a base change of `X` along the
identity of `k`.

## Main results

* `AlgebraicGeometry.hasFieldPointFibreGenus_curveFamilyOfScheme_iff`

## References

* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The fibre genus of the family of a proper scheme over a field** is the genus of the scheme:
every fibre of `X → Spec k` has genus `g` exactly when `X` has genus `g`. A fibre over a
field-valued point `Spec K → Spec k` is a base change of `X` along `K/k`, of the same genus
(Stacks 0BY9); conversely the fibre over the identity point is a base change of `X` along the
identity of `k`. -/
theorem hasFieldPointFibreGenus_curveFamilyOfScheme_iff {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) :
    CurveFamily.HasFieldPointFibreGenus B hZ (curveFamilyOfScheme X B hZ hk hdim) g ↔
      genus X.hom = g := by
  have hX : B.Contains X.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk
  -- a presentation of a fibre is a cartesian square of schemes
  have hfibsq : ∀ (p : Space.FieldValuedPoint B integerBase hZ
      (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj)
      (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
      (q : yoneda.obj V ⟶ (curveFamilyOfScheme X B hZ hk hdim).total.obj),
      IsPullback q (yoneda.map v) (curveFamilyOfScheme X B hZ hk hdim).toBase.hom
        (yonedaEquiv.symm p.value) →
      ∃ a : (BigFppfOver.toScheme B integerBase hZ).obj V ⟶ X.left,
        @IsPullback Scheme.{u} _ _ _ (Spec (.of p.carrier)) (Spec (.of k)) a
          ((BigFppfOver.toScheme B integerBase hZ).map v) X.hom
          ((BigFppfOver.toScheme B integerBase hZ).map p.value) := by
    intro p V v q hq
    have hval : yonedaEquiv.symm p.value = yoneda.map p.value :=
      yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map _).symm
    rw [hval] at hq
    exact ⟨_, isPullback_toScheme_of_isPullback_yoneda (c := integerSiteMap B hZ hX hk X.hom) hq⟩
  refine ⟨fun hfib => ?_, fun hgen p => ?_⟩
  · let p₀ : Space.FieldValuedPoint B integerBase hZ
        (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj :=
      ⟨k, hk, specULiftZIsTerminal.from _, 𝟙 _⟩
    have hp₀ : (BigFppfOver.toScheme B integerBase hZ).map p₀.value =
        Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
      exact (BigFppfOver.toScheme B integerBase hZ).map_id _
    obtain ⟨V, v, q, hq, hgV⟩ := hfib p₀
    obtain ⟨a, ha⟩ := hfibsq p₀ V v q hq
    rw [hp₀] at ha
    exact (genus_baseChange k k a _ X.hom ha).symm.trans hgV
  · obtain ⟨V, v, q, hq⟩ :=
      (curveFamilyOfScheme X B hZ hk hdim).exists_isPullback_yoneda_fieldValuedPoint p
    obtain ⟨a, ha⟩ := hfibsq p V v q hq
    set φ := (BigFppfOver.toScheme B integerBase hZ).map p.value
    let : Algebra k p.carrier := (Spec.preimage φ).hom.toAlgebra
    have hφ : Spec.map (CommRingCat.ofHom (algebraMap k p.carrier)) = φ := Spec.map_preimage φ
    rw [← hφ] at ha
    exact ⟨V, v, q, hq, (genus_baseChange k p.carrier a _ X.hom ha).trans hgen⟩

end AlgebraicGeometry

end
