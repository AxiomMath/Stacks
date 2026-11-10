module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelChart
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelUniqueHom
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelGlue
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.EtaleLocalContraction

/-!
# Existence of the stable model

A prestable family of curves `X ⟶ S` with fibres of genus `g ≥ 2` has a stable model, granted
étale-local scheme charts and the openness of the locus of stable families.

## Main results

* `AlgebraicGeometry.C1590Private.exists_isStableContraction_residueField`: the fibre at the
  residue field of a point of the base has a stable contraction, as a morphism of objects of the
  site.
* `AlgebraicGeometry.C1590Private.exists_isStableModel_of_etaleContraction`: the stable model
  exists, granted in addition the étale-local deformation of such a contraction.
* `AlgebraicGeometry.C1590Private.exists_isStableModel`: the stable model exists.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

open Stacks.Curves.StableModel in
/-- Let `X` be a prestable family of curves of genus `g ≥ 2` and `s` a point of its base. At the
residue field point `P` of `s` the fibre of `X` is presented by a scheme `V`, of dimension at most
one with `H⁰(V, 𝒪_V) = κ(s)`, and it has a stable contraction `V ⟶ W₀` to an object of the site. -/
theorem exists_isStableContraction_residueField {g : ℕ} {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) (hgen : X.HasFibresOfGenus g) (hg : 2 ≤ g)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    ∃ (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
      (e : CommRingCat.of ((BigFppfOver.toScheme B integerBase hZ).obj X.base |>.residueField s) ⟶
        CommRingCat.of P.carrier),
      IsIso e ∧
      Spec.map e ≫
          ((BigFppfOver.toScheme B integerBase hZ).obj X.base).fromSpecResidueField s =
        (BigFppfOver.toScheme B integerBase hZ).map P.value ∧
      ∃ (V W₀ : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject)
        (q : yoneda.obj V ⟶ X.total.obj),
        IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value) ∧
        ∃ (w₀ : W₀ ⟶ P.siteObject) (m₀ : V ⟶ W₀), m₀ ≫ w₀ = v ∧
          IsStableContraction ((BigFppfOver.toScheme B integerBase hZ).map v)
            ((BigFppfOver.toScheme B integerBase hZ).map w₀)
            ((BigFppfOver.toScheme B integerBase hZ).map m₀) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) ≤ 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of P.carrier)).inv ≫
            ((BigFppfOver.toScheme B integerBase hZ).map v).appTop) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  let P := residuePointVia (𝟙 X.base) s
  obtain ⟨V, v, q, hq⟩ := exists_presentation_of_fieldValuedPoint X P
  obtain ⟨hp, hdim, hH0, hnod⟩ := fibre_properties_of_isPrestableCurveFamily hX P v q hq
  have := hp
  have := hH0
  have hgV : genus (T.map v) = g := (hgen P).genus_eq v q hq
  obtain ⟨Y₀, gY, c, hc⟩ := exists_isStableContraction (T.map v) hdim (hgV ▸ hg) hnod
  have : IsProper gY := hc.isProper
  have hY₀ : B.Contains Y₀ :=
    Space.contains_of_locallyOfFiniteType_of_quasiCompact B integerBase hZ (Y₀ := P.siteObject) gY
  let W₀ := BigFppfOver.siteObjectOver B integerBase hZ P.siteObject hY₀ gY
  let w₀ : W₀ ⟶ P.siteObject := BigFppfOver.siteMapOver B integerBase hZ P.siteObject hY₀ gY
  let m₀ : V ⟶ W₀ := homOfToScheme c
  have hm₀ : m₀ ≫ w₀ = v := hom_ext_of_toScheme (by
    rw [Functor.map_comp]
    exact hc.comp_eq)
  let κ := CommRingCat.of ((T.obj X.base).residueField s)
  let e : κ ⟶ CommRingCat.of P.carrier := 𝟙 κ
  have : IsIso e := inferInstanceAs (IsIso (𝟙 κ))
  refine ⟨P, e, inferInstance, ?_, V, W₀, v, q, hq, w₀, m₀, hm₀, hc, hdim.le, hH0⟩
  change Spec.map (𝟙 κ) ≫ _ = _
  rw [Spec.map_id, Category.id_comp]
  change _ = T.map (Space.residueFieldMap B integerBase hZ X.base s _ ≫ 𝟙 X.base)
  rw [Functor.map_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

open Stacks.Curves.StableModel in
/-- Let `X` be a prestable family of curves with fibres of genus `g ≥ 2`. Granted étale-local
scheme charts (`h0E6F`), the openness of the locus of stable families (`h0E76`), and the
étale-local deformation `h0E7C` of the stable contraction of a fibre at a residue field, in the
shape produced by `AlgebraicGeometry.C1590Private.exists_isStableContraction_residueField`, `X` has
a stable model. -/
theorem exists_isStableModel_of_etaleContraction (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (h0E76 : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ))
    (h0E7C : ∀ (X : CurveFamily B hZ) (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base)
      (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
      (_ : ∃ e : CommRingCat.of
            ((BigFppfOver.toScheme B integerBase hZ).obj X.base |>.residueField s) ⟶
          CommRingCat.of P.carrier,
        IsIso e ∧
          Spec.map e ≫
              ((BigFppfOver.toScheme B integerBase hZ).obj X.base).fromSpecResidueField s =
            (BigFppfOver.toScheme B integerBase hZ).map P.value)
      ⦃V W₀ : BigFppfOver B integerBase hZ⦄ (v : V ⟶ P.siteObject)
      (q : yoneda.obj V ⟶ X.total.obj),
      IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value) →
      ∀ (w₀ : W₀ ⟶ P.siteObject) (m₀ : V ⟶ W₀), m₀ ≫ w₀ = v →
      IsStableContraction ((BigFppfOver.toScheme B integerBase hZ).map v)
        ((BigFppfOver.toScheme B integerBase hZ).map w₀)
        ((BigFppfOver.toScheme B integerBase hZ).map m₀) →
      topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) ≤ 1 →
      IsIso ((Scheme.ΓSpecIso (.of P.carrier)).inv ≫
        ((BigFppfOver.toScheme B integerBase hZ).map v).appTop) →
      ∃ (Y : CurveFamily B hZ) (t : Y.base ⟶ X.base)
        (u : (BigFppfOver.toScheme B integerBase hZ).obj Y.base),
        Etale ((BigFppfOver.toScheme B integerBase hZ).map t) ∧
        (BigFppfOver.toScheme B integerBase hZ).map t u = s ∧
        ∃ (A : AlgebraicSpaces B integerBase hZ) (iA : A ⟶ X.total) (pA : A ⟶ schemeSpace Y.base),
          IsPullback iA pA X.toBase (schemeSpaceMap t) ∧
          ∃ h : A ⟶ Y.total, h ≫ Y.toBase = pA ∧ FibresStableContractionsAt Y pA h u)
    {g : ℕ} (hg : 2 ≤ g) {X : CurveFamily B hZ} (hX : IsPrestableCurveFamily B hZ X)
    (hgen : X.HasFibresOfGenus g) :
    ∃ (Y : CurveFamily B hZ) (b : X.base ⟶ Y.base) (c : X.total ⟶ Y.total),
      IsStableModel B hZ g b c := by
  refine exists_isStableModel_of_locally hg hX hgen
    (fun hX₀ h₁ h₂ => IsStableModel.exists_hom h0E6F hX₀ hg h₁ h₂) fun s => ?_
  obtain ⟨P, e, he, heq, V, W₀, v, q, hq, w₀, m₀, hm₀, hc, hdimV, hH0⟩ :=
    exists_isStableContraction_residueField hX hgen hg s
  obtain ⟨Y, t, u, ht, hts, A, iA, pA, hsq, h, hh, hfib⟩ :=
    h0E7C X s P ⟨e, he, heq⟩ v q hq w₀ m₀ hm₀ hc hdimV hH0
  obtain ⟨X', Y', φ, b', c', hφ, hs, hst⟩ :=
    exists_isStableModel_of_fibresStableContractionsAt h0E6F h0E76 hX hgen hg Y t ht iA pA hsq h
      hh u hfib
  exact ⟨X', φ, hφ, hts ▸ hs, Y', b', c', hst⟩

/-- Granted étale-local scheme charts (`h0E6F`) and the openness of the locus of stable families
(`h0E76`), a prestable family of curves `X` with fibres of genus `g ≥ 2` has a stable model: a
family `Y`, an isomorphism of bases `b` and a morphism of total spaces `c` satisfying
`AlgebraicGeometry.C1590Private.IsStableModel`, with `Y` stable of genus `g`. -/
theorem exists_isStableModel (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (h0E76 : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ)) {g : ℕ} (hg : 2 ≤ g)
    {X : CurveFamily B hZ} (hX : IsPrestableCurveFamily B hZ X) (hgen : X.HasFibresOfGenus g) :
    ∃ (Y : CurveFamily B hZ) (b : X.base ⟶ Y.base) (c : X.total ⟶ Y.total),
      IsStableModel B hZ g b c :=
  exists_isStableModel_of_etaleContraction h0E6F h0E76 (exists_etale_contraction_of_fibre h0E6F)
    hg hX hgen

end AlgebraicGeometry.C1590Private

end
