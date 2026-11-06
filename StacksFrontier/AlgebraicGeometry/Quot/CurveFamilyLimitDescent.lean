module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeGlue
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent

/-!
# Families of curves along affine cofiltered limits

Descent of a family of curves (Stacks 0D55) and of a morphism between the total spaces of two
families (the fullness half of Stacks 07SK) from the vertex of a cofiltered system of affine
schemes of the site to one of its stages.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_hom_to_stage_of_isLimit`: a family of curves over the
  vertex is the base change of one over a stage.
* `AlgebraicGeometry.CurveFamily.exists_stage_totalMap_of_isLimit`: a morphism over the vertex
  between the total spaces of base changes of two families over a stage is the base change of a
  morphism over a later stage.

## References

* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

section LimitDescent

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ BigAffineFppf B integerBase hZ} (c : Cone D)
  (hc : IsLimit ((BigAffineFppf.toScheme B integerBase hZ).mapCone c))

include hc in
/-- **Descent of a family of curves along an affine cofiltered limit** (Stacks 0D55): a family of
curves over the vertex of a cofiltered system of affine schemes of the site, whose underlying
schemes form a limit, is the base change of a family of curves over one of the stages. -/
theorem exists_hom_to_stage_of_isLimit (G : CurveFamily B hZ)
    (hG : G.base = (BigAffineFppf.inclusion B integerBase hZ).obj c.pt) :
    ∃ (i : I) (Gi : CurveFamily B hZ)
      (hGi : Gi.base = (BigAffineFppf.inclusion B integerBase hZ).obj (D.obj i))
      (δ : G ⟶ Gi), δ.baseMap = eqToHom hG ≫
        (BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i) ≫ eqToHom hGi.symm := by
  have hlim := C1590Private.isLimitPreserving_curvesFiberedCategory B hZ
  let : (curvesFiberedCategory B hZ).val.p.IsFibered :=
    (curvesFiberedCategory B hZ).2.isFibered
  have := hlim I D c hc
  obtain ⟨i, ⟨Gi, hGi⟩, δ, hδ⟩ := Deformation.Artin.descentObj_of_essSurj
    (curvesFiberedCategory B hZ).val.p (D ⋙ BigAffineFppf.inclusion B integerBase hZ)
    ((BigAffineFppf.inclusion B integerBase hZ).mapCone c) ⟨G, hG⟩
  have hδ' : (curvesProjectionOver B hZ).IsHomLift
      ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) δ := hδ
  exact ⟨i, Gi, hGi, δ, IsHomLift.fac' (curvesProjectionOver B hZ)
    ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) δ⟩

/-- The comparison of two base changes of `F.ofBaseEq e` through a factorization of the base maps,
on the presheaf descriptions of the total spaces. -/
private theorem exists_hom_pullback_totalIso_of_comp (F : CurveFamily B hZ)
    {U W V : BigFppfOver B integerBase hZ} (e : F.base = V) {p : U ⟶ W} {q : W ⟶ V} {r : U ⟶ V}
    (hpq : p ≫ q = r) :
    ∃ ε : (F.ofBaseEq e).pullback r ⟶ (F.ofBaseEq e).pullback q, ε.baseMap = p ∧
      ε ≫ (F.ofBaseEq e).pullbackHom q = (F.ofBaseEq e).pullbackHom r ∧
      ε.totalMap.hom ≫ (F.pullbackTotalIsoOfEq e q).hom =
        (F.pullbackTotalIsoOfEq e r).hom ≫ pullbackBaseRestrict (F.toBaseYonedaOfEq e) hpq := by
  obtain ⟨ε, hε, hεc⟩ := (F.ofBaseEq e).exists_hom_pullback_of_comp _ _ _ hpq
  refine ⟨ε, hε, hεc, Limits.pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, F.pullbackTotalIsoOfEq_hom_fst, totalMap_toBaseYoneda, Category.assoc,
      pullbackBaseRestrict_fst, ← Category.assoc, F.pullbackTotalIsoOfEq_hom_fst, hε]
  · have hc' := congrArg (fun t => t.totalMap.hom) hεc
    simp only [comp_totalMap, ObjectProperty.FullSubcategory.comp_hom] at hc'
    rw [Category.assoc, F.pullbackTotalIsoOfEq_hom_snd, hc', Category.assoc,
      pullbackBaseRestrict_snd, F.pullbackTotalIsoOfEq_hom_snd]

include hc in
/-- **Descent of a morphism of total spaces of families of curves along an affine cofiltered
limit** (the fullness half of Stacks 07SK). Let `Fᵢ`, `Gᵢ` be families of curves over a stage
`Tᵢ` of a cofiltered system of affine schemes with limit `T` (their bases identified with `Tᵢ` by
`hFi`, `hGi`), and let `h` be a morphism over `T` between the total spaces of their base changes
to `T`. Then `h` is the base change of a morphism over a later stage `T_k` between the total
spaces of the base changes of `Fᵢ`, `Gᵢ` to `T_k`; the comparison morphisms `εF`, `εG` from the
base changes to `T` to those to `T_k` are compatible with the morphisms to `Fᵢ`, `Gᵢ`. -/
theorem exists_stage_totalMap_of_isLimit (i : I) (Fi Gi : CurveFamily B hZ)
    (hFi : Fi.base = (BigAffineFppf.inclusion B integerBase hZ).obj (D.obj i))
    (hGi : Gi.base = (BigAffineFppf.inclusion B integerBase hZ).obj (D.obj i))
    (h : ((Fi.ofBaseEq hFi).pullback
        ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i))).total ⟶
      ((Gi.ofBaseEq hGi).pullback
        ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i))).total)
    (hh : h ≫ ((Gi.ofBaseEq hGi).pullback
        ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i))).toBase =
      ((Fi.ofBaseEq hFi).pullback
        ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i))).toBase) :
    ∃ (k : I) (s : k ⟶ i)
      (hk : ((Fi.ofBaseEq hFi).pullback
          ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s))).total ⟶
        ((Gi.ofBaseEq hGi).pullback
          ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s))).total)
      (εF : (Fi.ofBaseEq hFi).pullback
          ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) ⟶
        (Fi.ofBaseEq hFi).pullback ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s)))
      (εG : (Gi.ofBaseEq hGi).pullback
          ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) ⟶
        (Gi.ofBaseEq hGi).pullback ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s))),
      hk ≫ ((Gi.ofBaseEq hGi).pullback
          ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s))).toBase =
        ((Fi.ofBaseEq hFi).pullback
          ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s))).toBase ∧
      εF.baseMap = (BigAffineFppf.inclusion B integerBase hZ).map (c.π.app k) ∧
      εG.baseMap = (BigAffineFppf.inclusion B integerBase hZ).map (c.π.app k) ∧
      εF ≫ (Fi.ofBaseEq hFi).pullbackHom
          ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s)) =
        (Fi.ofBaseEq hFi).pullbackHom
          ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) ∧
      εG ≫ (Gi.ofBaseEq hGi).pullbackHom
          ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s)) =
        (Gi.ofBaseEq hGi).pullbackHom
          ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) ∧
      εF.totalMap ≫ hk = h ≫ εG.totalMap := by
  set ι := BigAffineFppf.inclusion B integerBase hZ
  set eF := Fi.pullbackTotalIsoOfEq hFi (ι.map (c.π.app i))
  set eG := Gi.pullbackTotalIsoOfEq hGi (ι.map (c.π.app i))
  have hh' : h.hom ≫ ((Gi.ofBaseEq hGi).pullback (ι.map (c.π.app i))).toBaseYoneda =
      ((Fi.ofBaseEq hFi).pullback (ι.map (c.π.app i))).toBaseYoneda :=
    congrArg (fun t => t.hom) hh
  have hu : (eF.inv ≫ h.hom ≫ eG.hom) ≫
        Limits.pullback.fst (yoneda.map (ι.map (c.π.app i))) (Gi.toBaseYonedaOfEq hGi) =
      Limits.pullback.fst (yoneda.map (ι.map (c.π.app i))) (Fi.toBaseYonedaOfEq hFi) := by
    rw [Category.assoc, Category.assoc, Gi.pullbackTotalIsoOfEq_hom_fst, hh', Iso.inv_comp_eq,
      Fi.pullbackTotalIsoOfEq_hom_fst]
  obtain ⟨k, s, v, hv, hcomp⟩ := properFlatMorphismDescendsAlongAffineLimit B integerBase hZ
    I D c hc i Fi.total.obj Gi.total.obj Fi.total.property Gi.total.property
    (Fi.toBaseYonedaOfEq hFi) (Gi.toBaseYonedaOfEq hGi)
    (Fi.ofBaseEq hFi).finitePresentation (Fi.ofBaseEq hFi).flat (Fi.ofBaseEq hFi).proper
    (Gi.ofBaseEq hGi).finitePresentation (Gi.ofBaseEq hGi).flat (Gi.ofBaseEq hGi).proper
    (eF.inv ≫ h.hom ≫ eG.hom) hu
  set eFk := Fi.pullbackTotalIsoOfEq hFi (ι.map (D.map s))
  set eGk := Gi.pullbackTotalIsoOfEq hGi (ι.map (D.map s))
  let hk : ((Fi.ofBaseEq hFi).pullback (ι.map (D.map s))).total ⟶
      ((Gi.ofBaseEq hGi).pullback (ι.map (D.map s))).total :=
    ObjectProperty.homMk (eFk.hom ≫ v ≫ eGk.inv)
  have hk_hom : hk.hom = eFk.hom ≫ v ≫ eGk.inv := rfl
  have hw : ι.map (c.π.app k) ≫ ι.map (D.map s) = ι.map (c.π.app i) := by
    rw [← Functor.map_comp, c.w s]
  obtain ⟨εF, hεF, hεFc, keyF⟩ := Fi.exists_hom_pullback_totalIso_of_comp hFi hw
  obtain ⟨εG, hεG, hεGc, keyG⟩ := Gi.exists_hom_pullback_totalIso_of_comp hGi hw
  refine ⟨k, s, hk, εF, εG, ?_, hεF, hεG, hεFc, hεGc, ?_⟩
  · apply ObjectProperty.hom_ext
    show hk.hom ≫ ((Gi.ofBaseEq hGi).pullback (ι.map (D.map s))).toBaseYoneda =
      ((Fi.ofBaseEq hFi).pullback (ι.map (D.map s))).toBaseYoneda
    rw [hk_hom, Category.assoc, Category.assoc,
      ← Gi.pullbackTotalIsoOfEq_hom_fst hGi (ι.map (D.map s)), Iso.inv_hom_id_assoc, hv,
      Fi.pullbackTotalIsoOfEq_hom_fst]
  · apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom, hk_hom,
      ← Iso.cancel_iso_hom_right _ _ eGk]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    unfold coneBaseRestrict at hcomp
    rw [reassoc_of% keyF, hcomp, keyG]
    simp only [eF, eG, Category.assoc, Iso.hom_inv_id_assoc]

end LimitDescent

end CurveFamily

end AlgebraicGeometry

end
