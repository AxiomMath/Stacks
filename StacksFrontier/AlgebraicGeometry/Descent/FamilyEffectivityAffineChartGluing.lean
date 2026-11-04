module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityOverAffineOpens
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityRestrictionTransport
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeGluingOverBasis

/-!
# Gluing the charts of a descent datum over the affine opens of the base

Let `𝒰 = {X i ⟶ S}` be a covering family of a scheme `S` for the fpqc topology and let `D` be a
descent datum relative to `𝒰` whose restriction to every affine open `U` of `S` is effective.
The restricted datum then carries a chart: a scheme over `U` exhibiting every component of the
restricted datum as its base change.

Choosing one such chart for every affine open of `S`, the chosen schemes over the affine opens
form a gluing datum in the sense of
[Stacks, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH): the comparison morphism attached
to an inclusion `V ≤ U` of affine opens exhibits the scheme over `V` as the part of the scheme
over `U` lying over `V`, and these comparison morphisms compose *strictly*. Hence the chosen
schemes glue to a single scheme over `S`.

## Main definitions

* `AlgebraicGeometry.DescentData.restrictBaseObjMap`: the canonical map from a component of the
  datum restricted to `V` to the corresponding component of the datum restricted to `U`, for
  `V ≤ U` opens of the base.
* `AlgebraicGeometry.DescentData.affineChart`: the chart of the datum restricted to an affine
  open of the base, chosen once and for all.
* `AlgebraicGeometry.DescentData.res`: the comparison morphism of the chosen charts over two
  nested affine opens of the base.
* `AlgebraicGeometry.DescentData.basisGluingData`: the resulting gluing datum over the affine
  opens of the base.

## Main results

* `AlgebraicGeometry.DescentData.restrictBaseObjMap_trans`: the canonical maps between the
  components of the restricted data compose strictly.
* `AlgebraicGeometry.DescentData.proj_comp_res`: the comparison morphism of the chosen charts,
  read on the projections of the charts, is the canonical map between the components.
* `AlgebraicGeometry.DescentData.res_trans`: the comparison morphisms of the chosen charts
  compose strictly.
* `AlgebraicGeometry.DescentData.exists_glued_chart`: the schemes charting the restricted data
  over the affine opens of the base glue to a scheme over `S` whose part over each affine open is
  the corresponding chosen scheme.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits MorphismOfSchemeFamilies

namespace DescentData

variable {S : Scheme.{u}}

/-- The canonical map from a component of the datum restricted to `V` to the corresponding
component of the datum restricted to `U`, for `V ≤ U` opens of the base. -/
def restrictBaseObjMap (𝒰 : PreZeroHypercover.{u} S) (D : DescentData 𝒰.f) {V U : S.Opens}
    (h : V ≤ U) (i : 𝒰.I₀) :
    pullback (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ V).ι) ⟶
      pullback (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) :=
  pullback.map _ _ _ _ (𝟙 _) ((𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h)) (𝟙 _)
    (Category.comp_id _ |>.trans (Category.id_comp _).symm)
    (by rw [Category.comp_id, Scheme.homOfLE_ι])

/-- The map `restrictBaseObjMap` commutes with the first projections to the component of the
datum. -/
@[reassoc (attr := simp)]
lemma restrictBaseObjMap_fst (𝒰 : PreZeroHypercover.{u} S) (D : DescentData 𝒰.f)
    {V U : S.Opens} (h : V ≤ U) (i : 𝒰.I₀) :
    restrictBaseObjMap 𝒰 D h i ≫ pullback.fst (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) =
      pullback.fst (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ V).ι) := by
  rw [restrictBaseObjMap, pullback.lift_fst, Category.comp_id]

/-- The map `restrictBaseObjMap` is compatible, along the second projections, with the inclusion
of the preimage of `V` into the preimage of `U`. -/
@[reassoc (attr := simp)]
lemma restrictBaseObjMap_snd (𝒰 : PreZeroHypercover.{u} S) (D : DescentData 𝒰.f)
    {V U : S.Opens} (h : V ≤ U) (i : 𝒰.I₀) :
    restrictBaseObjMap 𝒰 D h i ≫ pullback.snd (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) =
      pullback.snd (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ V).ι) ≫
        (𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h) :=
  pullback.lift_snd _ _ _

/-- The canonical maps between the components of the restricted data compose strictly. -/
lemma restrictBaseObjMap_trans (𝒰 : PreZeroHypercover.{u} S) (D : DescentData 𝒰.f)
    {W V U : S.Opens} (hWV : W ≤ V) (hVU : V ≤ U) (i : 𝒰.I₀) :
    restrictBaseObjMap 𝒰 D (hWV.trans hVU) i =
      restrictBaseObjMap 𝒰 D hWV i ≫ restrictBaseObjMap 𝒰 D hVU i := by
  refine pullback.hom_ext ?_ ?_
  · rw [restrictBaseObjMap_fst, Category.assoc, restrictBaseObjMap_fst, restrictBaseObjMap_fst]
  · rw [restrictBaseObjMap_snd, Category.assoc, restrictBaseObjMap_snd,
      restrictBaseObjMap_snd_assoc, Scheme.homOfLE_homOfLE]

section Chosen

attribute [local implicit_reducible] MorphismOfSchemeFamilies.ofRestrictBase
  MorphismOfSchemeFamilies.pulledBackDatum

variable {𝒰 : PreZeroHypercover.{u} S}
  (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) (D : DescentData 𝒰.f)
  (hD : ∀ U : S.affineOpens, ((MorphismOfSchemeFamilies.pullbackFunctor
    (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U.1)).functor.obj D).IsFamilyEffective)

/-- A chart of the datum restricted to an affine open of the base, chosen once and for all. -/
def affineChart (U : S.affineOpens) : (pulledBackDatum (ofRestrictBase 𝒰 U.1) D).Chart :=
  (nonempty_chart_of_isFamilyEffective _ (hD U)).some

include h𝒰 in
/-- The comparison morphism of the chosen charts over two nested affine opens of the base
exists. -/
lemma exists_res {V U : S.affineOpens} (h : V.1 ≤ U.1) :
    ∃ r : (affineChart D hD V).base.left ⟶ (affineChart D hD U).base.left,
      IsPullback r (affineChart D hD V).base.hom (affineChart D hD U).base.hom
          (S.homOfLE h) ∧
        ∀ i, (affineChart D hD V).proj i ≫ r =
          restrictBaseObjMap 𝒰 D h i ≫ (affineChart D hD U).proj i := by
  obtain ⟨r, hr, hrproj⟩ := exists_isPullback_restrictBase 𝒰 D h (affineChart D hD U)
    (fun i ↦ ((𝒰.f i) ⁻¹ᵁ V.1).ι) (fun i ↦ (morphismRestrict_ι (𝒰.f i) V.1).symm)
    (funext fun i ↦ (Scheme.homOfLE_ι (𝒰.X i) ((𝒰.f i).preimage_mono h)).symm)
    (PreZeroHypercover.mem_fpqcPrecoverage_restrictBase 𝒰 V.1 h𝒰) (affineChart D hD V)
  exact ⟨r, hr, fun i ↦ hrproj i (restrictBaseObjMap 𝒰 D h i)
    (restrictBaseObjMap_fst 𝒰 D h i) (restrictBaseObjMap_snd 𝒰 D h i)⟩

/-- The comparison morphism of the chosen charts over two nested affine opens of the base. -/
def res {V U : S.affineOpens} (h : V.1 ≤ U.1) :
    (affineChart D hD V).base.left ⟶ (affineChart D hD U).base.left :=
  (exists_res h𝒰 D hD h).choose

/-- The square formed by `res`, the structure morphisms of the two charts and the inclusion
`V ⟶ U` of the base is a pullback. -/
lemma isPullback_res {V U : S.affineOpens} (h : V.1 ≤ U.1) :
    IsPullback (res h𝒰 D hD h) (affineChart D hD V).base.hom
      (affineChart D hD U).base.hom (S.homOfLE h) :=
  (exists_res h𝒰 D hD h).choose_spec.1

/-- The comparison morphism `res` is compatible with the projections of the charts and with
`restrictBaseObjMap`. -/
@[reassoc]
lemma proj_comp_res {V U : S.affineOpens} (h : V.1 ≤ U.1) (i : 𝒰.I₀) :
    (affineChart D hD V).proj i ≫ res h𝒰 D hD h =
      restrictBaseObjMap 𝒰 D h i ≫ (affineChart D hD U).proj i :=
  (exists_res h𝒰 D hD h).choose_spec.2 i

/-- The comparison morphisms of the chosen charts compose strictly. -/
lemma res_trans {W V U : S.affineOpens} (hWV : W.1 ≤ V.1) (hVU : V.1 ≤ U.1) :
    res h𝒰 D hD (hWV.trans hVU) = res h𝒰 D hD hWV ≫ res h𝒰 D hD hVU := by
  have hc₁ : res h𝒰 D hD (hWV.trans hVU) ≫ (affineChart D hD U).base.hom =
      (affineChart D hD W).base.hom ≫ S.homOfLE (hWV.trans hVU) :=
    (isPullback_res h𝒰 D hD (hWV.trans hVU)).w
  have hc₂ : (res h𝒰 D hD hWV ≫ res h𝒰 D hD hVU) ≫ (affineChart D hD U).base.hom =
      (affineChart D hD W).base.hom ≫ S.homOfLE (hWV.trans hVU) := by
    rw [Category.assoc, (isPullback_res h𝒰 D hD hVU).w, ← Category.assoc,
      (isPullback_res h𝒰 D hD hWV).w, Category.assoc, Scheme.homOfLE_homOfLE]
  have key : (Over.homMk (pullback.lift (res h𝒰 D hD (hWV.trans hVU))
          (affineChart D hD W).base.hom hc₁) (pullback.lift_snd _ _ _) :
        (affineChart D hD W).base ⟶
          (Over.pullback (S.homOfLE (hWV.trans hVU))).obj (affineChart D hD U).base) =
      Over.homMk (pullback.lift (res h𝒰 D hD hWV ≫ res h𝒰 D hD hVU)
        (affineChart D hD W).base.hom hc₂) (pullback.lift_snd _ _ _) := by
    refine Chart.hom_ext_of_proj_comp_eq_of_fpqc
      (PreZeroHypercover.mem_fpqcPrecoverage_restrictBase 𝒰 W.1 h𝒰)
      (affineChart D hD W) fun i ↦ ?_
    simp only [Over.homMk_left]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst]
      exact (proj_comp_res h𝒰 D hD (hWV.trans hVU) i).trans <|
        (eq_whisker (restrictBaseObjMap_trans 𝒰 D hWV hVU i) _).trans <|
          (Category.assoc _ _ _).trans <| (whisker_eq _ (proj_comp_res h𝒰 D hD hVU i).symm).trans
            (proj_comp_res_assoc h𝒰 D hD hWV i _).symm
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd]
  simpa only [Over.homMk_left, pullback.lift_fst] using congrArg (fun x ↦ Over.Hom.left x ≫
    pullback.fst (affineChart D hD U).base.hom (S.homOfLE (hWV.trans hVU))) key

/-- The gluing datum over the affine opens of the base formed by the chosen charts. -/
def basisGluingData : Scheme.BasisGluingData S S.affineOpens where
  obj U := (affineChart D hD U).base.left
  proj U := (affineChart D hD U).base.hom
  res h := res h𝒰 D hD h
  isPullback_res h := isPullback_res h𝒰 D hD h
  res_trans hWV hVU := res_trans h𝒰 D hD hWV hVU

/-- The schemes charting the restricted data over the affine opens of the base glue: the glued
scheme over the base receives a morphism from each of them, identifying it with the part lying
over the corresponding affine open, compatibly with the comparison morphisms. -/
lemma exists_glued_chart :
    ∃ (X : Scheme.{u}) (p : X ⟶ S)
      (c : ∀ U : S.affineOpens, (affineChart D hD U).base.left ⟶ X),
      (∀ U : S.affineOpens,
          IsPullback (affineChart D hD U).base.hom (c U) U.1.ι p) ∧
        ∀ {V U : S.affineOpens} (h : V.1 ≤ U.1), res h𝒰 D hD h ≫ c U = c V :=
  Scheme.BasisGluingData.exists_isPullback_res_comp (Scheme.isBasis_affineOpens S)
    (basisGluingData h𝒰 D hD)

end Chosen

end DescentData

end AlgebraicGeometry

end

end
