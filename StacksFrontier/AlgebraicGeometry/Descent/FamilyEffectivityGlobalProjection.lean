module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityAffineChartGluing
public import StacksFrontier.AlgebraicGeometry.Scheme.AffinePreimageGluing

/-!
# The projection of a descent datum onto the glued scheme over the base

Let `𝒰 = {X i ⟶ S}` be a covering family of a scheme `S` for the fpqc topology and let `D` be a
descent datum relative to `𝒰` whose restriction to every affine open of `S` is effective. The
schemes charting the restricted data over the affine opens of `S` glue to a scheme `X` over `S`
(`AlgebraicGeometry.DescentData.exists_glued_chart`), which receives a chart from each of them.
This file produces the projection of each component of `D` onto `X`.

The component at `i` of the datum restricted to an open `U` of the base is the part of the `i`-th
component of `D` lying over `U`: both are the preimage of `U` in `V i`, taken in two steps in one
case and in one step in the other. Under that identification the projections of the chosen charts
become morphisms `((V i ⟶ X i ⟶ S)⁻¹(U)) ⟶ X`, one for each affine open `U` of `S`, compatible
with the inclusions between those preimages; since the preimages of the affine opens of `S` cover
`V i` and are directed, they assemble into a single morphism `V i ⟶ X`.

## Main definitions

* `AlgebraicGeometry.DescentData.restrictBaseObjIso`: the identification of the component at `i`
  of the datum restricted to `U` with the part of the `i`-th component of the datum lying over
  `U`.
* `AlgebraicGeometry.DescentData.globalProj`: the projection of the `i`-th component of the datum
  onto the glued scheme.

## Main results

* `AlgebraicGeometry.DescentData.homOfLE_comp_restrictBaseObjIso`: the identifications carry the
  inclusions between the parts lying over the opens of the base to the canonical maps
  `AlgebraicGeometry.DescentData.restrictBaseObjMap` between the components of the restricted
  data.
* `AlgebraicGeometry.DescentData.ι_globalProj`: the projection restricted to the part lying over
  an affine open of the base is the projection of the chosen chart there, followed by that chart's
  inclusion into the glued scheme.

## References

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

section Preimage

attribute [local implicit_reducible] MorphismOfSchemeFamilies.ofRestrictBase
  MorphismOfSchemeFamilies.pulledBackDatum

/-- The identification of the component at `i` of the datum restricted to an open `U` of the
base with the part of the `i`-th component of the datum lying over `U`. -/
def restrictBaseObjIso (𝒰 : PreZeroHypercover.{u} S) (D : DescentData 𝒰.f) (U : S.Opens)
    (i : 𝒰.I₀) :
    ((((D.obj i).hom ≫ 𝒰.f i) ⁻¹ᵁ U).toScheme) ≅
      pullback (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) :=
  Scheme.preimageIsoPullback (D.obj i).hom ((𝒰.f i) ⁻¹ᵁ U)

/-- The identification `restrictBaseObjIso` followed by the first projection of the pullback is
the inclusion of the part of the `i`-th component lying over `U`. -/
@[reassoc]
lemma restrictBaseObjIso_hom_fst (𝒰 : PreZeroHypercover.{u} S) (D : DescentData 𝒰.f)
    (U : S.Opens) (i : 𝒰.I₀) :
    (restrictBaseObjIso 𝒰 D U i).hom ≫ pullback.fst (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) =
      ((((D.obj i).hom ≫ 𝒰.f i) ⁻¹ᵁ U).ι) :=
  Scheme.preimageIsoPullback_hom_fst (D.obj i).hom ((𝒰.f i) ⁻¹ᵁ U)

/-- The identification `restrictBaseObjIso` followed by the second projection of the pullback is
the restriction of the structure morphism of the `i`-th component to the preimage of `U`. -/
@[reassoc]
lemma restrictBaseObjIso_hom_snd (𝒰 : PreZeroHypercover.{u} S) (D : DescentData 𝒰.f)
    (U : S.Opens) (i : 𝒰.I₀) :
    (restrictBaseObjIso 𝒰 D U i).hom ≫ pullback.snd (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) =
      (D.obj i).hom ∣_ ((𝒰.f i) ⁻¹ᵁ U) :=
  (isPullback_morphismRestrict (D.obj i).hom ((𝒰.f i) ⁻¹ᵁ U)).flip.isoPullback_hom_snd

/-- The identification of the components with the parts of the datum lying over the opens of the
base carries the inclusions of those parts to the canonical maps between the components. -/
lemma homOfLE_comp_restrictBaseObjIso (𝒰 : PreZeroHypercover.{u} S) (D : DescentData 𝒰.f)
    {V U : S.Opens} (h : V ≤ U) (i : 𝒰.I₀) :
    (D.obj i).left.homOfLE (((D.obj i).hom ≫ 𝒰.f i).preimage_mono h) ≫
        (restrictBaseObjIso 𝒰 D U i).hom =
      (restrictBaseObjIso 𝒰 D V i).hom ≫ restrictBaseObjMap 𝒰 D h i := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, restrictBaseObjIso_hom_fst, Scheme.homOfLE_ι, Category.assoc,
      restrictBaseObjMap_fst, restrictBaseObjIso_hom_fst]
  · rw [Category.assoc, restrictBaseObjIso_hom_snd, Category.assoc, restrictBaseObjMap_snd,
      restrictBaseObjIso_hom_snd_assoc]
    exact (morphismRestrict_homOfLE (D.obj i).hom ((𝒰.f i) ⁻¹ᵁ V) ((𝒰.f i) ⁻¹ᵁ U)
      ((𝒰.f i).preimage_mono h)).symm

end Preimage

section Global

attribute [local implicit_reducible] MorphismOfSchemeFamilies.ofRestrictBase
  MorphismOfSchemeFamilies.pulledBackDatum

variable {𝒰 : PreZeroHypercover.{u} S}
  (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) (D : DescentData 𝒰.f)
  (hD : ∀ U : S.affineOpens, ((MorphismOfSchemeFamilies.pullbackFunctor
    (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U.1)).functor.obj D).IsFamilyEffective)
  {X : Scheme.{u}}
  (c : ∀ U : S.affineOpens, (affineChart D hD U).base.left ⟶ X)
  (hcres : ∀ {V U : S.affineOpens} (h : V.1 ≤ U.1), res h𝒰 D hD h ≫ c U = c V)

/-- The projection of the `i`-th component of the datum onto the glued scheme, assembled from
the projections of the chosen charts over the affine opens of the base. -/
def globalProj (i : 𝒰.I₀) : (D.obj i).left ⟶ X :=
  Scheme.glueOverAffinePreimages ((D.obj i).hom ≫ 𝒰.f i)
    (fun U ↦ (restrictBaseObjIso 𝒰 D U.1 i).hom ≫ (affineChart D hD U).proj i ≫ c U)
    (fun U V hUV ↦ by
      rw [← Category.assoc, homOfLE_comp_restrictBaseObjIso 𝒰 D hUV i, Category.assoc]
      exact whisker_eq _ ((proj_comp_res_assoc h𝒰 D hD hUV i (c V)).symm.trans
        (whisker_eq _ (hcres hUV))))

/-- The restriction of `globalProj` to the part of the `i`-th component lying over an affine open
`U` of the base is the projection of the chosen chart over `U` followed by `c U`. -/
@[reassoc]
lemma ι_globalProj (U : S.affineOpens) (i : 𝒰.I₀) :
    ((((D.obj i).hom ≫ 𝒰.f i) ⁻¹ᵁ U.1).ι) ≫ globalProj h𝒰 D hD c hcres i =
      (restrictBaseObjIso 𝒰 D U.1 i).hom ≫ (affineChart D hD U).proj i ≫ c U :=
  Scheme.ι_glueOverAffinePreimages _ _ _ U

end Global

end DescentData

end AlgebraicGeometry

end

end
