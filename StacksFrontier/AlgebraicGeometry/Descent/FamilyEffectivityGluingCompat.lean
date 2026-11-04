module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityGlobalPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The gluing isomorphisms preserve the projection onto the glued scheme

Let `𝒰 = {X i ⟶ S}` be a covering family of a scheme `S` for the fpqc topology and let `D` be a
descent datum relative to `𝒰` whose restriction to every affine open of `S` is effective. The
projections `AlgebraicGeometry.DescentData.globalProj` of the components of `D` onto the glued
scheme are compatible with the gluing isomorphisms of `D`.

The source of the gluing isomorphism of `D` at `(i, j)` is the fibre product `V i ×_S X j`. The
source of the gluing isomorphism of the datum restricted to an open `U` of the base is
`(V i)|_U ×_U (X j)|_U`, and the comparison map
`AlgebraicGeometry.MorphismOfSchemeFamilies.pulledBackDatumSourceMap` between them exhibits the
latter as the part of the former lying over `U`. As `U` runs over the affine opens of `S` these
parts cover `V i ×_S X j`.

## Main definitions

* `AlgebraicGeometry.DescentData.srcMapRestrictBase` and
  `AlgebraicGeometry.DescentData.tgtMapRestrictBase`: the comparison maps on the sources and the
  targets of the gluing isomorphisms of a datum restricted to an open of the base, with the
  fibre products spelled out.
* `AlgebraicGeometry.DescentData.gluingSourceCover`: the open cover of the source of a gluing
  isomorphism by the sources of the gluing isomorphisms of the restricted data.

## Main results

* `AlgebraicGeometry.isPullback_pullback_lift`: the fibre product of two base changes along a
  morphism is the base change of the fibre product.
* `AlgebraicGeometry.DescentData.isPullback_sourceMap_restrictBase`: the source of the gluing
  isomorphism of the datum restricted to an open `U` of the base is the part lying over `U` of
  the source of the gluing isomorphism of the datum.
* `AlgebraicGeometry.DescentData.compat_globalProj`: the gluing isomorphisms of the datum
  preserve the projection onto the glued scheme.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace MorphismOfSchemeFamilies

/-- The fibre product of two base changes along a morphism is the base change of the fibre
product: a morphism `m` of fibre products whose two projections are the given base changes `a` and
`b` is a base change of `i₃`. -/
@[ega "I 3.3.10"]
lemma isPullback_pullback_lift {A A' B B' S' T' : Scheme.{u}} {f₁ : A' ⟶ S'} {f₂ : B' ⟶ S'}
    {g₁ : A ⟶ T'} {g₂ : B ⟶ T'} {a : A' ⟶ A} {b : B' ⟶ B} {i₃ : S' ⟶ T'}
    (ha : IsPullback a f₁ g₁ i₃) (hb : IsPullback b f₂ g₂ i₃)
    (m : pullback f₁ f₂ ⟶ pullback g₁ g₂)
    (hm₁ : m ≫ pullback.fst g₁ g₂ = pullback.fst f₁ f₂ ≫ a)
    (hm₂ : m ≫ pullback.snd g₁ g₂ = pullback.snd f₁ f₂ ≫ b) :
    IsPullback m (pullback.fst f₁ f₂ ≫ f₁) (pullback.fst g₁ g₂ ≫ g₁) i₃ := by
  have s : IsPullback (m ≫ pullback.snd g₁ g₂) (pullback.fst f₁ f₂) g₂ (a ≫ g₁) := by
    rw [hm₂, ha.w]
    exact ((IsPullback.of_hasPullback f₁ f₂).flip).paste_horiz hb
  exact (IsPullback.of_right s hm₁ ((IsPullback.of_hasPullback g₁ g₂).flip)).paste_vert ha

namespace MorphismOfSchemeFamilies

end MorphismOfSchemeFamilies

namespace DescentData

variable {S : Scheme.{u}}

section SourceMap

attribute [local implicit_reducible] MorphismOfSchemeFamilies.ofRestrictBase
  MorphismOfSchemeFamilies.pulledBackDatum

variable (𝒰 : PreZeroHypercover.{u} S) (D : DescentData 𝒰.f)

/-- The comparison map on the sources of the gluing isomorphisms of the datum restricted to an
open of the base, with the two fibre products spelled out. -/
abbrev srcMapRestrictBase (U : S.Opens) (i j : 𝒰.I₀) :
    pullback (((pulledBackDatum (ofRestrictBase 𝒰 U) D).obj i).hom ≫
        (PreZeroHypercover.restrictBase 𝒰 U).f i)
        ((PreZeroHypercover.restrictBase 𝒰 U).f j) ⟶
      pullback ((D.obj i).hom ≫ 𝒰.f i) (𝒰.f j) :=
  pulledBackDatumSourceMap (ofRestrictBase 𝒰 U) D i j

/-- The comparison map on the targets of the gluing isomorphisms of the datum restricted to an
open of the base, with the two fibre products spelled out. -/
abbrev tgtMapRestrictBase (U : S.Opens) (i j : 𝒰.I₀) :
    pullback ((PreZeroHypercover.restrictBase 𝒰 U).f i)
        (((pulledBackDatum (ofRestrictBase 𝒰 U) D).obj j).hom ≫
          (PreZeroHypercover.restrictBase 𝒰 U).f j) ⟶
      pullback (𝒰.f i) ((D.obj j).hom ≫ 𝒰.f j) :=
  pulledBackDatumTargetMap (ofRestrictBase 𝒰 U) D i j

/-- The comparison map on the sources of the gluing isomorphisms of the datum restricted to an
open of the base, projected to the component of the datum. -/
@[reassoc]
lemma sourceMap_restrictBase_comp_fst (U : S.Opens) (i j : 𝒰.I₀) :
    srcMapRestrictBase 𝒰 D U i j ≫
        pullback.fst ((D.obj i).hom ≫ 𝒰.f i) (𝒰.f j) =
      pullback.fst (((pulledBackDatum (ofRestrictBase 𝒰 U) D).obj i).hom ≫
          (PreZeroHypercover.restrictBase 𝒰 U).f i)
          ((PreZeroHypercover.restrictBase 𝒰 U).f j) ≫
        pullback.fst (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) := by
  exact pulledBackDatumSourceMap_comp_fst (ofRestrictBase 𝒰 U) D i j

/-- The comparison map on the sources of the gluing isomorphisms of the datum restricted to an
open of the base, projected to the member of the family. -/
lemma sourceMap_restrictBase_comp_snd (U : S.Opens) (i j : 𝒰.I₀) :
    srcMapRestrictBase 𝒰 D U i j ≫
        pullback.snd ((D.obj i).hom ≫ 𝒰.f i) (𝒰.f j) =
      pullback.snd (((pulledBackDatum (ofRestrictBase 𝒰 U) D).obj i).hom ≫
          (PreZeroHypercover.restrictBase 𝒰 U).f i)
          ((PreZeroHypercover.restrictBase 𝒰 U).f j) ≫ (((𝒰.f j) ⁻¹ᵁ U).ι) :=
  pulledBackDatumSourceMap_comp_snd (ofRestrictBase 𝒰 U) D i j

/-- The comparison map on the targets of the gluing isomorphisms of the datum restricted to an
open of the base, projected to the component of the datum. -/
@[reassoc]
lemma targetMap_restrictBase_comp_snd (U : S.Opens) (i j : 𝒰.I₀) :
    tgtMapRestrictBase 𝒰 D U i j ≫
        pullback.snd (𝒰.f i) ((D.obj j).hom ≫ 𝒰.f j) =
      pullback.snd ((PreZeroHypercover.restrictBase 𝒰 U).f i)
          (((pulledBackDatum (ofRestrictBase 𝒰 U) D).obj j).hom ≫
            (PreZeroHypercover.restrictBase 𝒰 U).f j) ≫
        pullback.fst (D.obj j).hom (((𝒰.f j) ⁻¹ᵁ U).ι) := by
  exact pulledBackDatumTargetMap_comp_snd (ofRestrictBase 𝒰 U) D i j

/-- The gluing isomorphism of the datum restricted to an open of the base, compared with the
gluing isomorphism of the datum. -/
@[reassoc]
lemma gluing_restrictBase (U : S.Opens) (i j : 𝒰.I₀) :
    ((pulledBackDatum (ofRestrictBase 𝒰 U) D).gluingPullbackIso i j).hom ≫
        tgtMapRestrictBase 𝒰 D U i j =
      srcMapRestrictBase 𝒰 D U i j ≫ (D.gluingPullbackIso i j).hom :=
  pulledBackDatum_gluing (ofRestrictBase 𝒰 U) D i j

/-- **The source of the gluing isomorphism of the datum restricted to an open `U` of the base is
the part lying over `U` of the source of the gluing isomorphism of the datum.** -/
lemma isPullback_sourceMap_restrictBase (U : S.Opens) (i j : 𝒰.I₀) :
    IsPullback (srcMapRestrictBase 𝒰 D U i j)
      (pullback.fst (((pulledBackDatum (ofRestrictBase 𝒰 U) D).obj i).hom ≫
          (PreZeroHypercover.restrictBase 𝒰 U).f i)
          ((PreZeroHypercover.restrictBase 𝒰 U).f j) ≫
        ((pulledBackDatum (ofRestrictBase 𝒰 U) D).obj i).hom ≫
          (PreZeroHypercover.restrictBase 𝒰 U).f i)
      (pullback.fst ((D.obj i).hom ≫ 𝒰.f i) (𝒰.f j) ≫ (D.obj i).hom ≫ 𝒰.f i) U.ι :=
  isPullback_pullback_lift
    ((IsPullback.of_hasPullback (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι)).paste_vert
      (isPullback_morphismRestrict (𝒰.f i) U).flip)
    (isPullback_morphismRestrict (𝒰.f j) U).flip _
    (sourceMap_restrictBase_comp_fst 𝒰 D U i j) (sourceMap_restrictBase_comp_snd 𝒰 D U i j)

end SourceMap

section Step8

attribute [local implicit_reducible] MorphismOfSchemeFamilies.ofRestrictBase
  MorphismOfSchemeFamilies.pulledBackDatum

variable {𝒰 : PreZeroHypercover.{u} S}
  (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) (D : DescentData 𝒰.f)
  (hD : ∀ U : S.affineOpens, ((MorphismOfSchemeFamilies.pullbackFunctor
    (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U.1)).functor.obj D).IsFamilyEffective)
  {X : Scheme.{u}}
  (c : ∀ U : S.affineOpens, (affineChart D hD U).base.left ⟶ X)
  (hcres : ∀ {V U : S.affineOpens} (h : V.1 ≤ U.1), res h𝒰 D hD h ≫ c U = c V)

/-- The open cover of the source of a gluing isomorphism of the datum by the sources of the
gluing isomorphisms of the data restricted to the affine opens of the base. -/
def gluingSourceCover (i j : 𝒰.I₀) :
    (pullback ((D.obj i).hom ≫ 𝒰.f i) (𝒰.f j)).OpenCover where
  I₀ := S.affineOpens
  X U := pullback (((pulledBackDatum (ofRestrictBase 𝒰 U.1) D).obj i).hom ≫
    (PreZeroHypercover.restrictBase 𝒰 U.1).f i) ((PreZeroHypercover.restrictBase 𝒰 U.1).f j)
  f U := srcMapRestrictBase 𝒰 D U.1 i j
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun z ↦ ?_, fun U ↦ ?_⟩
    · obtain ⟨V, hV, hzV, -⟩ := Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S)
        (U := ⊤) (Opens.mem_top ((pullback.fst ((D.obj i).hom ≫ 𝒰.f i) (𝒰.f j) ≫
          (D.obj i).hom ≫ 𝒰.f i) z))
      obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback
        (isPullback_sourceMap_restrictBase 𝒰 D V i j) z ⟨_, hzV⟩ rfl
      exact ⟨⟨V, hV⟩, ⟨w, hw⟩⟩
    · exact MorphismProperty.of_isPullback
        (isPullback_sourceMap_restrictBase 𝒰 D U.1 i j).flip inferInstance

include hcres hD h𝒰 in
/-- **The gluing isomorphisms of the datum preserve the projection onto the glued scheme.** -/
lemma compat_globalProj (i j : 𝒰.I₀) :
    (D.gluingPullbackIso i j).hom ≫
        pullback.snd (𝒰.f i) ((D.obj j).hom ≫ 𝒰.f j) ≫ globalProj h𝒰 D hD c hcres j =
      pullback.fst ((D.obj i).hom ≫ 𝒰.f i) (𝒰.f j) ≫ globalProj h𝒰 D hD c hcres i := by
  refine Scheme.Cover.hom_ext (gluingSourceCover D i j) _ _ fun U ↦ ?_
  have hcompat : ((pulledBackDatum (ofRestrictBase 𝒰 U.1) D).gluingPullbackIso i j).hom ≫
      pullback.snd ((PreZeroHypercover.restrictBase 𝒰 U.1).f i)
          (((pulledBackDatum (ofRestrictBase 𝒰 U.1) D).obj j).hom ≫
            (PreZeroHypercover.restrictBase 𝒰 U.1).f j) ≫
        (affineChart D hD U).proj j =
      pullback.fst (((pulledBackDatum (ofRestrictBase 𝒰 U.1) D).obj i).hom ≫
          (PreZeroHypercover.restrictBase 𝒰 U.1).f i)
          ((PreZeroHypercover.restrictBase 𝒰 U.1).f j) ≫
        (affineChart D hD U).proj i := (affineChart D hD U).compat i j
  have hf : (gluingSourceCover D i j).f U = srcMapRestrictBase 𝒰 D U.1 i j := rfl
  rw [hf]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine ((gluing_restrictBase 𝒰 D U.1 i j).symm =≫ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (_ ≫= (Category.assoc _ _ _).symm).trans ?_
  refine (_ ≫= (targetMap_restrictBase_comp_snd 𝒰 D U.1 i j =≫ _)).trans ?_
  refine (_ ≫= Category.assoc _ _ _).trans ?_
  refine (_ ≫= (_ ≫= fst_comp_globalProj h𝒰 D hD c hcres U j)).trans ?_
  refine (_ ≫= (Category.assoc _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (hcompat =≫ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (_ ≫= (fst_comp_globalProj h𝒰 D hD c hcres U i).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine ((sourceMap_restrictBase_comp_fst 𝒰 D U.1 i j).symm =≫ _).trans ?_
  exact Category.assoc _ _ _

end Step8

end DescentData

end AlgebraicGeometry

end

end
