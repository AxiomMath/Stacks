module

public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace

/-!
# Equalizers in the small étale site and the functor to a category fibred in groupoids

Let `F` be a presheaf on the big fppf site of `S`. Its small étale site has fibre products and
binary products, hence equalizers, and the functor `F_étale ⥤ 𝒳` attached to an equivalence over
the site between a category fibred in groupoids `𝒳` and the category of elements of `F` preserves
both of those shapes: the fibre product of two étale charts is already their product in the
category of all scheme charts of `F`, and the remaining factors of the functor are equivalences.
Consequently, for every object `X` of `𝒳`, the category of étale charts of `F` equipped with a
morphism from `X` has binary products and equalizers, so it is cofiltered as soon as it is
nonempty.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.instHasEqualizers`: the small étale site of `F` has
  equalizers.
* `AlgebraicGeometry.Space.restrictionFunctor_preservesEqualizers`: the functor `F_étale ⥤ 𝒳`
  preserves equalizers.
* `AlgebraicGeometry.Space.restrictionFunctor_isCofilteredOrEmpty`: the comma category of étale
  charts of `F` over an object of `𝒳` is cofiltered or empty.

## References

* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

namespace SmallEtale

/-- The small étale site of a presheaf on the big fppf site of `S` has equalizers: it has fibre
products and binary products, and an equalizer is the fibre product of the two graphs. -/
instance instHasEqualizers : HasEqualizers (SmallEtale B S hS F) :=
  hasEqualizers_of_hasPullbacks_and_binary_products

/-- The two projections of the fibre product of two étale charts of `F` exhibit it as their
product in the category of *all* scheme charts of `F`. The universal property is the same one as
in the small étale site: a product cone over the two charts is a scheme chart together with two
factorizations through them in the big fppf site of `S`, and such a pair is turned into a unique
morphism to the fibre product by the representing base change. -/
noncomputable def prodIsLimitInclusion (X Y : SmallEtale B S hS F) :
    IsLimit (BinaryFan.mk ((inclusion B S hS F).map (prodFst B S hS F X Y))
      ((inclusion B S hS F).map (prodSnd B S hS F X Y))) := by
  refine BinaryFan.isLimitMk (fun s => CostructuredArrow.homMk
    (X.property.rep.lift' (s.fst : s.pt ⟶ X.obj).left (s.snd : s.pt ⟶ Y.obj).left
      ((CostructuredArrow.w (s.fst : s.pt ⟶ X.obj)).trans
        (CostructuredArrow.w (s.snd : s.pt ⟶ Y.obj)).symm)) ?_) ?_ ?_ ?_
  · change yoneda.map _ ≫ yoneda.map (X.property.rep.snd Y.obj.hom) ≫ Y.obj.hom = _
    rw [← Functor.map_comp_assoc, Functor.relativelyRepresentable.lift'_snd]
    exact CostructuredArrow.w (s.snd : s.pt ⟶ Y.obj)
  · exact fun _ =>
      CostructuredArrow.hom_ext _ _ (Functor.relativelyRepresentable.lift'_fst _ _ _ _)
  · exact fun _ =>
      CostructuredArrow.hom_ext _ _ (Functor.relativelyRepresentable.lift'_snd _ _ _ _)
  · intro s m h₁ h₂
    refine CostructuredArrow.hom_ext _ _ (Functor.relativelyRepresentable.hom_ext' _ ?_ ?_)
    · exact (congrArg (fun f : s.pt ⟶ X.obj => f.left) h₁).trans
        (Functor.relativelyRepresentable.lift'_fst _ _ _ _).symm
    · exact (congrArg (fun f : s.pt ⟶ Y.obj => f.left) h₂).trans
        (Functor.relativelyRepresentable.lift'_snd _ _ _ _).symm

/-- The inclusion of the étale charts of `F` into all its scheme charts preserves binary
products, the fibre product of two étale charts being their fibre product as scheme charts. -/
instance instPreservesBinaryProductsInclusion :
    PreservesLimitsOfShape (Discrete WalkingPair) (inclusion B S hS F) := by
  constructor
  intro K
  have : PreservesLimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩))
      (inclusion B S hS F) :=
    preservesLimit_of_preserves_limit_cone (prodIsLimit B S hS F _ _)
      ((isLimitMapConeBinaryFanEquiv _ _ _).symm (prodIsLimitInclusion B S hS F _ _))
  exact preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm

end SmallEtale

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)

/-- The functor `F_étale ⥤ 𝒳` preserves binary products: it is the inclusion of the étale charts
into all scheme charts, which preserves them, followed by two equivalences. -/
instance restrictionFunctor_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (restrictionFunctor B S hS F p e) :=
  letI : e.inv.functor.IsEquivalence := inferInstanceAs e.toEquivalence.inverse.IsEquivalence
  inferInstanceAs (PreservesLimitsOfShape (Discrete WalkingPair)
    (SmallEtale.inclusion B S hS F ⋙
      PresheafOfCategories.costructuredArrowToElements F ⋙ e.inv.functor))

/-- The functor `F_étale ⥤ 𝒳` preserves equalizers: the small étale site has fibre products and
binary products, and the functor preserves both. -/
instance restrictionFunctor_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (restrictionFunctor B S hS F p e) :=
  preservesEqualizers_of_preservesPullbacks_and_binaryProducts _

/-- For an object `X` of `𝒳`, the category of étale charts of `F` equipped with a morphism from
`X` is cofiltered as soon as it is nonempty: it has binary products and equalizers, inherited
from the small étale site because the functor `F_étale ⥤ 𝒳` preserves both shapes. -/
instance restrictionFunctor_isCofilteredOrEmpty (X : 𝒳) :
    IsCofilteredOrEmpty (StructuredArrow X (restrictionFunctor B S hS F p e)) :=
  ⟨fun Y Z => ⟨Y ⨯ Z, prod.fst, prod.snd, trivial⟩,
    fun {_ _} f g => ⟨equalizer f g, equalizer.ι f g, equalizer.condition f g⟩⟩

end AlgebraicGeometry.Space

end
