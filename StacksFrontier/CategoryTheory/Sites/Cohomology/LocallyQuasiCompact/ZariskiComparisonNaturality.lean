module

public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.CategoryTheory.Sites.Localization.OverPullbackMorphism
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationTriangle
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
import StacksCore.Tactic.StacksAttribute

/-!
# Naturality of the Zariski comparison morphism

A morphism `f : X ⟶ Y` of the locally quasi-compact Zariski site induces a morphism of the
slice topoi, `Sh(LC_Zar/X) → Sh(LC_Zar/Y)`, by postcomposition on slices. Part of Stacks 0DCU
is the assertion that this morphism commutes with the comparison morphisms to the ordinary
Zariski topoi of the underlying spaces, i.e. that the square

```
Sh(LC_Zar/X) ---> Sh(X_Zar)
     |                |
     |                |
     v                v
Sh(LC_Zar/Y) ---> Sh(Y_Zar)
```

commutes. Commutativity is recorded as a natural isomorphism of the two composite
inverse-image functors.

The square comes from one isomorphism of site-level functors: taking the open `V ⊆ Y` to
`f^{-1}V ⊆ X` and then to the slice over `X` is the same as taking `V` to the slice over `Y`
and then pulling back along `f`. Both are the open subspace `f^{-1}V` of `X`, which is where
`zariskiOpenPullbackIso` comes from; the key input is `pullback_openEmbedding_range`, which says
that the fibre product of an open immersion `V → Y` along `f` is again an open immersion, with
image the preimage of the image of `V`. That holds because the inclusion of the site into
`TopCat` creates fibre products, so the categorical fibre product in the site is the topological
one.

The isomorphism of inverse images is then the adjoint mate of the resulting isomorphism of
direct images, by uniqueness of left adjoints.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiOpenPullbackIso`: the
  site-level identification of `f^{-1}V ⊆ X` with the pullback along `f` of `V ⊆ Y`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiSliceMorphism`: the morphism of
  slice topoi induced by `f`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiComparisonDirectImageSquareIso`:
  the commutative square on direct images.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensMap_isContinuous`: restriction of
  opens along the underlying continuous map of a morphism of the site is continuous.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.pullback_openEmbedding_range`: a fibre
  product of an open immersion in the site is an open immersion with the expected image.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiComparisonSquareIso`: the
  commutative square, as a natural isomorphism of inverse-image functors.

## Implementation notes

`overOpenEmbeddingIso` is the uniqueness statement that makes everything here canonical: two
objects over `T` whose structure morphisms are open embeddings with the same image are uniquely
isomorphic over `T`. It is what identifies the two descriptions of `f^{-1}V` without choosing
anything.

The construction of `zariskiComparisonSquareIso` is deliberately left transparent, so that
adjoint mates computed from it can be identified with the corresponding base-change maps.

Of the seven clauses of Stacks 0DCU, the last of which the source splits into (7a) and (7b),
`zariskiComparisonSquareIso` is clause (5) and carries the tag for it. The others are the
cohomology comparison `zariskiCohomologyComparisonIso` (1), the exactness of the direct image
`abelianComparisonDirectImage_exact` (2), the invertibility of the unit
`abelianComparisonAdjunction_unit_isIso` (3), its derived counterpart
`abelianDerivedComparisonAdjunction_unit_isIso` (4), the relative cohomology comparison
`relativeZariskiCohomologyIso` (6), and the compatibility of the comparison with pushforward
along a *proper* morphism, `properDirectImageComparisonIsoOfProperMap` (7a) and
`properDerivedImageComparison_isIso` (7b).

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v a b t

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}}
  {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
  {X Y : S.category} (f : X ⟶ Y)

/-- Restriction of opens along the underlying continuous map of a morphism of the site is a
continuous functor of sites. This is Mathlib's instance for a morphism of `TopCat`, made
available in the spelling that the Zariski site uses. -/
instance opensMap_isContinuous :
    (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).IsContinuous
      (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj) := by
  let g : TopCat.of X.obj ⟶ TopCat.of Y.obj :=
    (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f
  change (Opens.map g).IsContinuous _ _
  exact Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map g)
    (coverPreserving_opens_map g)

/-- Two objects over `T` whose structure morphisms are open embeddings with the same image are
isomorphic over `T`, canonically: the isomorphism is the induced homeomorphism of the two
sources onto that common image, which lies in the site because the inclusion into `TopCat` is
fully faithful. -/
def overOpenEmbeddingIso
    {T : S.category} (a b : Over T)
    (he : Topology.IsOpenEmbedding (a.hom : a.left.obj → T.obj))
    (hd : Topology.IsOpenEmbedding (b.hom : b.left.obj → T.obj))
    (hrange : Set.range (a.hom : a.left.obj → T.obj) =
      Set.range (b.hom : b.left.obj → T.obj)) :
    a ≅ b := by
  let I := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let hI : (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)
  let h := he.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr hrange).trans hd.isEmbedding.toHomeomorph.symm)
  let eTop : I.obj a.left ≅ I.obj b.left := TopCat.isoOfHomeo h
  refine Over.isoMk (hI.preimageIso eTop) ?_
  apply hI.faithful.map_injective
  apply TopCat.Hom.ext
  ext x
  change b.hom (h x) = a.hom x
  have hh : hd.isEmbedding.toHomeomorph (h x) =
      (Homeomorph.setCongr hrange) (he.isEmbedding.toHomeomorph x) := by
    simp [h]
  exact congrArg Subtype.val hh

/-- The inclusion of the bounded subcategory into `LC` creates fibre products: the bounded
subcategory is closed under countable limits, and a cospan is a countable shape. -/
@[instance_reducible]
def boundedSiteInclusionCreatesPullbacks :
    CreatesLimitsOfShape WalkingCospan S.qcSite.inclusion := by
  let P : ObjectProperty LocallyQuasiCompactHausdorff := fun Z => lcSize Z < S.qcSite.cutoff
  let J := ULiftHom.{u} (ULift.{u} WalkingCospan)
  let _ : HasLimitsOfShape J LocallyQuasiCompactHausdorff :=
    hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv WalkingCospan)
  let _ : P.IsClosedUnderLimitsOfShape J :=
    S.qcSite.boundedSubcategory.closedUnderCountableLimits J
  let _ : CreatesLimitsOfShape J S.qcSite.inclusion := by
    change CreatesLimitsOfShape J (ObjectProperty.ι P)
    infer_instance
  exact createsLimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv WalkingCospan).symm
    S.qcSite.inclusion

/-- The fibre product of an open immersion `j : U ⟶ Y` along any `f : X ⟶ Y` in the site is
again an open immersion, whose image is the preimage under `f` of the image of `j`. The fibre
product of the site is computed in `TopCat`, where this is the standard statement about open
embeddings. -/
theorem pullback_openEmbedding_range
    {U : S.category} (j : U ⟶ Y) (hj : Topology.IsOpenEmbedding (j : U.obj → Y.obj)) :
    Topology.IsOpenEmbedding (pullback.snd j f : _ → _) ∧
      Set.range (pullback.snd j f : _ → _) =
        {x : X.obj | (f : X.obj → Y.obj) x ∈ Set.range (j : U.obj → Y.obj)} := by
  let I : S.category ⥤ TopCat := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let c := cospan j f
  let _ : CreatesLimitsOfShape WalkingCospan S.qcSite.inclusion :=
    boundedSiteInclusionCreatesPullbacks S
  let cTop := cospan (I.map j) (I.map f)
  let hdiag : c ⋙ I ≅ cTop := cospanCompIso I j f
  let eTop := (preservesLimitIso I c).trans (HasLimit.isoOfNatIso hdiag)
  have hπ : Topology.IsOpenEmbedding ⇑(limit.π cTop WalkingCospan.right) := by
    rw [show limit.π cTop WalkingCospan.right = pullback.snd (I.map j) (I.map f) from
      PullbackCone.snd_limit_cone _ _]
    exact TopCat.snd_isOpenEmbedding_of_left hj (I.map f)
  have hproj : eTop.hom ≫ limit.π cTop WalkingCospan.right = I.map (pullback.snd j f) := by
    dsimp [eTop]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π]
    simp only [cospan_right, Functor.comp_obj, cospanCompIso_hom_app_right, Category.comp_id,
      c, cTop, hdiag]
    rw [← preservesLimitIso_hom_π]
  refine ⟨?_, ?_⟩
  · show Topology.IsOpenEmbedding (I.map (pullback.snd j f))
    rw [← hproj]
    exact hπ.comp (TopCat.homeoOfIso eTop).isOpenEmbedding
  · show Set.range (I.map (pullback.snd j f)) = _
    rw [← hproj]
    show Set.range
      ((ConcreteCategory.hom (limit.π cTop WalkingCospan.right)) ∘
        (ConcreteCategory.hom eTop.hom)) = _
    have hsurj : Function.Surjective (ConcreteCategory.hom eTop.hom) :=
      (TopCat.homeoOfIso eTop).surjective
    rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ,
      TopCat.pullback_snd_range]
    exact Set.ext fun _ => Iff.rfl

/-- Restricting an open `V ⊆ Y` to `f^{-1}V ⊆ X` and then viewing it over `X` gives the same
object of the slice over `X` as viewing `V` over `Y` and then pulling back along `f`: both are
the open subspace `f^{-1}V` of `X`. -/
def zariskiOpenPullbackComponent
    (V : Opens ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj Y)) :
    (S.opensToSlice X).1.obj
        ((Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj V) ≅
      ((S.opensToSlice Y).1 ⋙ Over.pullback f).obj V := by
  let I : S.category ⥤ TopCat := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let g := I.map f
  have hg (x : X.obj) : (g : I.obj X → I.obj Y) x = (f : X.obj → Y.obj) x := rfl
  let a := (S.opensToSlice X).1.obj ((Opens.map g).obj V)
  let b := ((S.opensToSlice Y).1 ⋙ Over.pullback f).obj V
  have ha := (S.opensToSlice X).2 ((Opens.map g).obj V)
  have hy := (S.opensToSlice Y).2 V
  have hp := pullback_openEmbedding_range (S := S) (X := X) (Y := Y) (f := f)
    (j := ((S.opensToSlice Y).1.obj V).hom) (hj := hy.1)
  have hb : Topology.IsOpenEmbedding (b.hom : b.left.obj → X.obj) := by
    simpa [b, Over.pullback] using hp.1
  have hLeft : Set.range (a.hom : a.left.obj → X.obj) =
      {x : X.obj | (g : I.obj X → I.obj Y) x ∈ (V : Set (I.obj Y))} := by
    rw [ha.2]
    ext x
    simp [Opens.map_coe]
  have hRight : Set.range (b.hom : b.left.obj → X.obj) =
      {x : X.obj | (g : I.obj X → I.obj Y) x ∈ (V : Set (I.obj Y))} := by
    calc
      Set.range (b.hom : b.left.obj → X.obj) =
          {x : X.obj | (f : X.obj → Y.obj) x ∈
            Set.range ((S.opensToSlice Y).1.obj V).hom} := by
        simpa [b, I, Over.pullback] using hp.2
      _ = {x : X.obj | (g : I.obj X → I.obj Y) x ∈ (V : Set (I.obj Y))} := by
        ext x
        simp [hy.2, hg]
  exact overOpenEmbeddingIso S a b ha.1 hb (hLeft.trans hRight.symm)

/-- The identification `zariskiOpenPullbackComponent` is natural in the open `V`: both sides,
composed with the structure morphism of the target, are the structure morphism of the source,
which determines them because that structure morphism is a monomorphism. -/
theorem zariskiOpenPullbackComponent_naturality
    {V W : Opens ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj Y)} (h : V ⟶ W) :
    (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) ⋙
          (S.opensToSlice X).1).map h ≫ (zariskiOpenPullbackComponent S f W).hom =
      (zariskiOpenPullbackComponent S f V).hom ≫
        ((S.opensToSlice Y).1 ⋙ Over.pullback f).map h := by
  let g := (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f
  let bW := ((S.opensToSlice Y).1 ⋙ Over.pullback f).obj W
  let aMap := (S.opensToSlice X).1.map ((Opens.map g).map h)
  let bMap := ((S.opensToSlice Y).1 ⋙ Over.pullback f).map h
  let eV := zariskiOpenPullbackComponent S f V
  let eW := zariskiOpenPullbackComponent S f W
  have hpW := pullback_openEmbedding_range (S := S) (X := X) (Y := Y) (f := f)
    (j := ((S.opensToSlice Y).1.obj W).hom) (hj := ((S.opensToSlice Y).2 W).1)
  let _ : Mono bW.hom :=
    ConcreteCategory.mono_of_injective bW.hom hpW.1.isEmbedding.injective
  apply Over.OverMorphism.ext
  apply (cancel_mono bW.hom).1
  show aMap.left ≫ eW.hom.left ≫ bW.hom = eV.hom.left ≫ bMap.left ≫ bW.hom
  rw [Over.w eW.hom, Over.w aMap, Over.w bMap, Over.w eV.hom]

/-- Restricting an open `V ⊆ Y` to `f^{-1}V ⊆ X` and then viewing it over `X` is the same as
viewing `V` over `Y` and then pulling back along `f`: both are the open subspace `f^{-1}V`
of `X`. -/
def zariskiOpenPullbackIso :
    Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) ⋙
        (S.opensToSlice X).1 ≅
      (S.opensToSlice Y).1 ⋙ Over.pullback f :=
  NatIso.ofComponents (zariskiOpenPullbackComponent S f)
    (zariskiOpenPullbackComponent_naturality S f)

/-- The commutative square on direct images: it is restriction along the canonical
identification `zariskiOpenPullbackIso` of the two composite continuous functors. -/
def zariskiComparisonDirectImageSquareIso
    (A : Type a) [Category.{b} A] :
    S.comparisonDirectImage X A ⋙
        Functor.sheafPushforwardContinuous
          (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f))
          A (Opens.grothendieckTopology
            ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj Y))
          (Opens.grothendieckTopology
            ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X)) ≅
      (Over.pullback f).sheafPushforwardContinuous A
          (S.zariskiTopology.over Y) (S.zariskiTopology.over X) ⋙
        S.comparisonDirectImage Y A := by
  let I := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let g := I.map f
  let JX := Opens.grothendieckTopology (I.obj X)
  let JY := Opens.grothendieckTopology (I.obj Y)
  let KX := S.zariskiTopology.over X
  let KY := S.zariskiTopology.over Y
  let uX := (S.opensToSlice X).1
  let uY := (S.opensToSlice Y).1
  let vOpen := Opens.map g
  let pOver := Over.pullback f
  let _ : uX.IsContinuous JX KX := S.opensToSlice_isContinuous X
  let _ : uY.IsContinuous JY KY := S.opensToSlice_isContinuous Y
  let _ : (vOpen ⋙ uX).IsContinuous JY KX := Functor.isContinuous_comp vOpen uX JY JX KX
  let _ : (uY ⋙ pOver).IsContinuous JY KX := Functor.isContinuous_comp uY pOver JY KY KX
  exact Functor.sheafPushforwardContinuousComp' (Iso.refl (vOpen ⋙ uX)) A JY JX KX ≪≫
    Functor.sheafPushforwardContinuousIso (zariskiOpenPullbackIso S f) A JY KX ≪≫
      (Functor.sheafPushforwardContinuousComp' (Iso.refl (uY ⋙ pOver)) A JY KY KX).symm

/-! ### Smallness of the shapes computing the two Kan extensions along the slice functors

Both slice sites are essentially small in the universe `u` of the spaces
(`essentiallySmall_over`), so the comma categories indexing the Kan extensions along
`Over.map f` and `Over.pullback f` are too. That is what makes the morphism of slice topoi, and
the commutative square of clause (5), available for coefficients in **any** universe containing
`u` — in particular in `Type u` itself, the universe in which sheaves of sets on the underlying
topological spaces live.
-/

/-- The shapes computing the right Kan extension along `(Over.map f)ᵒᵖ` are essentially small in
the universe of the spaces. -/
theorem essentiallySmall_structuredArrow_overMap (Z : (Over Y)ᵒᵖ) :
    EssentiallySmall.{max u t} (StructuredArrow Z (Over.map f).op) :=
  have := essentiallySmall_over.{u, w, t} S X
  StructuredArrow.essentiallySmall

/-- The shapes computing the left Kan extension along `(Over.pullback f)ᵒᵖ` are essentially small
in the universe of the spaces. -/
theorem essentiallySmall_costructuredArrow_overPullback (Z : (Over X)ᵒᵖ) :
    EssentiallySmall.{max u t} (CostructuredArrow (Over.pullback f).op Z) :=
  have := essentiallySmall_over.{u, w, t} S Y
  CostructuredArrow.essentiallySmall

/-- Right Kan extensions along `(Over.map f)ᵒᵖ` exist pointwise, for coefficients of types in any
universe containing the universe of the spaces. -/
theorem hasPointwiseRightKanExtension_overMap (F : (Over X)ᵒᵖ ⥤ Type (max u t)) :
    (Over.map f).op.HasPointwiseRightKanExtension F := fun Z => by
  have := essentiallySmall_structuredArrow_overMap.{u, w, t} S f Z
  have : HasLimitsOfShape (StructuredArrow Z (Over.map f).op) (Type (max u t)) :=
    hasLimitsOfShape_of_essentiallySmall.{max u t} _ _
  infer_instance

/-- The shapes computing the left Kan extension along `(Over.map f)ᵒᵖ` are essentially small in
the universe of the spaces. -/
theorem essentiallySmall_costructuredArrow_overMap (Z : (Over Y)ᵒᵖ) :
    EssentiallySmall.{max u t} (CostructuredArrow (Over.map f).op Z) :=
  have := essentiallySmall_over.{u, w, t} S X
  CostructuredArrow.essentiallySmall

/-- Left Kan extensions along `L` exist when the comma categories `CostructuredArrow L Z` are
essentially small in the universe of the spaces. -/
private theorem hasLeftKanExtension_of_essentiallySmall.{c, c₁, c₂, c₃, c₄}
    {C : Type c₁} {D : Type c₂} [Category.{c₃} C] [Category.{c₄} D]
    (L : C ⥤ D) (F : C ⥤ Type c) (h : ∀ Z, EssentiallySmall.{c} (CostructuredArrow L Z)) :
    L.HasLeftKanExtension F :=
  have : L.HasPointwiseLeftKanExtension F := fun Z => by
    have := h Z
    have : HasColimitsOfShape (CostructuredArrow L Z) (Type c) :=
      hasColimitsOfShape_of_essentiallySmall.{c} _ _
    infer_instance
  inferInstance

/-- Left Kan extensions along `(Over.map f)ᵒᵖ` exist, for coefficients of types in any universe
containing the universe of the spaces. In particular restriction along `Over.map f` is a right
adjoint, hence left exact, which is what makes the inverse image of the morphism of slice topoi
`zariskiSliceMorphism` a morphism of topoi. -/
theorem hasLeftKanExtension_overMap (F : (Over X)ᵒᵖ ⥤ Type (max u t)) :
    (Over.map f).op.HasLeftKanExtension F :=
  hasLeftKanExtension_of_essentiallySmall _ F
    (essentiallySmall_costructuredArrow_overMap.{u, w, t} S f)

/-- Left Kan extensions along `(Over.pullback f)ᵒᵖ` exist, for coefficients of types in any
universe containing the universe of the spaces. -/
theorem hasLeftKanExtension_overPullback (F : (Over Y)ᵒᵖ ⥤ Type (max u t)) :
    (Over.pullback f).op.HasLeftKanExtension F :=
  hasLeftKanExtension_of_essentiallySmall _ F
    (essentiallySmall_costructuredArrow_overPullback.{u, w, t} S f)

/-- **Stacks 0DCU, the slice-morphism clause.** The morphism of Zariski slice topoi induced by
`f : X ⟶ Y`. Its inverse image is restriction along postcomposition on slice objects, and its
direct image is the cocontinuous pushforward along the same functor.

The coefficients are types in an arbitrary universe containing the universe of the spaces. -/
def zariskiSliceMorphism :
    MorphismOfTopoi
      (Sheaf (S.zariskiTopology.over X) (Type (max u t)))
      (Sheaf (S.zariskiTopology.over Y) (Type (max u t))) :=
  letI := hasPointwiseRightKanExtension_overMap.{u, w, t} S f
  letI := hasLeftKanExtension_overMap.{u, w, t} S f
  letI : HasSheafify (S.zariskiTopology.over Y) (Type (max u t)) :=
    hasSheafify_zariskiTopology_over.{u, w, t} S Y
  { pushforward := (Over.map f).sheafPushforwardCocontinuous
      (Type (max u t)) (S.zariskiTopology.over X) (S.zariskiTopology.over Y)
    inverseImage := (Over.map f).sheafPushforwardContinuous
      (Type (max u t)) (S.zariskiTopology.over X) (S.zariskiTopology.over Y)
    adj := (Over.map f).sheafAdjunctionCocontinuous
      (Type (max u t)) (S.zariskiTopology.over X) (S.zariskiTopology.over Y)
    preservesFiniteLimits := inferInstance }

/-- **Stacks 0DCU, clause (5): the commutative square of topoi.** The square whose horizontal
arrows are `f_Zar : Sh(LC_Zar/X) → Sh(LC_Zar/Y)` and `f : Sh(X_Zar) → Sh(Y_Zar)` and whose
vertical arrows are the comparison morphisms `π_X` and `π_Y` commutes: read on inverse images,
which is where a morphism of topoi lives, `π_X^{-1} ∘ f^{-1} ≅ f_Zar^{-1} ∘ π_Y^{-1}`.

It is obtained from `zariskiComparisonDirectImageSquareIso` by uniqueness of left adjoints,
using the specified comparison and slice adjunctions.

The coefficients are types in an arbitrary universe containing the universe of the spaces. -/
@[stacks 0DCU "commutative_square"]
def zariskiComparisonSquareIso :
    (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).sheafPullback
        (Type (max u t))
        (Opens.grothendieckTopology
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj Y))
        (Opens.grothendieckTopology
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X)) ⋙
      comparisonInverseImage.{u, w, t} S X ≅
    comparisonInverseImage.{u, w, t} S Y ⋙ (zariskiSliceMorphism.{u, w, t} S f).inverseImage := by
  let I : S.category ⥤ TopCat := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let g := I.map f
  let A := Type (max u t)
  let JX := Opens.grothendieckTopology (I.obj X)
  let JY := Opens.grothendieckTopology (I.obj Y)
  let KX := S.zariskiTopology.over X
  let KY := S.zariskiTopology.over Y
  let uX := (S.opensToSlice X).1
  let uY := (S.opensToSlice Y).1
  let vOpen := Opens.map g
  let pOver := Over.pullback f
  let _ : HasSheafify KX A := hasSheafify_zariskiTopology_over.{u, w, t} S X
  let _ : HasSheafify KY A := hasSheafify_zariskiTopology_over.{u, w, t} S Y
  let _ : ∀ F : (Over Y)ᵒᵖ ⥤ A, pOver.op.HasLeftKanExtension F :=
    hasLeftKanExtension_overPullback.{u, w, t} S f
  let _ : ∀ F : (Over X)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension F :=
    hasPointwiseRightKanExtension_overMap.{u, w, t} S f
  let _ : uX.IsContinuous JX KX := S.opensToSlice_isContinuous X
  let _ : uY.IsContinuous JY KY := S.opensToSlice_isContinuous Y
  let _ : (vOpen ⋙ uX).IsContinuous JY KX := Functor.isContinuous_comp vOpen uX JY JX KX
  let _ : (uY ⋙ pOver).IsContinuous JY KX := Functor.isContinuous_comp uY pOver JY KY KX
  let _ : (uX.sheafPushforwardContinuous A JX KX).IsRightAdjoint :=
    comparisonDirectImage_isRightAdjoint.{u, w, t} S X
  let _ : (uY.sheafPushforwardContinuous A JY KY).IsRightAdjoint :=
    comparisonDirectImage_isRightAdjoint.{u, w, t} S Y
  let adjOpen := vOpen.sheafAdjunctionContinuous A JY JX
  let adjX := uX.sheafAdjunctionContinuous A JX KX
  let adjY := uY.sheafAdjunctionContinuous A JY KY
  let adjP := pOver.sheafAdjunctionContinuous A KY KX
  let eSquarePullback := (adjOpen.comp adjX).leftAdjointUniq
    ((adjY.comp adjP).ofNatIsoRight (zariskiComparisonDirectImageSquareIso S f A).symm)
  let eX : comparisonInverseImage.{u, w, t} S X ≅ uX.sheafPullback A JX KX :=
    Adjunction.leftAdjointUniq (comparisonAdjunction.{u, w, t} S X) adjX
  let eY : comparisonInverseImage.{u, w, t} S Y ≅ uY.sheafPullback A JY KY :=
    Adjunction.leftAdjointUniq (comparisonAdjunction.{u, w, t} S Y) adjY
  let eP : pOver.sheafPullback A KY KX ≅
      (Over.map f).sheafPushforwardContinuous A KX KY :=
    (Over.mapPullbackAdj f).sheafPullbackIso A
  exact Functor.isoWhiskerLeft (vOpen.sheafPullback A JY JX) eX ≪≫
    eSquarePullback ≪≫
      Functor.isoWhiskerRight eY.symm (pOver.sheafPullback A KY KX) ≪≫
        Functor.isoWhiskerLeft (comparisonInverseImage.{u, w, t} S Y) eP

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
