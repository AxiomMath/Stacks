module

public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldSpectrumCoverFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldSpectrumCoverSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType

/-!
# Algebraic stacks that are reduced with a single point

For an algebraic stack `𝒵` the following are equivalent (Stacks 06MN):

1. `𝒵` is reduced and `|𝒵|` is a singleton;
2. there is a surjective flat 1-morphism `Spec k ⟶ 𝒵` with `k` a field;
3. there is such a 1-morphism which is moreover locally of finite type.

For an algebraic stack `𝒵` consider moreover the conditions (Stacks 06MP)

1. `𝒵` is reduced, locally Noetherian, and `|𝒵|` is a singleton;
2. there is a 1-morphism `Spec k ⟶ 𝒵` with `k` a field which is locally of finite presentation,
   surjective and flat.

This file proves that the second implies the first.

## Main definitions

* `AlgebraicGeometry.Stack.IsReducedWithUniquePoint`: condition (1) of Stacks 06MN.
* `AlgebraicGeometry.Stack.HasFlatFieldSpectrumCover`: condition (2).
* `AlgebraicGeometry.Stack.HasLocallyOfFiniteTypeFlatFieldSpectrumCover`: condition (3).
* `AlgebraicGeometry.Stack.IsReducedLocallyNoetherianWithUniquePoint`: condition (1) of
  Stacks 06MP.
* `AlgebraicGeometry.Stack.HasLocallyOfFinitePresentationFlatFieldSpectrumCover`: its
  condition (2).

## Main results

* `AlgebraicGeometry.Stack.tfae_isReducedWithUniquePoint`: the three conditions of Stacks 06MN
  are equivalent.
* `AlgebraicGeometry.Stack.isReducedWithUniquePoint_iff_hasFlatFieldSpectrumCover`: conditions
  (1) and (2) of Stacks 06MN are equivalent.
* `AlgebraicGeometry.Stack.isReducedStack_of_flatFieldSpectrumCover`: an algebraic stack
  admitting a surjective flat 1-morphism from the algebraic stack of the spectrum of a field is
  reduced.
* `AlgebraicGeometry.Stack.isFlat_of_isReducedWithUniquePoint`: over an algebraic stack
  satisfying condition (1) of Stacks 06MN, *every* 1-morphism from the algebraic stack of the
  spectrum of a field is flat.
* `AlgebraicGeometry.Stack.hasFlatFieldSpectrumCover_of_locallyOfFiniteType`: condition (3) of
  Stacks 06MN implies its condition (2).
* `hasLocallyOfFiniteTypeFlatFieldSpectrumCover_of_hasFlatFieldSpectrumCover`: condition (2) of
  Stacks 06MN implies its condition (3).
* `AlgebraicGeometry.Stack.exists_mono_locallyOfFiniteType_specField`: a nonempty scheme receives
  a monomorphism, locally of finite type, from the spectrum of a field.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_schemeFibredCategoryMap` and
  `AlgebraicGeometry.Stack.isFlat_schemeFibredCategoryMap`: a morphism of the site which is
  locally of finite type, resp. flat, induces a 1-morphism of represented algebraic stacks with
  the same property.
* `AlgebraicGeometry.Stack.flat_fromSpecStalk_of_isField`: the spectrum of a local ring of a
  scheme which is a field is flat over the scheme.
* `isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation`: condition (2) of
  Stacks 06MP implies its condition (1).
* `AlgebraicGeometry.Stack.isLocallyNoetherianStack_of_locallyOfFinitePresentationFlatFieldCover`:
  an algebraic stack admitting a 1-morphism from the algebraic stack of the spectrum of a field
  which is locally of finite presentation, surjective and flat is locally Noetherian.

## Implementation notes

The spectrum of a field is taken as `AlgebraicGeometry.Stack.FieldSpectrum`, an object of the big
fppf site of `S` presented with an isomorphism of its underlying scheme onto the spectrum of a
field. Reducedness of an algebraic stack is `AlgebraicGeometry.Stack.IsReducedStack`, and local
Noetherianity is `AlgebraicGeometry.Stack.IsLocallyNoetherianStack`: the existential scheme
criterion of Stacks 04YF at reducedness, resp. local Noetherianity, of schemes.

That `|𝒵|` is a singleton is spelled as nonemptiness together with subsingletonness of the point
space of Stacks 04XG. It is not phrased through `AlgebraicGeometry.Stack.HasUniquePointOver`,
which asks for a unique point *lying over a prescribed point of a prescribed target*.

## References

* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 06MI](https://stacks.math.columbia.edu/tag/06MI)
* [Stacks Project, Tag 06FT](https://stacks.math.columbia.edu/tag/06FT)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 06MM](https://stacks.math.columbia.edu/tag/06MM)
* [Stacks Project, Tag 06MN](https://stacks.math.columbia.edu/tag/06MN)
* [Stacks Project, Tag 06MJ](https://stacks.math.columbia.edu/tag/06MJ)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06Q5](https://stacks.math.columbia.edu/tag/06Q5)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 034C](https://stacks.math.columbia.edu/tag/034C)
* [Stacks Project, Tag 0GB3](https://stacks.math.columbia.edu/tag/0GB3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack over `S` is reduced and its space of points is a singleton, i.e.
nonempty and a subsingleton. -/
abbrev IsReducedWithUniquePoint (𝒵 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  IsReducedStack B S hS 𝒵 ∧
    Nonempty (AlgebraicStacks.points B S hS 𝒵) ∧
      Subsingleton (AlgebraicStacks.points B S hS 𝒵)

/-- An algebraic stack over `S` admits a surjective flat 1-morphism from the algebraic stack of
the spectrum of a field. -/
abbrev HasFlatFieldSpectrumCover (𝒵 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ (F : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵),
    IsSurjective B S hS f ∧ AlgebraicStacks.IsFlat B S hS f

/-- An algebraic stack over `S` admits a surjective flat 1-morphism, locally of finite type, from
the algebraic stack of the spectrum of a field. -/
abbrev HasLocallyOfFiniteTypeFlatFieldSpectrumCover
    (𝒵 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ (F : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵),
    AlgebraicStacks.IsLocallyOfFiniteType B S hS f ∧
      IsSurjective B S hS f ∧ AlgebraicStacks.IsFlat B S hS f

/-- The underlying scheme of an `AlgebraicGeometry.Stack.FieldSpectrum` is reduced. -/
theorem isReduced_fieldSpectrum (F : FieldSpectrum B S hS) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj F.base) :=
  have : IsReduced (Spec (CommRingCat.of F.carrier)) := inferInstance
  isReduced_of_isOpenImmersion F.isSpec.hom

/-- The algebraic space represented by an `AlgebraicGeometry.Stack.FieldSpectrum` has the
étale-local scheme property of being reduced. -/
theorem hasEtaleLocalProperty_isReduced_fieldSpectrum (F : FieldSpectrum B S hS) :
    Space.HasEtaleLocalProperty B S hS (yoneda.obj F.base)
      (fun X : Scheme.{u} => IsReduced X) :=
  (Space.exists_atlas_iff_of_representable B S hS (yoneda.obj F.base)
    (fun X : Scheme.{u} => IsReduced X) F.base (Iso.refl _)).mpr
      (isReduced_fieldSpectrum B S hS F)

/-- For a smooth 1-morphism `b : V ⟶ 𝒵` and a surjective flat `f : F ⟶ 𝒵` from the spectrum of a
field, the 2-fibre product `Q` is represented by an algebraic space `R` whose projection to `F` is
smooth and whose projection to `V` is flat and surjective, and locally of finite presentation if
`f` is. -/
private theorem exists_representingMaps_of_flatFieldSpectrumCover
    {𝒵 : AlgebraicStacks.{u, w} B S hS} {F : FieldSpectrum B S hS} {V : BigFppfOver B S hS}
    {f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵} {b : schemeStack.{u, w} B S hS V ⟶ 𝒵}
    (hbSmooth : AlgebraicStacks.IsSmooth B S hS b) (hsurj : IsSurjective B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (Q : Bicategory.TwoCommSq f b)
    (hQ : Q = twoFibreProductSquareAlgebraicStacks B S hS f b) :
    ∃ (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS R)
      (eR : StacksRepresentableCFG.EquivalenceOver Q.pt.val.val.p
        (presheafOfCategories (R ⋙ typeToCat)).p),
      Space.IsSmooth B S hS (representingMap B S hS Q.pt.val
        (schemeStack.{u, w} B S hS F.base).val R (yoneda.obj F.base) eR
        (PresheafOfCategories.sliceElementsEquivalenceOver F.base) Q.fst.hom) ∧
      Space.IsFlat B S hS (representingMap B S hS Q.pt.val
        (schemeStack.{u, w} B S hS V).val R (yoneda.obj V) eR
        (PresheafOfCategories.sliceElementsEquivalenceOver V) Q.snd.hom) ∧
      Space.IsSurjective B S hS (representingMap B S hS Q.pt.val
        (schemeStack.{u, w} B S hS V).val R (yoneda.obj V) eR
        (PresheafOfCategories.sliceElementsEquivalenceOver V) Q.snd.hom) ∧
      (AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f →
        Space.IsLocallyOfFinitePresentation B S hS (representingMap B S hS Q.pt.val
          (schemeStack.{u, w} B S hS V).val R (yoneda.obj V) eR
          (PresheafOfCategories.sliceElementsEquivalenceOver V) Q.snd.hom)) := by
  subst hQ
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f b
  have hbrep : IsRepresentableByAlgebraicSpaces B S hS b.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒵.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V) b.hom
  have hrep : IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f b).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒵.val
      (schemeStack.{u, w} B S hS F.base).val (schemeStack.{u, w} B S hS V).val
      f.hom.hom b.hom.hom hbrep
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base)
  obtain ⟨R, hR, ⟨eR⟩⟩ := hrep
  have hm := isSmooth_representingMap_of_isSmooth B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) R (yoneda.obj F.base) hR
    (isAlgebraicSpace_yoneda B S hS F.base) eR
    (PresheafOfCategories.sliceElementsEquivalenceOver F.base) _
    (AlgebraicStacks.isSmooth_baseChange B S hS b f _ hQ hbSmooth)
  have hswap := Bicategory.isTwoFibreProduct_swap hQ
  have hn := isFlat_representingMap_of_isFlat.{u, w} B S hS R (yoneda.obj V) hR
    (isAlgebraicSpace_yoneda B S hS V) eR
    (PresheafOfCategories.sliceElementsEquivalenceOver V) _
    (AlgebraicStacks.isFlat_baseChange B S hS f b _ hswap hflat)
  have hnsurj := isSurjective_representingMap_of_isSurjective B S hS R (yoneda.obj V) eR
    (PresheafOfCategories.sliceElementsEquivalenceOver V) _
    (isSurjective_of_isTwoFibreProduct B S hS _ hQ hsurj)
  refine ⟨R, hR, eR, hm, hn, hnsurj, fun hlfp => ?_⟩
  have hnlfp :=
    isLocallyOfFinitePresentation_representingMap_of_isLocallyOfFinitePresentation.{u, w}
      B S hS R (yoneda.obj V) hR (isAlgebraicSpace_yoneda B S hS V) eR
      (PresheafOfCategories.sliceElementsEquivalenceOver V) _
      (AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS f b _ hswap hlfp)
  exact hnlfp

/-- An algebraic stack admitting a surjective flat 1-morphism from the algebraic stack of the
spectrum of a field is reduced. -/
theorem isReducedStack_of_flatFieldSpectrumCover
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (F : FieldSpectrum B S hS)
    (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵)
    (hsurj : IsSurjective B S hS f) (hflat : AlgebraicStacks.IsFlat B S hS f) :
    IsReducedStack B S hS 𝒵 := by
  obtain ⟨V, b, hbSmooth, hbSurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒵
  obtain ⟨R, hR, eR, hm, hn, hnsurj, -⟩ :=
    exists_representingMaps_of_flatFieldSpectrumCover.{u, w} B S hS hbSmooth hsurj hflat _ rfl
  have hRred := Space.isReduced_source_of_isSmooth B S hS hR
    (isAlgebraicSpace_yoneda B S hS F.base) _ hm
    (hasEtaleLocalProperty_isReduced_fieldSpectrum B S hS F)
  have hVred := Space.isReduced_of_flat_of_surjective B S hS hR
    (isAlgebraicSpace_yoneda B S hS V) _ hn hnsurj hRred
  exact ⟨V, b, hbSurj, hbSmooth,
    (Space.exists_atlas_iff_of_representable B S hS (yoneda.obj V)
      (fun X : Scheme.{u} => IsReduced X) V (Iso.refl _)).mp hVred⟩

/-- An algebraic stack admitting a surjective flat 1-morphism from the algebraic stack of the
spectrum of a field is reduced and has a single point. -/
theorem isReducedWithUniquePoint_of_hasFlatFieldSpectrumCover
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (h : HasFlatFieldSpectrumCover B S hS 𝒵) :
    IsReducedWithUniquePoint B S hS 𝒵 := by
  obtain ⟨F, f, hsurj, hflat⟩ := h
  have := subsingleton_points_fieldSpectrumStack.{u, w} B S hS F
  obtain ⟨p⟩ := nonempty_points_fieldSpectrumStack.{u, w} B S hS F
  exact ⟨isReducedStack_of_flatFieldSpectrumCover.{u, w} B S hS 𝒵 F f hsurj hflat,
    ⟨AlgebraicStacks.pointsMap B S hS f p⟩, hsurj.subsingleton⟩

/-- If the local ring of a scheme `X` at `x` is a field, then the canonical morphism
`Spec 𝒪_{X,x} ⟶ X` is flat. -/
theorem flat_fromSpecStalk_of_isField {X : Scheme.{u}} (x : X)
    (hfield : IsField (X.presheaf.stalk x)) : Flat (X.fromSpecStalk x) := by
  let : Field (X.presheaf.stalk x) := hfield.toField
  let : _root_.IsReduced (X.presheaf.stalk x) := inferInstance
  let : Subsingleton (Spec (X.presheaf.stalk x)) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.2 hfield
  refine Flat.of_stalkMap (X.fromSpecStalk x) fun z => ?_
  obtain rfl : z = IsLocalRing.closedPoint (X.presheaf.stalk x) := Subsingleton.elim _ _
  have hcomp : IsIso (Scheme.stalkClosedPointTo (X.fromSpecStalk x)) := by
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  let : IsIso ((X.fromSpecStalk x).stalkMap
      (IsLocalRing.closedPoint (X.presheaf.stalk x)) ≫
    (stalkClosedPointIso (CommRingCat.of (X.presheaf.stalk x))).hom) := hcomp
  let : IsIso ((X.fromSpecStalk x).stalkMap
      (IsLocalRing.closedPoint (X.presheaf.stalk x))) :=
    IsIso.of_isIso_comp_right _
      (stalkClosedPointIso (CommRingCat.of (X.presheaf.stalk x))).hom
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)

/-- A morphism `j` of the big fppf site whose Yoneda image has a smooth-local property `P` induces
a 1-morphism of represented algebraic stacks with `P` on some smooth diagram. -/
private theorem hasPropertyOnSomeSmoothDiagram_schemeFibredCategoryMap
    {P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P) {V U : BigFppfOver B S hS} (j : V ⟶ U)
    (hj : P (yoneda.map j)) :
    HasPropertyOnSomeSmoothDiagram B S hS P
      (Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS j) :
        schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS U).hom := by
  rw [hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _ hP
      (schemeStack.{u, w} B S hS V).property (schemeStack.{u, w} B S hS U).property
      (yoneda.obj V) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS U)
      (PresheafOfCategories.sliceElementsEquivalenceOver V)
      (PresheafOfCategories.sliceElementsEquivalenceOver U),
    representingMap_schemeFibredCategoryMap]
  exact hj

/-- A flat morphism of objects of the big fppf site induces a flat 1-morphism of the algebraic
stacks they represent. -/
theorem isFlat_schemeFibredCategoryMap {V U : BigFppfOver B S hS} (j : V ⟶ U)
    (hj : Flat ((BigFppfOver.toScheme B S hS).map j)) :
    AlgebraicStacks.IsFlat B S hS
      (Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS j) :
        schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS U) := by
  exact hasPropertyOnSomeSmoothDiagram_schemeFibredCategoryMap.{u, w} B S hS
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) j
    ((Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Flat.isEtaleLocalOnSourceAndTarget j).2 hj)

/-- A reduced algebraic stack with a single point admits a surjective flat 1-morphism from the
algebraic stack of the spectrum of a field. -/
theorem hasFlatFieldSpectrumCover_of_isReducedWithUniquePoint
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (h : IsReducedWithUniquePoint B S hS 𝒵) :
    HasFlatFieldSpectrumCover B S hS 𝒵 := by
  obtain ⟨⟨U, a, haSurj, haSmooth, hUred⟩, ⟨z⟩, hsub⟩ := h
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj U) := hUred
  obtain ⟨zU, -⟩ := haSurj z
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  set X := (BigFppfOver.toScheme B S hS).obj U with hX
  have x : X := pointsHomeomorphScheme B S hS U zU
  set η : genericPoints X := genericPoints.ofComponent
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩ with hη
  have hηfield : IsField (X.presheaf.stalk η.1) :=
    isField_stalk_of_closure_mem_irreducibleComponents X η.1 η.2
  let : Field (X.presheaf.stalk η.1) := hηfield.toField
  have hjflat₀ : Flat (X.fromSpecStalk η.1) := flat_fromSpecStalk_of_isField η.1 hηfield
  have hcontains : B.Contains (Spec (CommRingCat.of (X.presheaf.stalk η.1))) :=
    BigFppfSite.contains_of_mono B (X.fromSpecStalk η.1) U.left.2
  obtain ⟨Z, j, e, hje⟩ :=
    Space.exists_siteObject_toScheme_map_eq B S hS hcontains (X.fromSpecStalk η.1)
  have hjflat : Flat ((BigFppfOver.toScheme B S hS).map j) := by
    rw [hje]
    infer_instance
  refine ⟨{ carrier := X.presheaf.stalk η.1, base := Z, isSpec := e },
    Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS j) ≫ a, ?_, ?_⟩
  · obtain ⟨p⟩ := nonempty_points_fieldSpectrumStack.{u, w} B S hS
      { carrier := X.presheaf.stalk η.1, base := Z, isSpec := e }
    exact fun _ => ⟨p, Subsingleton.elim _ _⟩
  · exact AlgebraicStacks.isFlat_comp B S hS _ a
      (isFlat_schemeFibredCategoryMap.{u, w} B S hS j hjflat)
      (AlgebraicStacks.isFlat_of_isSmooth B S hS a haSmooth)

/-- Every 1-morphism from the algebraic stack of the spectrum of a field to a reduced algebraic
stack with a single point is flat. -/
theorem isFlat_of_isReducedWithUniquePoint (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h : IsReducedWithUniquePoint B S hS 𝒵) (F : FieldSpectrum B S hS)
    (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵) :
    AlgebraicStacks.IsFlat B S hS f :=
  have ⟨F₀, f₀, hf₀surj, hf₀flat⟩ :=
    hasFlatFieldSpectrumCover_of_isReducedWithUniquePoint.{u, w} B S hS 𝒵 h
  isFlat_of_fieldSpectrum_cover.{u, w} B S hS 𝒵 F₀ F f₀ f hf₀surj hf₀flat

/-- An algebraic stack over `S` is reduced with a single point exactly when it admits a surjective
flat 1-morphism from the algebraic stack of the spectrum of a field. -/
theorem isReducedWithUniquePoint_iff_hasFlatFieldSpectrumCover
    (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    IsReducedWithUniquePoint B S hS 𝒵 ↔ HasFlatFieldSpectrumCover B S hS 𝒵 :=
  ⟨hasFlatFieldSpectrumCover_of_isReducedWithUniquePoint.{u, w} B S hS 𝒵,
    isReducedWithUniquePoint_of_hasFlatFieldSpectrumCover.{u, w} B S hS 𝒵⟩

/-- An algebraic stack admitting a surjective flat 1-morphism, locally of finite type, from the
algebraic stack of the spectrum of a field admits a surjective flat 1-morphism from it. -/
theorem hasFlatFieldSpectrumCover_of_locallyOfFiniteType
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h : HasLocallyOfFiniteTypeFlatFieldSpectrumCover B S hS 𝒵) :
    HasFlatFieldSpectrumCover B S hS 𝒵 := by
  obtain ⟨F, f, -, h⟩ := h
  exact ⟨F, f, h⟩

/-- A nonempty scheme receives a monomorphism, locally of finite type, from the spectrum of a
field. -/
theorem exists_mono_locallyOfFiniteType_specField {X : Scheme.{u}} (x : X) :
    ∃ (k : Type u) (_ : Field k) (m : Spec (CommRingCat.of k) ⟶ X),
      Mono m ∧ LocallyOfFiniteType m := by
  set R := X.affineOpenCover.X (X.affineOpenCover.idx x) with hR
  set ι := X.affineOpenCover.f (X.affineOpenCover.idx x) with hι
  obtain ⟨y, -⟩ := X.affineOpenCover.covers x
  obtain ⟨p, hp, -⟩ := Ideal.exists_le_maximal y.asIdeal y.2.ne_top
  obtain ⟨w, hw⟩ : ∃ w : Spec R, IsClosed {w} :=
    ⟨⟨p, hp.isPrime⟩, (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hp⟩
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((Spec R).fromSpecResidueField w) :=
    isClosed_singleton_iff_isClosedImmersion.mp hw
  exact ⟨(Spec R).residueField w, inferInstance,
    (Spec R).fromSpecResidueField w ≫ ι, inferInstance, inferInstance⟩

/-- A morphism of objects of the big fppf site which is locally of finite type induces a
1-morphism of the algebraic stacks they represent which is locally of finite type. -/
theorem isLocallyOfFiniteType_schemeFibredCategoryMap {V U : BigFppfOver B S hS} (j : V ⟶ U)
    (hj : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map j)) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS j) :
        schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS U) := by
  refine (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (schemeStack.{u, w} B S hS V).property (schemeStack.{u, w} B S hS U).property _).2 ?_
  exact hasPropertyOnSomeSmoothDiagram_schemeFibredCategoryMap.{u, w} B S hS
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS) j
    ((Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget j).2 hj)

/-- An algebraic stack admitting a surjective flat 1-morphism `Spec k ⟶ 𝒵` from the spectrum of a
field admits one which is moreover locally of finite type. -/
theorem hasLocallyOfFiniteTypeFlatFieldSpectrumCover_of_hasFlatFieldSpectrumCover
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (h : HasFlatFieldSpectrumCover B S hS 𝒵) :
    HasLocallyOfFiniteTypeFlatFieldSpectrumCover B S hS 𝒵 := by
  obtain ⟨F, f, hsurj, hflat⟩ := h
  obtain ⟨U, a, haSmooth, haSurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒵
  obtain ⟨z⟩ := nonempty_points_fieldSpectrumStack.{u, w} B S hS F
  obtain ⟨zU, -⟩ := haSurj (AlgebraicStacks.pointsMap B S hS f z)
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  set X := (BigFppfOver.toScheme B S hS).obj U with hX
  have x : X := pointsHomeomorphScheme B S hS U zU
  obtain ⟨k, hk, m, hmono, hlft⟩ := exists_mono_locallyOfFiniteType_specField x
  let : Field k := hk
  have : Mono m := hmono
  have : LocallyOfFiniteType m := hlft
  have hcontains : B.Contains (Spec (CommRingCat.of k)) :=
    BigFppfSite.contains_of_mono B m U.left.2
  obtain ⟨Z, j, e, hje⟩ := Space.exists_siteObject_toScheme_map_eq B S hS hcontains m
  have hjlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map j) := by
    rw [hje]
    infer_instance
  refine ⟨{ carrier := k, base := Z, isSpec := e },
    Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS j) ≫ a, ?_, ?_, ?_⟩
  · exact AlgebraicStacks.isLocallyOfFiniteType_comp B S hS _ a
      (isLocallyOfFiniteType_schemeFibredCategoryMap.{u, w} B S hS j hjlft)
      (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a haSmooth))
  · exact isSurjective_of_fieldSpectrum_cover.{u, w} B S hS 𝒵 F _ f _ hsurj
  · exact isFlat_of_fieldSpectrum_cover.{u, w} B S hS 𝒵 F _ f _ hsurj hflat

/-- For an algebraic stack `𝒵` over `S` the following are equivalent:

1. `𝒵` is reduced and its space of points `|𝒵|` is a singleton;
2. there is a surjective flat 1-morphism `Spec k ⟶ 𝒵` with `k` a field;
3. there is a surjective flat 1-morphism `Spec k ⟶ 𝒵`, locally of finite type, with `k` a field. -/
@[stacks 06MN]
theorem tfae_isReducedWithUniquePoint (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    List.TFAE
      [IsReducedWithUniquePoint B S hS 𝒵,
        HasFlatFieldSpectrumCover B S hS 𝒵,
        HasLocallyOfFiniteTypeFlatFieldSpectrumCover B S hS 𝒵] := by
  tfae_have 1 ↔ 2 :=
    isReducedWithUniquePoint_iff_hasFlatFieldSpectrumCover.{u, w} B S hS 𝒵
  tfae_have 2 → 3 :=
    hasLocallyOfFiniteTypeFlatFieldSpectrumCover_of_hasFlatFieldSpectrumCover.{u, w} B S hS 𝒵
  tfae_have 3 → 2 :=
    hasFlatFieldSpectrumCover_of_locallyOfFiniteType.{u, w} B S hS 𝒵
  tfae_finish

/-! ### Reduced locally Noetherian algebraic stacks with a single point -/

/-- An algebraic stack over `S` is reduced, locally Noetherian, and its space of points is a
singleton. -/
abbrev IsReducedLocallyNoetherianWithUniquePoint (𝒵 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  IsReducedWithUniquePoint B S hS 𝒵 ∧ IsLocallyNoetherianStack B S hS 𝒵

/-- An algebraic stack over `S` admits a 1-morphism from the algebraic stack of the spectrum of a
field which is locally of finite presentation, surjective and flat. -/
abbrev HasLocallyOfFinitePresentationFlatFieldSpectrumCover
    (𝒵 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ (F : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵),
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f ∧
      IsSurjective B S hS f ∧ AlgebraicStacks.IsFlat B S hS f

/-- The underlying scheme of an `AlgebraicGeometry.Stack.FieldSpectrum` is locally Noetherian. -/
theorem isLocallyNoetherian_fieldSpectrum (F : FieldSpectrum B S hS) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj F.base) :=
  have : IsLocallyNoetherian (Spec (CommRingCat.of F.carrier)) := inferInstance
  isLocallyNoetherian_of_isOpenImmersion F.isSpec.hom

/-- The algebraic space represented by an `AlgebraicGeometry.Stack.FieldSpectrum` has the
étale-local scheme property of being locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_fieldSpectrum (F : FieldSpectrum B S hS) :
    Space.HasEtaleLocalProperty B S hS (yoneda.obj F.base)
      (fun X : Scheme.{u} => IsLocallyNoetherian X) :=
  (Space.exists_atlas_iff_of_representable B S hS (yoneda.obj F.base)
    (fun X : Scheme.{u} => IsLocallyNoetherian X) F.base (Iso.refl _)).mpr
      (isLocallyNoetherian_fieldSpectrum B S hS F)

/-- An algebraic stack admitting a 1-morphism from the algebraic stack of the spectrum of a field
which is locally of finite presentation, surjective and flat is locally Noetherian. -/
theorem isLocallyNoetherianStack_of_locallyOfFinitePresentationFlatFieldCover
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (F : FieldSpectrum B S hS)
    (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hsurj : IsSurjective B S hS f) (hflat : AlgebraicStacks.IsFlat B S hS f) :
    IsLocallyNoetherianStack B S hS 𝒵 := by
  obtain ⟨V, b, hbSmooth, hbSurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒵
  obtain ⟨R, hR, eR, hm, hn, hnsurj, hnlfp⟩ :=
    exists_representingMaps_of_flatFieldSpectrumCover.{u, w} B S hS hbSmooth hsurj hflat _ rfl
  have hRnoeth := Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hR
    (isAlgebraicSpace_yoneda B S hS F.base) _
    (Space.isLocallyOfFiniteType_of_isSmooth B S hS hm)
    (hasEtaleLocalProperty_isLocallyNoetherian_fieldSpectrum B S hS F)
  have hVnoeth :=
    Space.isLocallyNoetherian_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation
      B S hS hR (isAlgebraicSpace_yoneda B S hS V) _ (hnlfp hlfp) hn hnsurj hRnoeth
  exact ⟨V, b, hbSurj, hbSmooth,
    (Space.exists_atlas_iff_of_representable B S hS (yoneda.obj V)
      (fun X : Scheme.{u} => IsLocallyNoetherian X) V (Iso.refl _)).mp hVnoeth⟩

/-- An algebraic stack admitting a 1-morphism from the algebraic stack of the spectrum of a field
which is locally of finite presentation, surjective and flat is reduced, locally Noetherian, and
has a single point. -/
theorem isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h : HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒵) :
    IsReducedLocallyNoetherianWithUniquePoint B S hS 𝒵 := by
  obtain ⟨F, f, hlfp, hsurj, hflat⟩ := h
  exact ⟨isReducedWithUniquePoint_of_hasFlatFieldSpectrumCover.{u, w} B S hS 𝒵 ⟨F, f, hsurj, hflat⟩,
    isLocallyNoetherianStack_of_locallyOfFinitePresentationFlatFieldCover.{u, w}
      B S hS 𝒵 F f hlfp hsurj hflat⟩

end AlgebraicGeometry.Stack

end
