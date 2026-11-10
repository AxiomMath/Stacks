module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SchemeModels
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms

/-!
# A cartesian morphism of thickenings presented by two morphisms of algebraic spaces

`AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings` presents the square

```
X --f--→ Y
|        |
i        j
↓        ↓
X' -f'-→ Y'
```

of Stacks 0BPJ by giving the two smaller spaces as *subfunctors* of the two ambient ones, as
Stacks 05ZK part (1) defines a thickening. The conditions of Stacks 04XB on a 1-morphism of
categories fibred in groupoids are instead stated at a
`CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpaces B S hS)`, applied to a
morphism of the *category* of algebraic spaces over `S`; so a square whose four spaces are
objects of that category and whose two vertical maps are thickenings in the morphism sense of
`AlgebraicGeometry.Space.IsThickeningHom` is the shape in which Stacks 0BPJ can be fed to the
point test of Stacks 03YK.

This module converts the second presentation into the first. The range of a thickening
`i : X ⟶ X'` is a thickening subspace of `X'` and `i` is an isomorphism onto it, so the square
of morphisms of algebraic spaces becomes a square of subfunctor inclusions after composing the
two horizontal maps with those two isomorphisms, and the étale-chart condition of Stacks 03MJ
through which every property here is expressed is invariant under that composition.

## Main definitions

* `AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings.ofIsThickeningHom`:
  the cartesian morphism of thickenings of a cartesian square of morphisms of algebraic spaces
  whose two vertical maps are thickenings and whose two horizontal maps are locally of finite
  type.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_cartesianSquareOfThickeningHoms`: a
  property of morphisms of schemes which is étale local on the source and target is invariant
  across such a square as soon as it is invariant across every cartesian, locally finite type
  morphism of thickenings of schemes.
* `AlgebraicGeometry.Space.isThickeningHom_sourceι` and
  `AlgebraicGeometry.Space.isThickeningHom_targetι`: the converse passage, reading the two
  subfunctor inclusions of a cartesian morphism of thickenings as thickenings in the morphism
  sense. With the `isPullback_spaces` field accessor of
  `AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings` these turn a
  statement about such a square back into one about the structure.

## Implementation notes

The two isomorphisms onto the ranges are the content of
`AlgebraicGeometry.Space.IsThickeningHom`, whose first clause is exactly
`IsIso (CategoryTheory.Subfunctor.toRange i.hom)`; no new geometry is needed, and in particular
the fact that the range of a closed immersion of algebraic spaces is again an algebraic space —
which this library does not have — is not used, since the subfunctor presentation never asks
for it.

Invariance of the chart condition under pre- and post-composition with an isomorphism of
presheaves is `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso_presheaf`, read
through `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`. It is used twice: once to carry the
local-finite-type hypothesis on the smaller horizontal map into the field of the structure, and
once to carry the conclusion back.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' Y Y' : AlgebraicSpaces B S hS} {i : X ⟶ X'} {j : Y ⟶ Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The isomorphism of a thickening of algebraic spaces onto its range. -/
noncomputable def IsThickeningHom.isoRange (hi : IsThickeningHom B S hS i) :
    X.1 ≅ (Subfunctor.range i.hom).toFunctor :=
  have := hi.1
  asIso (Subfunctor.toRange i.hom)

/-- The isomorphism of a thickening onto its range, followed by the inclusion of the range, is
the thickening itself. -/
@[simp]
theorem IsThickeningHom.isoRange_hom_ι (hi : IsThickeningHom B S hS i) :
    hi.isoRange.hom ≫ (Subfunctor.range i.hom).ι = i.hom :=
  Subfunctor.toRange_ι i.hom

/-- The map between the two ranges induced by a commuting square of morphisms of algebraic
spaces whose two vertical maps are thickenings. -/
noncomputable def rangeMap (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j)
    (f : X ⟶ Y) :
    (Subfunctor.range i.hom).toFunctor ⟶ (Subfunctor.range j.hom).toFunctor :=
  hi.isoRange.inv ≫ f.hom ≫ hj.isoRange.hom

/-- The commuting square of a morphism of thickenings of algebraic spaces, read at the two
ranges. -/
theorem rangeMap_comp_ι (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j)
    (hw : f.hom ≫ j.hom = i.hom ≫ f'.hom) :
    rangeMap hi hj f ≫ (Subfunctor.range j.hom).ι =
      (Subfunctor.range i.hom).ι ≫ f'.hom := by
  have hιi : (Subfunctor.range i.hom).ι = hi.isoRange.inv ≫ i.hom :=
    (Iso.eq_inv_comp _).mpr (IsThickeningHom.isoRange_hom_ι hi)
  rw [rangeMap, hιi, Category.assoc, Category.assoc, IsThickeningHom.isoRange_hom_ι, hw,
    Category.assoc]

/-- The induced map between the two ranges is the original map, up to the two isomorphisms onto
the ranges. -/
noncomputable def rangeMapArrowIso (hi : IsThickeningHom B S hS i)
    (hj : IsThickeningHom B S hS j) (f : X ⟶ Y) :
    Arrow.mk f.hom ≅ Arrow.mk (rangeMap hi hj f) :=
  Arrow.isoMk hi.isoRange hj.isoRange (by simp [rangeMap])

/-- A property of morphisms of presheaves which respects isomorphisms holds of a map of
algebraic spaces exactly when it holds of the induced map between the two ranges. -/
theorem rangeMap_iff {R : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hR : R.RespectsIso) (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j)
    (f : X ⟶ Y) :
    R f.hom ↔ R (rangeMap hi hj f) :=
  have := hR
  MorphismProperty.arrow_mk_iso_iff R (rangeMapArrowIso hi hj f)

/-- A property of morphisms of schemes holds on every étale chart of a map of algebraic spaces
exactly when it holds on every étale chart of the induced map between the two ranges. -/
theorem holdsOnEveryEtaleChart_rangeMap_iff (P : MorphismProperty Scheme.{u})
    (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j) (f : X ⟶ Y) :
    HoldsOnEveryEtaleChart B S hS P f.hom ↔
      HoldsOnEveryEtaleChart B S hS P (rangeMap hi hj f) :=
  rangeMap_iff (holdsOnEveryEtaleChart_respectsIso_presheaf B S hS P) hi hj f

namespace CartesianLocallyFiniteTypeMorphismOfThickenings

/-- **The square of Stacks 0BPJ, read at morphisms of the category of algebraic spaces.** A
cartesian square of morphisms of algebraic spaces over `S` whose two vertical maps are
thickenings and whose two horizontal maps are locally of finite type is a cartesian,
locally-finite-type morphism of thickenings of algebraic spaces. -/
noncomputable def ofIsThickeningHom (hi : IsThickeningHom B S hS i)
    (hj : IsThickeningHom B S hS j) (hsq : IsPullback f i j f')
    (hft : IsLocallyOfFiniteType B S hS f.hom) (hft' : IsLocallyOfFiniteType B S hS f'.hom) :
    CartesianLocallyFiniteTypeMorphismOfThickenings B S hS where
  X' := X'
  Y' := Y'
  X := Subfunctor.range i.hom
  Y := Subfunctor.range j.hom
  sourceThickening := hi.2
  targetThickening := hj.2
  morphism :=
    Arrow.homMk (rangeMap hi hj f) f'.hom
      (rangeMap_comp_ι hi hj (congrArg (fun k => k.hom) hsq.w))
  locallyOfFiniteType_left :=
    (holdsOnEveryEtaleChart_rangeMap_iff _ hi hj f).mp hft
  locallyOfFiniteType_right := hft'
  cartesian := by
    refine (AlgebraicSpaces.isPullback_hom B S hS hsq).of_iso hi.isoRange hj.isoRange
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [rangeMap]
    · simp
    · simp
    · simp

variable (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS)

/-- A thickening subspace, read as a morphism of the category of algebraic spaces over `S`, is
a thickening in the sense of `AlgebraicGeometry.Space.IsThickeningHom`: a subfunctor inclusion
is a monomorphism, and its range is the subfunctor itself. -/
theorem isThickeningHom_homMk_ι {Z : AlgebraicSpaces B S hS} {G : Subfunctor Z.1}
    (hG : IsThickening B S hS Z G) :
    IsThickeningHom B S hS
      (ObjectProperty.homMk G.ι : (⟨G.toFunctor, hG.1.1⟩ : AlgebraicSpaces B S hS) ⟶ Z) := by
  refine ⟨?_, ?_⟩
  · rw [ObjectProperty.homMk_hom]
    infer_instance
  · change IsThickening B S hS Z (Subfunctor.range G.ι)
    rwa [Subfunctor.range_ι]

/-- The source inclusion of a cartesian morphism of thickenings is a thickening in the morphism
sense of `AlgebraicGeometry.Space.IsThickeningHom`. -/
theorem isThickeningHom_sourceι :
    IsThickeningHom B S hS (ObjectProperty.homMk T.X.ι : T.sourceSpace ⟶ T.X') :=
  isThickeningHom_homMk_ι T.sourceThickening

/-- The target inclusion of a cartesian morphism of thickenings is a thickening in the morphism
sense of `AlgebraicGeometry.Space.IsThickeningHom`. -/
theorem isThickeningHom_targetι :
    IsThickeningHom B S hS (ObjectProperty.homMk T.Y.ι : T.targetSpace ⟶ T.Y') :=
  isThickeningHom_homMk_ι T.targetThickening

end CartesianLocallyFiniteTypeMorphismOfThickenings

/-- **Stacks 0BPJ, reduced to the morphism of thickenings of schemes, at a square of morphisms
of the category of algebraic spaces.** A property of morphisms of schemes which is étale local
on the source and target is invariant across a cartesian square of morphisms of algebraic
spaces whose two vertical maps are thickenings and whose two horizontal maps are locally of
finite type, as soon as it is invariant across every cartesian, locally finite type morphism of
thickenings of schemes. -/
theorem holdsOnEveryEtaleChart_iff_of_cartesianSquareOfThickeningHoms
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    (hSchemes : ∀ E : Stacks.Thickenings.CartesianFiniteTypeMorphism.{u}, P E.f ↔ P E.f')
    (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j) (hsq : IsPullback f i j f')
    (hft : IsLocallyOfFiniteType B S hS f.hom) (hft' : IsLocallyOfFiniteType B S hS f'.hom) :
    HoldsOnEveryEtaleChart B S hS P f.hom ↔ HoldsOnEveryEtaleChart B S hS P f'.hom :=
  (holdsOnEveryEtaleChart_rangeMap_iff P hi hj f).trans
    (holdsOnEveryEtaleChart_iff_of_cartesianMorphismOfThickenings B S hS
      (CartesianLocallyFiniteTypeMorphismOfThickenings.ofIsThickeningHom hi hj hsq hft hft')
      P hP hSchemes)

end AlgebraicGeometry.Space

end
