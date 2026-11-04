module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Cartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SchemeModels
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# Cartesian morphisms of finite-order thickenings of algebraic spaces

Let

```
X --f--→ Y
|        |
↓        ↓
X' -f'-→ Y'
```

be a commutative square of algebraic spaces over a scheme `S` in which `X ⊂ X'` and `Y ⊂ Y'`
are thickenings, the thickening `Y ⊂ Y'` is of finite order, and the square identifies `X`
with `Y ×_{Y'} X'`. This is the situation of Stacks 09ZZ, and the question it answers is which
properties of `f` are shared by its deformation `f'`.

For every property of morphisms of schemes which is étale local on the source and target the
answer is the scheme-level answer of Stacks 09ZW. Indeed the square has a compatible system of
surjective étale scheme charts whose lower row is the base change of the upper one: choose a
surjective étale chart `V' → Y'` of the ambient target, lift it through `f'` to a surjective
étale chart `U' → X' ×_{Y'} V'` of the ambient source, and base change both charts along the
two inclusions. The two resulting vertical maps of schemes are finite-order thickenings,
because the order of a thickening of algebraic spaces is read on étale charts, and the square
they form with the two horizontal maps is cartesian. The property therefore holds on every
étale chart of `f` exactly when it holds on every étale chart of `f'`.

Specialising to local finite type gives part (2) of Stacks 09ZZ.

## What is carried

Nothing is assumed without proof. The scheme-level invariance of the property under a
cartesian morphism of finite-order thickenings of schemes is a hypothesis of
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderMorphismOfThickenings`,
and for local finite type it is discharged by
`Stacks.Thickenings.locallyOfFiniteType_iff_of_isFiniteOrderThickening`.

## Main definitions

* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings` packages the two
  thickenings, the finite order of the target one, their morphism and the cartesian condition.

## Main results

* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.sourceFiniteOrder`: the
  source thickening is of finite order as well, by Stacks 09ZX.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderMorphismOfThickenings`
  states that a property of morphisms of schemes which is étale local on the source and target
  is invariant under such a morphism of thickenings as soon as it is invariant under every
  cartesian morphism of finite-order thickenings of schemes.
* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.isLocallyOfFiniteType_iff`:
  part (2) of Stacks 09ZZ.

## Implementation notes

**The finite-order hypothesis is on the target thickening `Y ⊂ Y'`, not on the source
`X ⊂ X'`.** The text of Stacks 09ZZ states it for the source, but the lemma it reduces to,
Stacks 09ZW, puts finite order on the target, and the proof of 09ZZ itself says "by induction
on the order of the thickening we may assume that `Y ⊂ Y'` is a first order thickening". In the
presence of the cartesian square, finite order on the target implies finite order on the
source, by Stacks 09ZX; the converse fails, so the hypothesis used here is strictly stronger
than the one the tag's text announces, and the statements below are correspondingly weaker. The
source-order version would need the target `Y'` to be replaced by the closed subspace cut out
by a power of the ideal of `Y`, which this library does not construct.

As in `AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings`, the smaller
spaces are `CategoryTheory.Subfunctor`s of the ambient ones and the morphism of thickenings is
a morphism in the arrow category of presheaves, whose `left` and `right` components are the two
horizontal maps; this avoids choosing the algebraic-space structure on the smaller spaces, which
the thickening hypotheses already provide. The cartesian condition is recorded by
`CategoryTheory.IsPullback`, so no fibre-product object is chosen.

The lower-row charts are produced by
`AlgebraicGeometry.Space.exists_finiteOrderThickening_chart_pullback`, which both base changes
the thickening along the chart and records that the resulting thickening
of schemes is of finite order; a finite-order thickening of schemes is a thickening, so no
separate descent of surjectivity on points is needed. Cartesianness of the square of charts is
proved in the presheaf category, by cancelling the cartesian lower-row chart square with
`CategoryTheory.IsPullback.of_right`; it is reflected to the site by the fully faithful Yoneda
embedding and then transported to schemes by `CategoryTheory.IsPullback.map`.

## References

* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

/-- A cartesian morphism of thickenings of algebraic spaces over `S` whose target thickening
is of finite order: the situation of Stacks 09ZZ, with the finite-order hypothesis on
`Y ⊂ Y'` rather than on `X ⊂ X'`; see the implementation notes of this file. -/
structure CartesianFiniteOrderMorphismOfThickenings
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The ambient source algebraic space `X'`. -/
  X' : AlgebraicSpaces B S hS
  /-- The ambient target algebraic space `Y'`. -/
  Y' : AlgebraicSpaces B S hS
  /-- The smaller source algebraic space `X ⊂ X'`. -/
  X : Subfunctor X'.1
  /-- The smaller target algebraic space `Y ⊂ Y'`. -/
  Y : Subfunctor Y'.1
  /-- The source inclusion is a thickening. -/
  sourceThickening : IsThickening B S hS X' X
  /-- The target inclusion is a thickening of finite order. -/
  targetFiniteOrder : IsFiniteOrderThickening B S hS Y' Y
  /-- The commutative square `(f, f')` between the two thickenings. -/
  morphism : Arrow.mk X.ι ⟶ Arrow.mk Y.ι
  /-- The square identifies `X` with `Y ×_{Y'} X'`. -/
  cartesian : IsPullback morphism.left X.ι Y.ι morphism.right

namespace CartesianFiniteOrderMorphismOfThickenings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The map `f : X ⟶ Y` between the smaller algebraic spaces. -/
abbrev f (M : CartesianFiniteOrderMorphismOfThickenings B S hS) :
    M.X.toFunctor ⟶ M.Y.toFunctor := M.morphism.left

/-- The map `f' : X' ⟶ Y'` between the ambient algebraic spaces. -/
abbrev f' (M : CartesianFiniteOrderMorphismOfThickenings B S hS) :
    M.X'.1 ⟶ M.Y'.1 := M.morphism.right

/-- The target inclusion is a thickening: a finite-order thickening is one. -/
theorem targetThickening (M : CartesianFiniteOrderMorphismOfThickenings B S hS) :
    IsThickening B S hS M.Y' M.Y :=
  M.targetFiniteOrder.choose_spec.1

/-- The ambient morphism, as a morphism of algebraic spaces. -/
abbrev ambientHom (M : CartesianFiniteOrderMorphismOfThickenings B S hS) : M.X' ⟶ M.Y' :=
  ObjectProperty.homMk M.f'

/-- The cartesian square identifies the smaller source with the inverse image of the smaller
target: the two subfunctors of `X'` are equal. -/
theorem source_eq_preimage (M : CartesianFiniteOrderMorphismOfThickenings B S hS) :
    M.X = M.Y.preimage M.f' := by
  have h : Subfunctor.range M.X.ι = (Subfunctor.range M.Y.ι).preimage M.f' := by
    ext U x
    exact Set.ext_iff.mp (Types.range_snd_of_isPullback (M.cartesian.app U)) x
  rwa [Subfunctor.range_ι, Subfunctor.range_ι] at h

/-- **Stacks 09ZX.** The source thickening of a cartesian morphism of thickenings whose target
thickening is of finite order is itself of finite order, being its inverse image. -/
theorem sourceFiniteOrder (M : CartesianFiniteOrderMorphismOfThickenings B S hS) :
    IsFiniteOrderThickening B S hS M.X' M.X :=
  M.source_eq_preimage ▸ isFiniteOrderThickening_preimage B S hS M.Y M.ambientHom
    M.targetFiniteOrder

/-- A cartesian morphism of finite-order thickenings whose two component maps are locally of
finite type is a cartesian locally-finite-type morphism of thickenings. -/
def toCartesianLocallyFiniteTypeMorphismOfThickenings
    (M : CartesianFiniteOrderMorphismOfThickenings B S hS)
    (hf : IsLocallyOfFiniteType B S hS M.f) (hf' : IsLocallyOfFiniteType B S hS M.f') :
    CartesianLocallyFiniteTypeMorphismOfThickenings B S hS where
  X' := M.X'
  Y' := M.Y'
  X := M.X
  Y := M.Y
  sourceThickening := M.sourceThickening
  targetThickening := M.targetThickening
  morphism := M.morphism
  locallyOfFiniteType_left := hf
  locallyOfFiniteType_right := hf'
  cartesian := M.cartesian

end CartesianFiniteOrderMorphismOfThickenings

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 09ZZ, the étale-local cases.** A property of morphisms of schemes which is étale
local on the source and target holds on every étale chart of the morphism of smaller spaces of a
cartesian morphism of finite-order thickenings of algebraic spaces exactly when it holds on
every étale chart of the morphism of ambient spaces, as soon as it is invariant under every
cartesian morphism of finite-order thickenings of schemes.

This is the reduction of Stacks 09ZZ to Stacks 09ZW; the hypothesis `hSchemes` is 09ZW-shaped,
with the finite-order condition on both vertical maps of the square of schemes. -/
theorem holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderMorphismOfThickenings
    (M : CartesianFiniteOrderMorphismOfThickenings B S hS) (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hSchemes : ∀ {U U' V V' : Scheme.{u}} (iU : U ⟶ U') (iV : V ⟶ V')
      (g : U ⟶ V) (g' : U' ⟶ V'), Stacks.Thickenings.IsFiniteOrderThickening iU →
      Stacks.Thickenings.IsFiniteOrderThickening iV → IsPullback iU g g' iV → (P g ↔ P g')) :
    HoldsOnEveryEtaleChart B S hS P M.f ↔ HoldsOnEveryEtaleChart B S hS P M.f' := by
  let F := BigFppfOver.toScheme B S hS
  let Psurjective :=
    MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) F
  let Petale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F
  have : Psurjective.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have : Petale.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  have : Psurjective.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Psurjective
  have : Petale.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Petale
  -- A surjective étale chart of the ambient target, and one of the ambient source over it.
  obtain ⟨V', v', hv'_surjective, hv'_etale⟩ := M.Y'.property.exists_atlas
  obtain ⟨U', uambient, g', hambientComm, huambient_surjective, huambient_etale⟩ :=
    exists_surjective_etale_presentation_lift B S hS M.X'.property M.Y'.property M.f' V' v'
      hv'_surjective hv'_etale
  -- The two lower-row charts, as base changes of the two inclusions, with their orders.
  obtain ⟨V, iV, v, target_pullback, hiV⟩ :=
    exists_finiteOrderThickening_chart_pullback B S hS M.targetFiniteOrder V' v' hv'_etale
  obtain ⟨U, iU, u, source_pullback, hiU⟩ :=
    exists_finiteOrderThickening_chart_pullback B S hS M.sourceFiniteOrder U' uambient
      huambient_etale
  have hv_etale : Petale.presheaf v :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback target_pullback.flip hv'_etale
  have hu_etale : Petale.presheaf u :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback source_pullback.flip huambient_etale
  have hu_surjective : Psurjective.presheaf u :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback source_pullback.flip
      huambient_surjective
  have hmor : M.f ≫ M.Y.ι = M.X.ι ≫ M.f' := M.morphism.w
  have hcomp : (u ≫ M.f) ≫ M.Y.ι = yoneda.map (iU ≫ g') ≫ v' := by
    rw [Category.assoc, hmor, ← Category.assoc, source_pullback.w]
    simp [hambientComm]
  let g := yoneda.preimage (target_pullback.lift (u ≫ M.f) (yoneda.map (iU ≫ g')) hcomp)
  have small_compat : u ≫ M.f = yoneda.map g ≫ v := by simp [g]
  have hsq : yoneda.map g ≫ yoneda.map iV = yoneda.map iU ≫ yoneda.map g' := by simp [g]
  -- Cartesianness of the square of charts, proved in the presheaf category.
  have hFinalSite : IsPullback g iU iV g' :=
    IsPullback.of_map yoneda (yoneda.map_injective (by simpa using hsq)) <|
      IsPullback.of_right (by
        rw [← small_compat, ← hambientComm]
        exact IsPullback.paste_horiz source_pullback M.cartesian) hsq target_pullback
  -- The resulting cartesian morphism of finite-order thickenings of schemes.
  have hscheme : P (F.map g) ↔ P (F.map g') :=
    hSchemes (F.map iU) (F.map iV) (F.map g) (F.map g') hiU hiV
      ((IsPullback.map F hFinalSite).flip)
  have hsmall : HoldsOnEveryEtaleChart B S hS P M.f ↔ P (F.map g) := by
    refine ⟨fun h => h U V u v g hu_etale hv_etale small_compat.symm, fun hp => ?_⟩
    refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP M.sourceThickening.1.1
      M.targetThickening.1.1 M.f).mpr ?_
    exact ⟨U, V, u, v, g, hu_etale, hv_etale, hu_surjective, small_compat.symm, hp⟩
  have hambient : HoldsOnEveryEtaleChart B S hS P M.f' ↔ P (F.map g') := by
    refine ⟨fun h => h U' V' uambient v' g' huambient_etale hv'_etale hambientComm.symm,
      fun hp => ?_⟩
    refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP M.X'.property
      M.Y'.property M.f').mpr ?_
    exact ⟨U', V', uambient, v', g', huambient_etale, hv'_etale, huambient_surjective,
      hambientComm.symm, hp⟩
  exact hsmall.trans (hscheme.trans hambient.symm)

namespace CartesianFiniteOrderMorphismOfThickenings

variable {B S hS}

/-- **Stacks 09ZZ, part (2).** Local finite type is invariant under a cartesian morphism of
thickenings of algebraic spaces whose target thickening is of finite order: the map between the
smaller spaces is locally of finite type exactly when the map between the ambient spaces is.

The hypothesis is the finite order of the target thickening `Y ⊂ Y'`, which is stronger than
the finite order of the source thickening `X ⊂ X'` that the tag's text states; see the
implementation notes of this file. -/
@[stacks 09ZZ "part (2), locally of finite type; the finite-order hypothesis is on the TARGET \
thickening Y ⊆ Y', which is strictly stronger than the source hypothesis X ⊆ X' in the tag's \
text, so this is a weaker theorem than the tag announces. It is the hypothesis the tag's own \
proof uses: it reduces to Tag 09ZW, which puts finite order on the target, and says 'by \
induction on the order of the thickening we may assume that Y ⊆ Y' is a first order \
thickening'. Cartesianness plus target finite order gives source finite order by Tag 09ZX, \
but not conversely"]
theorem isLocallyOfFiniteType_iff (M : CartesianFiniteOrderMorphismOfThickenings B S hS) :
    IsLocallyOfFiniteType B S hS M.f ↔ IsLocallyOfFiniteType B S hS M.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderMorphismOfThickenings B S hS M
    (@LocallyOfFiniteType.{u}) LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    fun iU iV g g' _ hiV hcart =>
      Stacks.Thickenings.locallyOfFiniteType_iff_of_isFiniteOrderThickening iU iV g g' hiV hcart

end CartesianFiniteOrderMorphismOfThickenings

end AlgebraicGeometry.Space

end
