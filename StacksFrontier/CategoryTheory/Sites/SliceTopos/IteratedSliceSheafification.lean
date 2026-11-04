module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Sheafification hypotheses descend the tower of slice sites

A slice of a slice is a slice: for `Y : C` and `Z : Over Y` the iterated slice equivalence
`Over.iteratedSliceEquiv Z : Over Z ≌ Over Z.left` identifies the site
`((J.over Y).over Z)` with the site `(J.over Z.left)`, one level *lower* in the tower of slice
sites. Mathlib records that this equivalence is an equivalence of sites
(`Over.iteratedSliceEquiv Z |>.inverse |>.IsDenseSubsite`), so every property of a site that
transports along an equivalence of sites descends the tower.

This file does that for the three such properties that the coherence theory of sheaves of
modules assumes at each level separately — `HasSheafify`, `HasSheafCompose` and
`GrothendieckTopology.WEqualsLocallyBijective`. The consequence is that a theorem which needs
one of them at slice depth `n + 1` needs to assume it only at depth `1`: the deeper levels are
theorems. See
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherenceSite`, where this removes six
instance hypotheses from Stacks 03L6 (7).

## Main results

* `CategoryTheory.hasSheafify_over_over`,
  `CategoryTheory.hasSheafCompose_over_over` and
  `CategoryTheory.wEqualsLocallyBijective_over_over`: **each of the three hypotheses at
  `(J.over Y).over Z` follows from the same hypothesis at `J.over Z.left`.**

## Implementation notes

**The step is stated for one object, not as a `∀` over the level.** `hasSheafify_over_over`
assumes `HasSheafify (J.over Z.left) A` for the single object `Z.left : C` under consideration,
rather than `∀ Y : C, HasSheafify (J.over Y) A`. Both forms are usable — a consumer carrying the
`∀` form discharges the single instance by synthesis — but only the one-object form iterates:
to reach depth three one applies the step with `J := J.over Y`, and the hypothesis it then
demands is a *depth-two* instance at one object, which is what the previous application
produced.

**None of the three is an `instance`.** Each is keyed on a goal of the shape
`P ((J.over Y).over Z)`, which is matched by every level of the tower above the first, so as
instances they would be tried on the way to resolving themselves. They are applied by name
instead; a consumer that wants them in scope at several depths introduces them with `have`.

**`EssSurj` of the pushforward is supplied by name** in
`wEqualsLocallyBijective_over_over`. `GrothendieckTopology.WEqualsLocallyBijective.transport`
asks for it as an instance, and Mathlib proves it only from
`IsEquivalence (Functor.sheafPushforwardContinuous ..)`, which is not itself an instance here.
For an equivalence of sites the pushforward *is* the functor of `Equivalence.sheafCongr` — both
are `ObjectProperty.lift` of precomposition with `e.inverse.op` — so the instance is the
essential surjectivity of one half of an equivalence of categories.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v u v' u' v'' u''

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A]

/-- **`HasSheafify` descends the tower of slice sites.** The iterated slice equivalence
identifies the site `(J.over Y).over Z` with the site `J.over Z.left`, which is one level
lower. -/
theorem hasSheafify_over_over {Y : C} (Z : Over Y) [HasSheafify (J.over Z.left) A] :
    HasSheafify ((J.over Y).over Z) A :=
  Equivalence.hasSheafify ((J.over Y).over Z) (J.over Z.left) Z.iteratedSliceEquiv A

/-- **`HasSheafCompose` descends the tower of slice sites.** -/
theorem hasSheafCompose_over_over {B : Type u''} [Category.{v''} B] (F : A ⥤ B) {Y : C}
    (Z : Over Y) [(J.over Z.left).HasSheafCompose F] :
    ((J.over Y).over Z).HasSheafCompose F :=
  Equivalence.hasSheafCompose ((J.over Y).over Z) (J.over Z.left) Z.iteratedSliceEquiv F

/-- **`WEqualsLocallyBijective` descends the tower of slice sites.** -/
theorem wEqualsLocallyBijective_over_over {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] {Y : C} (Z : Over Y)
    [(J.over Z.left).WEqualsLocallyBijective A] :
    ((J.over Y).over Z).WEqualsLocallyBijective A :=
  have : (Z.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A
      (J.over Z.left) ((J.over Y).over Z)).EssSurj :=
    inferInstanceAs (Functor.EssSurj (Equivalence.sheafCongr ((J.over Y).over Z)
      (J.over Z.left) Z.iteratedSliceEquiv A).functor)
  GrothendieckTopology.WEqualsLocallyBijective.transport ((J.over Y).over Z) (J.over Z.left)
    Z.iteratedSliceEquiv.inverse
    (Functor.IsDenseSubsite.coverPreserving (J.over Z.left) ((J.over Y).over Z)
      Z.iteratedSliceEquiv.inverse)

end CategoryTheory

end
