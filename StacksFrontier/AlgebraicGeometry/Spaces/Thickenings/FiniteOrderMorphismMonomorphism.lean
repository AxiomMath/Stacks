module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismImmersions

/-!
# Monomorphy across a cartesian morphism of finite-order thickenings of algebraic spaces

Let

```
X --f--→ Y
|        |
↓        ↓
X' -f'-→ Y'
```

be a commutative square of algebraic spaces over a scheme `S` in which `X ⊂ X'` and `Y ⊂ Y'`
are thickenings, the thickening `Y ⊂ Y'` is of finite order, and the square identifies `X` with
`Y ×_{Y'} X'`; that is, let it be a
`AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings`. This file proves part (9)
of Stacks 09ZZ: `f` is a monomorphism exactly when `f'` is.

One direction needs nothing but the cartesian square: `f` is a base change of `f'`, and a base
change of a monomorphism is a monomorphism.

The other direction is the content of the clause. A morphism is a monomorphism exactly when the
first projection of its self-fibre-product is an isomorphism, so it suffices to show that
`pullback.fst f' f'` is an isomorphism. That projection sits in a *new* cartesian morphism of
finite-order thickenings, obtained from the given one by pulling the source thickening
`X ⊆ X'` back along `pullback.fst f' f'`:

```
X ×_{X'} (X' ×_{Y'} X') --→ X
|                           |
↓                           ↓
X' ×_{Y'} X' ------fst-----→ X'
```

Its target thickening is `X ⊆ X'`, which is of finite order by Stacks 09ZX, and its two
vertical maps are thickenings because an inverse image of a thickening is one. Its morphism of
smaller spaces sends a pair `(a, b)` of sections of `X'` with `f'(a) = f'(b)` and `a` a section
of `X` to `a`; monomorphy of `f` makes that map an *isomorphism*, the inverse being the
diagonal, because `a` being a section of `X` forces `b` to be one as well — the square
identifies `X` with the inverse image of `Y` — and then `f(a) = f(b)` forces `a = b`. An
isomorphism of presheaves is a closed immersion, so part (1) of this tag, already proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/FiniteOrderMorphismImmersions.lean`, makes
`pullback.fst f' f'` a closed immersion, hence a monomorphism. It is also a split epimorphism,
retracted by the diagonal of `f'`, and a monomorphism which is a split epimorphism is an
isomorphism. Monomorphy of `f'` is then read off the kernel-pair square.

## What is carried

Nothing is assumed without proof, and no step routes back through this clause. The only input
from Stacks 09ZZ is part (1), `isClosedImmersion_iff`, whose proof goes through the universally
closed, unramified, universally injective characterisation of Stacks 05W8 — entry (3) of the
`AlgebraicGeometry.Space.closedImmersion_conditions_tfae` list — and not through the entry
which characterises a closed immersion as a universally closed monomorphism locally of finite
type. Using that entry to produce monomorphy of `f'` would be circular with the statement
proved here, and it is not used.

**Why the proof of the source is not followed.** Stacks 09ZZ proves part (9) by comparing the
conormal sheaf of the diagonal of `f` with that of the diagonal of `f'`, which rests on the
spaces analogue of Stacks 08S2, the identification of the sheaf of relative differentials with
the conormal sheaf of the diagonal. The spaces analogue is **not** available in this library:
Stacks 08S2 is proved for schemes by
`Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal`, and nothing transports it
to algebraic spaces. The route taken here uses no differentials and no conormal sheaf at all.

## Main results

* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.firstProjection`: the
  derived cartesian morphism of finite-order thickenings whose ambient map is the first
  projection of `X' ×_{Y'} X'`.
* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.mono_pullback_fst`: if `f`
  is a monomorphism then `pullback.fst f' f'` is one.
* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.mono_iff`: part (9) of
  Stacks 09ZZ.

## Implementation notes

**The finite-order hypothesis is on the target thickening `Y ⊂ Y'`, not on the source
`X ⊂ X'`.** This is the convention of the frame file
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/CartesianFiniteOrderMorphism.lean`, whose
implementation notes explain it: the tag's text puts finite order on the source, but the lemma
it reduces to, Stacks 09ZW, puts it on the target, and the tag's own proof argues by induction
on the order of the thickening `Y ⊂ Y'`. In the presence of the cartesian square target finite
order implies source finite order, by Stacks 09ZX, but not conversely, so the statement below
is weaker than the tag's text announces. The clause string of the theorem says so.

The derived diagram is built with no choice of fibre-product object for its smaller source: the
inverse image of a subfunctor along a morphism of presheaves is Mathlib's
`CategoryTheory.Subfunctor.preimage`, a subfunctor on the nose, and its cartesian square is
`CategoryTheory.Subfunctor.isPullback_preimage`, which is Stacks 083Q. Its morphism of smaller
spaces is therefore literally `CategoryTheory.Subfunctor.fromPreimage`, and the statements
below are about that map rather than about a comparison morphism.

Everything happens in the category of presheaves on the big fppf site of `S`; the properties
`AlgebraicGeometry.Space.IsClosedImmersion` and `CategoryTheory.Mono` are both properties of
morphisms of presheaves, so no passage to the category of algebraic spaces is needed and
`AlgebraicGeometry.Space.mono_hom_iff_mono` is not used.

## References

* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 05W8](https://stacks.math.columbia.edu/tag/05W8)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 042M](https://stacks.math.columbia.edu/tag/042M)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (M : CartesianFiniteOrderMorphismOfThickenings B S hS)

/-! ### The self-fibre-product of the ambient morphism -/

/-- The self-fibre-product `X' ×_{Y'} X'` of the ambient morphism is an algebraic space over
`S`, by Stacks 02X2. -/
theorem isAlgebraicSpace_selfPullback : IsAlgebraicSpace B S hS (pullback M.f' M.f') :=
  isAlgebraicSpace_pullback B S hS M.f' M.f' M.X'.2 M.X'.2 M.Y'.2

/-- The self-fibre-product `X' ×_{Y'} X'` of the ambient morphism, as an algebraic space
over `S`. -/
abbrev selfPullbackSpace : AlgebraicSpaces B S hS :=
  ⟨pullback M.f' M.f', M.isAlgebraicSpace_selfPullback⟩

/-- The first projection `X' ×_{Y'} X' ⟶ X'`, as a morphism of algebraic spaces over `S`. -/
abbrev selfPullbackFst : M.selfPullbackSpace ⟶ M.X' :=
  ObjectProperty.homMk (pullback.fst M.f' M.f')

/-- The inverse image of the smaller source `X ⊆ X'` along the first projection of
`X' ×_{Y'} X'`: the smaller source of the derived diagram. -/
abbrev preimageFst : Subfunctor M.selfPullbackSpace.1 :=
  M.X.preimage (pullback.fst M.f' M.f')

/-- **Stacks 09ZX.** The inverse image of the source thickening along the first projection of
`X' ×_{Y'} X'` is a thickening: the source thickening is of finite order, and an inverse image
of a finite-order thickening is a finite-order thickening, hence a thickening. -/
theorem isThickening_preimageFst :
    IsThickening B S hS M.selfPullbackSpace M.preimageFst :=
  (isFiniteOrderThickening_preimage B S hS M.X M.selfPullbackFst
    M.sourceFiniteOrder).choose_spec.1

/-! ### The derived cartesian morphism of finite-order thickenings -/

/-- The cartesian morphism of finite-order thickenings derived from `M` by pulling the source
thickening `X ⊆ X'` back along the first projection of `X' ×_{Y'} X'`:

```
X ×_{X'} (X' ×_{Y'} X') --→ X
|                           |
↓                           ↓
X' ×_{Y'} X' ------fst-----→ X'
```

Its target thickening is the source thickening of `M`, of finite order by Stacks 09ZX; its
source thickening is the inverse image of that one; its ambient morphism is the first
projection `pullback.fst f' f'`; and its morphism of smaller spaces is the canonical map
`CategoryTheory.Subfunctor.fromPreimage` out of the inverse image. Cartesianness is Stacks
083Q, the identification of an inverse image with a fibre product. -/
def firstProjection : CartesianFiniteOrderMorphismOfThickenings B S hS where
  X' := M.selfPullbackSpace
  Y' := M.X'
  X := M.preimageFst
  Y := M.X
  sourceThickening := M.isThickening_preimageFst
  targetFiniteOrder := M.sourceFiniteOrder
  morphism := Arrow.homMk (M.X.fromPreimage (pullback.fst M.f' M.f'))
    (pullback.fst M.f' M.f') (Subfunctor.fromPreimage_ι M.X _)
  cartesian := Subfunctor.isPullback_preimage (pullback.fst M.f' M.f') M.X

/-- The morphism of smaller spaces of the derived diagram is the canonical map out of the
inverse image of `X` along the first projection of `X' ×_{Y'} X'`. -/
theorem firstProjection_f :
    M.firstProjection.f = M.X.fromPreimage (pullback.fst M.f' M.f') := rfl

/-- The ambient morphism of the derived diagram is the first projection of `X' ×_{Y'} X'`. -/
theorem firstProjection_f' : M.firstProjection.f' = pullback.fst M.f' M.f' := rfl

/-! ### The diagonal section of the derived morphism of smaller spaces -/

/-- The diagonal of `f'` restricted to `X` lands in the inverse image of `X` along the first
projection, because the first projection undoes the diagonal. -/
theorem range_le_preimageFst :
    Subfunctor.range (M.X.ι ≫ pullback.diagonal M.f') ≤ M.preimageFst := by
  rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp,
    show (M.X.ι ≫ pullback.diagonal M.f') ≫ pullback.fst M.f' M.f' = M.X.ι by simp]
  exact (Subfunctor.range_ι M.X).le

/-- The diagonal of `f'` read as a map from `X` into the inverse image of `X` along the first
projection of `X' ×_{Y'} X'`, that is into the smaller source of the derived diagram. -/
def diagonalSection : M.X.toFunctor ⟶ M.preimageFst.toFunctor :=
  Subfunctor.lift (M.X.ι ≫ pullback.diagonal M.f') M.range_le_preimageFst

/-- The diagonal section followed by the inclusion of the inverse image of `X` into
`X' ×_{Y'} X'` is the inclusion of `X` into `X'` followed by the diagonal of `f'`. -/
@[simp]
theorem diagonalSection_ι :
    M.diagonalSection ≫ M.preimageFst.ι = M.X.ι ≫ pullback.diagonal M.f' :=
  Subfunctor.lift_ι _ _

/-- The diagonal section is a section of the derived morphism of smaller spaces: composing it
with the projection to `X` gives the identity. This needs no hypothesis. -/
theorem diagonalSection_comp_fromPreimage :
    M.diagonalSection ≫ M.X.fromPreimage (pullback.fst M.f' M.f') = 𝟙 M.X.toFunctor := by
  refine (cancel_mono M.X.ι).mp ?_
  rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, M.diagonalSection_ι]
  simp

/-! ### Monomorphy of the ambient morphism -/

/-- If `f` is a monomorphism then the two projections of `X' ×_{Y'} X'` agree on the inverse
image of `X` along the first one.

A section of that inverse image is a pair `(a, b)` of sections of `X'` with `f'(a) = f'(b)` and
`a` a section of `X`. The cartesian square identifies `X` with the inverse image of `Y` in
`X'`, so the common value `f'(a) = f'(b)` being a section of `Y` exhibits `b` as a second
factorisation of the pair through `X`, with the same image under `f`; monomorphy of `f` then
identifies it with the first. -/
theorem preimageFst_ι_fst_eq_snd (hf : Mono M.f) :
    M.preimageFst.ι ≫ pullback.fst M.f' M.f' =
      M.preimageFst.ι ≫ pullback.snd M.f' M.f' := by
  have hw : M.f ≫ M.Y.ι = M.X.ι ≫ M.f' := M.morphism.w
  have hcond : (M.X.fromPreimage (pullback.fst M.f' M.f') ≫ M.f) ≫ M.Y.ι =
      (M.preimageFst.ι ≫ pullback.snd M.f' M.f') ≫ M.f' := by
    rw [Category.assoc, hw, Subfunctor.fromPreimage_ι_assoc, pullback.condition, Category.assoc]
  rw [← M.cartesian.lift_snd _ _ hcond, (cancel_mono M.f).mp (M.cartesian.lift_fst _ _ hcond),
    Subfunctor.fromPreimage_ι]

/-- If `f` is a monomorphism then the derived morphism of smaller spaces is an isomorphism, the
inverse being the diagonal section. -/
theorem isIso_fromPreimage_fst (hf : Mono M.f) :
    IsIso (M.X.fromPreimage (pullback.fst M.f' M.f')) := by
  refine ⟨M.diagonalSection, ?_, M.diagonalSection_comp_fromPreimage⟩
  refine (cancel_mono M.preimageFst.ι).mp ?_
  rw [Category.assoc, M.diagonalSection_ι, ← Category.assoc, Subfunctor.fromPreimage_ι,
    Category.id_comp]
  refine pullback.hom_ext ?_ ?_
  · simp
  · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id]
    exact M.preimageFst_ι_fst_eq_snd hf

/-- If `f` is a monomorphism then the first projection of `X' ×_{Y'} X'` is a monomorphism.

The derived diagram `firstProjection` is a cartesian morphism of finite-order thickenings whose
morphism of smaller spaces is an isomorphism, hence a closed immersion; part (1) of Stacks 09ZZ
transfers that to its ambient morphism, which is the first projection, and a closed immersion
of algebraic spaces is a monomorphism by Stacks 04CH. -/
theorem mono_pullback_fst (hf : Mono M.f) : Mono (pullback.fst M.f' M.f') := by
  have := M.isIso_fromPreimage_fst hf
  refine mono_of_isClosedImmersion B S hS _ (M.firstProjection.isClosedImmersion_iff.mp ?_)
  show IsClosedImmersion B S hS (M.X.fromPreimage (pullback.fst M.f' M.f'))
  exact isClosedImmersion_of_isIso B S hS _

/-- **Stacks 09ZZ, part (9).** Being a monomorphism is invariant under a cartesian morphism of
thickenings of algebraic spaces whose target thickening is of finite order: the map between the
smaller spaces is a monomorphism exactly when the map between the ambient spaces is.

The implication from the ambient morphism to the morphism of smaller spaces is base change
along the cartesian square. In the other direction, the first projection of `X' ×_{Y'} X'` is a
monomorphism by `mono_pullback_fst` and a split epimorphism retracted by the diagonal of `f'`,
hence an isomorphism, and a morphism whose kernel pair has invertible first projection is a
monomorphism. -/
@[stacks 09ZZ "part (9), monomorphism; the finite-order hypothesis is on the TARGET \
thickening Y ⊆ Y', which is strictly stronger than the source hypothesis X ⊆ X' in the tag's \
text, so this is a weaker theorem than the tag announces. It is the hypothesis the tag's own \
proof uses: it reduces to Tag 09ZW, which puts finite order on the target, and says 'by \
induction on the order of the thickening we may assume that Y ⊆ Y' is a first order \
thickening'. Cartesianness plus target finite order gives source finite order by Tag 09ZX, \
but not conversely"]
theorem mono_iff : Mono M.f ↔ Mono M.f' := by
  refine ⟨fun hf => ?_, fun _ => M.cartesian.mono_fst_of_mono⟩
  have := M.mono_pullback_fst hf
  have : IsSplitEpi (pullback.fst M.f' M.f') :=
    IsSplitEpi.mk' ⟨pullback.diagonal M.f', pullback.diagonal_fst M.f'⟩
  have : IsIso (pullback.fst M.f' M.f') := isIso_of_mono_of_isSplitEpi _
  exact IsKernelPair.mono_of_isIso_fst (IsPullback.of_hasPullback M.f' M.f')

end AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings

end
