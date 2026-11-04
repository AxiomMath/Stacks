module

public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# The canonical morphism between universal first-order thickenings

A *universal first-order thickening* of a morphism `h : Z ⟶ X` is a first-order thickening
`i : Z ⟶ Z'` together with a structure morphism `h' : Z' ⟶ X` over `X`, such that every
morphism into `Z` from the closed subscheme of a first-order thickening extends uniquely,
over `X`, to the ambient scheme of that thickening.

A commutative square
```
Z --h--→ X
|        |
f        g
↓        ↓
W --h'-→ Y
```
and universal first-order thickenings `Z ⟶ Z'` of `h` and `W ⟶ W'` of `h'` then determine a
canonical morphism `Z' ⟶ W'`, namely the unique lift of `f` over `Y` along the universal
property of `W'`. This is the first assertion of Tag 04F7.

## Main definitions

* `Stacks.Thickenings.IsUniversalFirstOrderThickening` expresses the first-order and universal
  mapping properties of a thickening over a base.
* `Stacks.Thickenings.UniversalFirstOrderThickening` packages a scheme with its inclusion,
  structure morphism, and universal property.
* `Stacks.Thickenings.universalFirstOrderThickeningMap` is the canonical morphism between the
  ambient schemes of two universal first-order thickenings fitting in a commutative square.

## Main results

* `Stacks.Thickenings.UniversalFirstOrderThickening.existsUnique_map` is the unique-existence
  statement that selects the canonical morphism.
* `Stacks.Thickenings.universalFirstOrderThickeningMap_inclusion` and
  `Stacks.Thickenings.universalFirstOrderThickeningMap_toBase` give the commutative diagram:
  the canonical morphism restricts to `f` on the closed subscheme and is a morphism over `Y`.
* `Stacks.Thickenings.universalFirstOrderThickeningMap_unique` characterizes the canonical
  morphism by that diagram, so it is the unique morphism of thickenings over `Y` extending
  `f`.

## Implementation notes

The universal thickening is packaged as data rather than as an existential statement, so that
subsequent definitions can use it directly. The unique lifting property is stated for arbitrary
first-order thickenings of schemes over the target, not just affine ones, and it includes
compatibility with both the closed subscheme and the structure morphism to the base.

Everything here is stated for *given* universal first-order thickenings of the two morphisms,
rather than for a chosen one attached to a formally unramified morphism. Existence of a
universal first-order thickening for a formally unramified morphism is Tag 04F3, now proved in
`StacksFrontier.AlgebraicGeometry.Thickenings.Existence` as
`Stacks.Thickenings.nonempty_universalFirstOrderThickening`; the statements of Tag 04F7 are the
specializations of the results here at the two chosen thickenings. Stating them this way avoids
committing to a particular construction and makes the uniqueness clause apply to any model of
the universal property.

The condition `IsFirstOrderThickening` is `Stacks.Thickenings.IsFirstOrderThickening`: a closed
immersion whose kernel ideal sheaf is square-zero. Stacks 04EX asks in addition that a
first-order thickening be surjective on points; that is not dropped but derived, by
`Stacks.Thickenings.IsFirstOrderThickening.isThickening`.

The test thickenings `j : T ⟶ T'` in `existsUnique_lift` are quantified over the single
universe `u`, as are all the schemes here. This is forced rather than chosen:
`AlgebraicGeometry.Scheme` is a single-universe category, so a morphism between schemes in
different universes cannot be written at all. The predicate is therefore formally *weaker*
than the Stacks statement, which quantifies over test thickenings of any size — fewer test
objects make the universal property easier to satisfy. That matters for whoever proves
existence (Tag 04F3), and is harmless for the results proved here, where the only test
thickening ever used is the inclusion of the other universal thickening and so lives in
`Scheme.{u}` by construction. The ring-level sibling
`Algebra.Extension.IsUniversalFirstOrderThickening` in
`StacksFrontier/RingTheory/Unramified/Thickening.lean` documents the same restriction.

Neither structure carries a `@[stacks 04F3]` attribute: Tag 04F3 is the
*existence* of a universal first-order thickening for a formally unramified morphism, which
nothing in this file proves. It is proved in
`StacksFrontier.AlgebraicGeometry.Thickenings.Existence`, which carries the tag.

## References

* [Stacks Project, Tag 04F7](https://stacks.math.columbia.edu/tag/04F7)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings

/-- A first-order thickening `i : Z ⟶ Z'` over `X`, with structure morphism `h' : Z' ⟶ X`, is
**universal** for `h : Z ⟶ X` if every morphism `a : T ⟶ Z` out of the closed subscheme of a
first-order thickening `j : T ⟶ T'`, together with a morphism `b : T' ⟶ X` making the square
commute, extends uniquely to a morphism `T' ⟶ Z'` over `X`. -/
structure IsUniversalFirstOrderThickening {Z X Z' : Scheme.{u}}
    (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X) : Prop where
  /-- The defining ideal sheaf of the inclusion is square-zero. -/
  isFirstOrderThickening : IsFirstOrderThickening i
  /-- The thickening is over the specified base. -/
  inclusion_toBase : i ≫ h' = h
  /-- Every compatible morphism from a first-order thickening extends uniquely. -/
  existsUnique_lift :
    ∀ {T T' : Scheme.{u}} (j : T ⟶ T'),
      IsFirstOrderThickening j →
      ∀ (a : T ⟶ Z) (b : T' ⟶ X),
        j ≫ b = a ≫ h →
        ∃! a' : T' ⟶ Z', (j ≫ a' = a ≫ i) ∧ (a' ≫ h' = b)

/-- A universal first-order thickening of `h : Z ⟶ X`, consisting of its ambient scheme, the
closed immersion of `Z` into it, the structure morphism to `X`, and the universal property. -/
structure UniversalFirstOrderThickening {Z X : Scheme.{u}} (h : Z ⟶ X) where
  /-- The ambient scheme of the thickening. -/
  ambient : Scheme.{u}
  /-- The inclusion of the original scheme. -/
  inclusion : Z ⟶ ambient
  /-- The structure morphism to the base. -/
  toBase : ambient ⟶ X
  /-- The square-zero and universal lifting properties. -/
  isUniversal : IsUniversalFirstOrderThickening h inclusion toBase

namespace UniversalFirstOrderThickening

variable {Z X W Y : Scheme.{u}} {h : Z ⟶ X} {h' : W ⟶ Y}

/-- The ambient scheme of a universal first-order thickening is a first-order thickening of
the closed subscheme, so in particular its inclusion is a closed immersion. -/
instance isClosedImmersion_inclusion (t : UniversalFirstOrderThickening h) :
    IsClosedImmersion t.inclusion :=
  t.isUniversal.isFirstOrderThickening.1

/-- A commutative square `h ≫ g = f ≫ h'` makes the composite `tZ.toBase ≫ g` a morphism to
`Y` compatible with `f` along the inclusion of `Z`, which is the hypothesis needed to apply the
universal property of a universal first-order thickening of `h'`. -/
private theorem inclusion_comp_toBase_comp (tZ : UniversalFirstOrderThickening h)
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    tZ.inclusion ≫ (tZ.toBase ≫ g) = f ≫ h' := by
  rw [← Category.assoc, tZ.isUniversal.inclusion_toBase]
  exact comm

/-- There is a unique morphism between the ambient schemes of two universal first-order
thickenings which restricts to `f` on the closed subschemes and is compatible with the
structure morphisms over `g`. This is the unique-existence statement behind the canonical
morphism of Tag 04F7, obtained by applying the universal property of `tW` to the first-order
thickening `tZ.inclusion`. -/
@[stacks 04F7 "unique existence of the canonical morphism of thickenings"]
theorem existsUnique_map (tZ : UniversalFirstOrderThickening h)
    (tW : UniversalFirstOrderThickening h')
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    ∃! k : tZ.ambient ⟶ tW.ambient,
      (tZ.inclusion ≫ k = f ≫ tW.inclusion) ∧ (k ≫ tW.toBase = tZ.toBase ≫ g) :=
  tW.isUniversal.existsUnique_lift tZ.inclusion tZ.isUniversal.isFirstOrderThickening f
    (tZ.toBase ≫ g)
    (tZ.inclusion_comp_toBase_comp f g comm)

end UniversalFirstOrderThickening

variable {Z X W Y : Scheme.{u}} {h : Z ⟶ X} {h' : W ⟶ Y}

/-- The canonical morphism between the ambient schemes of two universal first-order thickenings
associated to a commutative square. It is selected by the unique lifting property of the target
thickening. -/
@[stacks 04F7 "the canonical morphism of thickenings"]
noncomputable def universalFirstOrderThickeningMap
    (tZ : UniversalFirstOrderThickening h) (tW : UniversalFirstOrderThickening h')
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    tZ.ambient ⟶ tW.ambient :=
  (tZ.existsUnique_map tW f g comm).exists.choose

/-- The canonical morphism restricts to `f` on the closed subscheme. -/
@[stacks 04F7 "compatibility with the inclusions"]
theorem universalFirstOrderThickeningMap_inclusion
    (tZ : UniversalFirstOrderThickening h) (tW : UniversalFirstOrderThickening h')
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    tZ.inclusion ≫ universalFirstOrderThickeningMap tZ tW f g comm = f ≫ tW.inclusion :=
  (tZ.existsUnique_map tW f g comm).exists.choose_spec.1

/-- The canonical morphism is a morphism over `Y`. -/
@[stacks 04F7 "compatibility with the base"]
theorem universalFirstOrderThickeningMap_toBase
    (tZ : UniversalFirstOrderThickening h) (tW : UniversalFirstOrderThickening h')
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    universalFirstOrderThickeningMap tZ tW f g comm ≫ tW.toBase = tZ.toBase ≫ g :=
  (tZ.existsUnique_map tW f g comm).exists.choose_spec.2

/-- The canonical morphism is the unique extension of `f` over `Y`: any morphism of the ambient
schemes restricting to `f` and compatible with the structure morphisms over `g` equals it. -/
@[stacks 04F7 "uniqueness of the canonical morphism"]
theorem universalFirstOrderThickeningMap_unique
    (tZ : UniversalFirstOrderThickening h) (tW : UniversalFirstOrderThickening h')
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h')
    (k : tZ.ambient ⟶ tW.ambient)
    (hk₁ : tZ.inclusion ≫ k = f ≫ tW.inclusion)
    (hk₂ : k ≫ tW.toBase = tZ.toBase ≫ g) :
    k = universalFirstOrderThickeningMap tZ tW f g comm :=
  ((tZ.existsUnique_map tW f g comm).unique ⟨hk₁, hk₂⟩
    ⟨universalFirstOrderThickeningMap_inclusion tZ tW f g comm,
      universalFirstOrderThickeningMap_toBase tZ tW f g comm⟩)

/-- The canonical morphism associated to an identity square is the identity. -/
theorem universalFirstOrderThickeningMap_id (tZ : UniversalFirstOrderThickening h) :
    universalFirstOrderThickeningMap tZ tZ (𝟙 Z) (𝟙 X) (by simp) = 𝟙 tZ.ambient :=
  (universalFirstOrderThickeningMap_unique tZ tZ (𝟙 Z) (𝟙 X) (by simp) (𝟙 tZ.ambient)
    (by simp) (by simp)).symm

end Stacks.Thickenings

end
