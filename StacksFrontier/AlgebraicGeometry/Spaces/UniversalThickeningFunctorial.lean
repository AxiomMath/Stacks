module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Universal

/-!
# Functoriality of the universal first-order thickening of algebraic spaces

Let

```
  Z --h--→ X
  |        |
  f        g
  ↓        ↓
  W --h'-→ Y
```

be a commutative square of algebraic spaces over a scheme `S`, let `Z ⊂ Z'` be a universal
first-order thickening of `Z` over `X`, with structure morphism `p : Z' ⟶ X`, and let `W ⊂ W'`
be a universal first-order thickening of `W` over `Y`, with structure morphism `q : W' ⟶ Y`.
This file constructs the canonical morphism `(f, f') : (Z, Z') ⟶ (W, W')` of thickenings over
`Y` of Stacks 060A, together with the commutativities of the diagram of that tag, and the map
of conormal modules `f^*𝒞_{W/Y} ⟶ 𝒞_{Z/X}` which the source deduces from it.

The construction is the one of the source: the morphism `f'` is obtained by applying the
universal property of `W ⊂ W'` to the solid diagram made of the first-order thickening
`Z ⊂ Z'`, the morphism `f : Z ⟶ W` and the morphism `Z' --p--→ X --g--→ Y`.  The solid-diagram
hypothesis of Stacks 0602 for that datum is exactly commutativity of the given square, because
the morphism `Z ⟶ X` of the source is the composite `Z ⊂ Z' --p--→ X` and likewise for
`W ⟶ Y`.  The conormal map is the map of Stacks 04CP for the resulting square of closed
immersions, which is `AlgebraicGeometry.Space.conormalMap`.

## Main definitions

* `AlgebraicGeometry.Space.universalThickeningMap`: **Stacks 060A**, the canonical morphism
  `f' : Z' ⟶ W'` of algebraic spaces.
* `AlgebraicGeometry.Space.universalThickeningHom`: the pair `(f, f')` packaged as a morphism
  `Arrow.mk Z.ι ⟶ Arrow.mk W.ι` in the arrow category.  That is a packaging of the commuting
  square, not the definition of a morphism of thickenings: the definition is Stacks 05ZK,
  parts (5) and (6), namely `AlgebraicGeometry.Space.IsMorphismOfThickenings` and, over a
  base, `AlgebraicGeometry.Space.IsMorphismOfThickeningsOver`.
* `AlgebraicGeometry.Space.universalThickeningConormalMap`: the induced map of conormal
  modules `f^*𝒞_{W/W'} ⟶ 𝒞_{Z/Z'}`, which is the map `f^*𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of the source
  since the conormal module of a formally unramified morphism is by Stacks 0607 the conormal
  module of its source in its universal first-order thickening.

## Main results

* `AlgebraicGeometry.Space.universalThickeningMap_restrict`: the canonical morphism restricts
  to `f` on `Z`, that is `Z ⊂ Z' --f'--→ W'` equals `Z --f--→ W ⊂ W'`.  This is the front face
  of the diagram of Stacks 060A, and it is what makes `(f, f')` a morphism of thickenings.
* `AlgebraicGeometry.Space.universalThickeningMap_over`: the canonical morphism lies over `Y`,
  that is `Z' --f'--→ W' --q--→ Y` equals `Z' --p--→ X --g--→ Y`.  This is what makes `(f, f')`
  a morphism of thickenings *over `Y`*.
* `AlgebraicGeometry.Space.eq_universalThickeningMap`: those two commutativities characterise
  the canonical morphism, so it is canonical: any morphism `Z' ⟶ W'` having them is it.

## Implementation notes

**The thickenings are hypotheses, and formal unramifiedness is not.** The source assumes `h`
and `h'` formally unramified and then speaks of *the* universal first-order thickenings, whose
existence is Stacks 0606.  Stacks 0606 is not available in this library — see the *What is not
proved here* section of
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalFirstOrderThickening.lean` — so the two
thickenings are taken as hypotheses, in the form of
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening`.  Nothing is lost by dropping the
formal unramifiedness of `h` and `h'`: by Stacks 0606 it is equivalent to the existence of the
universal first-order thickening which is being assumed, and the proof of the source uses it
only through that existence.  The same choice is made by
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etalePullback`, the library's form of
Stacks 0605.

**The morphisms `h` and `h'` are not separate data either.** As in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Universal.lean`, the smaller space of a
thickening is a `CategoryTheory.Subfunctor` of the bigger one, so `h` is the composite
`Z.ι ≫ p.hom` and `h'` is `W.ι ≫ q.hom`; the commutativity hypothesis `hsq` below is
`h ≫ g = f ≫ h'` written in those terms, with the left-hand side grouped as the universal
property of Stacks 0602 consumes it.  For the same reason `f` is a morphism of the underlying
functors rather than of algebraic spaces; `AlgebraicGeometry.Space.universalThickeningMap`
produces a morphism of algebraic spaces because `Z'` and `W'` are given as such.

**Why the morphism is read off the universal property and nothing else.** The universal
property of Stacks 0602 gives a *unique* dotted arrow, so the datum extracted from it is
determined by the two equations
`AlgebraicGeometry.Space.universalThickeningMap_restrict` and
`AlgebraicGeometry.Space.universalThickeningMap_over`;
`AlgebraicGeometry.Space.eq_universalThickeningMap` is that statement.  No choice is made
beyond the one the universal property already pins down.

**The conormal modules are those of the thickenings.** Stacks 0607 defines the conormal sheaf
`𝒞_{Z/X}` of a formally unramified morphism `h : Z ⟶ X` to be the conormal sheaf of `Z` in its
universal first-order thickening `Z'`; that definition is not carried in this library, so the
induced map below is stated between
`AlgebraicGeometry.Space.conormalModule`s of the closed subspaces `Z ⊂ Z'` and `W ⊂ W'`, which
is the same module under that definition.  The closed-subspace data are read off the
first-order thickening clause of the universal property, since a first-order thickening is in
particular a closed subspace.

## References

* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0605](https://stacks.math.columbia.edu/tag/0605)
* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z' W' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {W : Subfunctor W'.obj}
    {p : Z' ⟶ X} {q : W' ⟶ Y}

/-! ### The canonical morphism of universal first-order thickenings -/

/-- **Stacks 060A, the canonical morphism.** Let the square

```
  Z --h--→ X
  |        |
  f        g
  ↓        ↓
  W --h'-→ Y
```

of algebraic spaces over `S` commute, where `h = Z.ι ≫ p.hom` and `h' = W.ι ≫ q.hom`, let
`Z ⊂ Z'` be a universal first-order thickening of `Z` over `X` with structure morphism `p`,
and let `W ⊂ W'` be a universal first-order thickening of `W` over `Y` with structure morphism
`q`.  The *canonical morphism* `f' : Z' ⟶ W'` is the dotted arrow furnished by the universal
property of `W ⊂ W'`, applied to the first-order thickening `Z ⊂ Z'`, the morphism
`f : Z ⟶ W` and the morphism `p ≫ g : Z' ⟶ Y`.

Together with `f` it is the morphism `(f, f') : (Z, Z') ⟶ (W, W')` of thickenings over `Y` of
the source; see `AlgebraicGeometry.Space.universalThickeningHom`. -/
@[stacks 060A "the canonical morphism"]
noncomputable def universalThickeningMap (g : X ⟶ Y) (f : Z.toFunctor ⟶ W.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (hW : IsUniversalFirstOrderThickening B S hS W q)
    (hsq : Z.ι ≫ p.hom ≫ g.hom = f ≫ W.ι ≫ q.hom) :
    Z' ⟶ W' :=
  ObjectProperty.homMk
    (hW.existsUnique_lift Z hZ.firstOrder f (p.hom ≫ g.hom) hsq).exists.choose

/-- The canonical morphism restricts to `f` on `Z` and lies over `Y`, on the level of functors. -/
private theorem universalThickeningMap_spec (g : X ⟶ Y) (f : Z.toFunctor ⟶ W.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (hW : IsUniversalFirstOrderThickening B S hS W q)
    (hsq : Z.ι ≫ p.hom ≫ g.hom = f ≫ W.ι ≫ q.hom) :
    Z.ι ≫ (universalThickeningMap B S hS g f hZ hW hsq).hom = f ≫ W.ι ∧
      (universalThickeningMap B S hS g f hZ hW hsq).hom ≫ q.hom = p.hom ≫ g.hom :=
  (hW.existsUnique_lift Z hZ.firstOrder f (p.hom ≫ g.hom) hsq).exists.choose_spec

/-- **Stacks 060A, commutativity: the canonical morphism restricts to `f`.** The composite
`Z ⊂ Z' --f'--→ W'` is `Z --f--→ W ⊂ W'`.  This is the front face of the diagram of the source,
and it says that `(f, f')` is a morphism of the thickenings. -/
@[stacks 060A "commutativity: the canonical morphism restricts to f"]
theorem universalThickeningMap_restrict (g : X ⟶ Y) (f : Z.toFunctor ⟶ W.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (hW : IsUniversalFirstOrderThickening B S hS W q)
    (hsq : Z.ι ≫ p.hom ≫ g.hom = f ≫ W.ι ≫ q.hom) :
    Z.ι ≫ (universalThickeningMap B S hS g f hZ hW hsq).hom = f ≫ W.ι :=
  (universalThickeningMap_spec ..).1

/-- **Stacks 060A, commutativity: the canonical morphism is a morphism over `Y`.** The
composite `Z' --f'--→ W' --q--→ Y` is `Z' --p--→ X --g--→ Y`.  This is the commutativity of the
two squares of the diagram of the source which involve the base, and it says that `(f, f')` is
a morphism of thickenings *over `Y`*. -/
@[stacks 060A "commutativity: the canonical morphism lies over Y"]
theorem universalThickeningMap_over (g : X ⟶ Y) (f : Z.toFunctor ⟶ W.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (hW : IsUniversalFirstOrderThickening B S hS W q)
    (hsq : Z.ι ≫ p.hom ≫ g.hom = f ≫ W.ι ≫ q.hom) :
    universalThickeningMap B S hS g f hZ hW hsq ≫ q = p ≫ g :=
  ObjectProperty.hom_ext _
    (universalThickeningMap_spec ..).2

/-- **The canonical morphism of Stacks 060A is canonical.** A morphism `c : Z' ⟶ W'` which
restricts to `f` on `Z` and lies over `Y` is the canonical morphism: the dotted arrow of the
universal property of `W ⊂ W'` is unique. -/
theorem eq_universalThickeningMap (g : X ⟶ Y) (f : Z.toFunctor ⟶ W.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (hW : IsUniversalFirstOrderThickening B S hS W q)
    (hsq : Z.ι ≫ p.hom ≫ g.hom = f ≫ W.ι ≫ q.hom) (c : Z' ⟶ W')
    (hc : Z.ι ≫ c.hom = f ≫ W.ι) (hc' : c ≫ q = p ≫ g) :
    c = universalThickeningMap B S hS g f hZ hW hsq := by
  apply ObjectProperty.hom_ext
  exact (hW.existsUnique_lift Z hZ.firstOrder f (p.hom ≫ g.hom) hsq).unique
    ⟨hc, congrArg (·.hom) hc'⟩ (universalThickeningMap_spec ..)

/-- **Stacks 060A, the canonical morphism as a morphism of thickenings.** The pair `(f, f')`,
read as a morphism `Arrow.mk Z.ι ⟶ Arrow.mk W.ι` of the inclusions in the arrow category: a
packaging of the commuting square of
`AlgebraicGeometry.Space.universalThickeningMap_restrict`.

The arrow category records the square and nothing else; it is not the definition of a
morphism of thickenings, which is Stacks 05ZK, parts (5) and (6), namely
`AlgebraicGeometry.Space.IsMorphismOfThickenings`. That the pair is a morphism over `Y` —
the part-(6) clause on `f'` — is `AlgebraicGeometry.Space.universalThickeningMap_over`. -/
@[stacks 060A "the canonical morphism of thickenings"]
noncomputable def universalThickeningHom (g : X ⟶ Y) (f : Z.toFunctor ⟶ W.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (hW : IsUniversalFirstOrderThickening B S hS W q)
    (hsq : Z.ι ≫ p.hom ≫ g.hom = f ≫ W.ι ≫ q.hom) :
    Arrow.mk Z.ι ⟶ Arrow.mk W.ι :=
  Arrow.homMk f (universalThickeningMap B S hS g f hZ hW hsq).hom
    (universalThickeningMap_restrict B S hS g f hZ hW hsq).symm

/-! ### The induced map of conormal modules -/

/-- **Stacks 060A, the induced map of conormal modules.** The morphism `(f, f')` of thickenings
induces the map `f^*𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of the source: it is the map of Stacks 04CP,
`AlgebraicGeometry.Space.conormalMap`, for the square of closed immersions

```
  Z ⊂ Z'
  |    |
  f    f'
  ↓    ↓
  W ⊂ W'
```

whose commutativity is `AlgebraicGeometry.Space.universalThickeningMap_restrict`.

By Stacks 0607 the conormal sheaf of the formally unramified `h : Z ⟶ X` is the conormal sheaf
of `Z` in `Z'`, which is how the two spellings agree; see the implementation notes of this
file. -/
@[stacks 060A "the induced map of conormal modules"]
noncomputable def universalThickeningConormalMap (g : X ⟶ Y) (f : Z.toFunctor ⟶ W.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (hW : IsUniversalFirstOrderThickening B S hS W q)
    (hsq : Z.ι ≫ p.hom ≫ g.hom = f ≫ W.ι ≫ q.hom) :
    (modulePullback B S hS (ObjectProperty.homMk f :
          (⟨Z.toFunctor, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1.1⟩ :
            AlgebraicSpaces B S hS) ⟶
          ⟨W.toFunctor, (IsNthOrderThickening.isThickening B S hS hW.firstOrder).1.1⟩)).obj
        (conormalModule B S hS W'
          ⟨W, (IsNthOrderThickening.isThickening B S hS hW.firstOrder).1⟩) ⟶
      conormalModule B S hS Z'
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩ :=
  conormalMap B S hS ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
    ⟨W, (IsNthOrderThickening.isThickening B S hS hW.firstOrder).1⟩
    (universalThickeningMap B S hS g f hZ hW hsq) (ObjectProperty.homMk f)
    (ObjectProperty.hom_ext _ (universalThickeningMap_restrict B S hS g f hZ hW hsq))

end AlgebraicGeometry.Space

end
