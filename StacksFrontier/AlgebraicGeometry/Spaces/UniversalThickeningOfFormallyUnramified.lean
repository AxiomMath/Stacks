module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Universal

/-!
# The universal first-order thickening of a formally unramified morphism of algebraic spaces

Let `S` be a scheme and let `h : Z ⟶ X` be a formally unramified morphism of algebraic spaces
over `S`.  Stacks 0607 names two things:

1. the *universal first order thickening of `Z` over `X`* is the thickening `Z ⊂ Z'`
   constructed in Stacks 0606;
2. the *conormal sheaf of `Z` over `X`* is the conormal sheaf of `Z` in that universal first
   order thickening `Z'` over `X`, in the sense of Stacks 04CN.

The source writes the conormal sheaf of part (2) as `𝒞_{Z/X}`; that is the sheaf
`AlgebraicGeometry.Space.conormalSheaf` below realizes, and it is the same notation the source
uses in Stacks 04CN for the conormal sheaf of an immersion, which is why no new notation is
declared here — see the implementation notes.

The file also carries the argument of the neighbouring Stacks 0609, which asserts that the
ambient space `Z'` of the universal first order thickening is formally unramified over `X`.  The
argument of the source is a double application of the *uniqueness* half of the universal
property of Stacks 0602.  Given a first-order thickening `T ⊂ T'` and two morphisms
`a, b : T' ⟶ Z'` over `X` which agree on `T`, form the scheme-theoretic inverse image
`a⁻¹(Z) ⊂ T'`.  Then

* `a` restricted to `a⁻¹(Z)` factors through `Z` — that is what the inverse image means — and
  `a` and `b` agree on `T ∩ a⁻¹(Z)`, which is the inverse image of `T` in `a⁻¹(Z)`; so the two
  restrictions of `a` and `b` to `a⁻¹(Z)` are dotted arrows for one and the same solid diagram
  of Stacks 0602, built from the thickening `T ∩ a⁻¹(Z) ⊂ a⁻¹(Z)`, and therefore agree;
* `a` and `b` are then themselves dotted arrows for one and the same solid diagram, built from
  the thickening `a⁻¹(Z) ⊂ T'`, and therefore agree.

That argument is formalized below with the two thickenings it uses as explicit hypotheses.  Both
hypotheses are instances of the order part of Stacks 09ZX, which
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/BaseChangeOrder.lean` proves for an arbitrary
morphism, so Stacks 0609 itself is proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningUnramified.lean`, as
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversalFirstOrderThickening`.

## Main definitions

* `AlgebraicGeometry.Space.UniversalFirstOrderThickening`: **Stacks 0607, part (1)**, a
  universal first order thickening of a formally unramified `h : Z ⟶ X`: the ambient algebraic
  space `Z'` with its structure morphism to `X`, the closed subspace of `Z'` which the
  universal property of Stacks 0602 is about, and the identification of `Z` with that closed
  subspace over `X`.
* `AlgebraicGeometry.Space.conormalSheaf`: **Stacks 0607, part (2)**, the conormal sheaf
  `𝒞_{Z/X}` of `Z` over `X`: the conormal module of Stacks 04CN of the closed subspace
  `Z ⊂ Z'`, transported to `Z` along the identification.

## Main results

* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.eq_of_lifts`: two dotted arrows for
  one solid diagram of Stacks 0602 are equal.  This is the uniqueness half of the universal
  property, packaged as an equality of two given morphisms rather than as an `ExistsUnique`.
* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.lifts_unique`: a universal first
  order thickening already forces uniqueness of lifts *into its closed subspace* across every
  first-order thickening of algebraic spaces.  This is why the formal unramifiedness of `h`
  which the source assumes is not an extra condition on the data of part (1); see the
  implementation notes.
* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.eq_of_isFirstOrderThickening_preimage`:
  **the argument of Stacks 0609**, with the two inverse-image thickenings as hypotheses: two
  morphisms `a, b : T' ⟶ Z'` over `X` which agree on a subfunctor `T` of `T'` are equal, as soon
  as `a⁻¹(Z) ⊂ T'` and `T ∩ a⁻¹(Z) ⊂ a⁻¹(Z)` are first-order thickenings.
* `AlgebraicGeometry.Space.conormalSheaf_eq`: the defining equation of the conormal sheaf,
  available to consumers as a rewrite without unfolding the definition.

## Implementation notes

**Why part (1) is a structure and not a construction.**  Stacks 0607, part (1) is a naming
definition: it attaches a name to the thickening *constructed* in Stacks 0606, the existence of
a universal first order thickening of a formally unramified morphism.  Stacks 0606 is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/UniversalExistence.lean`, as
`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`, and its conclusion is
`Nonempty` of the structure below, so nothing is extracted from it here.  What is formalized below is
therefore the *datum* the source names: a bundle of the
ambient algebraic space `Z'`, its structure morphism `p : Z' ⟶ X`, the closed subspace of `Z'`,
the universal property of Stacks 0602 for it, and the identification of `Z` with that subspace
over `X`.  No object is chosen out of an existence statement, and the definite article of the
source is licensed by the uniqueness clause of Stacks 0602 rather than reproduced by a choice:
a universal first order thickening is unique up to a unique isomorphism, and this is a bundle of
one of them.  This is the shape the functoriality statement Stacks 060A already takes in this
library, where `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening` appears as a hypothesis
for the same reason.

**The smaller space of the thickening is a subfunctor, so `Z` enters up to isomorphism.**  As
everywhere in `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/`, a thickening presents its
smaller space as a `CategoryTheory.Subfunctor` of the ambient algebraic space, so that the
inclusion is the canonical one.  A subfunctor of `Z'` is never literally `Z`, so the
identification of `Z` with it is the field `sourceIso`, and the compatibility with `h` is
`sourceIso_ι_toBase`: the composite `Z ≅ Z'.sub ⊂ Z' ⟶ X` is `h`.  This is what makes the datum
a thickening *of `Z` over `X`* and not merely some thickening.

**Formal unramifiedness of `h` is carried, and it is the source's own hypothesis.**  Stacks 0607
is stated for a formally unramified `h`, so `formallyUnramified` is a field; no hypothesis absent
from the source is added.  It is also not an extra condition in substance: by Stacks 0606 formal
unramifiedness of `h` is equivalent to the existence of the rest of the data, and the uniqueness
clause of Stacks 0602 already gives the uniqueness of lifts into the subspace across first-order
thickenings of algebraic spaces, which is
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.lifts_unique` below.  The step from
that to `AlgebraicGeometry.Space.FormallyUnramified`, whose test objects are square-zero closed
immersions of affine *objects of the site*, is
`AlgebraicGeometry.Space.isFirstOrderThickening_range_yoneda_map` of
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningUnramified.lean`.  The field is kept
because it is the hypothesis the source states, not because it could not be derived.

**Which universal property is used.**  The unprimed
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Universal.lean` is the one used here, not the
primed `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening'` of
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalFirstOrderThickening.lean`.  The two differ in
the order condition they build on: the unprimed one asks the closed subspace to be a
*thickening* with square-zero defining ideal (Stacks 05ZK, parts (1) and (2)), the primed one
only that it be closed.  The unprimed one is what Stacks 0605
(`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etalePullback`), Stacks 0604
(`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.comp_formallyEtale`) and Stacks 060A
(`AlgebraicGeometry.Space.universalThickeningMap`) consume, and it is the one whose first-order
clause yields the closed-subspace datum that the conormal module of Stacks 04CN needs; using it
is what makes the conormal sheaf below the module that Stacks 060A maps into.

**Why no new notation is declared.**  The source's `𝒞_{Z/X}` is the same symbol Stacks 04CN uses
for the conormal sheaf of an immersion, which in this library is
`AlgebraicGeometry.Space.conormalModule`; that definition does not declare notation either, and
records the symbol in its documentation.  Declaring `𝒞` here would attach it to one of the two
spellings of one notion and so read as a second notation; the documentation convention of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean` is followed instead.

**The conormal sheaf is transported to `Z`, not left on the subspace.**  The source's `𝒞_{Z/X}`
is a sheaf on `Z`.  `AlgebraicGeometry.Space.conormalModule` produces a module on the closed
subspace of `Z'`, so the definition below pulls it back along the identification
`Z ≅ Z'.sub`, which is an isomorphism of algebraic spaces and hence transports modules.  Up to
that transport this is exactly the module which
`AlgebraicGeometry.Space.universalThickeningConormalMap` of Stacks 060A maps between; the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningFunctorial.lean` record that it had to
spell the module out because this definition did not exist.

**The inverse images of the 0609 argument.**  The inverse image `a⁻¹(Z)` is the preimage
subfunctor `CategoryTheory.Subfunctor.preimage`, and the factorization of `a` through `Z` on it
is `CategoryTheory.Subfunctor.fromPreimage`, whose defining equation
`CategoryTheory.Subfunctor.fromPreimage_ι` says exactly that the composite
`a⁻¹(Z) ⊂ T' --a--→ Z'` is `a⁻¹(Z) ⟶ Z ⊂ Z'`.  The scheme-theoretic intersection `T ∩ a⁻¹(Z)`
of the source appears as the inverse image of `T` in `a⁻¹(Z)`, that is as
`T.preimage (Z.preimage a).ι`; `CategoryTheory.Subfunctor.isPullback_preimage` identifies that
inverse image with the fibre product, which is the source's reading of it.  The two morphisms
being compared are transformations of the underlying presheaves rather than morphisms of
algebraic spaces, because that is the form in which the universal property of Stacks 0602 states
its dotted arrow, and the form in which the Yoneda translation of
`AlgebraicGeometry.Space.FormallyUnramified` delivers them; the category of algebraic spaces
over `S` is full in presheaves, so nothing is lost.

## What is not proved here

* **Stacks 0606 is not proved *here***: it is proved in
  `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/UniversalExistence.lean`, which carries
  `@[stacks 0606]` on `AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`, so the
  datum of part (1) is inhabited for every formally unramified morphism.
* Stacks 0609 is not proved *here*; it is proved in
  `StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningUnramified.lean`, which imports this
  file and supplies the two hypotheses of
  `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.eq_of_isFirstOrderThickening_preimage`
  from the order part of Stacks 09ZX
  (`AlgebraicGeometry.Space.isFirstOrderThickening_preimage`).

## References

* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 0609](https://stacks.math.columbia.edu/tag/0609)
* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0605](https://stacks.math.columbia.edu/tag/0605)
* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 04G8](https://stacks.math.columbia.edu/tag/04G8)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Uniqueness of the dotted arrow of Stacks 0602 -/

namespace IsUniversalFirstOrderThickening

variable {B S hS} {X Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {p : Z' ⟶ X}

/-- **The uniqueness half of Stacks 0602, as an equality of two given morphisms.**  Let
`Z ⊂ Z'` be a universal first-order thickening of `Z` over `X` with structure morphism
`p : Z' ⟶ X`, let `T ⊂ T'` be a first-order thickening of algebraic spaces over `S`, let
`a₀ : T ⟶ Z` and let `β : T' ⟶ X`.  Two morphisms `T' ⟶ Z'` which both restrict to `a₀` on `T`
and both lie over `β` are equal.

The solid-diagram hypothesis of Stacks 0602 is not an argument here: it follows from the two
clauses for either of the two morphisms. -/
theorem eq_of_lifts (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.obj)
    (hT : IsFirstOrderThickening B S hS T' T) (a₀ : T.toFunctor ⟶ Z.toFunctor)
    (β : T'.obj ⟶ X.obj) (c₁ c₂ : T'.obj ⟶ Z'.obj)
    (h₁ : T.ι ≫ c₁ = a₀ ≫ Z.ι) (h₁' : c₁ ≫ p.hom = β)
    (h₂ : T.ι ≫ c₂ = a₀ ≫ Z.ι) (h₂' : c₂ ≫ p.hom = β) :
    c₁ = c₂ :=
  (hZ.existsUnique_lift T hT a₀ β (by
    rw [← h₁', ← Category.assoc, h₁, Category.assoc])).unique ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩

/-- **A universal first-order thickening makes its smaller space unramified over the base.**
Let `Z ⊂ Z'` be a universal first-order thickening of algebraic spaces over `S` with structure
morphism `p : Z' ⟶ X`.  Across any first-order thickening `T ⊂ T'` of algebraic spaces, two
morphisms `T' ⟶ Z` which agree on `T` and lie over the same morphism to `X` are equal.

This is the uniqueness half of the condition that `Z ⟶ X` be formally unramified, read on
first-order thickenings of algebraic spaces instead of on square-zero closed immersions of
affine objects of the site: the two composites with the inclusion `Z ⊂ Z'` are dotted arrows for
one and the same solid diagram of Stacks 0602, whose dotted arrow is unique, and the inclusion
of a subfunctor is a monomorphism.  It is why the formal unramifiedness of `h` which Stacks 0607
assumes is not a condition on the data of
`AlgebraicGeometry.Space.UniversalFirstOrderThickening` beyond what the universal property
already gives; the implementation notes of this file record what the step to
`AlgebraicGeometry.Space.FormallyUnramified` itself would still need. -/
theorem lifts_unique (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.obj)
    (hT : IsFirstOrderThickening B S hS T' T) (w₁ w₂ : T'.obj ⟶ Z.toFunctor)
    (hw : T.ι ≫ w₁ = T.ι ≫ w₂)
    (hp : w₁ ≫ Z.ι ≫ p.hom = w₂ ≫ Z.ι ≫ p.hom) :
    w₁ = w₂ :=
  (cancel_mono Z.ι).1 (hZ.eq_of_lifts T hT (T.ι ≫ w₁) (w₁ ≫ Z.ι ≫ p.hom) (w₁ ≫ Z.ι) (w₂ ≫ Z.ι)
    (by rw [Category.assoc]) (Category.assoc _ _ _) (by rw [← Category.assoc, ← hw])
    (by rw [Category.assoc, hp]))

/-- **The argument of Stacks 0609.**  Let `Z ⊂ Z'` be a universal first-order thickening of `Z`
over `X` with structure morphism `p : Z' ⟶ X`, let `T ⊂ T'` be a first-order thickening of
algebraic spaces over `S`, and let `a, b : T' ⟶ Z'` agree on `T` and lie over one morphism
`T' ⟶ X`.  If the inverse image `a⁻¹(Z) ⊂ T'` and the inverse image `T ∩ a⁻¹(Z) ⊂ a⁻¹(Z)` are
first-order thickenings, then `a = b`.

This is the double application of the uniqueness clause of Stacks 0602 which the source makes:
first on the thickening `T ∩ a⁻¹(Z) ⊂ a⁻¹(Z)`, where the restrictions of `a` and `b` are dotted
arrows for one solid diagram and hence agree, and then on the thickening `a⁻¹(Z) ⊂ T'`, where
`a` and `b` themselves are.

That `T ⊂ T'` is itself a first-order thickening is not an argument: the argument uses it only
through the two inverse-image hypotheses, and otherwise only that `a` and `b` agree on `T`.  So
`T` is any subfunctor of `T'` on which the two morphisms agree, which is how the statement is
phrased.

It is the engine of Stacks 0609 rather than its statement: the source obtains the two
hypotheses from the order part of Stacks 09ZX
(`AlgebraicGeometry.Space.isFirstOrderThickening_preimage`) and states the conclusion as formal
unramifiedness of `Z'` over `X`, which is
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversalFirstOrderThickening`. -/
theorem eq_of_isFirstOrderThickening_preimage
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.obj) (a b : T'.obj ⟶ Z'.obj)
    (hab : T.ι ≫ a = T.ι ≫ b) (hp : a ≫ p.hom = b ≫ p.hom)
    (hpre : IsFirstOrderThickening B S hS T' (Z.preimage a))
    (hpre' : IsFirstOrderThickening B S hS
      (⟨(Z.preimage a).toFunctor,
        (IsNthOrderThickening.isThickening B S hS hpre).1.1⟩ : AlgebraicSpaces B S hS)
      (T.preimage (Z.preimage a).ι)) :
    a = b := by
  -- The restrictions of `a` and `b` to the inverse image `a⁻¹(Z)` agree, because they are
  -- dotted arrows for the solid diagram built from the thickening `T ∩ a⁻¹(Z) ⊂ a⁻¹(Z)`.
  have hmid : (Z.preimage a).ι ≫ a = (Z.preimage a).ι ≫ b := by
    refine hZ.eq_of_lifts (T' := ⟨(Z.preimage a).toFunctor,
        (IsNthOrderThickening.isThickening B S hS hpre).1.1⟩)
      (T.preimage (Z.preimage a).ι) hpre'
      ((T.preimage (Z.preimage a).ι).ι ≫ Z.fromPreimage a)
      ((Z.preimage a).ι ≫ a ≫ p.hom) _ _ ?_ (Category.assoc _ _ _) ?_
      (by rw [Category.assoc, hp])
    · simp only [Category.assoc, Subfunctor.fromPreimage_ι]
    · rw [← Subfunctor.fromPreimage_ι_assoc (G := T) (p := (Z.preimage a).ι), ← hab,
        Subfunctor.fromPreimage_ι_assoc]
      simp only [Category.assoc, Subfunctor.fromPreimage_ι]
  -- Hence `a` and `b` are dotted arrows for the solid diagram built from the thickening
  -- `a⁻¹(Z) ⊂ T'`, and so they agree.
  exact hZ.eq_of_lifts (Z.preimage a) hpre (Z.fromPreimage a) (a ≫ p.hom) a b
    (Subfunctor.fromPreimage_ι Z a).symm rfl
    (hmid.symm.trans (Subfunctor.fromPreimage_ι Z a).symm) hp.symm

end IsUniversalFirstOrderThickening

/-! ### The universal first-order thickening of a formally unramified morphism -/

/-- **Stacks 0607, part (1).**  A *universal first order thickening* of a formally unramified
morphism `h : Z ⟶ X` of algebraic spaces over `S`: the thickening `Z ⊂ Z'` of `Z` over `X` whose
existence is Stacks 0606, presented as the datum it consists of.

The ambient algebraic space is `ambient`, written `Z'` in the source, with structure morphism
`toBase : Z' ⟶ X`; the smaller space is the closed subspace `sub` of `Z'`, which `sourceIso`
identifies with `Z` compatibly with `h`; and `isUniversal` is the universal property of
Stacks 0602 for that thickening over `X`.

Stacks 0606, the existence of such a datum for every formally unramified `h`, is
`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`; it concludes `Nonempty` of this
structure, so the datum is taken as given rather than chosen out of an existence statement, and
the uniqueness clause of `isUniversal` is what licenses the source's definite article. -/
@[stacks 0607 "the universal first order thickening"]
structure UniversalFirstOrderThickening {Z X : AlgebraicSpaces B S hS} (h : Z ⟶ X) where
  /-- The morphism which is being thickened is formally unramified, as Stacks 0607 assumes. -/
  formallyUnramified : FormallyUnramified h.hom
  /-- The ambient algebraic space `Z'` of the thickening. -/
  ambient : AlgebraicSpaces B S hS
  /-- The structure morphism `p : Z' ⟶ X` of the thickening over `X`. -/
  toBase : ambient ⟶ X
  /-- The smaller space of the thickening, as a subfunctor of the ambient space. -/
  sub : Subfunctor ambient.obj
  /-- The thickening is a universal first-order thickening over `X`, in the sense of
  Stacks 0602. -/
  isUniversal : IsUniversalFirstOrderThickening B S hS sub toBase
  /-- The identification of `Z` with the smaller space of the thickening. -/
  sourceIso : Z.obj ≅ sub.toFunctor
  /-- The identification is one of thickenings *of `Z` over `X`*: the composite
  `Z ≅ sub ⊂ Z' ⟶ X` is `h`. -/
  sourceIso_ι_toBase : sourceIso.hom ≫ sub.ι ≫ toBase.hom = h.hom

namespace UniversalFirstOrderThickening

variable {B S hS} {Z X : AlgebraicSpaces B S hS} {h : Z ⟶ X}

/-- The smaller space of a universal first-order thickening is a closed subspace of the ambient
space: a first-order thickening is in particular one, by Stacks 05ZK. -/
abbrev closedSub (t : UniversalFirstOrderThickening B S hS h) :
    ClosedSubspaces B S hS t.ambient.obj :=
  ⟨t.sub, (IsNthOrderThickening.isThickening B S hS t.isUniversal.firstOrder).1⟩

/-- The smaller space of a universal first-order thickening, as an algebraic space: a closed
subspace of an algebraic space is one. -/
abbrev subSpace (t : UniversalFirstOrderThickening B S hS h) : AlgebraicSpaces B S hS :=
  ⟨t.sub.toFunctor, t.closedSub.2.1⟩

/-- The identification of `Z` with the smaller space of a universal first-order thickening,
read as a morphism of algebraic spaces. -/
abbrev sourceInclusion (t : UniversalFirstOrderThickening B S hS h) : Z ⟶ t.subSpace :=
  ObjectProperty.homMk t.sourceIso.hom

end UniversalFirstOrderThickening

/-! ### The conormal sheaf of a formally unramified morphism -/

/-- **Stacks 0607, part (2).**  The *conormal sheaf* `𝒞_{Z/X}` of a formally unramified
morphism `h : Z ⟶ X` of algebraic spaces over `S`, relative to a universal first order
thickening `Z ⊂ Z'` of `Z` over `X`: the conormal module of Stacks 04CN of the closed subspace
`Z ⊂ Z'`, transported to `Z` along the identification of `Z` with that closed subspace.

The source writes this `𝒞_{Z/X}`, the same symbol Stacks 04CN uses for the conormal sheaf of an
immersion, which in this library is `AlgebraicGeometry.Space.conormalModule`; no notation is
declared, following the convention of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean`. -/
@[stacks 0607 "the conormal sheaf"]
noncomputable def conormalSheaf {Z X : AlgebraicSpaces B S hS} {h : Z ⟶ X}
    (t : UniversalFirstOrderThickening B S hS h) :
    Modules.{u, u} B S hS Z.obj Z.property :=
  (modulePullback B S hS t.sourceInclusion).obj
    (conormalModule B S hS t.ambient t.closedSub)

/-- The conormal sheaf of a formally unramified morphism is the conormal module of its source in
its universal first order thickening, transported along the identification of the source with
the smaller space of the thickening.  This is the defining equation, stated so that consumers
may rewrite with it rather than unfold the definition. -/
theorem conormalSheaf_eq {Z X : AlgebraicSpaces B S hS} {h : Z ⟶ X}
    (t : UniversalFirstOrderThickening B S hS h) :
    conormalSheaf B S hS t =
      (modulePullback B S hS t.sourceInclusion).obj
        (conormalModule B S hS t.ambient t.closedSub) :=
  rfl

end AlgebraicGeometry.Space

end
