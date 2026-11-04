module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocusClosed0BF0
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The descent locus of a finite locally free module

Let `f : X ⟶ S` be a morphism of schemes and `E` a sheaf of modules on `X`. A base change
`g : T ⟶ S` satisfies the descent condition `AlgebraicGeometry.DescendsFromBase f E g` when the
pullback of `E` to `X ×_S T` comes from a finite locally free module on `T`.
[Stacks, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP) says that, for `f` flat, proper and
of finite presentation whose structure sheaf is unchanged by pushforward after every base change,
this condition is *represented* by an immersion of finite presentation `Z ⟶ S`.

This file introduces the representing object. `AlgebraicGeometry.IsDescentLocus f E Z` says that
`Z : Over S` is such a representing object, and `AlgebraicGeometry.descentLocus f E` names one.
Representability itself — the existence statement, which is the content of Tag 0BDP — is **not**
proved here: its proof rests on cohomology and base change for perfect complexes
([Stacks, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)) and on
[Stacks, Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL), neither of which is available. What
is proved is that a representing object is unique up to a unique isomorphism over `S`, which is
what licenses the article in "*the* descent locus".

## Main definitions

* `AlgebraicGeometry.IsDescentLocus` says that a scheme over `S` represents the descent condition.
* `AlgebraicGeometry.HasDescentLocus` is the representability statement for one `f` and `E`.
* `AlgebraicGeometry.descentLocus` names the representing object.

## Main results

* `AlgebraicGeometry.IsDescentLocus.isoOfIsDescentLocus`: two descent loci for the same data are
  isomorphic over `S`, and `AlgebraicGeometry.IsDescentLocus.subsingleton_iso` says that the
  isomorphism between them is unique.
* `AlgebraicGeometry.IsDescentLocus.factorsThrough_of_nonempty_iso_unit`: a base change whose
  pulled-back module is trivial factors through a descent locus.
* `AlgebraicGeometry.isImmersion_descentLocus`,
  `AlgebraicGeometry.finitePresentation_descentLocus` and
  `AlgebraicGeometry.factorsThrough_descentLocus_iff` are the three properties of
  `descentLocus`, each of them taking representability as a hypothesis.

## Implementation notes

`descentLocus` is total, so that statements about the locus are written with no representability
hypothesis in their *type*; outside `HasDescentLocus` it is the junk value `Over.mk (𝟙 S)`, as
`descentLocus_of_not_hasDescentLocus` records.

That junk value is itself an immersion of finite presentation, so `isImmersion_descentLocus` and
`finitePresentation_descentLocus` could have been stated with no hypothesis at all. They are not,
deliberately: their unconditional forms would be true for a reason that has nothing to do with
descent, and would therefore be a weakening of `IsDescentLocus.isImmersion` and
`IsDescentLocus.finitePresentation` dressed as the corresponding assertions of Tag 0BDP. For the
same reason **no declaration in this file carries a `@[stacks 0BDP]` attribute**: the tag asserts
that the descent condition *is* represented, and that is `HasDescentLocus`, which is not proved
here.

The hypothesis-free formulations through `IsDescentLocus` are the ones to prove theorems about: a
statement quantified over every descent locus implies the corresponding statement about
`descentLocus` (by `isDescentLocus_descentLocus`), while the converse fails on the junk branch.

Uniqueness is proved from the universal property alone: an immersion is a monomorphism, each locus
satisfies the descent condition along its own structure morphism and so factors through the other,
and the two factorizations compose to the identity after cancelling a monomorphism. Neither
flatness, properness, nor finite presentation of `f`, nor the condition on the direct image of the
structure sheaf, is used; they are hypotheses of the *existence* statement only, which is why they
appear nowhere in this file.

## References

* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
* [Stacks Project, Tag 0BF0](https://stacks.math.columbia.edu/tag/0BF0)
* [Stacks Project, Tag 0EX8](https://stacks.math.columbia.edu/tag/0EX8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- `IsDescentLocus f E Z` says that the scheme `Z` over `S` **is a descent locus** for the sheaf
of modules `E` on `X` over `f : X ⟶ S`: its structure morphism is an immersion of finite
presentation, and a morphism `g : T ⟶ S` factors through it exactly when `E` descends along the
base change `g`, that is when `AlgebraicGeometry.DescendsFromBase f E g` holds.

Stacks Tag 0BDP asserts that such a `Z` exists when `f` is flat, proper and of finite presentation
and the structure sheaf of `X` is unchanged by pushforward along every base change; that existence
is `AlgebraicGeometry.HasDescentLocus` and is not proved. Those conditions on `f` are hypotheses
of the existence statement and play no part in this definition. -/
structure IsDescentLocus {X S : Scheme.{u}} (f : X ⟶ S)
    (E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (Z : Over S) : Prop where
  /-- The structure morphism of a descent locus is an immersion. -/
  isImmersion : IsImmersion Z.hom
  /-- The structure morphism of a descent locus is of finite presentation. -/
  finitePresentation : FinitePresentation Z.hom
  /-- A base change factors through a descent locus exactly when the module descends along it. -/
  factorsThrough_iff {T : Scheme.{u}} (g : T ⟶ S) :
    (∃ h : T ⟶ Z.left, h ≫ Z.hom = g) ↔ DescendsFromBase f E g

namespace IsDescentLocus

variable {X S : Scheme.{u}} {f : X ⟶ S}
  {E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} {Z Z' : Over S}

/-- The structure morphism of a descent locus is a monomorphism, being an immersion. -/
theorem mono (hZ : IsDescentLocus f E Z) : Mono Z.hom :=
  have := hZ.isImmersion
  inferInstance

/-- The module descends along the structure morphism of a descent locus, since the locus factors
through itself by the identity. -/
theorem descendsFromBase_hom (hZ : IsDescentLocus f E Z) : DescendsFromBase f E Z.hom :=
  (hZ.factorsThrough_iff Z.hom).1 ⟨𝟙 Z.left, Category.id_comp Z.hom⟩

/-- A descent locus factors through any other descent locus for the same data. -/
theorem exists_hom (hZ : IsDescentLocus f E Z) (hZ' : IsDescentLocus f E Z') :
    ∃ a : Z.left ⟶ Z'.left, a ≫ Z'.hom = Z.hom :=
  (hZ'.factorsThrough_iff Z.hom).2 hZ.descendsFromBase_hom

/-- Two descent loci for the same data are isomorphic as schemes over `S`: each factors through
the other, and the two factorizations compose to the identity because the structure morphisms are
monomorphisms. -/
noncomputable def isoOfIsDescentLocus (hZ : IsDescentLocus f E Z)
    (hZ' : IsDescentLocus f E Z') : Z ≅ Z' :=
  have := hZ.mono
  have := hZ'.mono
  Over.isoMk
    { hom := (hZ.exists_hom hZ').choose
      inv := (hZ'.exists_hom hZ).choose
      hom_inv_id := by
        refine (cancel_mono Z.hom).1 ?_
        rw [Category.assoc, (hZ'.exists_hom hZ).choose_spec,
          (hZ.exists_hom hZ').choose_spec, Category.id_comp]
      inv_hom_id := by
        refine (cancel_mono Z'.hom).1 ?_
        rw [Category.assoc, (hZ.exists_hom hZ').choose_spec,
          (hZ'.exists_hom hZ).choose_spec, Category.id_comp] }
    (hZ.exists_hom hZ').choose_spec

/-- The isomorphism between two descent loci is unique, because the structure morphism of the
target is a monomorphism and both isomorphisms commute with it. -/
theorem subsingleton_iso (_hZ : IsDescentLocus f E Z) (hZ' : IsDescentLocus f E Z') :
    Subsingleton (Z ≅ Z') := by
  have := hZ'.mono
  refine ⟨fun e e' ↦ Iso.ext (Over.OverMorphism.ext ((cancel_mono Z'.hom).1 ?_))⟩
  rw [Over.w e.hom, Over.w e'.hom]

/-- A base change whose pulled-back module is trivial, that is isomorphic to the structure sheaf
of the base change, factors through a descent locus.

This is the implication by which the conclusion of Stacks Tag 0EX8 produces a factorization
through the locus, which is how the proof of Stacks Tag 0BF0 uses it. -/
theorem factorsThrough_of_nonempty_iso_unit (hZ : IsDescentLocus f E Z) {T : Scheme.{u}}
    (g : T ⟶ S)
    (h : Nonempty ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj E ≅
      SheafOfModules.unit (structureSheafRing (pullback f g).toRingedSpace))) :
    ∃ k : T ⟶ Z.left, k ≫ Z.hom = g :=
  (hZ.factorsThrough_iff g).2 (descendsFromBase_of_nonempty_iso_unit f E g h)

end IsDescentLocus

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- `HasDescentLocus f E` says that the descent condition for `E` over `f` is represented by an
immersion of finite presentation into the base. This is the conclusion of Stacks Tag 0BDP, whose
hypotheses are that `f` be flat, proper and of finite presentation and that the structure sheaf of
`X` be unchanged by pushforward along every base change. It is not proved here. -/
abbrev HasDescentLocus : Prop := ∃ Z : Over S, IsDescentLocus f E Z

open scoped Classical in
/-- **The descent locus** of `E` over `f`: the scheme over `S` through which a base change factors
exactly when `E` descends along it.

The definition is total, so that statements about the locus are writable with no representability
hypothesis in their type. Where the descent condition is not representable — everything outside
Stacks Tag 0BDP's hypotheses, and not known even inside them — this is the junk value
`Over.mk (𝟙 S)`. Nothing about the locus should be read off the definition: use
`isDescentLocus_descentLocus`, and prefer stating results for an arbitrary `Z` satisfying
`IsDescentLocus f E Z`, which implies the corresponding result for `descentLocus f E` while not
following from it. -/
noncomputable def descentLocus : Over S :=
  if h : HasDescentLocus f E then h.choose else Over.mk (𝟙 S)

/-- Where the descent condition is representable, `descentLocus` is a descent locus. -/
theorem isDescentLocus_descentLocus (h : HasDescentLocus f E) :
    IsDescentLocus f E (descentLocus f E) := by
  rw [descentLocus, dite_eq_left h]
  exact h.choose_spec

/-- Where the descent condition is not representable, `descentLocus` is the identity of the base.
This is the junk branch of the definition and says nothing about descent. -/
theorem descentLocus_of_not_hasDescentLocus (h : ¬ HasDescentLocus f E) :
    descentLocus f E = Over.mk (𝟙 S) := by
  rw [descentLocus, dite_eq_right h]

/-- The descent locus is immersed in the base. -/
theorem isImmersion_descentLocus (h : HasDescentLocus f E) :
    IsImmersion (descentLocus f E).hom :=
  (isDescentLocus_descentLocus f E h).isImmersion

/-- The immersion of the descent locus is of finite presentation. -/
theorem finitePresentation_descentLocus (h : HasDescentLocus f E) :
    FinitePresentation (descentLocus f E).hom :=
  (isDescentLocus_descentLocus f E h).finitePresentation

/-- A base change factors through the descent locus exactly when the pulled-back module comes from
a finite locally free module on the base. This is the characterizing property of Stacks Tag 0BDP,
and it needs representability: on the junk branch every base change factors through the locus. -/
theorem factorsThrough_descentLocus_iff (h : HasDescentLocus f E) {T : Scheme.{u}} (g : T ⟶ S) :
    (∃ k : T ⟶ (descentLocus f E).left, k ≫ (descentLocus f E).hom = g) ↔
      DescendsFromBase f E g :=
  (isDescentLocus_descentLocus f E h).factorsThrough_iff g

/-- Every descent locus is isomorphic over `S` to `descentLocus`, which is therefore an
unambiguous name for it. -/
noncomputable def isoDescentLocus {Z : Over S} (hZ : IsDescentLocus f E Z) :
    descentLocus f E ≅ Z :=
  (isDescentLocus_descentLocus f E ⟨Z, hZ⟩).isoOfIsDescentLocus hZ

end AlgebraicGeometry

end
