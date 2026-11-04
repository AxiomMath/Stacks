module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import StacksCore.Tactic.StacksAttribute

/-!
# Conservative families of points, and sites with enough points

Let `(C, J)` be a site. A family of points `{p_i}_{i ∈ I}` of the site is *conservative* if a map
of sheaves of sets `φ : F ⟶ G` is an isomorphism as soon as every one of its fibres
`F_{p_i} ⟶ G_{p_i}` is; and `C` *has enough points* if some conservative family exists. This file
states both, for a family indexed by an arbitrary type in an arbitrary universe and with no
smallness condition on the family, and compares them with Mathlib's
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints` and
`CategoryTheory.GrothendieckTopology.HasEnoughPoints`.

## Main definitions

* `CategoryTheory.GrothendieckTopology.IsConservativeFamily`: Stacks 00YK (1), conservativity of a
  family of points `p : ι → J.Point` indexed by an arbitrary type.
* `CategoryTheory.GrothendieckTopology.HasConservativeFamily`: Stacks 00YK (2), the existence of a
  conservative family of points.

## Main results

* `CategoryTheory.GrothendieckTopology.isConservativeFamily_iff_ofObj`: conservativity of
  `p : ι → J.Point` is Mathlib's `ObjectProperty.IsConservativeFamilyOfPoints` of the image
  `ObjectProperty.ofObj p`.
* `CategoryTheory.GrothendieckTopology.IsConservativeFamily.hasConservativeFamily`: a conservative
  family indexed by *any* type, in any universe, witnesses `HasConservativeFamily`.
* `CategoryTheory.GrothendieckTopology.hasEnoughPoints_iff_exists_small_conservativeFamily`:
  Mathlib's `HasEnoughPoints.{w}` is `HasConservativeFamily.{w}` together with `w`-smallness of the
  family. Hence `HasConservativeFamily.of_hasEnoughPoints` in one direction, and
  `hasEnoughPoints_of_isConservativeFamily` back again once the index type is `w`-small.

## Implementation notes

* **Part (1) is exactly Mathlib's.** `ObjectProperty.IsConservativeFamilyOfPoints`, which Mathlib
  itself tags `@[stacks 00YK "(1)"]`, presents the family as a `P : ObjectProperty J.Point` and
  asks that the fibre functors `Φ.obj.sheafFiber : Sheaf J (Type w) ⥤ Type w`, `Φ` ranging over
  `P.FullSubcategory`, jointly reflect isomorphisms. It carries no smallness instance and no
  hypothesis beyond the site itself. Presenting an indexed family `p : ι → J.Point` as
  `ObjectProperty.ofObj p` loses nothing, because `ObjectProperty.ofObj_iff` says `ofObj p` is the
  literal image `fun q ↦ ∃ i, p i = q`, and conservativity of a family depends only on the set of
  fibre functors it names, not on the indexing. `isConservativeFamily_iff_ofObj` is that
  comparison; `isConservativeFamily_iff_of_forall_iff` is the common generalization, which needs
  only that the predicate and the indexed family have the same image. So part (1) here is a
  restatement in the source's indexed-family shape, not new content.
* **Part (2) is a strictly weaker hypothesis than Mathlib's.** Mathlib's
  `GrothendieckTopology.HasEnoughPoints.{w}` is not "there exists a conservative family": its field
  is `∃ P, ObjectProperty.Small.{w} P ∧ P.IsConservativeFamilyOfPoints`, i.e. there exists a
  `w`-*small* conservative family, and its docstring says so. Stacks 00YK (2) asks only for a
  conservative family. `HasConservativeFamily` below therefore drops the smallness conjunct, and
  `hasEnoughPoints_iff_exists_small_conservativeFamily` isolates the difference as exactly that
  conjunct. Whether the two agree is the question of SGA 4 IV 6.5: given a conservative family one
  wants to choose, for each non-covering sieve, one point detecting it, which yields a family
  indexed by the sieves of `C` and so is `w`-small only under a smallness hypothesis on `C`
  itself. No such reduction is proved here, and none is claimed; the implication that *is* proved
  runs from Mathlib's notion to the source's.
* The family in part (2) is existentially quantified as a predicate `Point.{w} J → Prop` rather
  than as an indexed family, since `∃ (ι : Type t) (p : ι → J.Point), _` would fix the index
  universe `t` and thereby impose a smallness condition of its own — the very thing part (2) does
  not ask for. Nothing is lost: `IsConservativeFamily.hasConservativeFamily` produces
  `HasConservativeFamily` from a conservative family indexed by an arbitrary type in an arbitrary
  universe, by passing to its image. `Point.{w} J → Prop` is `ObjectProperty (Point.{w} J)`, which
  is an `abbrev` for exactly that, and its `Subtype` is the one `ObjectProperty.Small` speaks
  about; writing the predicate out avoids the mismatch between `Subtype S` and the `Set`
  membership coercion.
* Fibres are taken in sheaves of sets, `Sheaf J (Type w)`, which is the source's `Sh(C)`. The
  universe `w` is a parameter throughout, as it is in Mathlib: a point of `(C, J)` relative to `w`
  is a fibre functor `C ⥤ Type w`.
* The hypothesis of part (1) is an explicit `∀ i, IsIso _` rather than an instance binder, so that
  the definition reads as the source's implication; `JointlyReflectIsomorphisms.isIso_iff` converts
  between the two shapes.

## References

* [Stacks 00YK](https://stacks.math.columbia.edu/tag/00YK)
  (`sites-definition-conservative`), in the section "Sites with enough points" (Stacks 00YJ).
* [SGA4], Exposé IV, 6.5.

Tags covered: 00YK.
-/

@[expose] public section

namespace CategoryTheory.GrothendieckTopology

universe w v u t

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Stacks 00YK (1).** A family of points `{p_i}_{i ∈ I}` of a site `(C, J)` is *conservative* if
every map of sheaves of sets `φ : F ⟶ G` which is an isomorphism on all the fibres
`F_{p_i} ⟶ G_{p_i}` is an isomorphism. -/
@[stacks 00YK "(1)", sga "4 IV 6.4.1" "conservative family"]
def IsConservativeFamily {ι : Type t} (p : ι → Point.{w} J) : Prop :=
  ∀ {F G : Sheaf J (Type w)} (φ : F ⟶ G),
    (∀ i, IsIso (((p i).sheafFiber (A := Type w)).map φ)) → IsIso φ

/-- **Stacks 00YK (2).** A site `(C, J)` *has enough points* if there exists a conservative family
of points. No smallness is required of the family; contrast
`CategoryTheory.GrothendieckTopology.HasEnoughPoints`, which asks for a `w`-small one. -/
@[stacks 00YK "(2)", sga "4 IV 6.4.1" "enough points"]
def HasConservativeFamily (J : GrothendieckTopology C) : Prop :=
  ∃ S : Point.{w} J → Prop,
    IsConservativeFamily (Subtype.val : Subtype S → Point.{w} J)

/-- Conservativity of a family of points depends only on the family's image: if a predicate `P` on
points and an indexed family `p` pick out the same points, then `p` is a conservative family in the
sense of Stacks 00YK (1) if and only if `P` is one in the sense of Mathlib's
`ObjectProperty.IsConservativeFamilyOfPoints`. -/
theorem isConservativeFamily_iff_of_forall_iff {ι : Type t} {p : ι → Point.{w} J}
    {P : ObjectProperty (Point.{w} J)} (hp : ∀ q, P q ↔ ∃ i, p i = q) :
    IsConservativeFamily p ↔ P.IsConservativeFamilyOfPoints := by
  constructor
  · intro h
    refine ⟨⟨?_⟩⟩
    intro F G φ hinst
    exact h φ fun i ↦ hinst ⟨p i, (hp (p i)).2 ⟨i, rfl⟩⟩
  · intro hP F G φ hφ
    rw [hP.jointlyReflectIsomorphisms_type.isIso_iff]
    rintro ⟨q, hq⟩
    obtain ⟨i, rfl⟩ := (hp q).1 hq
    exact hφ i

/-- A family of points `p : ι → J.Point` is conservative in the sense of Stacks 00YK (1) if and
only if its image `ObjectProperty.ofObj p` is a conservative family in Mathlib's sense. -/
theorem isConservativeFamily_iff_ofObj {ι : Type t} (p : ι → Point.{w} J) :
    IsConservativeFamily p ↔ (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints :=
  isConservativeFamily_iff_of_forall_iff (ObjectProperty.ofObj_iff p)

/-- A predicate `P` on the points of `(C, J)` is a conservative family in Mathlib's sense if and
only if the family it indexes, `Subtype.val : Subtype P → J.Point`, is conservative in the sense of
Stacks 00YK (1). -/
theorem isConservativeFamily_subtypeVal_iff (P : ObjectProperty (Point.{w} J)) :
    IsConservativeFamily (Subtype.val : Subtype P → Point.{w} J) ↔
      P.IsConservativeFamilyOfPoints :=
  isConservativeFamily_iff_of_forall_iff
    (fun q ↦ ⟨fun h ↦ ⟨⟨q, h⟩, rfl⟩, fun ⟨i, hi⟩ ↦ hi ▸ i.2⟩)

/-- A conservative family of points indexed by an arbitrary type, in an arbitrary universe,
witnesses that the site has enough points. -/
theorem IsConservativeFamily.hasConservativeFamily {ι : Type t} {p : ι → Point.{w} J}
    (hp : IsConservativeFamily p) : HasConservativeFamily.{w} J :=
  ⟨ObjectProperty.ofObj p,
    (isConservativeFamily_subtypeVal_iff _).2 ((isConservativeFamily_iff_ofObj p).1 hp)⟩

/-- Having enough points in the sense of Stacks 00YK (2) is the existence of a conservative family
of points in Mathlib's sense, with no smallness condition. -/
theorem hasConservativeFamily_iff_exists (J : GrothendieckTopology C) :
    HasConservativeFamily.{w} J ↔
      ∃ P : ObjectProperty (Point.{w} J), P.IsConservativeFamilyOfPoints :=
  exists_congr isConservativeFamily_subtypeVal_iff

/-- Mathlib's `GrothendieckTopology.HasEnoughPoints.{w}` is Stacks 00YK (2) *together with*
`w`-smallness of the conservative family: it asserts the existence of a `w`-small conservative
family, whereas the source asks only for a conservative family. -/
theorem hasEnoughPoints_iff_exists_small_conservativeFamily (J : GrothendieckTopology C) :
    HasEnoughPoints.{w} J ↔
      ∃ S : Point.{w} J → Prop, Small.{w} (Subtype S) ∧
        IsConservativeFamily (Subtype.val : Subtype S → Point.{w} J) := by
  constructor
  · intro h
    obtain ⟨P, hPs, hP⟩ := HasEnoughPoints.exists_objectProperty.{w} J
    exact ⟨P, hPs, (isConservativeFamily_subtypeVal_iff P).2 hP⟩
  · rintro ⟨S, hS, h⟩
    exact ⟨⟨S, hS, (isConservativeFamily_subtypeVal_iff S).1 h⟩⟩

/-- A site with enough points in Mathlib's sense has enough points in the sense of
Stacks 00YK (2). -/
theorem HasConservativeFamily.of_hasEnoughPoints (J : GrothendieckTopology C)
    [HasEnoughPoints.{w} J] : HasConservativeFamily.{w} J :=
  let ⟨S, _, h⟩ := (hasEnoughPoints_iff_exists_small_conservativeFamily J).1 ‹_›
  ⟨S, h⟩

/-- A conservative family of points indexed by a `w`-small type gives Mathlib's
`GrothendieckTopology.HasEnoughPoints.{w}`, whose conservative family is required to be
`w`-small. -/
theorem hasEnoughPoints_of_isConservativeFamily {ι : Type t} [Small.{w} ι] (p : ι → Point.{w} J)
    (hp : IsConservativeFamily p) : HasEnoughPoints.{w} J :=
  ⟨⟨ObjectProperty.ofObj p, inferInstance, (isConservativeFamily_iff_ofObj p).1 hp⟩⟩

end CategoryTheory.GrothendieckTopology
