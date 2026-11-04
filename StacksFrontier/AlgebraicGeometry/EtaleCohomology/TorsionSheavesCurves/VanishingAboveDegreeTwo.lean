module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# Statement (1) of Situation 0A52: vanishing of étale cohomology above degree two

Stacks Project Tag 0A52 sets up a situation — an algebraically closed field `k`, a separated
finite-type scheme `X` of dimension at most one over `k`, and a torsion abelian sheaf `F` on the
small étale site of `X` — and then lists eight statements, Tags 0A53 to 0A5A, which the rest of
that section proves hold in it (Tag 03SC). The first of the eight, Tag 0A53, is

> `H^q_étale(X, F) = 0` for `q > 2`.

This file is that statement, as a predicate on `F`. It is not the assertion that the predicate
holds: that is Tag 03SC, whose proof occupies the whole of Section 59.83 of the source.

## Main definitions

* `Stacks.EtaleCohomology.IsVanishingAboveDegreeTwo` is Tag 0A53: the étale cohomology of `F`
  vanishes in every degree greater than two.

## Main results

* `Stacks.EtaleCohomology.isVanishingAboveDegreeTwo_of_subsingleton_of_one_lt` is the implication
  the source uses whenever it has the sharper vanishing available: étale cohomology that vanishes
  above degree one vanishes above degree two. It is how statements (2) and (3) of the list, Tags
  0A54 and 0A55, each give this one, and how Tag 0A5B obtains this statement in the case where
  the torsion is `p`-power for `p` the characteristic.
* `Stacks.EtaleCohomology.isVanishingAboveDegreeTwo_of_curveCohomologyStatements` identifies the
  predicate with the corresponding field of `Stacks.EtaleCohomology.CurveCohomologyStatements`,
  the conjunction of all eight statements used by Tags 0A5C and 0A5D.

## Implementation notes

**No hypothesis of Situation 0A52 is imposed.** Item (1) of that list mentions only `X`, `F` and
the degree `q`; the algebraically closed base field, the separatedness, the finite type and the
dimension bound, and the standing assumption that `F` is torsion, are what make the item a
*theorem* at Tag 03SC, not part of the item. The predicate below is therefore defined for an
arbitrary scheme and an arbitrary abelian sheaf on its small étale site, which is more general
than the source's item and specialises to it. Unlike statements (6), (7) and (8) the item names
no second scheme and no morphism, so the predicate depends on `X` and `F` alone.

**Relation to `CurveCohomologyStatements`.** That structure, in
`TorsionSheavesCurves/FiniteDirectImage.lean`, already carries this statement, as its field
`vanishing`. A structure field cannot carry an attribute, and there the statement is bundled with
the other seven and so is stated relative to a fixed structure morphism `π : X ⟶ Spec k`, a fixed
morphism `i` along which cohomology is restricted, two integers and a constructibility predicate,
none of which item (1) mentions. The definition below is the standalone form of that field, and
`isVanishingAboveDegreeTwo_of_curveCohomologyStatements` is the one-step bridge between them.

**Which universe hypotheses are genuinely needed.** `CategoryTheory.Sheaf.H` is an `Ext`-group in
the category of abelian sheaves, so it needs that category to admit sheafification and to have a
choice of `Ext`-universe. Only the second is a hypothesis here. Sheafification is an instance at
this library's étale coefficient universe,
`AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology` of
`EtaleCohomology/Sheafification/SmallEtaleAbelian.lean`, which covers
`AddCommGrpCat.{max (u + 1) v}` for every `X : Scheme.{u}` and arbitrary `v`; it is Mathlib's own
instance that is restricted to `AddCommGrpCat.{u}`, never the universe in which étale cohomology
of `X` is computed. `CategoryTheory.HasExt` is deliberately not an instance, a category having in
general several reasonable `Ext`-universes, so it is carried; it is not vacuous, since
`CategoryTheory.HasExt.standard` provides one.

Vanishing is spelled `Subsingleton`, matching `CategoryTheory.Sheaf.H`, which is an `Ext`-group
and so has no canonical zero element to compare against. The coefficient universe is
`AddCommGrpCat.{max (u + 1) v}` for schemes in `Scheme.{u}`, the family of universes in which
this library computes étale cohomology.

## References

* [Stacks Project, Tag 0A53](https://stacks.math.columbia.edu/tag/0A53)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Stacks Project, Tag 0A53.** Statement (1) of the list of Situation 0A52: the étale
cohomology `H^q_étale(X, F)` vanishes for every degree `q > 2`. -/
@[stacks 0A53 "item (1) of 0A52: H^q(X, F) = 0 for q > 2"]
def IsVanishingAboveDegreeTwo
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) : Prop :=
  ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H.{w} F q)

/-- Étale cohomology that vanishes above degree one vanishes above degree two. This is the
implication by which statements (2) and (3) of the list of Situation 0A52, Tags 0A54 and 0A55,
each give statement (1), and by which Tag 0A5B obtains statement (1) in the case of `p`-power
torsion for `p` the characteristic of the base field, where Tag 0A3N supplies the sharper
vanishing. -/
theorem isVanishingAboveDegreeTwo_of_subsingleton_of_one_lt
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} F q)) :
    IsVanishingAboveDegreeTwo.{u, v, w} F :=
  fun q hq => h q (by omega)

/-- Statement (1) of Situation 0A52 is the field `vanishing` of
`Stacks.EtaleCohomology.CurveCohomologyStatements`, the conjunction of all eight statements of
that list. The conjunction is stated relative to data that item (1) does not mention — a
structure morphism, a morphism along which cohomology is restricted, two integers and a
constructibility predicate — and this is the projection onto the part that it does. -/
theorem isVanishingAboveDegreeTwo_of_curveCohomologyStatements {Z' : Scheme.{u}} {i : Z' ⟶ X}
    {k : Type u} [Field k] {π : X ⟶ Spec (.of k)} {l p : ℕ}
    {constructible : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    [HasExt.{w} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (c : CurveCohomologyStatements.{u, v, w} i π l p constructible F) :
    IsVanishingAboveDegreeTwo.{u, v, w} F :=
  c.vanishing

end Stacks.EtaleCohomology

end
