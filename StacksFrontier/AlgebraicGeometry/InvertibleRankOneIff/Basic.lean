module

public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact

/-!
# Invertible and rank-one locally free, at the ringed-space spelling of Stacks Tag 0B8M

Stacks Tag 0B8M has three clauses: on a ringed space `(X, 𝒪_X)` a locally free module of rank one
is invertible; when all stalks `𝒪_{X, x}` are local rings the converse holds; and without that
hypothesis the converse fails. This file states clauses 1 and 2 **for a ringed space, in the
spelling of the tagged statement**, and discharges both from results already in the
repository. Clause 3 is not formalized; see *What is not done*.

Nothing mathematical is new here. The work is the spelling, and the two frictions it exposes --
one universe, one instance -- are recorded below.

## Main results

* `Stacks.InvertibleRankOneIff.isInvertible_of_isFiniteLocallyFreeOfRank_one`: **clause 1.** A
  sheaf of modules over `structureSheaf X.sheaf` that is finite locally free of rank one is
  invertible. No hypothesis on the stalks, no descent hypothesis. The content is
  `Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one`.
* `Stacks.InvertibleRankOneIff.isInvertible_iff_isFiniteLocallyFreeOfRank_one`: **clause 2, as a
  biconditional.** On a ringed space all of whose stalks are local rings, a sheaf of modules is
  invertible exactly when it is finite locally free of rank one. The forward implication is
  `Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible`; the reverse is clause 1,
  which needs no hypothesis on the stalks, so the local-stalk assumption is consumed by one
  direction only.

Both predicates are the library ones:
`AlgebraicGeometry.SheafOfModules.IsInvertible` of
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean` (Stacks Tag 01CS) and
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` of
`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean` (Stacks Tag 01C6, part 3). The structure
sheaf is `structureSheaf` of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact`
(Stacks Tag 01CO), the `RingCat`-valued sheaf obtained from `X.sheaf` by forgetting
commutativity.

## How the universes turned out

`AlgebraicGeometry.RingedSpace` has **two** universe parameters -- the rings' and the carrier's --
and `RingedSpace.{u}` leaves the second free. That matters, and the sibling file
`StacksFrontier/AlgebraicGeometry/SheafRankOne/Basic.lean` records the consequence: with the two
universes genuinely distinct, `CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X)
AddCommGrpCat.{u}` is **not** synthesized, so no sheaf-of-modules statement over the site of `X`
can be made at all. This has been checked and is true: for `X : RingedSpace.{u, v}` with `v`
unrelated to `u`, that instance search fails; for `X : RingedSpace.{u, u}` it succeeds.

The free universe is nevertheless harmless in the spelling used here, and this is the point of
the file. `structureSheaf` of Tag 01CO takes `Rc : TopCat.Sheaf CommRingCat.{v} Y` for
`Y : TopCat.{v}` -- carrier and rings in **one** universe. So the mere act of writing
`structureSheaf X.sheaf` unifies the two parameters of `X`, and `RingedSpace.{u}` elaborates as
`RingedSpace.{u, u}`: the sheafification instances are then found, and both statements below are
as universe-polymorphic as a ringed space whose rings live in `Type u` can be. The three site
universes and the module universe of `SheafOfModules` all collapse to `u`, which is what
`Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one` needs: its module universe is
`max u v w` rather than an independent `w`, because its hand-built dual quantifies over objects
and morphisms of the site.

Had the structure sheaf been written `Stacks.SheafOfModules.TensorSheafification.structureSheaf
  X.presheaf h𝒪` instead, the carrier
universe would have stayed free -- that spelling never mentions the carrier's universe -- and the
statement would not elaborate. The two spellings are definitionally equal objects with different
universe-inference behaviour.

## Transparency gotchas

One, and it is the known one. `Stacks.SheafOfModules.TensorSheafification.structureSheaf` is a
  `def`, so `structureSheaf X.sheaf`
of Tag 01CO and `Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
  (structureSheaf X.sheaf).property` are
definitionally equal (the underlying presheaves are equal by `rfl`, and the sheaf conditions are
proofs) but are not syntactically equal. Instance search is keyed syntactically, so the rank-one
hypothesis taken at the first spelling is not found at the second. Each direction therefore opens
with a one-line `have` restating the hypothesis at the spelling the applied theorem uses; the
definitional-equality check at `have` is at default transparency and goes through. The clause-2
forward direction needs the same restatement for invertibility, at `X.presheaf` in place of
`X.sheaf.obj`.

No compiler option is set, no attribute is made locally reducible, and no instance is introduced:
the two `have`s are the whole of the bridging.

## Stacks attributes

Tag 0B8M labels its three clauses separately, so each label is its own covering set and is
earned independently. The two proved here carry the tag, under the labels for rank-one local
freeness implying invertibility and for the characterization at local stalks, the first also
being an instance as the tagged statement declares it. The third label, for the failure of the
converse on a general ringed space, is deliberately withheld: its clause is unproved.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)

## What is not done

* **Clause 3 of Tag 0B8M** -- the one-point space whose ring has nontrivial Picard group, showing
  the converse fails without the local-stalk hypothesis -- is not formalized, here or anywhere in
  the repository, and nothing here bears on it. Two things are missing, independently. First, the
  witness: at this Mathlib pin no concrete commutative ring is proved to have a nontrivial Picard
  group. `Mathlib.RingTheory.PicardGroup` proves the Picard group *trivial* in every case it
  settles (local rings, finitely many maximal ideals, GCD domains), and even
  `Counterexamples.InvertibleModuleNotIdeal` takes `Nontrivial (CommRing.Pic R)` as a hypothesis
  rather than exhibiting an `R`. Second, the transport: invertibility here is the universal
  property of the tensor functor on sheaves of modules, so turning an invertible non-free
  `R`-module into an invertible sheaf of modules on the one-point site needs the comparison
  between that category and `ModuleCat R`, which the repository does not have.
* Nothing is proved about the stalks of the module, and no `AlgebraicGeometry.LocallyRingedSpace`
  form of either clause is given; the hypothesis is the explicit one that every stalk of the
  structure sheaf is a local ring.
* Neither clause is restated as an instance, and neither underlying theorem is reproved.
* No statement is made at the general-site generality that
  `Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one` and
  `Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible` already have; this file is
  only the ringed-space specialization at the spelling of the tagged statement.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.InvertibleRankOneIff

/-- **Clause 1 of Stacks Tag 0B8M.** A finite locally free module of rank one on a ringed space
is invertible. There is no hypothesis on the stalks of the structure sheaf, and none on the site.

The content is `Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one`; what is done
here is to restate it over `structureSheaf X.sheaf`, which forces the carrier universe of the
ringed space to agree with the universe of its rings and so makes the sheafification instances
available. -/
@[stacks 0B8M "locally free of rank one implies invertible", instance]
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one
    (X : RingedSpace.{u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) L 1] :
    SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L := by
  have hL : SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj (structureSheaf
        X.sheaf).property) L 1 :=
    inferInstanceAs (SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := structureSheaf X.sheaf) L 1)
  exact Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one _ _ L

/-- **Clause 2 of Stacks Tag 0B8M.** On a ringed space all of whose stalks `𝒪_{X, x}` are local
rings, a sheaf of modules is invertible exactly when it is finite locally free of rank one.

The forward implication is `Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible`
and is where the local-stalk hypothesis is spent; the reverse implication is clause 1, which
holds on every ringed space. -/
@[stacks 0B8M "characterization for local stalks"]
theorem isInvertible_iff_isFiniteLocallyFreeOfRank_one
    (X : RingedSpace.{u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)] :
    SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L ↔
      SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
        (J := Opens.grothendieckTopology X) L 1 := by
  refine ⟨fun h ↦ ?_, fun _ ↦ isInvertible_of_isFiniteLocallyFreeOfRank_one X L⟩
  have h' : SheafOfModules.IsInvertible X.presheaf (structureSheaf X.sheaf).property L := h
  exact Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible
    (X := X) (structureSheaf X.sheaf).property L

end Stacks.InvertibleRankOneIff

end
