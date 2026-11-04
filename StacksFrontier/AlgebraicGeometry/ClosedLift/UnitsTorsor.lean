module

public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.ModuleAssociatedToAUnitTorsor
public import StacksFrontier.AlgebraicGeometry.SheafDescent.Basic
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 09NU's two halves at Tag 09NU's own hypothesis

Stacks Tag 09NU identifies the invertible modules on a ringed space, up to isomorphism, with the
torsors under the sheaf of units `𝒪_X^*`, hence with `H¹(X, 𝒪_X^*)`. Both halves of the
correspondence are built in `StacksDraft.Ch20.Sec6.Tag09NUGenerators` and
`StacksDraft.Ch20.Sec6.Tag09NUAssociated`, but they are stated with the hypothesis
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank L 1` in place of Tag 09NU's own
hypothesis, invertibility. The two clauses of Stacks Tag 0B8M make the
hypotheses interchangeable.

**This file is that composition.** Clause 1 of Tag 0B8M
is `Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one`, which is unconditional;
clause 2 on a scheme is
`Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme`, with no
hypothesis on the stalks. Composing each with the corresponding half of Tag 09NU gives the two
statements below. No new mathematics is involved; the content is that the two existing
derivations compose.

## Main results

* `Stacks.AlgebraicGeometry.Tag09NY.isInvertible_torsorAssociatedSheafOfModules`: the sheaf of
  modules glued from a torsor under `𝒪_X^*` is **invertible**, on an arbitrary ringed space. This
  is the surjectivity half of Tag 09NU at Tag 09NU's own conclusion; the existing statement stops
  at rank-one local freeness.
* `Stacks.AlgebraicGeometry.Tag09NY.generatorTorsorOfIsInvertible`: an **invertible** sheaf of
  modules on a scheme has a torsor of generators under `𝒪_X^*`. This is the injectivity half at
  Tag 09NU's own hypothesis; the existing statement asks for rank-one local freeness.

## Why there is no `stacks` attribute here

Tag 09NU's assertion is a *bijection* between isomorphism classes of invertible modules and
`H¹(X, 𝒪_X^*)`, and this file supplies neither direction's inverse: the two round-trip
identifications are `Stacks.Cohomology.Generators.torsorAssociatedGeneratorTorsorHom_isIso` and
`Stacks.Cohomology.Generators.generatorTorsor_iso_of_iso`, and assembling them with
`Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne` into the bijection is the work
that remains. Attaching the tag to either statement below would be a claim about a covering set
that is not complete, so none is attached. The second statement also carries a hypothesis Tag
09NU does not — that the ringed space is a scheme — because clause 2 of Tag 0B8M is proved in
that generality; the ringed-space form of clause 2 needs local stalks, which Tag 09NU does
hypothesise, so this is a restriction of convenience, not of substance.

## Implementation notes

**Both statements are a spelling exercise, and the spelling is the whole difficulty.** Three
definitionally equal descriptions of the structure sheaf of rings meet here —
`Stacks.structureSheaf X.sheaf` (a `sheafCompose` of the `CommRingCat`-valued sheaf, which Tag
09NU is stated over), `Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO` (a pair of a
  presheaf and a proof, which
Tag 0B8M clause 1 is stated over) and `AlgebraicGeometry.Scheme.ringCatSheaf` (which clause 2 is
stated over) — and **instance search crosses none of them**. Concretely: the rank-one
hypothesis of `Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one` cannot be
synthesized even though the instance `torsorAssociatedSheafOfModules_isFiniteLocallyFreeOfRank`
applies, because the goal is at the `Stacks.SheafOfModules.TensorSheafification.structureSheaf`
  spelling and the instance at the
`Stacks.structureSheaf` one. The fix in both proofs is the same and needs no compiler option: put
the hypothesis in the local context **with its ring sheaf given explicitly as a named implicit
argument**, where the defeq is checked by `isDefEq` at default transparency rather than by
instance synthesis, and let the local instance be found. No `eqToHom`, no transport and no module
sheaf is moved anywhere.

## References

* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.Cohomology.Generators

universe u

namespace Stacks.AlgebraicGeometry.Tag09NY

/-! ### The surjectivity half of Tag 09NU, at Tag 09NU's conclusion -/

/-- **The sheaf of modules glued from a torsor under `𝒪_X^*` is invertible.**

`Stacks.Cohomology.Generators.torsorAssociatedSheafOfModules_isFiniteLocallyFreeOfRank` proves
unconditionally that the glued module is finite locally free of rank one, and clause 1 of Stacks
Tag 0B8M, `Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one`, turns that into
invertibility with no descent hypothesis. The header of
`StacksDraft.Ch20.Sec6.Tag09NUAssociated` says of exactly this step that "nothing in this
development concludes that"; it is concluded here. -/
theorem isInvertible_torsorAssociatedSheafOfModules
    {X : _root_.AlgebraicGeometry.RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)}
    (D : TorsorCoverData X F) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheaf X.sheaf).property (torsorAssociatedSheafOfModules D) := by
  have rankOne : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj (structureSheaf
        X.sheaf).property)
      (torsorAssociatedSheafOfModules D) 1 :=
    torsorAssociatedSheafOfModules_isFiniteLocallyFreeOfRank D
  exact Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one X.sheaf.obj
    (structureSheaf X.sheaf).property (torsorAssociatedSheafOfModules D)

/-! ### The generator half of Tag 09NU, at Tag 09NU's hypothesis -/

/-- **An invertible sheaf of modules on a scheme has a torsor of generators under `𝒪_X^*`.**

`Stacks.Cohomology.Generators.generatorTorsor` asks for the module to be finite locally free of
rank one; clause 2 of Stacks Tag 0B8M on a scheme,
`Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme`, supplies that from
invertibility with no hypothesis on the stalks, since the stalks of a scheme are local rings. The
header of `StacksDraft.Ch20.Sec6.Tag09NUGenerators` says of exactly this step that it is "clause
2 of Tag 0B8M, which nothing in this development concludes"; it is concluded here.

Invertibility is an explicit argument rather than an instance binder, because instance search
does not see through `AlgebraicGeometry.Scheme.ringCatSheaf`. -/
@[ega "IV 21.13.13" "special case", sga "4½ Cycle 1.1.6"]
def generatorTorsorOfIsInvertible (X : Scheme.{u})
    (L : SheafOfModules.{u} X.ringCatSheaf)
    (hL : _root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    GeneratorTorsor X.toRingedSpace L := by
  have rankOne : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := X.ringCatSheaf) L 1 :=
    @Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X L hL
  exact generatorTorsor X.toRingedSpace L

end Stacks.AlgebraicGeometry.Tag09NY

end
