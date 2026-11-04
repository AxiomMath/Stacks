module

public import StacksFrontier.AlgebraicGeometry.SectionRatioNoAmple.Pullback
public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.Basic

/-!
# Stacks Tag 09MW: ampleness across a thickening, with no Noetherian hypothesis

Let `i : Z ⟶ X` be a closed immersion of schemes inducing a homeomorphism of underlying
topological spaces and let `L` be an invertible `𝒪_X`-module. [Stacks, Tag 09MW] asserts

> `i^* L` is ample on `Z` if and only if `L` is ample on `X`.

This is [Stacks, Tag 09MS] with the Noetherian hypothesis on `Z` and `X` removed; the source
proves it by writing `X` as a directed limit of finite-type `ℤ`-schemes and applying
[Stacks, Tag 09MS] at a stage.

## Main results

* `Stacks.AmpleThickeningLimit.isAmple_modulePullback`: **the implication `L` ample `⟹` `i^* L`
  ample of [Stacks, Tag 09MW], with no hypothesis beyond the source's.** No Noetherian
  hypothesis anywhere, and no limit argument: a closed immersion is affine, hence quasi-affine,
  and part (2) of [Stacks, Tag 0892] is available for a quasi-affine morphism unconditionally.
* `Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback`: the converse implication, for
  `X` locally Noetherian and granted the cohomological lift
  `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`. The converse with no hypothesis beyond the
  source's is `Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback_of_isHomeomorph`, and
  the full tag is `Stacks.AmpleThickeningLimit.isAmple_modulePullback_iff_of_isHomeomorph`, both in
  `StacksFrontier/AlgebraicGeometry/AmpleThickeningLimit/Unconditional.lean`.
* `Stacks.AmpleThickeningLimit.isAmple_modulePullback_iff`: the biconditional, under the same two
  hypotheses as the converse.

## Which ampleness predicate

`Stacks.Ample.IsAmple`, the [Stacks, Tag 01PS] predicate of
`StacksFrontier/AlgebraicGeometry/AmpleWire/Basic.lean`, over which the whole 09MS/09MW cluster of
this repository is written, with invertibility as `Stacks.Ample.IsInvertibleModule`. The module
`i^* L` is written `(RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L`, which
is the spelling of the tagged statement and is what `Stacks.AmpleLocallyClosed.pullbackModule` is an
`abbrev` for, so the imported theorems apply to it directly.

No other ampleness predicate is used: one defined through a nonvanishing locus of Tag 01CY whose
openness is left as an unproved placeholder would put `sorryAx` into `#print axioms` of any proof
stated with it, however complete the proof. `StacksFrontier/AlgebraicGeometry/Inputs/Basic.lean` records the same
substitution for [Stacks, Tag 09MS] and checks the binder order of the tagged statement against it.

## The topological hypothesis

Stated as `IsHomeomorph i.base`, the source's own condition, rather than as `Surjective i`. For a
closed immersion the two are equivalent — a closed immersion is a homeomorphism onto a closed
subset, so it is a homeomorphism exactly when it is surjective — and the imported theorems are
stated with `Surjective i`; `Stacks.AmpleThickeningLimit.surjective_of_isHomeomorph_base`
performs the conversion. This repository has no predicate for "closed immersion inducing a
homeomorphism" as such: `Stacks.Thickenings.IsThickening` is about formal/adic thickenings and
`Stacks.AmpleClosedImmersion` and `Stacks.AmpleSurjectiveThickening` both spell the condition out
as `[IsClosedImmersion i] [Surjective i]`, so the condition is spelled out here too rather than
bundled into a new class.

## What is carried that the source does not have

`Stacks.AmpleThickeningLimit.isAmple_modulePullback` carries nothing the source lacks; it carries
the topological hypothesis without using it, which is noted on the declaration.

The converse carries two hypotheses the source does not have, and both are named in its clause
label:

* `[IsLocallyNoetherian X]`. [Stacks, Tag 09MW] has no Noetherian hypothesis; this is what its
  limit argument removes from [Stacks, Tag 09MS], and that argument is not carried out here.
* `hlift : Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L`, the cohomological lift, which
  is the one input the converse of [Stacks, Tag 09MS] still owes in this repository.
  `StacksFrontier/AlgebraicGeometry/AmpleSurjectiveThickening/Basic.lean` discharges the other input,
  Chevalley's criterion, outright.

So the converse clause below is **weaker than the source**, and it carries no tag attribute: the
tag is carried by `Stacks.AmpleThickeningLimit.isAmple_modulePullback_iff_of_isHomeomorph`. The
forward clause is the source's own statement.

## References

* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.AmpleThickeningLimit

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- A morphism whose underlying map is a homeomorphism is surjective. This is the conversion
between the source's topological hypothesis on `i` and the `Surjective i` instance the imported
theorems are stated with. -/
theorem surjective_of_isHomeomorph_base (hi : IsHomeomorph i.base) : Surjective i :=
  ⟨hi.surjective⟩

/-- **The implication `L` ample `⟹` `i^* L` ample of [Stacks, Tag 09MW].** For a closed immersion
`i : Z ⟶ X` inducing a homeomorphism of underlying spaces and an invertible `𝒪_X`-module `L`,
ampleness of `L` gives ampleness of `i^* L`. No Noetherian hypothesis.

The homeomorphism hypothesis is **not used** — hence its binder is named `_hi`: the proof needs
only that `i` is an affine morphism. It is carried so that this is literally one half of the
source statement rather than a
more general lemma wearing the tag of [Stacks, Tag 09MW]. Neither is this half of the source any
harder than part (2) of [Stacks, Tag 0892] for a quasi-affine morphism, which
`Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom` proves with no premise; a
closed immersion is affine, and an affine morphism is quasi-affine because the inverse image of an
affine open is affine.

This is `Stacks.AmpleSurjectiveThickening.isAmple_modulePullback` — the same half of
[Stacks, Tag 09MS] — with its `[Surjective i]` and `[IsNoetherian X]` hypotheses dropped, which is
exactly the difference between the two tags on this side of the biconditional. -/
@[stacks 09MW "the implication `L` ample ⟹ `i^* L` ample"]
theorem isAmple_modulePullback [IsClosedImmersion i] (_hi : IsHomeomorph i.base)
    (hL : IsAmple X L) :
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) := by
  have : IsQuasiAffineHom i := by
    refine ⟨fun U hU => ?_⟩
    have : IsAffine (i ⁻¹ᵁ U).toScheme := hU.preimage i
    infer_instance
  exact Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom i L hL

/-- **A special case of the implication `i^* L` ample `⟹` `L` ample of [Stacks, Tag 09MW], for `X`
locally Noetherian and granted the cohomological lift.** For a closed immersion `i : Z ⟶ X`
inducing a homeomorphism of underlying spaces onto a locally Noetherian scheme, ampleness of
`i^* L` gives ampleness of `L`, granted `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L`.
The implication with neither hypothesis is
`Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback_of_isHomeomorph`, the `mp` half of
`Stacks.AmpleThickeningLimit.isAmple_modulePullback_iff_of_isHomeomorph`, which carries the tag.

**Two hypotheses the source does not have.** `[IsLocallyNoetherian X]` is what the limit argument
of [Stacks, Tag 09MW] exists to remove, and that argument is not carried out here; `hlift` is the
cohomological lift that the converse of [Stacks, Tag 09MS] still owes in this repository. Both
are used. Quasi-compactness of `X` is *not* assumed: it comes from quasi-compactness of `Z`,
which ampleness of `i^* L` asserts, along the surjection, which is why the source's `Noetherian`
weakens to `IsLocallyNoetherian` here.

The proof is `Stacks.AmpleSurjectiveThickening.isAmple_of_isAmple_modulePullback`, which has
Chevalley's criterion for a surjective closed immersion already discharged. -/
theorem isAmple_of_isAmple_modulePullback [IsClosedImmersion i] (hi : IsHomeomorph i.base)
    [IsLocallyNoetherian X]
    (hlift : Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L)
    (h : IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L)) :
    IsAmple X L :=
  have : Surjective i := surjective_of_isHomeomorph_base i hi
  Stacks.AmpleSurjectiveThickening.isAmple_of_isAmple_modulePullback i L hlift h

/-- **[Stacks, Tag 09MW] for `X` locally Noetherian, granted the cohomological lift.** The
biconditional. The `mpr` half is `Stacks.AmpleThickeningLimit.isAmple_modulePullback`, which uses
neither hypothesis; the `mp` half is
`Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback`, which uses both. No attribute is
attached to the biconditional: a biconditional carrying hypotheses the source does not make is not
the source statement. The biconditional with neither hypothesis is
`Stacks.AmpleThickeningLimit.isAmple_modulePullback_iff_of_isHomeomorph`. -/
theorem isAmple_modulePullback_iff [IsClosedImmersion i] (hi : IsHomeomorph i.base)
    [IsLocallyNoetherian X]
    (hlift : Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L) :
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) ↔ IsAmple X L :=
  ⟨isAmple_of_isAmple_modulePullback i L hi hlift, isAmple_modulePullback i L hi⟩

end Stacks.AmpleThickeningLimit

end
