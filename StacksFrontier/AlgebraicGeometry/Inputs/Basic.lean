module

public import StacksFrontier.AlgebraicGeometry.AmpleClosedImmersion.Converse
public import StacksFrontier.AlgebraicGeometry.SerreCriterionH1.Hgroup

/-!
# Stacks Tag 09MS: its first input is Serre's criterion, and the statement is faithful

[Stacks, Tag 09MS] asserts that for a surjective closed immersion `i : Z ⟶ X` of Noetherian
schemes and an invertible `𝒪_X`-module `L`, the module `i^* L` is ample on `Z` if and only if `L`
is ample on `X`. `Stacks.AmpleClosedImmersion.isAmple_modulePullback_iff` proves the
biconditional from two hypotheses —
`Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion` (a scheme
receiving a surjective closed immersion from an affine scheme is affine) and
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` (the cohomological lift) — and records both
as open with no route.

This file does two things, neither of which is new mathematics.

1. **It discharges the first hypothesis down to one cohomological vanishing.** Serre's
   criterion is in the library and carries the attribute for
   [Stacks, Tag 01XF] — `Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal`, with the
   repository-cohomology
   spelling `Stacks.SerreCriterionH1.isAffine_of_forall_isZero_hgroup_one_ideal` — and it gives
   the first input directly, with no finiteness, no dévissage and no appeal to Tag 01YQ at all:
   quasi-compactness of the target is inherited from the affine source along the surjection.

2. **It records the faithfulness of the theorem against the source statement of the tag**, in
   its binder order and with its own expression `(modulePullback
   i.toLRSHom.toShHom).obj L` for `i^* L`, so that the two hypotheses the biconditional
   carries are exactly visible as the obstruction to the covering set.

## Main definitions

* `Stacks.Tag09MSInputs.IdealCohomologyVanishesOnThickening`: for a surjective closed immersion
  from an affine scheme into a locally Noetherian scheme, the first cohomology of every
  quasi-coherent sheaf of ideals on the target vanishes. This is the specialization to a
  thickening of the vanishing that the source of [Stacks, Tag 01YQ] establishes by the dévissage
  [Stacks, Tag 01YM]; it is a true statement, not a vacuous one, and on the source's intended
  route it is proved from nilpotence of the ideal ([Stacks, Tag 01Y9]).

## Main results

* `Stacks.Tag09MSInputs.affineOfSurjectiveClosedImmersion_of_isZero_hgroup`: the first input of
  [Stacks, Tag 09MS] follows from that vanishing **and from Serre's criterion alone**.
* `Stacks.Tag09MSInputs.isAmple_modulePullback_iff_of_isZero_hgroup`: [Stacks, Tag 09MS] with its
  first hypothesis replaced by the vanishing, so that both of its remaining obligations are
  cohomological statements about the thickening rather than one of them being an affineness
  criterion with no route.

## What is not done, and why no attribute is attached

**[Stacks, Tag 09MS] is not proved and no `stacks` attribute is attached in this directory.** The
tag is a single *biconditional* carrying one unlabelled attribute, so no part of it can be
registered separately, and the theorem below still carries two hypotheses the source does not
grant. The two remaining obligations need [Stacks, Tag 01Y9] (nilpotence of the ideal of a
surjective closed immersion into a Noetherian scheme), [Stacks, Tag 0B8S] (the boundary map of the
graded sum is a derivation) and [Stacks, Tag 01XR], none of which is formalized in the library,
under its tag or under another name.

[Stacks, Tag 01QY] is a different and better case.
Its content is available at the level of ringed **topoi**, which is [Stacks, Tag 08M3]:
`AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful`
(`Algebra/Category/ModuleCat/Sheaf/PushforwardFullyFaithful/Basic.lean:147`) and
`AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardEssentialImageDirect/Criterion.lean`
line 129), the second of which characterizes the essential image exactly by annihilation by
the kernel ideal. What remains is therefore the
08KS-from-08M3 **bridge**, whose local-surjectivity half is also proved
(`Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isLocallySurjective_c_of_isClosedImmersion`,
`StacksFrontier/AlgebraicGeometry/ClosedImmersionTFAE/Basic.lean`), and not the theorem.

[Stacks, Tag 01XB] and [Stacks, Tag 089W], the cohomological inputs that *are* available, are not
enough on their own: what is missing is the filtration of a quasi-coherent module by the powers
of the ideal, which no declaration in the library constructs.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.Tag09MSInputs

/-! ### The first input of Stacks Tag 09MS is Serre's criterion -/

/-- **The vanishing that the first input of [Stacks, Tag 09MS] needs.** For every surjective
closed immersion `j : A ⟶ B` with `A` affine and `B` locally Noetherian, the first cohomology of
every quasi-coherent sheaf of ideals on `B` vanishes.

This is the hypothesis of Serre's criterion, quantified over exactly the situations the first
input of [Stacks, Tag 09MS] ranges over, and nothing more: the universal quantifier is bounded by
the existence of the thickening, so this is the specialization of the vanishing of [Stacks, Tag
01YQ] and not the false blanket claim that `H¹` of an ideal sheaf vanishes on any quasi-compact
scheme. On the source's route it is proved by filtering a quasi-coherent module by the powers of
the ideal of `j`, which are finitely many because that ideal is nilpotent ([Stacks, Tag 01Y9]),
and identifying the successive quotients with pushforwards from the affine `A` ([Stacks, Tag
01QY], [Stacks, Tag 089W]). -/
def IdealCohomologyVanishesOnThickening : Prop :=
  ∀ (A B : Scheme.{u}) (j : A ⟶ B), IsClosedImmersion j → Surjective j →
    IsLocallyNoetherian B → IsAffine A →
    ∀ I : Subobject (SheafOfModules.unit B.ringCatSheaf),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (Hgroup B.ringCatSheaf ⊤ 1 (Subobject.underlying.obj I))

/-- **The first input of [Stacks, Tag 09MS] from Serre's criterion.** If `H¹(B, 𝓘) = 0` for every
quasi-coherent sheaf of ideals on a locally Noetherian scheme `B` receiving a surjective closed
immersion from an affine scheme, then every such `B` is affine.

Neither finiteness nor [Stacks, Tag 01YQ] is used: [Stacks, Tag 01XF] needs only
quasi-compactness of `B`, which is the image of the quasi-compact `A` under a surjection
(`Stacks.AmpleClosedImmersion.compactSpace_of_surjective`). This replaces the recorded status of
`Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion` — "Stacks Tag 01YQ has no
attachment anywhere in either tree" — which was true when written and was overtaken by the
landing of Serre's criterion. -/
theorem affineOfSurjectiveClosedImmersion_of_isZero_hgroup
    (hvan : IdealCohomologyVanishesOnThickening.{u}) :
    Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion.{u} := by
  intro A B j hji hjs hB hA
  have := hji
  have := hA
  have : CompactSpace B :=
    Stacks.AmpleClosedImmersion.compactSpace_of_surjective j hjs inferInstance
  exact Stacks.SerreCriterionH1.isAffine_of_forall_isZero_hgroup_one_ideal B
    (hvan A B j hji hjs hB hA)

/-! ### Stacks Tag 09MS with its first hypothesis replaced -/

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **[Stacks, Tag 09MS] from the cohomological vanishing and the section lift.** For a surjective
closed immersion `i : Z ⟶ X` of Noetherian schemes and an invertible `𝒪_X`-module `L`, the module
`i^* L` is ample on `Z` exactly when `L` is ample on `X`, granted the vanishing
`Stacks.Tag09MSInputs.IdealCohomologyVanishesOnThickening` and the lift
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`.

The `mpr` direction uses neither hypothesis; it is
`Stacks.AmpleClosedImmersion.isAmple_modulePullback_of_surjective_isClosedImmersion`, which is
unconditional.
Both remaining hypotheses are statements about cohomology of the thickening, which is what
makes what remains of Tag 09MS legible. -/
theorem isAmple_modulePullback_iff_of_isZero_hgroup [IsClosedImmersion i] [Surjective i]
    [IsNoetherian X] (hvan : IdealCohomologyVanishesOnThickening.{u})
    (hlift : Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L) :
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) ↔ IsAmple X L :=
  Stacks.AmpleClosedImmersion.isAmple_modulePullback_iff i L
    (affineOfSurjectiveClosedImmersion_of_isZero_hgroup hvan) hlift

/-! ### Faithfulness against the source statement

The statement of Tag 09MS reads, in this binder order,

    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i] [IsNoetherian X]
      (L : X.Modules) [invertible L] :
      IsAmple Z ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L)
        ↔ IsAmple X L

with ampleness realized here by the library's [Stacks, Tag 01PS] predicate
`Stacks.Ample.IsAmple` and the
invertibility instance replaced by `Stacks.Ample.IsInvertibleModule`. The module `i^* L` is
written with the
**original expression**, not with the `Stacks.AmpleLocallyClosed.pullbackModule` abbreviation the
theorems are stated over, so that the two spellings are checked to agree rather than
assumed to. -/

example {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i] [IsNoetherian X]
    (L : X.Modules) [IsInvertibleModule X L]
    (hchev : Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion.{u})
    (hlift : Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L) :
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) ↔ IsAmple X L :=
  Stacks.AmpleClosedImmersion.isAmple_modulePullback_iff i L hchev hlift

/-- The `mpr` half carries no hypothesis the source statement lacks, which is why the obstruction
to Tag 09MS is the `mp` half alone; the tag's single unlabelled attribute covers the whole
biconditional, so neither half is registered separately. -/
example {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i] [IsNoetherian X]
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L) :
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) :=
  Stacks.AmpleClosedImmersion.isAmple_modulePullback_of_surjective_isClosedImmersion i L hL

end Stacks.Tag09MSInputs

end
