module

public import StacksFrontier.AlgebraicGeometry.HighTwistVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherRank.Basic

/-!
# The dévissage half of the converse of [Stacks, Tag 0B5V]

The converse of [Stacks, Tag 0B5V] — ampleness of `L` from ampleness of `f^* L` along a finite
surjective `f` — is proved in the source by verifying clause (2) of the cohomological criterion
[Stacks, Tag 0B5U] for `L` on `X`, i.e. that every coherent `𝒪_X`-module `ℱ` satisfies
`Stacks.HighTwistVanishing.HasHighTwistVanishing L ℱ`. That verification is the cohomological
dévissage [Stacks, Tag 01YM] applied to this property, and 01YM has four hypotheses.

Three of them are discharged for this property with no geometry, in
`StacksDraft.AlgebraicGeometry.F3.HighTwistVanishing.Basic`. This file feeds them to the
01YM engine, leaving clause (3) — the geometric one — as the single remaining hypothesis.

## Main results

* `Stacks.HighTwistVanishing.forall_of_hgeneric`: on a Noetherian scheme, 01YM's clause (3) for
  `HasHighTwistVanishing L` gives the property on every coherent module, modulo the two
  hypotheses the 01YM engine itself still carries ([Stacks, Tag 01YE] and
  [Stacks, Tag 01YL]).

## What this leaves: nothing

Writing `⟸` for the converse of [Stacks, Tag 0B5V], `forall_of_hgeneric` leaves exactly clause
(3) of [Stacks, Tag 01YM] for this property. **That clause is now proved**, as
`Stacks.AmpleFiniteSurjective.exists_coherent_generic_highTwist` in
`../AmpleFiniteSurjective/Basic.lean`, and with it the whole of [Stacks, Tag 0B5V]:
`Stacks.AmpleFiniteSurjective.isAmple_iff_isAmple_modulePullback` carries the bare tag. Clause
(3)'s module `G` is `f_* ℱ` for the `ℱ` of [Stacks, Tag 01YO], proved and tagged as
`exists_isCoherent_supp_pushforward_eq_range` in
`Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport`, and its ideal multiples come from
[Stacks, Tag 01YP]
(`Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf.idealPowSmul_pushforward_eq`).

The other inputs the converse uses are all in the library:

1. *the projection formula [Stacks, Tag 01E8]*: `@[stacks 01E8]` is attached at ten
   sites under `StacksFrontier/AlgebraicGeometry/ProjectionFormula/`, including the ringed-space
   forms in `ProjectionFormula/HigherDirectImageRingedSpace.lean`. What the converse actually
   needs is only the **degree-zero** clause for an invertible module,
   `Stacks.ProjectionFormula.pushforwardTensorRightNatIso`
   (`../ProjectionFormula/HigherDirectImage.lean:221`), not the higher direct images;
2. *[Stacks, Tag 0B5T], Serre vanishing*: `@[stacks 0B5T]` is attached
   twice in `../ProperAmpleCohomology/Basic.lean`, and the clause (4) the converse uses is
   `exists_isZero_Hgroup_tensorPowTwist` (`:181`). Its input [Stacks, Tag 02O5] is attached too,
   at `../ProperCoherenceWitness/ChowStalk.lean:297` and `:313`;
3. *the direction `(3) ⟹ (1)` of [Stacks, Tag 0B5U], which is [Stacks, Tag 0B5P]*:
   `AlgebraicGeometry.Scheme.Modules.isAmple_of_hasIdealTwistH1Vanishing`
   (`../AmpleDegreeCriterion/CohomologicalCriterion.lean:179`), over
   `isAmple_of_forall_isZero_h1_quasicoherentIdeal`, which carries `@[stacks 0B5P]` at
   `../AmpleDegreeCriterion/QuasicoherentIdeal.lean:207`.

Tag 01YO and the dévissage of Tag 01YM are likewise proved, and both are what the proof of the
converse uses.

## Implementation notes

**No `stacks` attribute is attached.** [Stacks, Tag 0B5V] is a single unlabelled biconditional,
so a step of its converse is not a clause of it, and the theorem below
carries three hypotheses the tag does not grant.

## References

* [Stacks Project, Tag 0B5V](https://stacks.math.columbia.edu/tag/0B5V)
* [Stacks Project, Tag 01YM](https://stacks.math.columbia.edu/tag/01YM)
* [Stacks Project, Tag 01YO](https://stacks.math.columbia.edu/tag/01YO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.HighTwistVanishing

/-- **[Stacks, Tag 01YM] applied to `HasHighTwistVanishing`, with only its geometric clause left
as a hypothesis.** On a Noetherian scheme carrying an invertible `L`, if for every integral closed
subscheme there is a coherent module supported exactly there, with annihilated generic stalk, and
with a generically-surjective coherent subsheaf of every ideal multiple satisfying
`HasHighTwistVanishing L`, then every coherent `𝒪_X`-module satisfies it.

The three non-geometric hypotheses of 01YM are discharged here from
`Stacks.HighTwistVanishing.terminal`, `Stacks.HighTwistVanishing.of_shortExact` and
`Stacks.HighTwistVanishing.of_finiteProduct`. The two remaining parameters `h01YE` and `h01YL`
are the ones the 01YM engine
`Stacks.AlgebraicGeometry.Tag01YMHigherRank.property_higher_rank_of_criteria` itself still
carries; they are properties of `X` alone and have nothing to do with `L`. -/
theorem forall_of_hgeneric (X : Scheme.{u}) [IsNoetherian X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (h01YE : Stacks.AlgebraicGeometry.Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub X)
    (h01YL : Stacks.AlgebraicGeometry.Tag01YMHigherRank.HasIrreducibleHigherRankCriterion X)
    (hgeneric : ∀ (I : X.IdealSheafData) [IsIntegral I.subscheme],
      ∃ G : X.Modules, G.IsCoherent ∧
        (∀ x : X, x ∈ I.support ↔ Nontrivial (G.presheaf.stalk x)) ∧
        Stacks.AlgebraicGeometry.Tag01YEStalkBridge.IsMaximalIdealAnnihilated G
          (I.subschemeι (genericPoint I.subscheme)) ∧
        (∀ J : X.IdealSheafData,
          I.subschemeι (genericPoint I.subscheme) ∉ J.support →
          ∃ G' : G.Submodule,
            G'.toSheafOfModules.IsCoherent ∧
            (∀ (U : X.affineOpens) (s : Γ(G'.toSheafOfModules, U.1)),
              (Scheme.Modules.Hom.app G'.ι U.1 s : Γ(G, U.1)) ∈
                J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) ∧
            Function.Surjective
              (((TopCat.Presheaf.stalkFunctor Ab
                (I.subschemeι (genericPoint I.subscheme))).map
                  (Scheme.Modules.Hom.mapPresheaf G'.ι)).hom) ∧
            HasHighTwistVanishing L G'.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → HasHighTwistVanishing L F :=
  Stacks.AlgebraicGeometry.Tag01YMHigherRank.property_higher_rank_of_criteria X h01YE h01YL
    (HasHighTwistVanishing L) (terminal L)
    (fun _ hS _ _ _ h₁ h₃ => of_shortExact hS h₁ h₃)
    (fun F _ ⟨_, hn⟩ => of_finiteProduct F hn)
    hgeneric

end Stacks.HighTwistVanishing

end
