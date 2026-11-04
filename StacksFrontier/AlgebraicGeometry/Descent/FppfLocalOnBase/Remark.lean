module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FppfLocalOnBase.Entries

/-!
# Remark 02WH as a single statement

Tag 02WH is a list: twenty-four properties of morphisms of schemes, each asserted to be *fpqc
local on the base* and a fortiori *fppf local on the base*, followed by the caveat that being an
immersion in general is only known to be fppf local on the base.

`StacksFrontier/AlgebraicGeometry/Descent/FppfLocalOnBase/Entries.lean` states the entries one at a
time. This file states the remark *whole*: a single theorem whose conclusion is the conjunction of
all twenty-four entries together with the closing caveat, so that the content of the remark can be
read off one statement. Nothing new is proved — the proof is the list of the entry-by-entry
theorems of `Entries.lean`.

## Main results

* `Stacks.Descent.fpqcAndFppfLocalOnBase_allEntries_and_isImmersion_fppf` — Remark 02WH in full.

## Implementation notes

Each entry contributes a three-fold conjunct: the property that entry names is stable under
arbitrary base change, it is local on the base for the fpqc precoverage, and it is local on the
base for the fppf precoverage. The third is the remark's parenthetical "a fortiori", and it is
asserted rather than left to the reader.

The twenty-fifth conjunct, the remark's last sentence, asserts of immersions *only* stability under
base change and fppf locality. It deliberately has no fpqc conjunct: the remark says that being an
immersion may fail to be fpqc local on the base, and only the three cases of entry (1) — closed,
open and quasi-compact immersions — are claimed fpqc local.

Seven of the twenty-four entries have two readings in Lean, because the source states them with a
parenthesis or a disjunction: `(quasi-)separated`, `(locally) of finite type`, `(locally)
quasi-finite`, `(locally) of finite presentation`, `unramified (resp. G-unramified)`, `finite or
integral`, and finite locally free with the rank unconstrained or fixed. Each such entry is a
conjunction of its two readings, so both are asserted. Entry (1) is a conjunction of its three
cases. The two entries carrying a numerical parameter — relative dimension `d` in entry (13) and
rank `d` in entry (22) — are universally quantified over it.

## References

* [Stacks Project, Tag 02WH](https://stacks.math.columbia.edu/tag/02WH)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-- **Stacks Project, Remark 02WH, in full.** Of the properties of morphisms of schemes which are
stable under base change, the following twenty-four are also *fpqc local on the base*, and a
fortiori *fppf local on the base*:

1. immersions, in the three cases
   (a) closed immersions (Descent, Lemma 02L6),
   (b) open immersions (Descent, Lemma 02L3), and
   (c) quasi-compact immersions (Descent, Lemma 02L8);
2. quasi-compact (Descent, Lemma 02KQ);
3. universally closed (Descent, Lemma 02KS);
4. (quasi-)separated (Descent, Lemmas 02KR and 02KU);
5. monomorphism (Descent, Lemma 02YK);
6. surjective (Descent, Lemma 02KV);
7. universally injective (Descent, Lemma 02KW);
8. affine (Descent, Lemma 02L5);
9. quasi-affine (Descent, Lemma 02L7);
10. (locally) of finite type (Descent, Lemmas 02KX and 02KZ);
11. (locally) quasi-finite (Descent, Lemma 02VI);
12. (locally) of finite presentation (Descent, Lemmas 02KY and 02L0);
13. locally of finite type of relative dimension `d` (Descent, Lemma 02VJ);
14. universally open (Descent, Lemma 02KT);
15. flat (Descent, Lemma 02L2);
16. syntomic (Descent, Lemma 02VK);
17. smooth (Descent, Lemma 02VL);
18. unramified, resp. G-unramified (Descent, Lemma 02VM);
19. étale (Descent, Lemma 02VN);
20. proper (Descent, Lemma 02L1);
21. finite or integral (Descent, Lemma 02LA);
22. finite locally free (Descent, Lemma 02VO), with the rank unconstrained or fixed;
23. universally submersive (Descent, Lemma 0CEW);
24. universal homeomorphism (Descent, Lemma 0CEX).

The final conjunct is the remark's last sentence: the property of being an immersion may *not* be
fpqc local on the base, but it is stable under base change and fppf local on the base, by Descent,
Lemma 02YM. No fpqc locality is asserted of immersions in general. -/
@[stacks 02WH "The remark in full, as one conjunction in the source's order: entry (n) is the \
n-th conjunct, and each conjunct states that the property that entry names is stable under \
arbitrary base change, local on the base for the fpqc precoverage, and a fortiori local on the \
base for the fppf precoverage. Entry (1) is the conjunction of its three cases, (a) closed, (b) \
open and (c) quasi-compact immersions; each entry with two readings, namely (4), (10), (11), \
(12), (18), (21) and (22), is the conjunction of both readings; and entries (13) and (22) are \
quantified over their numerical parameter. The twenty-fifth and last conjunct is the remark's \
closing sentence: being an immersion is stable under arbitrary base change and local on the base \
for the fppf precoverage, which is Descent, Lemma 02YM.",
  ega "IV 17.3.3" "(iii)",
  ega "IV 2.6.4" "more general",
  ega "IV 2.7.1" "more general",
  sga "1 IX 2.4" "special case",
  sga "1 IX 4.2" "Étaleness",
  sga "1 VIII 5.5" "more general",
  sga "3 IV 4.7" "(a)",
  sga "3 IV 6.4.1",
  sga "3 VIB 2.1.2",
  sga "3 VIIA 8.3.1" "Smoothness entry (17)",
  sga "3 XI 6.8" "partial"]
public theorem fpqcAndFppfLocalOnBase_allEntries_and_isImmersion_fppf :
    -- entry (1)(a), (b), (c): closed, open and quasi-compact immersions
    ((MorphismProperty.IsStableUnderBaseChange (@IsClosedImmersion : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@IsClosedImmersion : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@IsClosedImmersion : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
      (MorphismProperty.IsStableUnderBaseChange (@IsOpenImmersion : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@IsOpenImmersion : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@IsOpenImmersion : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
      (MorphismProperty.IsStableUnderBaseChange
           (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage)) ∧
    -- entry (2): quasi-compact
    (MorphismProperty.IsStableUnderBaseChange (@QuasiCompact : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@QuasiCompact : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@QuasiCompact : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (3): universally closed
    (MorphismProperty.IsStableUnderBaseChange (@UniversallyClosed : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@UniversallyClosed : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@UniversallyClosed : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (4): separated, and quasi-separated
    ((MorphismProperty.IsStableUnderBaseChange (@IsSeparated : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@IsSeparated : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@IsSeparated : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
      (MorphismProperty.IsStableUnderBaseChange (@QuasiSeparated : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@QuasiSeparated : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@QuasiSeparated : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage)) ∧
    -- entry (5): monomorphism
    (MorphismProperty.IsStableUnderBaseChange (MorphismProperty.monomorphisms Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (MorphismProperty.monomorphisms Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (MorphismProperty.monomorphisms Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (6): surjective
    (MorphismProperty.IsStableUnderBaseChange (@Surjective : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@Surjective : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@Surjective : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (7): universally injective
    (MorphismProperty.IsStableUnderBaseChange
         (@UniversallyInjective : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@UniversallyInjective : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@UniversallyInjective : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (8): affine
    (MorphismProperty.IsStableUnderBaseChange (@IsAffineHom : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@IsAffineHom : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@IsAffineHom : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (9): quasi-affine
    (MorphismProperty.IsStableUnderBaseChange (@IsQuasiAffineHom : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@IsQuasiAffineHom : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@IsQuasiAffineHom : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (10): locally of finite type, and of finite type
    ((MorphismProperty.IsStableUnderBaseChange
           (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
      (MorphismProperty.IsStableUnderBaseChange
           (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
           Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
           Scheme.fppfPrecoverage)) ∧
    -- entry (11): locally quasi-finite, and quasi-finite
    ((MorphismProperty.IsStableUnderBaseChange
           (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u})
           Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u})
           Scheme.fppfPrecoverage) ∧
      (MorphismProperty.IsStableUnderBaseChange
           ((@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ⊓
             @LocallyQuasiFinite) ∧
       MorphismProperty.IsLocalAtTarget
           ((@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ⊓
             @LocallyQuasiFinite) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           ((@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ⊓
             @LocallyQuasiFinite) Scheme.fppfPrecoverage)) ∧
    -- entry (12): locally of finite presentation, and of finite presentation
    ((MorphismProperty.IsStableUnderBaseChange
           (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
      (MorphismProperty.IsStableUnderBaseChange
           (@FinitePresentation : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@FinitePresentation : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@FinitePresentation : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage)) ∧
    -- entry (13): locally of finite type of relative dimension `d`
    (∀ d : ℕ,
      MorphismProperty.IsStableUnderBaseChange (locallyOfFiniteTypeRelativeDimension.{u} d) ∧
      MorphismProperty.IsLocalAtTarget
          (locallyOfFiniteTypeRelativeDimension.{u} d) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (locallyOfFiniteTypeRelativeDimension.{u} d) Scheme.fppfPrecoverage) ∧
    -- entry (14): universally open
    (MorphismProperty.IsStableUnderBaseChange (@UniversallyOpen : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@UniversallyOpen : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@UniversallyOpen : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (15): flat
    (MorphismProperty.IsStableUnderBaseChange (@Flat : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@Flat : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@Flat : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (16): syntomic
    (MorphismProperty.IsStableUnderBaseChange (@Syntomic : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@Syntomic : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@Syntomic : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (17): smooth
    (MorphismProperty.IsStableUnderBaseChange (@Smooth : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@Smooth : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@Smooth : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (18): unramified, and G-unramified
    ((MorphismProperty.IsStableUnderBaseChange (@Unramified : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@Unramified : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@Unramified : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
      (MorphismProperty.IsStableUnderBaseChange (@GUnramified : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@GUnramified : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@GUnramified : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage)) ∧
    -- entry (19): étale
    (MorphismProperty.IsStableUnderBaseChange (@Etale : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@Etale : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@Etale : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (20): proper
    (MorphismProperty.IsStableUnderBaseChange (@IsProper : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@IsProper : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@IsProper : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- entry (21): finite, and integral
    ((MorphismProperty.IsStableUnderBaseChange (@IsFinite : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@IsFinite : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@IsFinite : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
      (MorphismProperty.IsStableUnderBaseChange (@IsIntegralHom : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@IsIntegralHom : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@IsIntegralHom : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage)) ∧
    -- entry (22): finite locally free, of unconstrained and of fixed rank
    ((MorphismProperty.IsStableUnderBaseChange
           (@Stacks.Morphisms.IsFiniteLocallyFree : MorphismProperty Scheme.{u}) ∧
       MorphismProperty.IsLocalAtTarget
           (@Stacks.Morphisms.IsFiniteLocallyFree : MorphismProperty Scheme.{u})
           Scheme.fpqcPrecoverage ∧
       MorphismProperty.IsLocalAtTarget
           (@Stacks.Morphisms.IsFiniteLocallyFree : MorphismProperty Scheme.{u})
           Scheme.fppfPrecoverage) ∧
      (∀ d : ℕ,
        MorphismProperty.IsStableUnderBaseChange
            (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d) ∧
        MorphismProperty.IsLocalAtTarget
            (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d) Scheme.fpqcPrecoverage ∧
        MorphismProperty.IsLocalAtTarget
            (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d) Scheme.fppfPrecoverage)) ∧
    -- entry (23): universally submersive
    (MorphismProperty.IsStableUnderBaseChange
         ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally) ∧
     MorphismProperty.IsLocalAtTarget
         ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally)
         Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally)
         Scheme.fppfPrecoverage) ∧
    -- entry (24): universal homeomorphism
    (MorphismProperty.IsStableUnderBaseChange
         (@UniversalHomeomorphism : MorphismProperty Scheme.{u}) ∧
     MorphismProperty.IsLocalAtTarget
         (@UniversalHomeomorphism : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
     MorphismProperty.IsLocalAtTarget
         (@UniversalHomeomorphism : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage) ∧
    -- the last sentence (02YM): immersions in general are fppf local on the base, and no fpqc
    -- locality is claimed of them
    (MorphismProperty.IsStableUnderBaseChange (@IsImmersion : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget (@IsImmersion : MorphismProperty Scheme.{u})
        Scheme.fppfPrecoverage) :=
  have lqf :=
    locallyOfFiniteType_inf_locallyQuasiFinite_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf
  ⟨⟨isClosedImmersion_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
      isOpenImmersion_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
      isImmersion_inf_quasiCompact_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf⟩,
    quasiCompact_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    universallyClosed_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    ⟨isSeparated_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
      quasiSeparated_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf⟩,
    monomorphisms_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    surjective_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    universallyInjective_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    isAffineHom_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    isQuasiAffineHom_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    ⟨locallyOfFiniteType_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
      finiteType_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf⟩,
    ⟨lqf,
      finiteType_inf_locallyQuasiFinite_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf⟩,
    ⟨locallyOfFinitePresentation_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
      finitePresentation_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf⟩,
    fun d =>
      locallyOfFiniteTypeRelativeDimension_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf d,
    universallyOpen_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    flat_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    syntomic_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    smooth_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    ⟨unramified_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
      gUnramified_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf⟩,
    etale_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    isProper_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    ⟨isFinite_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
      isIntegralHom_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf⟩,
    ⟨isFiniteLocallyFree_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
      fun d => isFiniteLocallyFreeOfRank_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf d⟩,
    universallyQuotientMap_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    universalHomeomorphism_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf,
    isImmersion_isStableUnderBaseChange_and_isLocalAtTarget_fppf⟩

end Stacks.Descent

end
