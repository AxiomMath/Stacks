module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic

/-!
# Being projective is not local on the base

Many properties of morphisms of schemes are local on the base, even in the fpqc topology. For
projectivity this fails, and the failure is witnessed by Hironaka's Example B.3.4.1: a proper
morphism of smooth complex `3`-folds which is Zariski-locally projective and not projective.

This file does **not** build that morphism. What it does is fix the *shape* of the assertion and
prove the reduction, so that the construction is the only thing left owed. Two things are settled
here.

## The shape

"`𝒫` is Zariski local on the base" is `AlgebraicGeometry.IsZariskiLocalAtTarget 𝒫`, Mathlib's
abbreviation for `𝒫.IsLocalAtTarget Scheme.zariskiPrecoverage`, and the two properties the source
names are `Stacks.Examples.ProjectivityNotLocalOnBase.projectiveProperty` and
`Stacks.Examples.ProjectivityNotLocalOnBase.quasiProjectiveProperty`, the predicates
`AlgebraicGeometry.IsProjective` — the first condition of Tag 01W8, a closed immersion over the
base into the projective bundle of a quasi-coherent module of finite type — and
`AlgebraicGeometry.IsQuasiProjective`, read as morphism properties. So the assertion of the tag
is the conjunction of
`¬ IsZariskiLocalAtTarget projectiveProperty` and
`¬ IsZariskiLocalAtTarget quasiProjectiveProperty`,
and "a fortiori not fpqc local" is the same pair with `Scheme.zariskiPrecoverage` replaced by
`Scheme.fpqcPrecoverage`.

## The reduction

The repository already has a name for the local form of projectivity:
`AlgebraicGeometry.IsLocallyProjective` is the third condition of Tag 01W8, the base being
covered by opens over which the restriction of `f` is projective. The content of the reduction is
that Zariski-locality of projectivity is *exactly* what would collapse the first condition of
Tag 01W8 onto the third:

`Stacks.Examples.ProjectivityNotLocalOnBase.isLocallyProjective_iff_isProjective` — if
`projectiveProperty` were Zariski local at the target, then every locally projective morphism
would be projective and conversely.

That is proved unconditionally, from Mathlib's `AlgebraicGeometry.IsZariskiLocalAtTarget` API
alone: the forward direction is `IsZariskiLocalAtTarget.of_iSup_eq_top` applied to the covering
the local condition provides, and the backward direction is `IsZariskiLocalAtTarget.restrict` at
the one-member covering by `⊤`.

Consequently a morphism which is locally projective and not projective refutes Zariski-locality,
and the fpqc statement follows because `Scheme.zariskiPrecoverage ≤ Scheme.fpqcPrecoverage`
and `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le` turns an fpqc-local property into a
Zariski-local one.

## What is still owed, and why there is no theorem here

The refuting morphism is carried by
`Stacks.Examples.ProjectivityNotLocalOnBase.ProperLocallyProjectiveNotProjective`, a named
hypothesis asserting that some proper morphism of schemes is locally projective and not
projective. **This is Hironaka's example and nothing in this repository proves it**, so every
statement below that consumes it is an implication and none of them carries a `@[stacks]`
attribute: the tag's assertion is not available until the hypothesis is discharged by the
construction.

The construction, with what this repository has for each step, is this. Let `Y = ℙ³_ℂ` and let
`C` and `D` be the two smooth conics `{xy = z², w = 0}` and `{xy = w², z = 0}`, meeting in the
two reduced points `P = [1:0:0:0]` and `Q = [0:1:0:0]`. Over `Y - Q` blow up `C` and then the
strict transform of `D`; over `Y - P` blow up `D` and then the strict transform of `C`; the two
threefolds agree over `Y - P - Q`, so they glue to a smooth proper `V_Y → Y`. That morphism is
locally projective because it is a blow-up over each of `Y - P` and `Y - Q`, and it is not
projective because `V_Y` carries two lines `L₀` and `M₀'` with `L₀ + M₀'` rationally equivalent
to zero, which an ample line bundle could not have positive degree on.

1. **The two conics, their smoothness, and their intersection.** The ideal-theoretic step is
   done: `StacksFrontier/AlgebraicGeometry/Examples/HironakaConicIntersection.lean` proves that the
   sum of the two homogeneous ideals is the intersection of the ideals of `P` and `Q`, and that
   it is radical — "the intersection is reduced and consists of two points". Realising the conics
   as *closed subschemes* of `ℙ³_ℂ` and proving them smooth is not done.
2. **The two blow-up towers.** `Stacks.Blowup.blowUp` and the strict transform of a
   scheme, Tag 080D, are available: `Stacks.Blowup.strictTransform` and
   `Stacks.Blowup.strictTransformι` in
   `StacksFrontier/AlgebraicGeometry/Blowup/StrictTransform.lean`. What is missing is the iterated
   tower over an open of the base, and the smoothness and properness of the result.
3. **Local projectivity of each tower.** Tag 02NS part (2) is available:
   `AlgebraicGeometry.isRelativelyAmple_twist_reesSituation` in
   `StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebra/TwistAmple.lean` gives the relatively ample
   `𝒪_{X'}(1)` on a blow-up, so a blow-up is quasi-projective. Turning that into
   `AlgebraicGeometry.IsProjective` of the restriction needs clause (1) of Tag 0BCL for the
   projectivity of Tag 01W8 — the same input as `ProperQuasiProjectiveIsProjective` below — and
   the composition of two projective morphisms.
4. **The glueing.** The canonical isomorphism of the two towers over `Y - P - Q`, and the
   descent of smoothness and properness through `Scheme.GlueData`, are not done.
5. **Non-projectivity.** The `1`-cycle argument is not done, and it is the only step needing
   Chow theory. It consumes Stacks 02TI, which *is* present in this repository, as
   `Stacks.Chow.firstChernCapFactorsEverywhere_iff_killsPrincipalDivisor` in
   `StacksFrontier/AlgebraicGeometry/Chow/ChernCapRationalEquivalenceReduction.lean`: the statement
   that capping with the first Chern class of an invertible module kills principal divisors, so
   that `α ↦ c₁(L) ∩ α` descends from cycles to *rational equivalence classes* of cycles. The
   argument consumes it exactly once and exactly there — the rational equivalences
   `L ∼ L₀ + M₀` near `P` and `M ∼ L₀' + M₀'` near `Q` combine to `L₀ + M₀' ∼ 0`, and that
   relation is useless until degree, which is `c₁(H) ∩ ·` followed by the degree map, is known to
   be a function of the rational equivalence class rather than of the cycle. Given that, an ample
   `H` would have `deg(c₁(H) ∩ (L₀ + M₀')) > 0` and `= 0` at once. What is *not* present is the
   rest of the input: the rational equivalences themselves on the exceptional surface `E`, and
   the positivity of the degree of an ample invertible module on a curve.

The quasi-projective half needs, in addition, two comparisons between the notions of Tag 01W8 and
Tag 01VW, taken here as named hypotheses so that the reduction names each of the source's inputs:

* `Stacks.Examples.ProjectivityNotLocalOnBase.ProjectiveIsQuasiProjective`, Tag 07RL for the
  projectivity of Tag 01W8. It is a theorem over an arbitrary base,
  `AlgebraicGeometry.IsProjective.isQuasiProjective`.
* `Stacks.Examples.ProjectivityNotLocalOnBase.ProperQuasiProjectiveIsProjective`, one direction of
  clause (1) of Tag 0BCL for the same notion, stated over an arbitrary base. Over a quasi-compact
  quasi-separated base, the source's hypothesis, the full biconditional is proved as
  `AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper`; the base of Hironaka's
  example is projective `3`-space, which is quasi-compact and quasi-separated, so that theorem
  covers the instance the argument uses, though not the quantifier over all bases written here.

Both are theorems of the source, not assumptions about the counterexample.

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 07RL](https://stacks.math.columbia.edu/tag/07RL)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Examples.ProjectivityNotLocalOnBase

/-! ### The two properties, read as morphism properties -/

/-- **Projectivity as a morphism property.** The first condition of [Stacks, Tag 01W8]: a closed
immersion over the base into the projective bundle of a quasi-coherent module of finite type.
This is the `𝒫` of the first clause of [Stacks, Tag 08J1]. -/
def projectiveProperty : MorphismProperty Scheme.{u} := fun _ _ f ↦ IsProjective f

/-- **Quasi-projectivity as a morphism property.** [Stacks, Tag 01VW]: of finite type, with an
invertible module on the source ample relative to the morphism. This is the `𝒫` of the second
clause of [Stacks, Tag 08J1]. -/
def quasiProjectiveProperty : MorphismProperty Scheme.{u} := fun _ _ f ↦ IsQuasiProjective f

@[simp]
theorem projectiveProperty_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    projectiveProperty f ↔ IsProjective f := Iff.rfl

@[simp]
theorem quasiProjectiveProperty_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    quasiProjectiveProperty f ↔ IsQuasiProjective f := Iff.rfl

/-! ### Zariski-locality collapses the first condition of Tag 01W8 onto the third -/

/-- **If projectivity were Zariski local at the target, a locally projective morphism would be
projective.** The covering witnessing local projectivity is fed straight to
`AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top`. -/
theorem isProjective_of_isLocallyProjective
    (hloc : IsZariskiLocalAtTarget projectiveProperty.{u})
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsLocallyProjective f) : IsProjective f := by
  have := hloc
  obtain ⟨ι, U, hU, hUf⟩ := hf
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := projectiveProperty.{u}) U hU hUf

/-- **If projectivity were Zariski local at the target, a projective morphism would be locally
projective.** The one-member covering of the base by `⊤` does it, projectivity of the restriction
coming from `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`.

Unlike the other direction this is not formal: `AlgebraicGeometry.IsProjective` is *not* known in
this repository to imply `AlgebraicGeometry.IsLocallyProjective`, because that implication is the
base change `𝐏(ℰ) ×_S U ≅ 𝐏(ℰ|_U)` of Tag 01O3 along the inclusion of an open, which is not
available. -/
theorem isLocallyProjective_of_isProjective
    (hloc : IsZariskiLocalAtTarget projectiveProperty.{u})
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsProjective f) : IsLocallyProjective f := by
  have := hloc
  exact ⟨PUnit.{u + 1}, fun _ ↦ ⊤, iSup_const,
    fun _ ↦ IsZariskiLocalAtTarget.restrict (P := projectiveProperty.{u}) hf ⊤⟩

/-- **Zariski-locality of projectivity is exactly the collapse of the first condition of
[Stacks, Tag 01W8] onto the third.** This is the precise content that Hironaka's example refutes:
the example produces a morphism satisfying the third condition and not the first. -/
theorem isLocallyProjective_iff_isProjective
    (hloc : IsZariskiLocalAtTarget projectiveProperty.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) : IsLocallyProjective f ↔ IsProjective f :=
  ⟨isProjective_of_isLocallyProjective hloc, isLocallyProjective_of_isProjective hloc⟩

/-- **If quasi-projectivity were Zariski local at the target, a morphism quasi-projective over
the members of an open covering of the base would be quasi-projective.** -/
theorem isQuasiProjective_of_iSup_eq_top
    (hloc : IsZariskiLocalAtTarget quasiProjectiveProperty.{u})
    {X S : Scheme.{u}} {f : X ⟶ S} {ι : Type u} (U : ι → S.Opens) (hU : (⨆ i, U i) = ⊤)
    (hUf : ∀ i, IsQuasiProjective (f ∣_ U i)) : IsQuasiProjective f := by
  have := hloc
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := quasiProjectiveProperty.{u}) U hU hUf

/-! ### The witness, as a named hypothesis -/

/-- **Hironaka's Example B.3.4.1, as a named hypothesis.** There is a proper morphism of schemes
which is Zariski-locally projective and not projective.

This is a hypothesis and not a theorem: the morphism is Hironaka's, obtained by blowing up two
smooth conics in `ℙ³_𝐂` meeting in two reduced points in the two possible orders over the two
complements of a point and glueing, and this repository does not construct it. The construction
and the inputs it still needs are set out in
`StacksFrontier/AlgebraicGeometry/Examples/HironakaConicIntersection.lean`.

Properness is carried because the quasi-projective half of [Stacks, Tag 08J1] consumes it: the
source deduces that the morphism is not quasi-projective from the fact that it is proper and not
projective. -/
def ProperLocallyProjectiveNotProjective : Prop :=
  ∃ (V Y : Scheme.{u}) (f : V ⟶ Y), IsProper f ∧ IsLocallyProjective f ∧ ¬ IsProjective f

/-- **[Stacks, Tag 07RL] for the projectivity of [Stacks, Tag 01W8], as a named hypothesis.** A
projective morphism is quasi-projective.

The statement is a theorem for `AlgebraicGeometry.IsProjective`, over an arbitrary base:
`AlgebraicGeometry.IsProjective.isQuasiProjective` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjective`. It is kept as a named
hypothesis here only so that the reduction below names each of the source's inputs separately;
nothing stands between it and a proof. -/
def ProjectiveIsQuasiProjective : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsProjective f → IsQuasiProjective f

/-- **One direction of clause (1) of [Stacks, Tag 0BCL] for the projectivity of
[Stacks, Tag 01W8], as a named hypothesis.** A proper quasi-projective morphism is projective.

The source states the biconditional over a quasi-compact and quasi-separated base, and there it is
proved, as `AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper`; the base of
Hironaka's example is projective `3`-space, which is both. This definition quantifies over every
base, which that theorem does not cover. Clause (2) of the same tag — the H-projective analogue —
is proved unconditionally, as
`AlgebraicGeometry.isProjectiveMorphism_iff_isHQuasiProjective_and_isProper`. -/
def ProperQuasiProjectiveIsProjective : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsProper f → IsQuasiProjective f → IsProjective f

/-! ### The two clauses of Tag 08J1, granted the witness -/

/-- **Projectivity is not Zariski local on the base, granted Hironaka's example.** The first
clause of [Stacks, Tag 08J1]. A locally projective morphism which is not projective contradicts
`Stacks.Examples.ProjectivityNotLocalOnBase.isProjective_of_isLocallyProjective`. -/
theorem not_isZariskiLocalAtTarget_projectiveProperty
    (hH : ProperLocallyProjectiveNotProjective.{u}) :
    ¬ IsZariskiLocalAtTarget projectiveProperty.{u} := by
  obtain ⟨_, _, f, _, hfloc, hfnot⟩ := hH
  exact fun hloc ↦ hfnot (isProjective_of_isLocallyProjective hloc hfloc)

/-- **Quasi-projectivity is not Zariski local on the base, granted Hironaka's example and the two
comparisons of Tags 07RL and 0BCL.** The second clause of [Stacks, Tag 08J1].

This is the source's argument. Over each member of the covering the morphism is projective, hence
quasi-projective by `hRL`; so Zariski-locality would make it quasi-projective, and being proper it
would then be projective by `hBCL`, which it is not. -/
theorem not_isZariskiLocalAtTarget_quasiProjectiveProperty
    (hH : ProperLocallyProjectiveNotProjective.{u}) (hRL : ProjectiveIsQuasiProjective.{u})
    (hBCL : ProperQuasiProjectiveIsProjective.{u}) :
    ¬ IsZariskiLocalAtTarget quasiProjectiveProperty.{u} := by
  obtain ⟨V, Y, f, hfproper, hfloc, hfnot⟩ := hH
  obtain ⟨ι, U, hU, hUf⟩ := hfloc
  refine fun hloc ↦ hfnot (hBCL V Y f hfproper ?_)
  exact isQuasiProjective_of_iSup_eq_top hloc U hU fun i ↦ hRL _ _ _ (hUf i)

/-- **[Stacks, Tag 08J1], granted Hironaka's example and the two comparisons of Tags 07RL and
0BCL.** Neither projectivity nor quasi-projectivity is Zariski local on the base. -/
@[stacks 08J1 "the tag's two assertions REDUCED TO HIRONAKA'S EXAMPLE, which is NOT proved.  The \
witness is the named hypothesis `ProperLocallyProjectiveNotProjective` (:220) -- a proper, \
Zariski-locally projective, non-projective morphism -- and it carries the whole content of the \
tag; `hRL` and `hBCL` are the source's own Tags 07RL and 0BCL (1), also carried.  What IS proved \
unconditionally, and is the reason the reduction is exact rather than circular: \
`isLocallyProjective_iff_isProjective` (:192) shows that Zariski-locality of projectivity is \
precisely the collapse of Tag 01W8 (1) onto Tag 01W8 (3), i.e. of `IsProjective` onto \
`IsLocallyProjective`, so refuting locality is exactly exhibiting a morphism separating those two \
notions -- nothing more is needed and nothing less suffices.  The fpqc assertions follow from the \
Zariski ones at :293, :301, :310 via `zariskiPrecoverage_le_fpqcPrecoverage`.  Of the \
construction, step 3 is fully proved over any domain in \
`Examples/HironakaConicIntersection.lean`: the two conics meet exactly in the two points `P` and \
`Q` (`conicIdealC_sup_conicIdealD_eq_inf`, :366) and that intersection is reduced \
(`isRadical_conicIdealC_sup_conicIdealD`, :372).  Absent: the conics as smooth closed subschemes \
of `P^3`, the two iterated blow-up towers and their gluing over `Y - P - Q`, Tags 01OE and \
0BCL (1) for 01W8-projectivity, and the rational equivalences on the exceptional surface.  \
Tag 02TI, which the degree argument consumes, IS present \
(`Stacks.Chow.firstChernCapFactorsEverywhere_iff_killsPrincipalDivisor`)"]
theorem not_isZariskiLocalAtTarget (hH : ProperLocallyProjectiveNotProjective.{u})
    (hRL : ProjectiveIsQuasiProjective.{u}) (hBCL : ProperQuasiProjectiveIsProjective.{u}) :
    ¬ IsZariskiLocalAtTarget projectiveProperty.{u} ∧
      ¬ IsZariskiLocalAtTarget quasiProjectiveProperty.{u} :=
  ⟨not_isZariskiLocalAtTarget_projectiveProperty hH,
    not_isZariskiLocalAtTarget_quasiProjectiveProperty hH hRL hBCL⟩

/-! ### A fortiori, not fpqc local on the base

A Zariski covering is an fpqc covering, so a property local at the target for the fpqc
precoverage is local at the target for the Zariski precoverage. The two negative statements
therefore transfer with no further input. -/

/-- A property local at the target for the fpqc precoverage is local at the target for the
Zariski precoverage, because `Scheme.zariskiPrecoverage ≤ Scheme.fpqcPrecoverage`. -/
theorem isZariskiLocalAtTarget_of_isLocalAtTarget_fpqc (P : MorphismProperty Scheme.{u})
    (h : P.IsLocalAtTarget Scheme.fpqcPrecoverage) : IsZariskiLocalAtTarget P := by
  have := h
  exact MorphismProperty.IsLocalAtTarget.of_le Scheme.zariskiPrecoverage_le_fpqcPrecoverage

/-- **Projectivity is not fpqc local on the base, granted Hironaka's example.** -/
theorem not_isLocalAtTarget_fpqc_projectiveProperty
    (hH : ProperLocallyProjectiveNotProjective.{u}) :
    ¬ projectiveProperty.{u}.IsLocalAtTarget Scheme.fpqcPrecoverage :=
  fun h ↦ not_isZariskiLocalAtTarget_projectiveProperty hH
    (isZariskiLocalAtTarget_of_isLocalAtTarget_fpqc _ h)

/-- **Quasi-projectivity is not fpqc local on the base, granted Hironaka's example and the two
comparisons of Tags 07RL and 0BCL.** -/
theorem not_isLocalAtTarget_fpqc_quasiProjectiveProperty
    (hH : ProperLocallyProjectiveNotProjective.{u}) (hRL : ProjectiveIsQuasiProjective.{u})
    (hBCL : ProperQuasiProjectiveIsProjective.{u}) :
    ¬ quasiProjectiveProperty.{u}.IsLocalAtTarget Scheme.fpqcPrecoverage :=
  fun h ↦ not_isZariskiLocalAtTarget_quasiProjectiveProperty hH hRL hBCL
    (isZariskiLocalAtTarget_of_isLocalAtTarget_fpqc _ h)

/-- **[Stacks, Tag 08J1], the fpqc half, granted Hironaka's example and the two comparisons of
Tags 07RL and 0BCL.** -/
theorem not_isLocalAtTarget_fpqc (hH : ProperLocallyProjectiveNotProjective.{u})
    (hRL : ProjectiveIsQuasiProjective.{u}) (hBCL : ProperQuasiProjectiveIsProjective.{u}) :
    ¬ projectiveProperty.{u}.IsLocalAtTarget Scheme.fpqcPrecoverage ∧
      ¬ quasiProjectiveProperty.{u}.IsLocalAtTarget Scheme.fpqcPrecoverage :=
  ⟨not_isLocalAtTarget_fpqc_projectiveProperty hH,
    not_isLocalAtTarget_fpqc_quasiProjectiveProperty hH hRL hBCL⟩

end Stacks.Examples.ProjectivityNotLocalOnBase

end
