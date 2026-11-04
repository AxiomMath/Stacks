module

public import StacksFrontier.AlgebraicGeometry.BundleReduction.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 07RM at the predicate its statement uses

The statement of Tag 07RM concludes that a morphism is projective in the sense of the statement
of Tag 01W8: a closed immersion over the base into the projective bundle `𝐏(E)` of a finite-type
quasi-coherent module `E` on the base. That predicate, as spelled in the statement of Tag 01W8,
is `sorry`-contaminated *in its statement*, through the `Proj` axioms of the symmetric algebra
in the statement of Tag 01OB, so no proof of anything stated with it can be axiom-clean. Its library form is not contaminated and is already built:
`Stacks.Tag087SBundle.IsProjective`.

Two restatement routes avoiding that `sorry` exist, and
`Stacks.ProjectivityLabelChoice.cardStatementAtHProjective_iff` examines the first — restating
at Tag 01W8's one clean *label*, `Stacks.HProjective.IsHProjective` — and finds that it is **not**
Stacks Tag 07RM: it is part (2) of [Stacks, Tag 087S] with that lemma's hypothesis on the base
deleted, a strictly harder theorem. The second route, restating
Tag 01W8's own `IsProjective` over library names, is not ruled out by that comparison.

**This file takes the second route.** The statement of Tag 07RM is reproduced with
the projectivity predicate of the statement of Tag 01W8 replaced by
`Stacks.Tag087SBundle.IsProjective` and nothing else changed,
and it is reduced to exactly half 1 of the source's own proof — the immersion into `𝐏(E)` — with
no hypothesis on the base beyond the statement's own two.

**Tag 07RM itself is proved elsewhere, outright.** It is
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`
(`StacksFrontier/AlgebraicGeometry/QuasiProjectiveCompactification/Projective.lean`), at Definition
01W8's `AlgebraicGeometry.IsProjective`, with half 1 proved there as
`Stacks.QuasiProjectiveCompactification.immersionIntoProjective_isProjective`. This file's
reduction is kept for the bundle predicate `Stacks.Tag087SBundle.IsProjective`, which spells the
same closed immersion into the same bundle with the quasi-coherence of the pieces of `Sym(E)`
discharged inside the predicate; no declaration here converts between the two predicates, so the
statements below still take `Stacks.Tag07RMBundleRoute.ImmersionIntoBundle` as an argument.

## Instantiating the parameterised route

`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective` proves Tag 07RM
from a projectivity *parameter* `P : CategoryTheory.MorphismProperty Scheme` constrained by two
properties. Two obstacles stand in the way of taking `P` to be
`Stacks.Tag087SBundle.IsProjective`, and both are removed here:

1. The second side condition — a closed immersion into a projective `S`-scheme is projective over
   `S` — is not provided there. It is `Stacks.Tag07RMBundleRoute.projective_comp_of_isClosedImmersion`
   below, and it is three lines: closed immersions compose.
2. `Stacks.Tag087SBundle.IsProjective` **is not a `CategoryTheory.MorphismProperty Scheme`**, so
   it cannot be passed as `P` at all. Its base `S` is a section `variable`, so its elaborated
   type is `{S X : Scheme} → (X ⟶ S) → Prop` — the *target* is the first implicit argument,
   where a `MorphismProperty` takes the source first. `Stacks.Tag07RMBundleRoute.projective` is
   the argument-order adapter, and `Stacks.Tag07RMBundleRoute.projective_iff` is `Iff.rfl`: it is
   not a second notion of projectivity, and nothing below states anything about it that is not
   literally a statement about `Stacks.Tag087SBundle.IsProjective`.

## What remains, and it is the source's half 1 exactly

`Stacks.Tag07RMBundleRoute.ImmersionIntoBundle` is the source's half 1 verbatim: over a
quasi-compact quasi-separated base, a quasi-projective morphism admits an immersion over the base
into the projective bundle of a finite-type quasi-coherent module.
`Stacks.Tag07RMBundleRoute.immersionIntoProjective_iff` proves it **equivalent** to
`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` at this predicate, so the
reduction gives away nothing: asking for an immersion into an arbitrary projective `S`-scheme is
the same as asking for one into a bundle, because a projective `S`-scheme is by definition
closed-immersed in one.

Half 1 rests on three results, all of them now theorems, and they are assembled at
`AlgebraicGeometry.IsProjective` in
`StacksFrontier/AlgebraicGeometry/QuasiProjectiveCompactification/Projective.lean`:

* a power of a relatively ample module with generating sections pinning an immersion into `𝐏ⁿ`
  over each member of a finite affine covering of the base — [Stacks, Tag 01VU], (1) ⟹ (3), is
  `Stacks.VeryAmplePowersQuasiCompactBase.eventuallyVeryAmplePower_of_isRelativelyAmple`, and the
  form keeping the sections, used by Tag 07RM, is
  `Stacks.QuasiProjectiveCompactification.exists_finite_affine_cover_familyImmersionTwist`;
* finitely many sections of a quasi-coherent module over affine opens of a quasi-compact
  quasi-separated scheme lift to one quasi-coherent module of finite type — the use the source
  makes of [Stacks, Tag 01PG] — which is
  `Stacks.QuasiProjectiveCompactification.exists_isFiniteType_hom_lift`, from
  `Stacks.AlgebraicGeometry.Tag01PGColimitClose.affineSections_of_qcqs` and the directedness
  `AlgebraicGeometry.finiteTypeQuasicoherentSubobject_isFiltered`;
* [Stacks, Tag 02NP], generating sections of an invertible module defining an immersion into
  `𝐏ⁿ`: it is `Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple`, and in
  the proof of Tag 07RM its role is played by the generating families of the first bullet, which
  already pin immersions
  (`Stacks.QuasiProjectiveCompactification.eventually_familyImmersionTwist`), together with
  `Stacks.QuasiProjectiveCompactification.isImmersion_toSpecAway` on the charts of the morphism
  to `𝐏(ℰ)`.

**Tag 01PG, not Tag 01PK, is the lemma half 1 needs.** The Stacks Project gives
01PG as `properties-lemma-quasi-coherent-colimit-finite-type`, the colimit of **finite-type
submodules**, with `proof_uses = ['01PF']`; and 01PK as
`properties-lemma-directed-colimit-finite-presentation`, a directed system of modules of **finite
presentation** that need not be submodules, with `proof_uses = ['01PJ', '0032', '009E']`. The
source's proof of Tag 07RM cites 01PK, but half 1 needs a finite-type `ℰ`, which is what 01PG
supplies.

**So no Stacks tag attribute is attached anywhere in this file.** The tag is registered on
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`; the
statements here are at the bundle predicate and take
`Stacks.Tag07RMBundleRoute.ImmersionIntoBundle` as an argument.

## The two predicates are incomparable at this pin, which is why this route is the faithful one

`Stacks.HProjective.IsHProjective` asks for a closed immersion into
`AlgebraicGeometry.projectiveSpaceOver n S`, and `Stacks.Tag087SBundle.IsProjective` for one into
`𝐏(E)`.

The two are comparable: the isomorphism `𝐏(𝒪_S^{⊕(n+1)}) ≅ ℙⁿ_S` over a general base is
proved, unconditionally and in both halves, as [Stacks, Tag 01OE]:
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpace`
(`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/ProjectiveSpaceMorphism.lean:633`) is the
isomorphism and `..._hom_comp_fst` (`:644`) says it is an isomorphism *over* `X`; the binders of
both are `{X : Scheme.{u}} (n : ℕ)` and nothing else. Tag 01OE does not go
through the `ProjectiveSpaceCharts` route, whose hypothesis is discharged for no graded algebra
other than `polyAlgebra` (as `StacksFrontier/AlgebraicGeometry/ProjBundleSurjection/Bundle.lean`
records about that route); see also
`StacksFrontier/AlgebraicGeometry/AmpleImmersionReduction/EventualGeneration.lean:149`.

So the comparison of ambient spaces is available and the `IsHProjective` route is not closed off
by it. What is still missing along that route is only the twist/module half — that the
isomorphism carries `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S` to
`Stacks.Tag01VMVeryAmple.twistOne` of the free module, which no declaration asserts (a
chartwise/affine-base form is `Stacks.SymGraded.hasFreeBundleTwistOne`,
`SheafSymmetricAlgebra/ChartTwistOne.lean:49`). The route below is still the one taken here,
because it reaches the conclusion of Tag 07RM from the source's own half 1 without needing that
twist comparison — a reason of economy, not of impossibility.

## Main definitions

* `Stacks.Tag07RMBundleRoute.projective`: `Stacks.Tag087SBundle.IsProjective` with its implicit
  arguments in `CategoryTheory.MorphismProperty` order.
* `Stacks.Tag07RMBundleRoute.HasBundleImmersion`: an immersion over the base into the projective
  bundle of a finite-type quasi-coherent module.
* `Stacks.Tag07RMBundleRoute.ImmersionIntoBundle`: half 1 of the source's proof of Tag 07RM.

## Main results

* `Stacks.Tag07RMBundleRoute.projective_comp_of_isClosedImmersion`: **the side condition the
  bundle predicate was missing.**
* `Stacks.Tag07RMBundleRoute.exists_isOpenImmersion_isProjective_of_hasBundleImmersion`: **half 2
  of the source's proof at the statement's own predicate, with no hypothesis on the base.**
* `Stacks.Tag07RMBundleRoute.hasBundleImmersion_iff`: for a quasi-compact morphism, half 2's
  conclusion is *equivalent* to having an immersion into a bundle.
* `Stacks.Tag07RMBundleRoute.immersionIntoProjective_iff`: the residue is exactly the source's
  half 1.
* `Stacks.Tag07RMBundleRoute.exists_isOpenImmersion_isProjective`: **the statement of Tag `07RM` over
  library names**, from `Stacks.Tag07RMBundleRoute.ImmersionIntoBundle` alone. The tag itself, at
  `AlgebraicGeometry.IsProjective` and with no such argument, is
  `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`.

## References

* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.Tag07RMBundleRoute

/-! ### Projectivity in `MorphismProperty` argument order -/

/-- **`Stacks.Tag087SBundle.IsProjective` as a `CategoryTheory.MorphismProperty`.**

The base of `Stacks.Tag087SBundle.IsProjective` is a section `variable`, so it is elaborated as
`{S X : Scheme} → (X ⟶ S) → Prop`, with the target first; a `MorphismProperty` takes the source
first. This is that reordering and nothing else — see
`Stacks.Tag07RMBundleRoute.projective_iff`. -/
def projective : MorphismProperty Scheme.{u} := fun _ _ f => Stacks.Tag087SBundle.IsProjective f

/-- The adapter is the identity on propositions: `Stacks.Tag07RMBundleRoute.projective` holds
exactly when `Stacks.Tag087SBundle.IsProjective` does, by `Iff.rfl`. -/
theorem projective_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    projective f ↔ Stacks.Tag087SBundle.IsProjective f := Iff.rfl

/-! ### The two side conditions of the parameterised Tag 07RM -/

/-- **A projective morphism is separated**, in the shape of the hypothesis `hsep` of
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective`. This is
`Stacks.Tag087SBundle.IsProjective.isSeparated`, which is the use the source of [Stacks, Tag 07RM]
makes of [Stacks, Tag 03GI]. -/
theorem isSeparated_of_projective {Y S : Scheme.{u}} (q : Y ⟶ S) (hq : projective q) :
    IsSeparated q :=
  Stacks.Tag087SBundle.IsProjective.isSeparated hq

/-- **A closed immersion into a projective `S`-scheme is projective over `S`.**

This is the hypothesis `hcomp` of
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective` — the source's "and
`X' ⟶ S` is projective by definition" — and it is the side condition that theorem's module
documentation records as not stated for this predicate.

The whole content is that closed immersions compose: a projective `q` factors as a closed
immersion `i` into `𝐏(E)` followed by the bundle's structure morphism, and `c ≫ i` is again a
closed immersion into the *same* bundle, so the witnessing module `E` is unchanged and its
finite-type quasi-coherence is reused verbatim. -/
@[ega "II 5.5.5" "(ii)"]
theorem projective_comp_of_isClosedImmersion {X' Y S : Scheme.{u}} (c : X' ⟶ Y) (q : Y ⟶ S)
    (hc : IsClosedImmersion c) (hq : projective q) : projective (c ≫ q) := by
  obtain ⟨E, hqc, hft, i, hi, hiq⟩ := hq
  exact ⟨E, hqc, hft, c ≫ i, inferInstance, by rw [Category.assoc, hiq]⟩

/-! ### An immersion into a projective bundle -/

/- The target below is fixed: `𝐏(E)` for a finite-type quasi-coherent `E` on the base.
`Stacks.HProjective.HasHProjectiveImmersion` asks instead for an immersion into an arbitrary
H-projective `S`-scheme, so the two agree only once the bundle is known H-projective. -/

/-- **An immersion over the base into the projective bundle of a finite-type quasi-coherent
module.** This is what half 1 of the source's proof of [Stacks, Tag 07RM] produces, and the only
thing half 2 consumes.

Quasi-compactness of the immersion is deliberately *not* part of this condition: it is free from
quasi-compactness of `f`, because the bundle is separated over the base
(`Stacks.Tag087SBundle.isSeparated_projectiveBundleToBase`), which is the use the source makes of
[Stacks, Tag 03GI]. -/
def HasBundleImmersion {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (E : S.Modules) (hq : E.IsQuasicoherent), SheafOfModules.IsFiniteType.{u, u, u} E ∧
    ∃ i : X ⟶ Stacks.Tag087SBundle.projectiveBundle E hq,
      IsImmersion i ∧ i ≫ Stacks.Tag087SBundle.projectiveBundleToBase E hq = f

/-- The structure morphism of a projective bundle has an immersion into a projective bundle,
namely the identity. Recorded so that the condition is visibly inhabited and the implications
below are not implications from a false hypothesis. -/
theorem hasBundleImmersion_projectiveBundleToBase {S : Scheme.{u}} (E : S.Modules)
    (hq : E.IsQuasicoherent) (hft : SheafOfModules.IsFiniteType.{u, u, u} E) :
    HasBundleImmersion (Stacks.Tag087SBundle.projectiveBundleToBase E hq) :=
  ⟨E, hq, hft, 𝟙 _, inferInstance, Category.id_comp _⟩

/-! ### Half 2 of the source's proof, at the statement's own predicate -/

/-- **Half 2 of the proof of [Stacks, Tag 07RM], at `Stacks.Tag087SBundle.IsProjective`, with no
hypothesis on the base.**

Given an immersion over the base into `𝐏(E)`, the morphism factors as an open immersion followed
by a projective morphism. The immersion is quasi-compact because `f` is and `𝐏(E) ⟶ S` is
separated ([Stacks, Tag 03GI], as
`Stacks.QuasiProjectiveCompactification.quasiCompact_of_comp_isSeparated`), so
[Stacks, Tag 01RG] — Mathlib's
`AlgebraicGeometry.IsImmersion.isImmersion_iff_exists_of_quasiCompact`, in the shape
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isClosedImmersion` — factors it
through a closed subscheme of `𝐏(E)`, and that subscheme is projective over the base with the
*same* `E`.

Neither quasi-compactness nor quasi-separatedness of the base is used, and no ample module
appears: both are consumed entirely inside half 1. -/
theorem exists_isOpenImmersion_isProjective_of_hasBundleImmersion {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : QuasiCompact f) (h : HasBundleImmersion f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ Stacks.Tag087SBundle.IsProjective p ∧ i ≫ p = f := by
  obtain ⟨E, hqc, hft, i, hi, hif⟩ := h
  have hic : QuasiCompact (i ≫ Stacks.Tag087SBundle.projectiveBundleToBase E hqc) := by
    rwa [hif]
  have hiqc : QuasiCompact i :=
    Stacks.QuasiProjectiveCompactification.quasiCompact_of_comp_isSeparated i _
      (Stacks.Tag087SBundle.isSeparated_projectiveBundleToBase E hqc) hic
  obtain ⟨X', j, c, hj, hc, hjc⟩ :=
    Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isClosedImmersion i hi hiqc
  refine ⟨X', j, c ≫ Stacks.Tag087SBundle.projectiveBundleToBase E hqc, hj,
    ⟨E, hqc, hft, c, hc, rfl⟩, ?_⟩
  rw [← Category.assoc, hjc, hif]

/-- The converse of
`Stacks.Tag07RMBundleRoute.exists_isOpenImmersion_isProjective_of_hasBundleImmersion`: a morphism
factoring as an open immersion followed by a projective morphism has an immersion into a
projective bundle.

The open immersion composed with the closed immersion into `𝐏(E)` is an immersion, and the
witnessing module is carried over unchanged. -/
theorem hasBundleImmersion_of_exists_isOpenImmersion_isProjective {X S : Scheme.{u}} {f : X ⟶ S}
    (h : ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ Stacks.Tag087SBundle.IsProjective p ∧ i ≫ p = f) :
    HasBundleImmersion f := by
  obtain ⟨X', i, p, hi, ⟨E, hqc, hft, c, hc, hcp⟩, hip⟩ := h
  refine ⟨E, hqc, hft, i ≫ c, inferInstance, ?_⟩
  rw [Category.assoc, hcp, hip]

/-- **For a quasi-compact morphism, half 2's conclusion is *equivalent* to having an immersion
into a projective bundle.** So half 2 of the source's proof is lossless at this predicate: it
consumes exactly the content of half 1 and no more. Quasi-compactness is needed only for the
forward direction, and it is part of quasi-projectivity, which is Tag 07RM's hypothesis. -/
theorem hasBundleImmersion_iff {X S : Scheme.{u}} {f : X ⟶ S} (hf : QuasiCompact f) :
    HasBundleImmersion f ↔
      ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
        IsOpenImmersion i ∧ Stacks.Tag087SBundle.IsProjective p ∧ i ≫ p = f :=
  ⟨exists_isOpenImmersion_isProjective_of_hasBundleImmersion hf,
    hasBundleImmersion_of_exists_isOpenImmersion_isProjective⟩

/-! ### The residue, and that it is the source's half 1 -/

/-- **Half 1 of the source's proof of [Stacks, Tag 07RM].** Over a quasi-compact quasi-separated
base, every quasi-projective morphism admits an immersion over the base into the projective bundle
of a finite-type quasi-coherent module on the base.

These are exactly the hypotheses on the base in Tag 07RM — nothing is added and nothing is
strengthened — and it is the single input of Tag `07RM` at the bundle predicate. At Definition 01W8's
`AlgebraicGeometry.IsProjective` the same half 1 is the theorem
`Stacks.QuasiProjectiveCompactification.immersionIntoProjective_isProjective`; the three results
it rests on are named in the module documentation. -/
def ImmersionIntoBundle : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), CompactSpace S → QuasiSeparatedSpace S →
    Stacks.HProjective.IsQuasiProjective f → HasBundleImmersion f

/-- **The residue is exactly the source's half 1.**
`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` at this predicate — an immersion
into an *arbitrary* projective `S`-scheme — is equivalent to
`Stacks.Tag07RMBundleRoute.ImmersionIntoBundle`, an immersion into a projective *bundle*.

The two differ by nothing because a projective `S`-scheme is by definition closed-immersed over
`S` in a bundle: forward, compose the immersion with that closed immersion; backward, the bundle's
own structure morphism is projective
(`Stacks.Tag087SBundle.isProjective_projectiveBundleToBase`).

So the reduction of Tag `07RM` performed here is not a weakening of the statement, and the generality
of `Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective`'s intermediate scheme buys
nothing at this predicate. -/
theorem immersionIntoProjective_iff :
    Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective projective.{u} ↔
      ImmersionIntoBundle.{u} := by
  constructor
  · intro h X S f hcs hqs hf
    obtain ⟨Y, g, q, hg, ⟨E, hqc, hft, c, hc, hcq⟩, hgq⟩ := h X S f hcs hqs hf
    refine ⟨E, hqc, hft, g ≫ c, inferInstance, ?_⟩
    rw [Category.assoc, hcq, hgq]
  · intro h X S f hcs hqs hf
    obtain ⟨E, hqc, hft, i, hi, hif⟩ := h X S f hcs hqs hf
    exact ⟨Stacks.Tag087SBundle.projectiveBundle E hqc, i, _, hi,
      Stacks.Tag087SBundle.isProjective_projectiveBundleToBase E hqc hft, hif⟩

/-! ### Tag 07RM over library names -/

/-- **The statement of Tag `07RM` over library names.** A quasi-projective morphism over a
quasi-compact quasi-separated base factors as an open immersion followed by a projective
morphism.

This is the statement of Tag `07RM` verbatim — the same quantifier prefix, the same `CompactSpace S` and
`QuasiSeparatedSpace S`, the same quasi-projectivity hypothesis — with
the quasi-projectivity predicate of the statement of Tag 01VW replaced by
`Stacks.HProjective.IsQuasiProjective` and the projectivity predicate of the statement of Tag 01W8
by `Stacks.Tag087SBundle.IsProjective`, which are those two tagged
predicates with their folded definitions replaced by library names and nothing else changed.

The added argument is `Stacks.Tag07RMBundleRoute.ImmersionIntoBundle`, half 1 of the source's
own proof, which `Stacks.Tag07RMBundleRoute.immersionIntoProjective_iff` shows is no weaker than
`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` at this predicate. The tag
is registered on
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`, which
states it at `AlgebraicGeometry.IsProjective` and proves half 1 there
(`Stacks.QuasiProjectiveCompactification.immersionIntoProjective_isProjective`), so nothing here
carries the attribute. -/
theorem exists_isOpenImmersion_isProjective (hgap : ImmersionIntoBundle.{u}) {X S : Scheme.{u}}
    (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    (hf : Stacks.HProjective.IsQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ Stacks.Tag087SBundle.IsProjective p ∧ i ≫ p = f :=
  exists_isOpenImmersion_isProjective_of_hasBundleImmersion hf.quasiCompact
    (hgap X S f ‹CompactSpace S› ‹QuasiSeparatedSpace S› hf)

/-- The same conclusion obtained through the parameterised
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective`, which is what
proves that its projectivity parameter `P` is instantiable at the statement's own predicate: both of
that theorem's side conditions on `P` are discharged here, by
`Stacks.Tag07RMBundleRoute.isSeparated_of_projective` and
`Stacks.Tag07RMBundleRoute.projective_comp_of_isClosedImmersion`.

The conclusion is the same proposition as
`Stacks.Tag07RMBundleRoute.exists_isOpenImmersion_isProjective`'s by
`Stacks.Tag07RMBundleRoute.projective_iff`, so this records the instantiation rather than a new
result. -/
theorem exists_isOpenImmersion_projective
    (hgap : Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective projective.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    (hf : Stacks.HProjective.IsQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ projective p ∧ i ≫ p = f :=
  Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective (P := projective.{u})
    isSeparated_of_projective projective_comp_of_isClosedImmersion hgap f hf

end Stacks.Tag07RMBundleRoute

end
