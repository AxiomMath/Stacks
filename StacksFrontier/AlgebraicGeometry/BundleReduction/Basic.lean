module

public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.HProjective
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Bundle
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Basic

/-!
# Stacks Tag 087S with the projective bundle written down, and with ampleness doing the work

Stacks Tag 087S says that over a base `S` carrying an ample invertible sheaf every projective
morphism is H-projective (part (1)) and every quasi-projective morphism is H-quasi-projective
(part (2)). This file does two things that the rest of the tree's Tag 087S material does not.

## Part (1): projectivity is statable, so the hypothesis of the statement can be written down

Tag 01W8's `IsProjective` — the *hypothesis* of part (1) — is stated through the projective
bundle `𝐏(E) = Proj_S(Sym(E))`, and that bundle is available over library names for every
quasi-coherent `E`:

* `Stacks.SymGraded.schemeProjectiveBundle` (`../SheafSymmetricAlgebra/Scheme.lean:226`) builds
  `Proj_X(Sym(E))` for a module on an arbitrary scheme, carrying one hypothesis,
  `Stacks.SymGraded.IsQuasicoherentPieces E`;
* `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`
  (`../SymAlgebraQcohPieces/Basic.lean:424`) **discharges that hypothesis for every
  quasi-coherent `E`**, with no `sorry` anywhere in its file.

So the bundle is unconditional for a quasi-coherent module, and `Stacks.Tag087SBundle.IsProjective`
below is Tag 01W8 part (1) stated over it. The 22 places that said otherwise are inventoried under
"Corrections"; 19 have been struck and the remaining 3 are listed below.

With the hypothesis statable, part (1) becomes an *equivalence* rather than a one-way reduction:
`Stacks.Tag087SBundle.isHProjective_of_isProjective_iff` says that part (1) holds at a base `S`
exactly when every projective bundle of a finite-type quasi-coherent module on `S` is
H-projective. That is the source's own "by our definition of projective morphisms it suffices to
show that `𝐏(E) ⟶ S` is H-projective", with the "suffices" upgraded to "is equivalent to" — the
converse holds because `𝐏(E) ⟶ S` is itself projective, with the identity as its closed
immersion.

## Part (2): the ample sheaf on `S` is made to do real work

`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective` proves part (2) from
`Stacks.HProjective.ProjectiveCompactification`, and its own implementation notes say "Ampleness
of a sheaf on `S` is nowhere used".
`Stacks.QuasiProjectiveCompactification.projectiveCompactification_iff` explains why that is
a symptom rather than a strength: it shows that hypothesis is **equivalent to part (2)
itself**, so the reduction establishes nothing about part (2) that part (2) does not already say.

The hypothesis used here instead is
`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` at
`Stacks.HProjective.IsHProjective`: half 1 of Stacks Tag 07RM's own proof, with H-projectivity in
place of Definition 01W8's projectivity. At `AlgebraicGeometry.IsProjective` half 1 is a theorem,
`Stacks.QuasiProjectiveCompactification.immersionIntoProjective_isProjective`, and Tag 07RM is
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`; at
H-projectivity it is not proved, which is why it is a hypothesis here. It is weaker than the
sibling file's hypothesis in two independent ways: it asks only for an *immersion* into an
H-projective `S`-scheme rather than an open-immersion factorisation, and it asks for it only over
bases that are **quasi-compact and quasi-separated**, which is Tag 07RM's actual hypothesis. The
ample sheaf of the statement is exactly what supplies those two conditions, by two results
already in the library:

* `Stacks.Ample.IsAmple.compactSpace` (`../AmpleWire/Basic.lean:266`) — quasi-compactness of `S`,
  which is clause (1) of the definition of ampleness, Stacks Tag 01PS;
* `Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple`
  (`../AmplePullbackPart1/Basic.lean:317`) — quasi-separatedness of `S`, the first paragraph of the
  proof of Stacks Tag 01PY.

Composing them with the Tag 07RM material is all of
`Stacks.Tag087SBundle.isHQuasiProjective_of_isQuasiProjective_of_isAmple`.

**Two of Tag 087S's six recorded dependencies are therefore not needed.** The source derives "`S`
is quasi-compact and separated" from Tag 01PS, Tag 01Q1 and Tag 01MC, and then uses it only to
apply Tag 07RM — which needs quasi-compact and *quasi*-separated. Quasi-separated is strictly
weaker than separated, and the two results above reach it without Tag 01Q1 and without Tag
01MC. `StacksFrontier/AlgebraicGeometry/HProjective/Basic.lean` reasons from the unavailability of
Tag 01Q1 (correct: the
`Proj Γ_*(X, L)` route does not exist here) to a conclusion about separatedness of `S` that does
not follow, because separatedness of `S` is not what the argument consumes.

## Main definitions

* `Stacks.Tag087SBundle.projectiveBundle`, `Stacks.Tag087SBundle.projectiveBundleToBase`:
  `𝐏(E) = Proj_S(Sym(E))` and its structure morphism, for a quasi-coherent `E`, with the
  quasi-coherence of the homogeneous pieces discharged.
* `Stacks.Tag087SBundle.IsProjective`: **Stacks Tag 01W8 part (1), projectivity**, over library
  names: a closed immersion over `S` into the projective bundle of a finite-type quasi-coherent
  `𝒪_S`-module.
* `Stacks.Tag087SBundle.BundlesAreHProjective`: the geometric content of part (1) of Tag 087S,
  namely H-projectivity of every such bundle.

## Main results

* `Stacks.Tag087SBundle.isSeparated_projectiveBundleToBase`, and
  `Stacks.Tag087SBundle.IsProjective.isSeparated`: a projective morphism is separated. This is
  the separatedness half of "projective implies proper", available for the notion of
  projectivity of Tag 01W8 rather than only for H-projectivity.
* `Stacks.Tag087SBundle.isProjective_projectiveBundleToBase`: `𝐏(E) ⟶ S` is projective.
* `Stacks.Tag087SBundle.isHProjective_of_isProjective`: **part (1) of Stacks Tag 087S** from
  `Stacks.Tag087SBundle.BundlesAreHProjective`.
* `Stacks.Tag087SBundle.isHProjective_of_isProjective_iff`: **part (1) is equivalent to
  `BundlesAreHProjective`**, so that condition is exactly what part (1) owes, neither more nor
  less.
* `Stacks.Tag087SBundle.isHQuasiProjective_of_isQuasiProjective_of_isAmple`: **part (2) of Stacks
  Tag 087S** from `Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` alone, with
  the ample module of the statement supplying quasi-compactness and quasi-separatedness of the base.
* `Stacks.Tag087SBundle.immersionIntoProjective_of_projectiveCompactification`: the hypothesis
  used here is implied by the one the sibling file used, which is how the two are ordered.

## Implementation notes

**Quasi-coherence is an explicit argument, not an instance.**
`Stacks.SymGraded.schemeProjectiveBundle`
needs `Stacks.SymGraded.IsQuasicoherentPieces E`, which is produced from `E.IsQuasicoherent` by a
theorem taking that as an *instance*. Inside the existential of `IsProjective` there is no
instance to be had, so `Stacks.Tag087SBundle.projectiveBundle` takes the quasi-coherence
explicitly and applies the producing theorem with `@`. This keeps the predicate a plain `∃` with
no `letI` in its body, so destructuring it needs no instance plumbing.

**`SheafOfModules.IsFiniteType` is used with its universes pinned**, as
`SheafOfModules.IsFiniteType.{u, u, u}`, matching
`Stacks.AmpleGlobalGeneration.IsEventuallyGloballyGenerated` and
`Stacks.AmpleEventualGeneration.IsFinGenAfterSomeTwist`; those are where part (1)'s eventual
global generation input will have to come from, so the two must be stated at the same universes
to compose.

**`IsProjective` is a `def`, not an `abbrev`**, matching `Stacks.HProjective.IsHProjective`. The
existential data is reached through the lemmas below.

## The projective bundle and Tag 01OB

The projective bundle `𝐏(E)` of Tag 01OB has a library form for every quasi-coherent `E`: the
quasi-coherence of the pieces of `Sym(E)` is
`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`, and
`projectiveBundle` below is built from it. The absence of a 01OB attribute
does not mean that the bundle is absent, only that no tag is attached.

What remains absent for Tag 01OB is the relative twist `𝒪_{𝐏(E)}(n)` over
`SheafGradedAlgebra` data (`../RelativeProjTwists/Statement.lean:96` records that no `TwistData`
is constructed there — every occurrence is a parameter, never a construction) and
functoriality of the bundle in `E`, of which the base change along an isomorphism of the base is
the case `../ProjectiveCoherentImage/Locality.lean:118-128` needs.

## What is not done, and no tag is attached

**Neither part of Stacks Tag 087S is proved here, and no 087S attribute is attached anywhere in
this file.** The tag has exactly two parts, `"part (1)"` and `"part (2)"`, one assertion each.
Each theorem below carries one hypothesis the tag lacks —
`Stacks.Tag087SBundle.BundlesAreHProjective S` for part (1),
`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` for part (2) — so neither is
registered as that part.

The residual content of part (1), after the equivalence below, is exactly: a surjection
`𝒪_S^{⊕(n+1)} ⟶ E` induces a closed immersion `𝐏(E) ⟶ ℙⁿ_S` over `S`; `𝐏(E) ≅ 𝐏(E ⊗ L^{⊗n})`
over `S` ([Stacks, Tag 02NC]); and clause (7) of [Stacks, Tag 01Q3], which is a `def` at
`../AmpleGlobalGeneration/Basic.lean:173` and is reduced to the module-valued form of
[Stacks, Tag 01PW], which has no formalization here.

**Two inputs of that residual content are already in the library.**

* A morphism of *relative* Projs from a surjection of graded algebras, beyond the absolute case
  at `../RelativeProjChain/EventualSurjective.lean:206`:
  `Stacks.AlgebraicGeometry.RelativeProjMapDomain`
  `.isClosedImmersion_relativeMapHom_of_eventually_epi`
  (`../RelativeProjMapDomain/EventualSurjective.lean:186`, Tag 07ZI(2)/07ZK(2)) makes
  `r_ψ : Proj_S(B) ⟶ Proj_S(A)` a closed immersion whenever `A_d ⟶ B_d` is epi for `d ≫ 0`, and
  `relativeMapDomain_eq_top_of_eventually_epi` :170 puts its domain at the whole of `Proj_S(B)`.
  What part (1) still needs is therefore not that morphism but the two identifications around
  it: that `Sym^d` of a surjection of quasi-coherent modules is epi, and that
  `Proj_S(Sym(𝒪_S^{⊕(n+1)}))` is `ℙⁿ_S` over `S`.
* Tag 02NC is stated, in its relative form — over a scheme `S`, for a quasi-coherent graded
  `𝒪_S`-algebra twisted by an invertible `𝒪_S`-module, with the isomorphism `g` over `S`, the
  isomorphisms `θ_n` assembling into an isomorphism of `ℤ`-graded algebras, and the squares of
  clause (2) — as
  `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwist_tag`
  (`../Constructions/ProjInvertibleTwistRelativeTag.lean`). The graded-ring form over `Spec R` is
  `Stacks.GradedRing.InvertibleTwist.projTwistIsoGeneral`
  (`../Constructions/ProjInvertibleTwist.lean`).

## References

* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01PY](https://stacks.math.columbia.edu/tag/01PY)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.QuasiProjectiveCompactification
  (exists_isOpenImmersion_isHProjective isHQuasiProjective_of_exists_isOpenImmersion_isHProjective)

universe u

namespace Stacks.Tag087SBundle

/-! ### The projective bundle of a quasi-coherent module -/

variable {S : Scheme.{u}}

/-- **The projective bundle `𝐏(E) = Proj_S(Sym(E))`** of a quasi-coherent `𝒪_S`-module.

This is `Stacks.SymGraded.schemeProjectiveBundle` with its hypothesis
`Stacks.SymGraded.IsQuasicoherentPieces` discharged by
`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`. The quasi-coherence of `E` is an
explicit argument rather than an instance so that this can appear under an existential binder;
see the implementation notes. -/
def projectiveBundle (E : S.Modules) (hq : E.IsQuasicoherent) : Scheme.{u} :=
  (Stacks.SymGraded.schemeProjectiveBundle E
    (@Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _ E hq)).scheme

/-- The structure morphism `𝐏(E) ⟶ S` of the projective bundle. -/
def projectiveBundleToBase (E : S.Modules) (hq : E.IsQuasicoherent) :
    projectiveBundle E hq ⟶ S :=
  Stacks.SymGraded.schemeProjectiveBundleToBase E
    (@Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _ E hq)

/-- **The projective bundle is separated over its base.** This is
`Stacks.SymGraded.isSeparated_schemeProjectiveBundleToBase` with the quasi-coherence hypothesis
discharged, and it is the property of `𝐏(E) ⟶ S` that the proof of [Stacks, Tag 07RM] uses
through [Stacks, Tag 03GI]. -/
theorem isSeparated_projectiveBundleToBase (E : S.Modules) (hq : E.IsQuasicoherent) :
    IsSeparated (projectiveBundleToBase E hq) :=
  Stacks.SymGraded.isSeparated_schemeProjectiveBundleToBase E _

/-! ### Stacks Tag 01W8 part (1): projectivity -/

/-- **Stacks Tag 01W8 part (1), projectivity**, over library names: `f` factors as a closed
immersion over `S` into the projective bundle of a finite-type quasi-coherent `𝒪_S`-module.

This is the projectivity predicate of the statement of Tag 01W8, with the projective bundle of
Tag 01OB realized as `Stacks.Tag087SBundle.projectiveBundle` and nothing else changed. -/
def IsProjective {X : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (E : S.Modules) (hq : E.IsQuasicoherent), SheafOfModules.IsFiniteType.{u, u, u} E ∧
    ∃ i : X ⟶ projectiveBundle E hq,
      IsClosedImmersion i ∧ i ≫ projectiveBundleToBase E hq = f

/-- **A projective morphism is separated.** It factors as a closed immersion, which is a
monomorphism and hence separated, followed by the structure morphism of `𝐏(E)`, which is
separated by `Stacks.Tag087SBundle.isSeparated_projectiveBundleToBase`.

This is the separatedness half of "projective implies proper", for the notion of projectivity of
Tag 01W8. The corresponding statement for H-projectivity is
`Stacks.HProjective.IsHProjective.isSeparated`. -/
theorem IsProjective.isSeparated {X : Scheme.{u}} {f : X ⟶ S} (hf : IsProjective f) :
    IsSeparated f := by
  obtain ⟨E, hq, -, i, hi, hif⟩ := hf
  have := hi
  have := isSeparated_projectiveBundleToBase E hq
  exact hif ▸ inferInstance

/-- **The structure morphism of a projective bundle is projective**, with the identity as its
closed immersion. This is what makes the reduction below an equivalence. -/
theorem isProjective_projectiveBundleToBase (E : S.Modules) (hq : E.IsQuasicoherent)
    (hft : SheafOfModules.IsFiniteType.{u, u, u} E) :
    IsProjective (projectiveBundleToBase E hq) :=
  ⟨E, hq, hft, 𝟙 _, inferInstance, Category.id_comp _⟩

/-! ### The geometric content of part (1) -/

/-- **The geometric content of part (1) of Stacks Tag 087S**: every projective bundle of a
finite-type quasi-coherent `𝒪_S`-module is H-projective.

This is the source's "by our definition of projective morphisms it suffices to show that
`𝐏(E) ⟶ S` is H-projective". It is stated as a condition on `S` because that is where the
source's ample invertible sheaf lives, and because
`Stacks.Tag087SBundle.isHProjective_of_isProjective_iff` shows it is *equivalent* to part (1) at
that base. -/
def BundlesAreHProjective (S : Scheme.{u}) : Prop :=
  ∀ (E : S.Modules) (hq : E.IsQuasicoherent), SheafOfModules.IsFiniteType.{u, u, u} E →
    Stacks.HProjective.IsHProjective (projectiveBundleToBase E hq)

/-- **Part (1) of Stacks Tag 087S**, from `Stacks.Tag087SBundle.BundlesAreHProjective`: a
projective morphism over `S` is H-projective.

The closed immersion into `𝐏(E)` is composed with the closed immersion of `𝐏(E)` into `ℙⁿ_S`,
by `Stacks.HProjective.IsHProjective.comp_isClosedImmersion`; equivalently this is the backward
direction of `Stacks.HProjective.isHProjective_iff_hasHProjectiveClosedImmersion`.

No ample invertible sheaf on `S` appears. The tag states part (1) under one, and the ample sheaf
is used entirely inside `BundlesAreHProjective` — it is what the source's appeal to clause (7) of
[Stacks, Tag 01Q3] and to [Stacks, Tag 02NC] consumes. Dropping an unused hypothesis strengthens
the statement; the tag's own form follows by discarding it. -/
theorem isHProjective_of_isProjective (h : BundlesAreHProjective S) {X : Scheme.{u}} {f : X ⟶ S}
    (hf : IsProjective f) : Stacks.HProjective.IsHProjective f := by
  obtain ⟨E, hq, hft, i, hi, hif⟩ := hf
  have := hi
  exact hif ▸ (h E hq hft).comp_isClosedImmersion i

/-- **Part (1) of Stacks Tag 087S is *equivalent* to
`Stacks.Tag087SBundle.BundlesAreHProjective`.**

Forward is `Stacks.Tag087SBundle.isHProjective_of_isProjective`. Backward holds because
`𝐏(E) ⟶ S` is itself projective (`Stacks.Tag087SBundle.isProjective_projectiveBundleToBase`), so
applying part (1) to it gives exactly H-projectivity of the bundle.

So the source's reduction loses nothing, and `BundlesAreHProjective S` is precisely what part (1)
owes at the base `S`: no weaker condition suffices and no stronger one is needed. -/
theorem isHProjective_of_isProjective_iff (S : Scheme.{u}) :
    (∀ (X : Scheme.{u}) (f : X ⟶ S), IsProjective f → Stacks.HProjective.IsHProjective f) ↔
      BundlesAreHProjective S := by
  constructor
  · intro h E hq hft
    exact h _ _ (isProjective_projectiveBundleToBase E hq hft)
  · intro h X f hf
    exact isHProjective_of_isProjective h hf

/-! ### Part (2), with the ample sheaf supplying Tag 07RM's hypotheses on the base -/

/-- **A base carrying an ample invertible module is quasi-compact and quasi-separated**, which is
the hypothesis of [Stacks, Tag 07RM] on the base, and is what the first sentence of the proof of
Stacks Tag 087S is for.

Quasi-compactness is clause (1) of the definition of ampleness ([Stacks, Tag 01PS]);
quasi-separatedness is the first paragraph of the proof of [Stacks, Tag 01PY], formalized as
`Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple`. Neither goes through
[Stacks, Tag 01Q1] or [Stacks, Tag 01MC], which the source cites in order to obtain the stronger
conclusion that `S` is separated — stronger than Tag 07RM uses. -/
theorem compactSpace_and_quasiSeparatedSpace_of_isAmple (S : Scheme.{u}) (M : S.Modules)
    [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M) :
    CompactSpace S ∧ QuasiSeparatedSpace S :=
  ⟨Stacks.Ample.IsAmple.compactSpace S M hM,
    Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple M hM⟩

/-- **Part (2) of Stacks Tag 087S**: over a base carrying an ample invertible module, a
quasi-projective morphism is H-quasi-projective.

The single hypothesis is `Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` at
`Stacks.HProjective.IsHProjective`, half 1 of the proof of [Stacks, Tag 07RM] with the
intermediate scheme H-projective. (At Definition 01W8's projectivity half 1 is the theorem
`Stacks.QuasiProjectiveCompactification.immersionIntoProjective_isProjective`; the H-projective
form asked for here is not proved.) The ample module `M` of the statement supplies the two
conditions Tag 07RM asks of the base, by
`Stacks.Tag087SBundle.compactSpace_and_quasiSeparatedSpace_of_isAmple`;
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isHProjective` then produces the
factorisation, and `Stacks.QuasiProjectiveCompactification.`
`isHQuasiProjective_of_exists_isOpenImmersion_isHProjective` turns it into
H-quasi-projectivity against quasi-compactness of `f`.

This is part (2) of the tag with exactly one hypothesis added and nothing removed, and it is
stated at the same `Stacks.Ample.IsAmple` and `Stacks.Ample.IsInvertibleModule` that the
neighbouring statements use.

Unlike `Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective`, the hypothesis here is **not
equivalent to the conclusion**:
`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` quantifies only over
quasi-compact quasi-separated bases, whereas part (2) in full
(`Stacks.QuasiProjectiveCompactification.HQuasiProjectiveOfQuasiProjective`) quantifies over all
of them, and a
quasi-compact quasi-separated scheme need carry no ample invertible module. The ample hypothesis
of the tag is precisely what closes that difference, and it is why ampleness is used here where
the sibling file records that it is not used at all. -/
theorem isHQuasiProjective_of_isQuasiProjective_of_isAmple
    (hgap : Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective
      @Stacks.HProjective.IsHProjective.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules) [Stacks.Ample.IsInvertibleModule S M]
    (hM : Stacks.Ample.IsAmple S M) (hf : Stacks.HProjective.IsQuasiProjective f) :
    Stacks.HProjective.IsHQuasiProjective f := by
  obtain ⟨hqc, hqs⟩ := compactSpace_and_quasiSeparatedSpace_of_isAmple S M hM
  have := hqc
  have := hqs
  exact isHQuasiProjective_of_exists_isOpenImmersion_isHProjective hf.quasiCompact
    (exists_isOpenImmersion_isHProjective hgap f hf)

/-- **The hypothesis used here is implied by the one the sibling file used.**
`Stacks.HProjective.ProjectiveCompactification` produces an *open* immersion onto an H-projective
morphism over an arbitrary base;
`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` asks only for an immersion, and
only over a quasi-compact quasi-separated base. Recorded so that the two reductions of part (2)
are visibly ordered, and so that nothing is lost by moving to this one. -/
theorem immersionIntoProjective_of_projectiveCompactification
    (h : Stacks.HProjective.ProjectiveCompactification.{u}) :
    Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective
      @Stacks.HProjective.IsHProjective.{u} := by
  intro X S f _ _ hf
  obtain ⟨X', j, p, hj, hjp, hp⟩ := h X S f hf
  have := hj
  exact ⟨X', j, p, inferInstance, hp, hjp⟩

end Stacks.Tag087SBundle

end
