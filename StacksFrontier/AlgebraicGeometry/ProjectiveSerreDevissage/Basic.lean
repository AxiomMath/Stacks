module

public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Devissage
public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.FiniteSum
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# `step` for the twisted dévissage on `ℙⁿ_R`

[Stacks, Tag 01YS] assertion (4) — eventual vanishing of `Hⁱ(ℙⁿ_R, ℱ(d))` in each positive
degree `i`, for `ℱ` coherent over a Noetherian ring `R` — is reduced by the engine
`TwistFlatness.exists_isZero_hgroup_projectiveTwist_of_descending_devissage`
to two hypotheses: a uniform high-degree bound `hbound`, and a dévissage `step` presenting each
coherent module as the quotient term of a short exact sequence whose middle term is eventually
acyclic and whose sub term is again coherent. This file assembles that `step`, and the whole
conclusion, from the two statements of Serre's theorem that neither tree carries.

This is the `ℙⁿ_R` counterpart of
`StacksFrontier/AlgebraicGeometry/ProjSerreDevissage/Basic.lean`, which does the same for
[Stacks, Tag 0B5Q] assertion (3) over `Proj 𝒜`. The two statements are different —
`AlgebraicGeometry.projectiveSpaceOverRing` is a pullback presentation and not a `Proj` term — so
the assembly is carried out separately, as the twist infrastructure beneath it already is.

## Main definitions

All names below live in the namespace `Stacks.AlgebraicGeometry.ProjectiveSerreDevissage`.

* `HasEventuallyAcyclicProjectiveTwists`: **Serre vanishing for the twisting sheaves of `ℙⁿ_R`** —
  for each `k` the positive-degree cohomology of `𝒪(k)(d)` vanishes for all sufficiently large
  `d`.
* `HasProjectiveTwistQuotients`: **Serre's theorem on `ℙⁿ_R`** — every coherent
  `𝒪_{ℙⁿ_R}`-module is the target of an epimorphism from a finite direct sum `⨁ⱼ 𝒪(dⱼ)` of
  twisting sheaves. Stated through a `CategoryTheory.Limits.Bicone` with
  `CategoryTheory.Limits.Bicone.IsBilimit` rather than through `⨁`, for the reason recorded in
  `StacksFrontier/AlgebraicGeometry/HighTwistDevissage/FiniteSum.lean`: a derived `HasBiproduct`
  instance does not unify with the ambient one.
* `HasCoherentProjectiveTwistPresentation`: the same packaged as the short exact sequence the
  dévissage consumes, with the sub term asked to be coherent.
* `HasUniformProjectiveTwistBound`: the high-degree bound `hbound` asks for, with the bounding
  degree existentially quantified so that either shape of the cohomological-dimension statement
  discharges it.

## Main results

* `additive_hfunctor`, `additive_projectiveTwistFunctor_comp_hfunctor`: `Hᵐ(U, -)` and
  `Hᵐ(U, (-)(d))` on `ℙⁿ_R` are additive functors.
* `exists_isZero_hgroup_projectiveTwist_of_isBilimit`: a finite direct sum of twisting sheaves
  inherits Serre vanishing from its summands, with a **single** `d₀` good for every positive
  degree at once — the form `step` asks for.
* `isCoherent_of_isBilimit`: a finite direct sum of coherent modules is coherent, for the root
  coherence predicate and for a bicone-presented direct sum.
* `hasCoherentProjectiveTwistPresentation_of_hasProjectiveTwistQuotients`: Serre's theorem plus
  coherence of the twisting sheaves gives the packaged presentation; the kernel is coherent for
  free, by `AlgebraicGeometry.CoherentAbelian.isCoherent_kernel`.
* `step_of_hasCoherentProjectiveTwistPresentation`: **`step` exactly as the engine asks for it.**
  Unlike on `Proj 𝒜`, no flatness hypothesis appears: `𝒪_{ℙⁿ_R}(d)` is unconditionally
  invertible, so the engine used here already carries short exactness of every twist.
* `HasUniformProjectiveTwistBound`: the high-degree bound `hbound` asks for.
* `isZero_cohomology_high_twist_of_presentation`: **[Stacks, Tag 01YS] assertion (4) with the
  whole formal content of `step` discharged.** What is left standing is exactly Serre's theorem,
  Serre vanishing for the twisting sheaves, and the high-degree bound.

## Implementation notes

**Why `CategoryTheory.HasDerivedCategory` is an instance argument and not a local instance.**
`EnoughInjectives` is supplied here by a local instance, exactly as the library's statement of
[Stacks, Tag 01YS] supplies it, so that the conclusion carries no instance hypothesis of that
kind. Doing the same for the derived category — `attribute [local instance]
HasDerivedCategory.standard`, which is what the proof of that statement does — makes the
conclusion below **exceed the default heartbeat budget**: at this pin the file then fails with a
`whnf` timeout at 200000 heartbeats, and that proof correspondingly carries
`maxHeartbeats 1000000` on this very theorem. Carrying the two `HasDerivedCategory` instances as
arguments removes the need outright — the file elaborates in under six seconds — so that compiler
option is an artifact of installing the standard construction as an instance, not of the
mathematics.

**`IsNoetherianRing R` is not needed and is not assumed.** The statement of Tag 01YS carries it;
in its proof it is used only inside the two sorried inputs that are hypotheses here. Everything
this file proves holds over an arbitrary commutative ring, so the conclusion is stated that way
and the tagged statement is the special case.

## What this closes and what it does not

**Closed here.** Everything in the proof of [Stacks, Tag 01YS] assertion (4) that is not one
of those three statements: the passage from a surjection to a short exact sequence, coherence of
the sub term, coherence of the middle term from coherence of the summands, additivity of the
cohomology functors on `ℙⁿ_R`, the propagation of Serre vanishing through a finite direct sum,
the collapse of the per-summand degrees `d₀` to one degree uniform in the positive cohomological
degree, and the dévissage induction itself.

**Strictly weaker hypotheses than the library's proof of Tag 01YS asks for, in two places.**

1. That proof consumes a presentation each of whose *twists* is separately asserted to be
   short exact. That clause is unnecessary: short exactness of every twist on `ℙⁿ_R` is
   unconditional (`Stacks.AlgebraicGeometry.TwistFlatness.shortExact_map_projectiveTwistFunctor`,
   from invertibility of `𝒪_{ℙⁿ_R}(d)`), so only plain short exactness of the one sequence is
   asked here.
2. That proof uses the bound at `e = n` — vanishing above the dimension. Any bound will do,
   so `HasUniformProjectiveTwistBound` quantifies it existentially.

**NOT closed, and named.** Three hypotheses remain, none derivable from either tree:

1. `HasProjectiveTwistQuotients` — Serre's theorem on `ℙⁿ_R`, i.e. the surjection from a finite
   sum of twists. Absent: the only statement of this shape anywhere is
   `Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists`, which is for an *ample invertible*
   module and is a `def`, not a theorem; and its `Proj` counterpart
   `Stacks.AlgebraicGeometry.ProjSerreDevissage.HasTwistQuotients` is a hypothesis there too.
2. `HasEventuallyAcyclicProjectiveTwists` — Serre vanishing for `𝒪(k)` itself. Absent, for the
   same reason already recorded on the `Proj` side: there is no computation of `Hⁱ(ℙⁿ, 𝒪(d))` in
   either tree to bootstrap one from. The uniform bound does not supply it — a bound in
   degrees `p > e` says nothing in the range `0 < p ≤ e`, which is exactly what `step` needs.
3. `HasUniformProjectiveTwistBound` — the high-degree bound. Its `Proj 𝒜` counterpart is proved
   (`Stacks.AlgebraicGeometry.LerayAffineBase.exists_isZero_hgroup_twist`, from properness of
   `Proj 𝒜 ⟶ Spec 𝒜₀`); on `ℙⁿ_R` nothing in either tree states it, and the two shapes that
   would give it — vanishing above the dimension, and the bound from a finite affine cover
   ([Stacks, Tag 01XI]) — are both unattached. Note the ingredient for the second is available:
   `Stacks.AlgebraicGeometry.ProjBaseChange.iSup_baseChangeOpen_eq_top` covers `ℙⁿ_R` by `n + 1`
   affine charts.

**Which `IsCoherent`.** As on the `Proj` side, there are two coherence constants in this
repository, and inside a namespace beginning with `Stacks.` the spelling
`SheafOfModules.IsCoherent` resolves silently to the second. The root
`_root_.SheafOfModules.IsCoherent` is the one the statement of [Stacks, Tag 01YS] is made over — it is
what `F.IsCoherent` means for `F : X.Modules` — and it is the one used throughout here.

**No attribute is attached.** The label `eventual_vanishing` of [Stacks, Tag 01YS] is not proved:
Serre's theorem and the vanishing for `𝒪(k)` are hypotheses, so there is no covering set.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistFunctor

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSerreDevissage

variable {R : Type u} [CommRing R] (n : ℕ)

section Additivity

variable
  [EnoughInjectives (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)]
  [HasDerivedCategory
    (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)]
  [HasDerivedCategory AddCommGrpCat.{u}]

/-- **The cohomology functors of `ℙⁿ_R` are additive.** Read off the `additive` field of the
right derived `δ`-functor of sections, whose degree-`m` part is the degree-`m` right derived
functor of sections on the nose. -/
theorem additive_hfunctor (U : (projectiveSpaceOverRing n (.of R)).Opens) (m : ℕ) :
    (Hfunctor (projectiveSpaceOverRing n (.of R)).ringCatSheaf U m).Additive :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (secF (projectiveSpaceOverRing n (.of R)).ringCatSheaf U)).additive m

/-- `Hᵐ(U, (-)(d))` is additive: the twist on `ℙⁿ_R` is additive unconditionally and the
cohomology functors are additive by `additive_hfunctor`. -/
theorem additive_projectiveTwistFunctor_comp_hfunctor
    (U : (projectiveSpaceOverRing n (.of R)).Opens) (m : ℕ) (d : ℤ) :
    (projectiveTwistFunctor n d ⋙
      Hfunctor (projectiveSpaceOverRing n (.of R)).ringCatSheaf U m).Additive :=
  have := additive_hfunctor n U m
  inferInstance

end Additivity

section Vanishing

variable
  [EnoughInjectives (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)]
  [HasDerivedCategory
    (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)]
  [HasDerivedCategory AddCommGrpCat.{u}]

/-- **Serre vanishing for the twisting sheaves of `ℙⁿ_R`**, as a hypothesis: for each `k` the
twists `𝒪(k)(d)` of the `k`-th twisting sheaf have no positive-degree cohomology over `U` once
`d` is large enough. -/
def HasEventuallyAcyclicProjectiveTwists
    (U : (projectiveSpaceOverRing n (.of R)).Opens) : Prop :=
  ∀ k : ℤ, ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
    IsZero (Hgroup (projectiveSpaceOverRing n (.of R)).ringCatSheaf U m
      (projectiveTwist n (projectiveTwistingSheaf n k) d))

/-- **A finite direct sum of twisting sheaves inherits Serre vanishing from its summands**, with
one degree `d₀` serving every positive cohomological degree at once.

Both quantifier moves matter for the dévissage: `step` asks for a single `d₀` valid for all
`m > 0` simultaneously, and it asks it of the direct sum rather than of the summands. The first
is the `Finset`-sum collapse below, available because the family is finite; the second is
additivity of `Hᵐ(U, (-)(d))`. -/
theorem exists_isZero_hgroup_projectiveTwist_of_isBilimit
    (U : (projectiveSpaceOverRing n (.of R)).Opens)
    (hvan : HasEventuallyAcyclicProjectiveTwists n U)
    {r : ℕ} (dj : Fin r → ℤ)
    {b : Bicone fun j : Fin r => projectiveTwistingSheaf (R := R) n (dj j)}
    (hb : b.IsBilimit) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
      IsZero (Hgroup (projectiveSpaceOverRing n (.of R)).ringCatSheaf U m
        (projectiveTwist n b.pt d)) := by
  choose f hf using fun j : Fin r => hvan (dj j)
  refine ⟨∑ j : Fin r, max (f j) 0, fun d hd m hm => ?_⟩
  have hdj : ∀ j : Fin r, f j ≤ d := by
    intro j
    refine le_trans (le_trans (le_max_left (f j) 0) ?_) hd
    exact Finset.single_le_sum (f := fun k : Fin r => max (f k) 0)
      (fun k _ => le_max_right (f k) 0) (Finset.mem_univ j)
  have hadd := additive_projectiveTwistFunctor_comp_hfunctor n U m d
  exact Stacks.HighTwistDevissage.isZero_obj_of_isBilimit
    (projectiveTwistFunctor n d ⋙
      Hfunctor (projectiveSpaceOverRing n (.of R)).ringCatSheaf U m) hb
    (HasBiproduct.of_hasCoproduct _) fun j => hf j d (hdj j) m hm

end Vanishing

section Presentation

/-- **Serre's theorem on `ℙⁿ_R`.** Every coherent `𝒪_{ℙⁿ_R}`-module is the target of an
epimorphism from a finite direct sum `⨁_{j = 1, …, r} 𝒪(dⱼ)` of twisting sheaves. -/
def HasProjectiveTwistQuotients : Prop :=
  ∀ F : SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf,
    _root_.SheafOfModules.IsCoherent F →
      ∃ (r : ℕ) (dj : Fin r → ℤ)
        (b : Bicone fun j : Fin r => projectiveTwistingSheaf (R := R) n (dj j))
        (_ : b.IsBilimit) (φ : b.pt ⟶ F), Epi φ

/-- **Serre's theorem on `ℙⁿ_R`, packaged as the dévissage sequence.** The short exact sequence
`0 ⟶ ℱ' ⟶ ⨁ⱼ 𝒪(dⱼ) ⟶ ℱ ⟶ 0` with `ℱ'` again coherent. This is the shape the dévissage
consumes, and it is the hypothesis the library's proof of [Stacks, Tag 01YS] assumes — there with the
redundant extra clause that every twist of the sequence is separately short exact. -/
def HasCoherentProjectiveTwistPresentation : Prop :=
  ∀ F : SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf,
    _root_.SheafOfModules.IsCoherent F →
      ∃ (T : ShortComplex
            (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf))
        (r : ℕ) (dj : Fin r → ℤ)
        (b : Bicone fun j : Fin r => projectiveTwistingSheaf (R := R) n (dj j))
        (_ : b.IsBilimit) (_ : T.X₂ ≅ b.pt),
        T.ShortExact ∧ T.X₃ = F ∧ _root_.SheafOfModules.IsCoherent T.X₁

/-- **A finite direct sum of coherent modules is coherent**, for the root coherence predicate and
for a direct sum presented by a bicone rather than by `⨁`.

Transported across `AlgebraicGeometry.CoherentAbelian.isCoherent_iff_stacksIsCoherent` from
`Stacks.SheafOfModules.isCoherent_sigma`, which is where the finite-coproduct closure is proved;
the root predicate carries the weak Serre package but no coproduct instance of its own. -/
theorem isCoherent_of_isBilimit {ι : Type} [Finite ι]
    {f : ι → SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf}
    {b : Bicone f} (hb : b.IsBilimit)
    (hf : ∀ i, _root_.SheafOfModules.IsCoherent (f i)) :
    _root_.SheafOfModules.IsCoherent b.pt := by
  have : HasBiproduct f := HasBiproduct.mk ⟨b, hb⟩
  have hsig : Stacks.SheafOfModules.IsCoherent (∐ f) :=
    Stacks.SheafOfModules.isCoherent_sigma f fun i =>
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent (hf i)
  refine AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent ?_
  exact (Stacks.SheafOfModules.coherentModules
      (projectiveSpaceOverRing n (.of R)).ringCatSheaf).prop_of_iso
    ((biproduct.isoCoproduct f).symm.trans (biproduct.uniqueUpToIso f hb).symm) hsig

/-- **Serre's theorem gives the dévissage sequence**, as soon as the twisting sheaves themselves
are coherent. The sequence is the kernel sequence of the surjection; its middle term is coherent
by `isCoherent_of_isBilimit` and its sub term is then coherent because the kernel of a map of
coherent modules over a ringed space is coherent
(`AlgebraicGeometry.CoherentAbelian.isCoherent_kernel`), so no further hypothesis is needed. -/
theorem hasCoherentProjectiveTwistPresentation_of_hasProjectiveTwistQuotients
    (hquot : HasProjectiveTwistQuotients (R := R) n)
    (hcoh : ∀ k : ℤ,
      _root_.SheafOfModules.IsCoherent (projectiveTwistingSheaf (R := R) n k)) :
    HasCoherentProjectiveTwistPresentation (R := R) n := by
  intro F hF
  obtain ⟨r, dj, b, hb, φ, hφ⟩ := hquot F hF
  have hpt : _root_.SheafOfModules.IsCoherent b.pt :=
    isCoherent_of_isBilimit n hb fun j => hcoh (dj j)
  have hFc : _root_.SheafOfModules.IsCoherent F := hF
  refine ⟨ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ), r, dj, b, hb, Iso.refl _,
    ShortComplex.shortExact_mk_kernel_ι φ, rfl, ?_⟩
  exact AlgebraicGeometry.CoherentAbelian.isCoherent_kernel φ

end Presentation

section Step

variable
  [EnoughInjectives (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)]
  [HasDerivedCategory
    (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)]
  [HasDerivedCategory AddCommGrpCat.{u}]

/-- **`step` for the twisted dévissage on `ℙⁿ_R`**, in the form the engine
`TwistFlatness.exists_isZero_hgroup_projectiveTwist_of_descending_devissage`
asks for it.

No flatness hypothesis appears, in contrast with the `Proj 𝒜` counterpart: `𝒪_{ℙⁿ_R}(d)` is
unconditionally invertible, so that engine already carries short exactness of every twist. -/
theorem step_of_hasCoherentProjectiveTwistPresentation
    (U : (projectiveSpaceOverRing n (.of R)).Opens)
    (hpres : HasCoherentProjectiveTwistPresentation (R := R) n)
    (hvan : HasEventuallyAcyclicProjectiveTwists n U) :
    ∀ F : SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf,
      _root_.SheafOfModules.IsCoherent F →
        ∃ T : ShortComplex
            (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf),
          T.X₃ = F ∧ _root_.SheafOfModules.IsCoherent T.X₁ ∧ T.ShortExact ∧
          ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
            IsZero (Hgroup (projectiveSpaceOverRing n (.of R)).ringCatSheaf U m
              (projectiveTwist n T.X₂ d)) := by
  intro F hF
  obtain ⟨T, r, dj, b, hb, e, hse, hX₃, hX₁⟩ := hpres F hF
  obtain ⟨d₀, hd₀⟩ := exists_isZero_hgroup_projectiveTwist_of_isBilimit n U hvan dj hb
  refine ⟨T, hX₃, hX₁, hse, d₀, fun d hd m hm => ?_⟩
  have hadd := additive_projectiveTwistFunctor_comp_hfunctor n U m d
  exact IsZero.of_iso (hd₀ d hd m hm)
    ((projectiveTwistFunctor n d ⋙
      Hfunctor (projectiveSpaceOverRing n (.of R)).ringCatSheaf U m).mapIso e)

end Step

section Conclusion

/-- The category of module sheaves on `ℙⁿ_R` has enough injectives, being Grothendieck abelian.
Declared locally, in the spelling the statement of [Stacks, Tag 01YS] uses, so that the
conclusion below carries no instance hypothesis that statement lacks. -/
noncomputable local instance modulesEnoughInjectives (S : Type u) [CommRing S] (m : ℕ) :
    EnoughInjectives (SheafOfModules.{u} (projectiveSpaceOverRing m (.of S)).ringCatSheaf) :=
  IsGrothendieckAbelian.enoughInjectives

variable
  [HasDerivedCategory
    (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)]
  [HasDerivedCategory AddCommGrpCat.{u}]

/-- **The high-degree bound `hbound` asks for**, as a hypothesis: some degree `e` beyond which
all twists of every coherent module are acyclic over `U`.

Existentially quantified in `e` so that either available shape of the statement discharges it —
vanishing above the dimension of `ℙⁿ_R`, which is the `e = n` case the proof of [Stacks, Tag 01YS]
uses, or the bound from a finite affine cover of [Stacks, Tag 01XI]. -/
def HasUniformProjectiveTwistBound
    (U : (projectiveSpaceOverRing n (.of R)).Opens) : Prop :=
  ∃ e : ℕ, ∀ p : ℕ, e < p →
    ∀ F : SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf,
      _root_.SheafOfModules.IsCoherent F → ∀ d : ℤ,
        IsZero (Hgroup (projectiveSpaceOverRing n (.of R)).ringCatSheaf U p
          (projectiveTwist n F d))

/-- **[Stacks, Tag 01YS] assertion (4) from Serre's theorem, Serre vanishing for the twisting
sheaves, and the high-degree bound**, with everything else in its proof discharged.

The conclusion is the statement `isZero_cohomology_high_twist` of Tag 01YS, over this
repository's own names, with the three hypotheses above in place of that statement's three sorried
inputs. No attribute is attached: they are hypotheses, so there is no covering set for the label
`eventual_vanishing`. -/
theorem isZero_cohomology_high_twist_of_presentation
    (hbound : HasUniformProjectiveTwistBound (R := R) n ⊤)
    (hpres : HasCoherentProjectiveTwistPresentation (R := R) n)
    (hvan : HasEventuallyAcyclicProjectiveTwists (R := R) n ⊤)
    (F : (projectiveSpaceOverRing n (.of R)).Modules) [hF : F.IsCoherent]
    (i : ℕ) (hi : 0 < i) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projectiveSpaceOverRing n (.of R)).ringCatSheaf ⊤ i
        (projectiveTwist n F d)) := by
  obtain ⟨e, he⟩ := hbound
  exact TwistFlatness.exists_isZero_hgroup_projectiveTwist_of_descending_devissage n ⊤
    (fun G => _root_.SheafOfModules.IsCoherent G) e he
    (step_of_hasCoherentProjectiveTwistPresentation n ⊤ hpres hvan) i hi F hF

end Conclusion

end Stacks.AlgebraicGeometry.ProjectiveSerreDevissage

end
