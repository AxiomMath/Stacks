module

public import StacksFrontier.AlgebraicGeometry.LerayAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Basic
public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.FiniteSum
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact

/-!
# `step` for the twisted dévissage on `Proj 𝒜`

[Stacks, Tag 0B5Q] assertion (3) — the eventual vanishing of `Hᵖ(Proj 𝒜, ℱ(d))` for a coherent
`ℱ` — is reduced by `Stacks.AlgebraicGeometry.LerayAffineBase.exists_isZero_hgroup_twist_of_step`
to a single hypothesis `step`: a dévissage presenting each member of the class as the quotient
term of a short exact sequence whose middle term is eventually acyclic and whose sub is again in
the class. This file assembles that `step` out of Tag 0B5Q assertion (1) and Serre vanishing for
the twisting sheaves, and composes the result with the proved bound `hbound` to obtain assertion (3).

## Main definitions

All names below live in the namespace `Stacks.AlgebraicGeometry.ProjSerreDevissage`.

* `HasTwistQuotients`: **[Stacks, Tag 0B5Q] assertion (1)**, verbatim — every coherent
  `𝒪_{Proj 𝒜}`-module is the target of an epimorphism from a finite direct sum
  `⨁_{j} 𝒪(d_j)` of twisting sheaves. Stated through a `CategoryTheory.Limits.Bicone` together
  with `CategoryTheory.Limits.Bicone.IsBilimit` rather than through `⨁`, for the reason recorded
  in `StacksFrontier/AlgebraicGeometry/HighTwistDevissage/FiniteSum.lean`: a derived
  `HasBiproduct` instance does not unify with the ambient one.
* `HasEventuallyAcyclicTwists`: **Serre vanishing for the twisting sheaves** — for each `n` the
  positive-degree cohomology of `𝒪(n)(d)` over `Proj 𝒜` vanishes for all sufficiently large `d`.
* `HasCoherentTwistPresentation`: assertion (1) packaged as the short exact sequence the
  dévissage consumes, with the sub term asked to be coherent. This is the `Proj` analogue of the
  `hgen` hypothesis of
  `Stacks.HighTwistDevissage.isZero_hgroup_of_isAmple_of_isZero_negative_tensorPower`, which
  carries [Stacks, Tag 01Q3] clause (8) in exactly this shape.

## Main results

* `additive_hfunctor`, `additive_twistFunctor_comp_hfunctor`: `Hᵐ(U, -)` and `Hᵐ(U, (-)(d))` on
  `Proj 𝒜` are additive functors.
* `exists_isZero_hgroup_twist_of_isBilimit`: a finite direct sum of twisting sheaves inherits
  Serre vanishing from its summands, with a **single** `d₀` good for every positive degree at
  once — which is the form `step` asks for.
* `isCoherent_of_isBilimit`: a finite direct sum of coherent modules is coherent, for the root
  coherence predicate and for a bicone-presented direct sum.
* `hasCoherentTwistPresentation_of_hasTwistQuotients`: assertion (1) plus coherence of the
  twisting sheaves gives the packaged presentation. The middle term is coherent by
  `isCoherent_of_isBilimit` and the kernel then for free, by
  `AlgebraicGeometry.CoherentAbelian.isCoherent_kernel`.
* `step_of_hasCoherentTwistPresentation`: **`step` in the form
  `Stacks.AlgebraicGeometry.TwistFlatness.exists_isZero_hgroup_twist_of_descending_devissage`
  asks for it** (plain `T.ShortExact`).
* `step_twisted_of_hasCoherentTwistPresentation`: **`step` in the form
  `Stacks.AlgebraicGeometry.ProjTwistFunctor.exists_isZero_hgroup_twist_of_descending_devissage`
  and hence `Stacks.AlgebraicGeometry.LerayAffineBase.exists_isZero_hgroup_twist_of_step` ask
  for it** (every twist of the sequence short exact), under flatness of the twisting sheaves.
* `exists_isZero_hgroup_twist_of_presentation` and
  `exists_isZero_hgroup_twist_of_presentation_of_adjoin_degree_one`: **[Stacks, Tag 0B5Q]
  assertion (3) with `hbound` *and* the whole formal content of `step` discharged.** What is left
  standing in the hypotheses is exactly assertion (1), Serre vanishing for the twisting sheaves,
  and flatness of the twisting sheaves — the last of which is discharged outright when `𝒜` is
  generated in degree one.

## What this closes and what it does not

**Closed here.** Everything in `step` that is not one of those three statements: the passage from
a surjection to a short exact sequence (`CategoryTheory.ShortComplex.shortExact_mk_kernel_ι`),
coherence of the sub term (`AlgebraicGeometry.CoherentAbelian.isCoherent_kernel`, an instance for
the root `SheafOfModules.IsCoherent` over any ringed space, so it applies to `projRingSheaf 𝒜`
with no transport), coherence of the middle term from coherence of the summands, the additivity
of the cohomology functors on `Proj 𝒜`, the propagation of
Serre vanishing through a finite direct sum, the collapse of the per-summand degrees `d₀` to one
degree uniform in the positive cohomological degree, and the composition with the proved
`hbound`.

**NOT closed, and named.** Three hypotheses remain, none of them derivable from what is in either
tree:

1. `HasTwistQuotients` — [Stacks, Tag 0B5Q] assertion (1), i.e. Serre's theorem on `Proj`. The
   Stacks proof reduces it to [Stacks, Tag 0AG5], the degree-one-generated case, through the
   Veronese isomorphism [Stacks, Tag 0B5J].  Tag 0AG5 is attached, and unconditionally
   (`Stacks.AlgebraicGeometry.ProjTwistComparisonCompact.isIso_integerComparison`: the Tag 0B5I
   comparison `M̃ ⟶ ℱ` is an isomorphism for `Proj 𝒜` quasi-compact and `ℱ` quasi-coherent), but
   it is the recovery of a quasi-coherent sheaf from its twisted global sections, not the
   finiteness statement `HasTwistQuotients` asks for: it gives no finite set of twists whose sum
   surjects onto a coherent sheaf.  The only statement of this shape anywhere is
   `Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists`, which is for an *ample invertible*
   module and is itself a `def`, not a theorem.
2. `HasEventuallyAcyclicTwists` — Serre vanishing for `𝒪(n)` itself. There is
   no declaration in either tree whose statement is `Hᵖ` of a twisting sheaf, and no computation
   of `Hⁱ(ℙⁿ, 𝒪(d))` to bootstrap one from. The theorem
   `Stacks.AlgebraicGeometry.LerayAffineBase.exists_isZero_hgroup_twist` does not supply it: its
   bound `e` is uniform in the module but it says nothing in the degrees `0 < p ≤ e`, which is
   precisely the range `step` needs.
3. Flatness of the twisting sheaves, in the form `(twistFunctor 𝒜 d).PreservesMonomorphisms` for
   every `d`. For a graded ring that is not generated in degree one `𝒪(d)` is genuinely not
   invertible, so this cannot be a theorem at the tag's hypotheses; under degree-one generation
   it is `preservesMonomorphisms_twistFunctor_of_adjoin_degree_one` in the namespace
   `Stacks.AlgebraicGeometry.TwistFlatness`, and the corollary below discharges it.

A fourth hypothesis appears only on the route from the bare assertion (1) to the packaged
presentation: `∀ n, (twistingSheaf 𝒜 n).IsCoherent`. It too is absent, and for a located reason
— coherence of `𝒪(n)` is quasi-coherence (proved, as
`Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.isQuasicoherent_twistingSheaf`) together with
*finite type*, and nothing in either tree says `𝒪(n)` is of finite type.

**Which `IsCoherent`.** There are two distinct coherence constants in this repository: the root
`SheafOfModules.IsCoherent`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`) and
`Stacks.SheafOfModules.IsCoherent` (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`),
with identical fields. Inside a namespace beginning with `Stacks.` the spelling
`SheafOfModules.IsCoherent` resolves silently to the second, so the first is written here as
`_root_.SheafOfModules.IsCoherent` throughout. The root one is the constant
the statement of [Stacks, Tag 0B5Q] uses and the one whose kernel-closure instance and
`isQuasicoherent_of_isCoherent` are available, so it is the one this file is stated over.

**No attribute is attached.** The label `eventual_higher_cohomology_vanishing` of
[Stacks, Tag 0B5Q] is not proved: assertion (1) and the vanishing for `𝒪(n)` are hypotheses, so
there is no covering set. The other 0B5Q label live in the tree, `proj_noetherian`, is untouched.

## References

* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0AG5](https://stacks.math.columbia.edu/tag/0AG5)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistFunctor

universe u w

namespace Stacks.AlgebraicGeometry.ProjSerreDevissage

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]

section Additivity

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [EnoughInjectives (SheafOfModules.{u} (projRingSheaf 𝒜))]
  [HasDerivedCategory (SheafOfModules.{u} (projRingSheaf 𝒜))]
  [HasDerivedCategory AddCommGrpCat.{u}]

/-- **The cohomology functors of `Proj 𝒜` are additive.** Read off the `additive` field of the
right derived `δ`-functor of sections, whose degree-`m` part is the degree-`m` right derived
functor of sections on the nose. -/
theorem additive_hfunctor (U : Opens (ProjectiveSpectrum.top 𝒜)) (m : ℕ) :
    (Hfunctor (projRingSheaf 𝒜) U m).Additive :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (secF (projRingSheaf 𝒜) U)).additive m

/-- `Hᵐ(U, (-)(d))` is additive: the twist is additive unconditionally and the cohomology
functors of `Proj 𝒜` are additive by `additive_hfunctor`. -/
theorem additive_twistFunctor_comp_hfunctor (U : Opens (ProjectiveSpectrum.top 𝒜)) (m : ℕ)
    (d : ℤ) : (twistFunctor 𝒜 d ⋙ Hfunctor (projRingSheaf 𝒜) U m).Additive :=
  have := additive_hfunctor 𝒜 U m
  inferInstance

end Additivity

section Vanishing

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [EnoughInjectives (SheafOfModules.{u} (projRingSheaf 𝒜))]
  [HasDerivedCategory (SheafOfModules.{u} (projRingSheaf 𝒜))]
  [HasDerivedCategory AddCommGrpCat.{u}]

/-- **Serre vanishing for the twisting sheaves**, as a hypothesis: for each `n`, the twists
`𝒪(n)(d)` of the `n`-th twisting sheaf have no positive-degree cohomology over `U` once `d` is
large enough. -/
def HasEventuallyAcyclicTwists (U : Opens (ProjectiveSpectrum.top 𝒜)) : Prop :=
  ∀ n : ℤ, ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
    IsZero (Hgroup (projRingSheaf 𝒜) U m (twistSheafOfModules 𝒜 (twistingSheaf 𝒜 n) d))

/-- **A finite direct sum of twisting sheaves inherits Serre vanishing from its summands**, with
one degree `d₀` serving every positive cohomological degree at once.

Both quantifier moves matter for the dévissage: `step` asks for a single `d₀` valid for all
`m > 0` simultaneously, and it asks it of the direct sum rather than of the summands. The first
is the `Finset.sup`-style collapse below, which is available because the family is finite; the
second is additivity of `Hᵐ(U, (-)(d))`. -/
theorem exists_isZero_hgroup_twist_of_isBilimit
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (hvan : HasEventuallyAcyclicTwists 𝒜 U)
    {r : ℕ} (dj : Fin r → ℤ) {b : Bicone fun j : Fin r => twistingSheaf 𝒜 (dj j)}
    (hb : b.IsBilimit) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
      IsZero (Hgroup (projRingSheaf 𝒜) U m (twistSheafOfModules 𝒜 b.pt d)) := by
  choose f hf using fun j : Fin r => hvan (dj j)
  refine ⟨∑ j : Fin r, max (f j) 0, fun d hd m hm => ?_⟩
  have hdj : ∀ j : Fin r, f j ≤ d := by
    intro j
    refine le_trans (le_trans (le_max_left (f j) 0) ?_) hd
    exact Finset.single_le_sum (f := fun k : Fin r => max (f k) 0)
      (fun k _ => le_max_right (f k) 0) (Finset.mem_univ j)
  have hadd := additive_twistFunctor_comp_hfunctor 𝒜 U m d
  exact Stacks.HighTwistDevissage.isZero_obj_of_isBilimit
    (twistFunctor 𝒜 d ⋙ Hfunctor (projRingSheaf 𝒜) U m) hb
    (HasBiproduct.of_hasCoproduct _) fun j => hf j d (hdj j) m hm

end Vanishing

section Presentation

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **[Stacks, Tag 0B5Q] assertion (1).** Every coherent `𝒪_{Proj 𝒜}`-module is the target of an
epimorphism from a finite direct sum `⨁_{j = 1, …, r} 𝒪(d_j)` of twisting sheaves. -/
def HasTwistQuotients : Prop :=
  ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜), _root_.SheafOfModules.IsCoherent F →
    ∃ (r : ℕ) (dj : Fin r → ℤ) (b : Bicone fun j : Fin r => twistingSheaf 𝒜 (dj j))
      (_ : b.IsBilimit) (φ : b.pt ⟶ F), Epi φ

/-- **[Stacks, Tag 0B5Q] assertion (1), packaged as the dévissage sequence.** The short exact
sequence `0 ⟶ ℱ' ⟶ ⨁_j 𝒪(d_j) ⟶ ℱ ⟶ 0` with `ℱ'` again coherent. This is the shape the
dévissage consumes, and the `Proj` analogue of
`Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists`. -/
def HasCoherentTwistPresentation : Prop :=
  ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜), _root_.SheafOfModules.IsCoherent F →
    ∃ (T : ShortComplex (SheafOfModules.{u} (projRingSheaf 𝒜))) (r : ℕ) (dj : Fin r → ℤ)
      (b : Bicone fun j : Fin r => twistingSheaf 𝒜 (dj j)) (_ : b.IsBilimit) (_ : T.X₂ ≅ b.pt),
      T.ShortExact ∧ T.X₃ = F ∧ _root_.SheafOfModules.IsCoherent T.X₁

/-- **A finite direct sum of coherent modules is coherent**, for the root coherence predicate and
for a direct sum presented by a bicone rather than by `⨁`.

Transported across `AlgebraicGeometry.CoherentAbelian.isCoherent_iff_stacksIsCoherent` from
`Stacks.SheafOfModules.isCoherent_sigma`, which is where the finite-coproduct closure is proved;
the root predicate carries the weak Serre package but no coproduct instance of its own. -/
theorem isCoherent_of_isBilimit {ι : Type} [Finite ι]
    {f : ι → SheafOfModules.{u} (projRingSheaf 𝒜)} {b : Bicone f} (hb : b.IsBilimit)
    (hf : ∀ i, _root_.SheafOfModules.IsCoherent (f i)) :
    _root_.SheafOfModules.IsCoherent b.pt := by
  have : HasBiproduct f := HasBiproduct.mk ⟨b, hb⟩
  have hsig : Stacks.SheafOfModules.IsCoherent (∐ f) :=
    Stacks.SheafOfModules.isCoherent_sigma f fun i =>
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent (hf i)
  refine AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent ?_
  exact (Stacks.SheafOfModules.coherentModules (projRingSheaf 𝒜)).prop_of_iso
    ((biproduct.isoCoproduct f).symm.trans (biproduct.uniqueUpToIso f hb).symm) hsig

/-- **Assertion (1) gives the dévissage sequence**, as soon as the twisting sheaves themselves are
coherent. The sequence is the kernel sequence of the surjection; its middle term is coherent by
`isCoherent_of_isBilimit` and its sub term is then coherent because the kernel of a map of
coherent modules over a ringed space is coherent
(`AlgebraicGeometry.CoherentAbelian.isCoherent_kernel`), so no further hypothesis is needed. -/
theorem hasCoherentTwistPresentation_of_hasTwistQuotients
    (hquot : HasTwistQuotients 𝒜)
    (hcoh : ∀ n : ℤ, _root_.SheafOfModules.IsCoherent (twistingSheaf 𝒜 n)) :
    HasCoherentTwistPresentation 𝒜 := by
  intro F hF
  obtain ⟨r, dj, b, hb, φ, hφ⟩ := hquot F hF
  have hpt : _root_.SheafOfModules.IsCoherent b.pt :=
    isCoherent_of_isBilimit 𝒜 hb fun j => hcoh (dj j)
  have hFc : _root_.SheafOfModules.IsCoherent F := hF
  refine ⟨ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ), r, dj, b, hb, Iso.refl _,
    ShortComplex.shortExact_mk_kernel_ι φ, rfl, ?_⟩
  exact AlgebraicGeometry.CoherentAbelian.isCoherent_kernel φ

end Presentation

section Step

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [EnoughInjectives (SheafOfModules.{u} (projRingSheaf 𝒜))]
  [HasDerivedCategory (SheafOfModules.{u} (projRingSheaf 𝒜))]
  [HasDerivedCategory AddCommGrpCat.{u}]

/-- **`step` for the twisted dévissage, in the form that asks only `T.ShortExact`** — the
hypothesis of
`Stacks.AlgebraicGeometry.TwistFlatness.exists_isZero_hgroup_twist_of_descending_devissage`. -/
theorem step_of_hasCoherentTwistPresentation (U : Opens (ProjectiveSpectrum.top 𝒜))
    (hpres : HasCoherentTwistPresentation 𝒜) (hvan : HasEventuallyAcyclicTwists 𝒜 U) :
    ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜), _root_.SheafOfModules.IsCoherent F →
      ∃ T : ShortComplex (SheafOfModules.{u} (projRingSheaf 𝒜)), T.X₃ = F ∧
        _root_.SheafOfModules.IsCoherent T.X₁ ∧ T.ShortExact ∧
        ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
          IsZero (Hgroup (projRingSheaf 𝒜) U m (twistSheafOfModules 𝒜 T.X₂ d)) := by
  intro F hF
  obtain ⟨T, r, dj, b, hb, e, hse, hX₃, hX₁⟩ := hpres F hF
  obtain ⟨d₀, hd₀⟩ := exists_isZero_hgroup_twist_of_isBilimit 𝒜 U hvan dj hb
  refine ⟨T, hX₃, hX₁, hse, d₀, fun d hd m hm => ?_⟩
  have hadd := additive_twistFunctor_comp_hfunctor 𝒜 U m d
  exact IsZero.of_iso (hd₀ d hd m hm)
    ((twistFunctor 𝒜 d ⋙ Hfunctor (projRingSheaf 𝒜) U m).mapIso e)

/-- **`step` for the twisted dévissage, in the form that asks every twist of the sequence to be
short exact** — the hypothesis of
`Stacks.AlgebraicGeometry.ProjTwistFunctor.exists_isZero_hgroup_twist_of_descending_devissage`
and of `Stacks.AlgebraicGeometry.LerayAffineBase.exists_isZero_hgroup_twist_of_step`.

The extra input over `step_of_hasCoherentTwistPresentation` is flatness of the twisting sheaves:
right exactness of the twist is unconditional, so all that is asked is that it preserve
monomorphisms. -/
theorem step_twisted_of_hasCoherentTwistPresentation (U : Opens (ProjectiveSpectrum.top 𝒜))
    (hflat : ∀ d : ℤ, (twistFunctor 𝒜 d).PreservesMonomorphisms)
    (hpres : HasCoherentTwistPresentation 𝒜) (hvan : HasEventuallyAcyclicTwists 𝒜 U) :
    ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜), _root_.SheafOfModules.IsCoherent F →
      ∃ T : ShortComplex (SheafOfModules.{u} (projRingSheaf 𝒜)), T.X₃ = F ∧
        _root_.SheafOfModules.IsCoherent T.X₁ ∧
        (∀ d : ℤ, (T.map (twistFunctor 𝒜 d)).ShortExact) ∧
        ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
          IsZero (Hgroup (projRingSheaf 𝒜) U m (twistSheafOfModules 𝒜 T.X₂ d)) := by
  intro F hF
  obtain ⟨T, hX₃, hX₁, hse, hacyc⟩ := step_of_hasCoherentTwistPresentation 𝒜 U hpres hvan F hF
  refine ⟨T, hX₃, hX₁, fun d => ?_, hacyc⟩
  have := hflat d
  exact shortExact_map_twistFunctor_of_preservesMonomorphisms 𝒜 d hse

end Step

section Conclusion

variable {A : Type u} [CommRing A] {σ' : Type w} [SetLike σ' A] [AddSubgroupClass σ' A]
  (𝒜 : ℕ → σ') [GradedRing 𝒜] [IsNoetherianRing A]
  [EnoughInjectives (SheafOfModules.{u} (projRingSheaf 𝒜))]
  [HasDerivedCategory (SheafOfModules.{u} (projRingSheaf 𝒜))]
  [HasDerivedCategory AddCommGrpCat.{u}]

/-- **[Stacks, Tag 0B5Q] assertion (3) from assertion (1), Serre vanishing for the twisting
sheaves, and flatness of the twisting sheaves.** `hbound` is the theorem
`Stacks.AlgebraicGeometry.LerayAffineBase.exists_isZero_hgroup_twist` and is not a hypothesis
here; the class is coherence, which is quasi-coherent by
`isQuasicoherent_of_isCoherent`. -/
theorem exists_isZero_hgroup_twist_of_presentation
    (hflat : ∀ d : ℤ, (twistFunctor 𝒜 d).PreservesMonomorphisms)
    (hpres : HasCoherentTwistPresentation 𝒜) (hvan : HasEventuallyAcyclicTwists 𝒜 ⊤)
    (p : ℕ) (hp : 0 < p) (F : SheafOfModules.{u} (projRingSheaf 𝒜))
    (hF : _root_.SheafOfModules.IsCoherent F) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projRingSheaf 𝒜) ⊤ p (twistSheafOfModules 𝒜 F d)) :=
  LerayAffineBase.exists_isZero_hgroup_twist_of_step 𝒜
    (fun G => _root_.SheafOfModules.IsCoherent G)
    (fun G hG => have := hG; isQuasicoherent_of_isCoherent G)
    (step_twisted_of_hasCoherentTwistPresentation 𝒜 ⊤ hflat hpres hvan) p hp F hF

/-- **[Stacks, Tag 0B5Q] assertion (3) for `𝒜` generated in degree one**, from assertion (1) and
Serre vanishing for the twisting sheaves alone: under degree-one generation `𝒪(d)` is invertible
for every `d`, so the flatness hypothesis is discharged by
`Stacks.AlgebraicGeometry.TwistFlatness.preservesMonomorphisms_twistFunctor_of_adjoin_degree_one`,
which the corollary below applies. -/
theorem exists_isZero_hgroup_twist_of_presentation_of_adjoin_degree_one
    (hgen : Algebra.adjoin (𝒜 0) (Set.range fun f : 𝒜 1 => (f : A)) = ⊤)
    (hpres : HasCoherentTwistPresentation 𝒜) (hvan : HasEventuallyAcyclicTwists 𝒜 ⊤)
    (p : ℕ) (hp : 0 < p) (F : SheafOfModules.{u} (projRingSheaf 𝒜))
    (hF : _root_.SheafOfModules.IsCoherent F) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projRingSheaf 𝒜) ⊤ p (twistSheafOfModules 𝒜 F d)) :=
  exists_isZero_hgroup_twist_of_presentation 𝒜
    (fun d => TwistFlatness.preservesMonomorphisms_twistFunctor_of_adjoin_degree_one 𝒜 hgen d)
    hpres hvan p hp F hF

end Conclusion

end Stacks.AlgebraicGeometry.ProjSerreDevissage

end
