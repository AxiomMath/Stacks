module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.LocalProperties.InjectiveDimension
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Global dimension of a Noetherian ring is detected at the maximal ideals

Let `R` be a Noetherian ring and let `n : ℕ`. This file proves Stacks 00O9 in the sharp per-`n`
form: every `R`-module has projective dimension `≤ n` if and only if, for every maximal ideal `𝔪`
of `R`, every module over the localization `R_𝔪` has projective dimension `≤ n`.

Both implications go through the same two observations.

The first is that a bound on the global dimension is a statement about *cyclic* modules only:
for a ring `A`, every `A`-module has projective dimension `≤ n` as soon as every `A ⧸ I` does.
Indeed, `pd_A(A ⧸ I) ≤ n` for all ideals `I` makes `Ext^{n+1}(A ⧸ I, Y)` vanish for every `Y`,
which by Baer's criterion in its Ext form says that every `Y` has injective dimension `≤ n`; and
a uniform bound on injective dimensions makes `Ext^{n+1}(M, Y)` vanish for every `M` and `Y`,
that is, bounds every projective dimension by `n`. This is the mechanism behind Lemma 065T, and
it is what makes the two sides of the statement independent of the universe they are read in: the
cyclic modules of `A` live in the universe of `A`.

The second is that the two rings the source calls `R_𝔪` — the abstract localization `Rₘ 𝔪` and
`Localization 𝔪.primeCompl` — are isomorphic, and a bound on the global dimension is carried
across a ring isomorphism, and across a change of universe, by the previous observation together
with `ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv`.

With these in hand, the forward implication is Lemma 00O8: a module over a localization is its own
localization, so `ModuleCat.localizedModule_hasProjectiveDimensionLE` bounds its projective
dimension over `Localization S` by its projective dimension over `R`. The converse is Mathlib's
`ModuleCat.hasInjectiveDimensionLE_iff_forall_maximalSpectrum`, the local–global principle for
injective dimension, which needs no finiteness hypothesis and therefore replaces the source's
passage through a finite free resolution, Lemma 00O5 and Lemma 00NX: the hypothesis bounds the
injective dimension of every module over every `R_𝔪`, hence of every `R`-module, hence bounds
every projective dimension by `n`.

## Main results

* `Stacks.GlobalDimension.LocalGlobal.solution`: for a Noetherian ring, global dimension `≤ n` is
  equivalent to global dimension `≤ n` at every maximal ideal.

## Implementation notes

The source argues the converse through the `n`-th syzygy `K_n` of a finite module `M`: it is
finite, its localizations are projective by Lemma 00O5, and so `K_n` is finite projective by
Lemma 00NX. That route proves the bound for *finite* modules, and the passage from finite to
arbitrary modules is Lemma 065T. Since Mathlib's local–global principle for injective dimension
is already free of finiteness hypotheses, the proof below runs the dévissage of 065T once — in the
form of Baer's criterion, `ModuleCat.hasInjectiveDimensionLE_of_quotients` — and uses it both for
the universe transfer and in place of the syzygy argument. The mathematics is the same: 065T's
reduction to cyclic modules is the only ingredient the source's route needs beyond localization.

## References

* [StacksProject 00O9](https://stacks.math.columbia.edu/tag/00O9)
* [StacksProject 00O8](https://stacks.math.columbia.edu/tag/00O8)
* [StacksProject 065T](https://stacks.math.columbia.edu/tag/065T)
-/

@[expose] public section

namespace Stacks.GlobalDimension.LocalGlobal

universe u' w w' x x'

open CategoryTheory ModuleCat

/-- If every cyclic module `A ⧸ I` has projective dimension `≤ n`, then every `A`-module has
injective dimension `≤ n`. This is Baer's criterion, in the Ext form
`ModuleCat.hasInjectiveDimensionLE_of_quotients`. -/
@[ega "0 17.2.8" "(a') ⇒ (b)"]
private lemma forall_hasInjectiveDimensionLE_of_forall_quotient
    (A : Type w) [CommRing A] [Small.{w'} A] (n : ℕ)
    (h : ∀ I : Ideal A, HasProjectiveDimensionLE
      (ModuleCat.of A (Shrink.{w'} (A ⧸ I))) n) (Y : ModuleCat.{w'} A) :
    HasInjectiveDimensionLE Y n := by
  refine ModuleCat.hasInjectiveDimensionLE_of_quotients Y n (fun I => ?_)
  have := h I
  exact subsingleton_of_forall_eq 0
    (fun e => e.eq_zero_of_hasProjectiveDimensionLT (n + 1) le_rfl)

/-- If every `A`-module has injective dimension `≤ n`, then every `A`-module has projective
dimension `≤ n`: both say that `Ext^i` vanishes for `i > n`. -/
@[ega "0 17.2.8" "(b) ⇒ (a)"]
private lemma hasProjectiveDimensionLE_of_forall_hasInjectiveDimensionLE
    (A : Type w) [CommRing A] [Small.{w'} A] (n : ℕ)
    (h : ∀ Y : ModuleCat.{w'} A, HasInjectiveDimensionLE Y n) (M : ModuleCat.{w'} A) :
    HasProjectiveDimensionLE M n := by
  refine hasProjectiveDimensionLT_of_enoughInjectives M (n + 1) (fun Y => ?_)
  have := h Y
  exact subsingleton_of_forall_eq 0
    (fun e => e.eq_zero_of_hasInjectiveDimensionLT (n + 1) le_rfl)

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- A bound on the global dimension is carried along a ring isomorphism, and across a change of
the universe the modules are taken in: it is enough to carry it on cyclic modules, and a cyclic
module of `B` is a cyclic module of `A` for the `A`-action obtained from `e`. -/
private lemma forall_hasInjectiveDimensionLE_of_ringEquiv
    {A : Type w} [CommRing A] [Small.{w'} A] {B : Type x} [CommRing B] [Small.{x'} B]
    (e : A ≃+* B) (n : ℕ)
    (h : ∀ M : ModuleCat.{w'} A, HasProjectiveDimensionLE M n) (Y : ModuleCat.{x'} B) :
    HasInjectiveDimensionLE Y n := by
  refine forall_hasInjectiveDimensionLE_of_forall_quotient B n (fun I => ?_) Y
  have hsB : Small.{w'} B := small_of_surjective e.surjective
  have hsQ : Small.{w'} (B ⧸ I) := small_of_surjective Ideal.Quotient.mk_surjective
  let _ : Module A (B ⧸ I) := Module.compHom _ (e : A →+* B)
  let eid : (B ⧸ I) ≃ₛₗ[(e : A →+* B)] (B ⧸ I) :=
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
      invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let e' : Shrink.{w'} (B ⧸ I) ≃ₛₗ[(e : A →+* B)] Shrink.{x'} (B ⧸ I) :=
    ((Shrink.linearEquiv.{w'} A (B ⧸ I)).trans eid).trans
      (Shrink.linearEquiv.{x'} B (B ⧸ I)).symm
  have := h (.of A (Shrink.{w'} (B ⧸ I)))
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e
    (M := .of A (Shrink.{w'} (B ⧸ I))) (N := .of B (Shrink.{x'} (B ⧸ I))) e' n

/-- Stacks 00O8 (2). If every `R`-module has projective dimension `≤ n`, then so does every
module over a localization `S⁻¹R`: such a module is its own localization. -/
private lemma hasProjectiveDimensionLE_localization
    {R : Type u} [CommRing R] [Small.{u'} R] (S : Submonoid R) (n : ℕ)
    (h : ∀ M : ModuleCat.{u'} R, HasProjectiveDimensionLE M n)
    (Z : ModuleCat.{u'} (Localization S)) : HasProjectiveDimensionLE Z n := by
  have : Small.{u'} (Localization S) := small_of_surjective Localization.mkHom_surjective
  let M' := (Z : Type u')
  let _ : Module R M' := Module.compHom M' (algebraMap R (Localization S))
  have _ : IsScalarTower R (Localization S) M' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : IsLocalizedModule S (LinearMap.id : M' →ₗ[R] M') :=
    isLocalizedModule_id S M' (Localization S)
  let eA : ((ModuleCat.of R M').localizedModule S) ≃ₗ[Localization S] M' :=
    LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
      (IsLocalizedModule.linearEquiv S ((ModuleCat.of R M').localizedModuleMkLinearMap S)
        (LinearMap.id : M' →ₗ[R] M'))
  have := h (ModuleCat.of R M')
  have : HasProjectiveDimensionLE ((ModuleCat.of R M').localizedModule S) n :=
    ModuleCat.localizedModule_hasProjectiveDimensionLE n S _
  exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
    (M := (ModuleCat.of R M').localizedModule S) (N := Z) eA n

/-- **Global dimension of a Noetherian ring is detected at the maximal ideals.** -/
public theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ)
    (Rₘ : (𝔪 : Ideal R) → [𝔪.IsMaximal] → Type v)
    [∀ (𝔪 : Ideal R) [𝔪.IsMaximal], CommRing (Rₘ 𝔪)]
    [∀ (𝔪 : Ideal R) [𝔪.IsMaximal], Algebra R (Rₘ 𝔪)]
    [∀ (𝔪 : Ideal R) [𝔪.IsMaximal], IsLocalization.AtPrime (Rₘ 𝔪) 𝔪] :
    (∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M n) ↔
      ∀ (𝔪 : Ideal R) [𝔪.IsMaximal] (M : ModuleCat.{v} (Rₘ 𝔪)),
        HasProjectiveDimensionLE M n := by
  refine ⟨fun hR 𝔪 _ M => ?_, fun h => ?_⟩
  · exact hasProjectiveDimensionLE_of_forall_hasInjectiveDimensionLE (Rₘ 𝔪) n
      (forall_hasInjectiveDimensionLE_of_ringEquiv
        (IsLocalization.algEquiv 𝔪.primeCompl (Localization 𝔪.primeCompl) (Rₘ 𝔪)).toRingEquiv n
        (hasProjectiveDimensionLE_localization 𝔪.primeCompl n hR)) M
  · refine hasProjectiveDimensionLE_of_forall_hasInjectiveDimensionLE R n fun Y => ?_
    refine (ModuleCat.hasInjectiveDimensionLE_iff_forall_maximalSpectrum n Y).mpr fun m => ?_
    have := m.2
    exact forall_hasInjectiveDimensionLE_of_ringEquiv
      (IsLocalization.algEquiv m.1.primeCompl (Rₘ m.1) (Localization m.1.primeCompl)).toRingEquiv n
      (h m.1) _

end Stacks.GlobalDimension.LocalGlobal

end

/-!
# Global dimension of a Noetherian ring is detected at the maximal ideals

Let `R` be a Noetherian ring and let `n : ℕ`. Then every `R`-module has projective dimension
`≤ n` — that is, `R` has global dimension `≤ n` in the sense of Definition 00O6 — if and only if
for every maximal ideal `𝔪` of `R` every `R_𝔪`-module has projective dimension `≤ n`.

The forward implication is Lemma 00O8: localization is exact and carries projective modules to
projective modules, so it carries a projective resolution of length `≤ n` to one of length `≤ n`.
For the converse, let `M` be a finite `R`-module and choose a resolution
`0 → K → F_{n-1} → … → F_0 → M → 0` with the `F_i` finite free. Each `K ⊗_R R_𝔪` is then the
`n`-th syzygy of `M_𝔪`, hence projective by the hypothesis and Lemma 00O5; since `K` is finite,
Lemma 00NX makes `K` itself finite projective, so `M` has projective dimension `≤ n`. Finally a
bound on the projective dimensions of the *finite* modules bounds them all, by the transfinite
dévissage of Lemma 0D1U (Auslander) through Lemma 065T.

Taking `∃ n` on both sides recovers the source's phrasing, "`R` has finite global dimension if
and only if there is an integer `n` bounding the global dimensions of all the `R_𝔪`": it is
`exists_congr` applied to this statement.

## Main results

* `Ring.forall_hasProjectiveDimensionLE_iff_forall_isLocalization_maximal`: for a Noetherian ring,
  global dimension `≤ n` is equivalent to global dimension `≤ n` at every maximal ideal.

## Implementation notes

Mathlib has no predicate for the global dimension of a ring, so "`A` has global dimension `≤ n`"
is spelled out as `∀ M : ModuleCat.{w} A, HasProjectiveDimensionLE M n`, using the projective
dimension of an object of an abelian category (`CategoryTheory.HasProjectiveDimensionLE`, which
is `HasProjectiveDimensionLT _ (n + 1)`). This is the form in which the localization API of
`Mathlib.RingTheory.LocalProperties.ProjectiveDimension` is phrased, in particular the sibling
`ModuleCat.hasProjectiveDimensionLE_iff_forall_maximalSpectrum`, which is the same statement for
one fixed finite module in place of all modules at once.

The modules are quantified over one universe per ring — `ModuleCat.{u} R` for `R : Type u`, and
`ModuleCat.{v} (Rₘ 𝔪)` for `Rₘ 𝔪 : Type v` — rather than over all universes at once, which no
single statement can do. Nothing is lost: by Lemma 065T a bound on the projective dimensions of
the cyclic modules `A ⧸ I` alone bounds the projective dimension of every `A`-module, and the
cyclic modules already live in the universe of `A`. So each side is independent of the universe
it is read in.

The statement is per `n`, and is therefore sharper than the source's: the same `n` transfers in
both directions, which is what the source's proof in fact establishes.

Following `Ring.krullDimLE_of_isLocalization_maximal` and
`IsNoetherianRing.of_isLocalization_maximal`, `R_𝔪` is an abstract family `Rₘ` of `R`-algebras
with `IsLocalization.AtPrime (Rₘ 𝔪) 𝔪`, not the concrete `Localization.AtPrime 𝔪`; the concrete
family is one instantiation, and a reader holding any other localization applies the lemma
without transporting along `IsLocalization.algEquiv`.

Faithfulness. (1) No hypothesis is dead: `IsNoetherianRing R` is what makes the converse true, and
it fails without it, as `R = ∏_{i ∈ ℕ} 𝔽₂` shows — `R` is von Neumann regular, so every `R_𝔪` is a
field and has global dimension `0`, while `R` is not semisimple and so does not have global
dimension `0`; the localization instances are used to identify the rings `Rₘ 𝔪` of the conclusion,
and `n` occurs on both sides. (2) The scalars are the source's on each side: the left side is about
`R`-modules and their projective dimension over `R`, the right side about `Rₘ 𝔪`-modules and their
projective dimension over `Rₘ 𝔪`, which is what "`R_𝔪` has global dimension `≤ n`" asserts.
(3) The ring the source names as `R_𝔪` is pinned, not merely posited to be some local ring:
`IsLocalization.AtPrime (Rₘ 𝔪) 𝔪` pins it through the canonical `algebraMap R (Rₘ 𝔪)`, as the
localization of `R` at the complement of `𝔪`. (4) The instantiation is not degenerate: `R = ℤ`,
`Rₘ 𝔪 = Localization.AtPrime 𝔪` and `n = 1` satisfies both sides with content — every localization
`ℤ_(p)` is a discrete valuation ring of global dimension `1` and `ℤ` has global dimension `1` — and
both sides fail for `R = ℤ`, `n = 0`, so neither is vacuously true.

## References

* [StacksProject 00O9](https://stacks.math.columbia.edu/tag/00O9)

## Tags

global dimension, projective dimension, Noetherian ring, localization, maximal ideal
-/

@[expose] public section



open CategoryTheory

/-- **Global dimension of a Noetherian ring is detected at the maximal ideals.** For a Noetherian
ring `R` and `n : ℕ`, every `R`-module has projective dimension `≤ n` if and only if, for every
maximal ideal `𝔪` of `R`, every module over the localization `R_𝔪` has projective dimension `≤ n`.
Taking `∃ n` on both sides gives the source's statement that `R` has finite global dimension iff
the global dimensions of the `R_𝔪` are bounded. -/
@[stacks 00O9]
public theorem Ring.forall_hasProjectiveDimensionLE_iff_forall_isLocalization_maximal
    {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ)
    (Rₘ : (𝔪 : Ideal R) → [𝔪.IsMaximal] → Type v)
    [∀ (𝔪 : Ideal R) [𝔪.IsMaximal], CommRing (Rₘ 𝔪)]
    [∀ (𝔪 : Ideal R) [𝔪.IsMaximal], Algebra R (Rₘ 𝔪)]
    [∀ (𝔪 : Ideal R) [𝔪.IsMaximal], IsLocalization.AtPrime (Rₘ 𝔪) 𝔪] :
    (∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M n) ↔
      ∀ (𝔪 : Ideal R) [𝔪.IsMaximal] (M : ModuleCat.{v} (Rₘ 𝔪)),
        HasProjectiveDimensionLE M n := by apply Stacks.GlobalDimension.LocalGlobal.solution

end
