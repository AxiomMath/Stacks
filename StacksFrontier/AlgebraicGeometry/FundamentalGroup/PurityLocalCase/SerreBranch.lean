module

public import StacksFrontier.Algebra.Module.LocalizedRingEquiv
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumSerreAlgebraization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.LocalLefschetz
public import StacksFrontier.RingTheory.AssociatedPrime.Spellings
public import StacksFrontier.RingTheory.Catenary.FormalFibresAssociatedDimension
public import StacksFrontier.RingTheory.Catenary.Saturated
public import StacksFrontier.RingTheory.Depth.UnqualifiedDepth
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Branch (c)(i) of the hypotheses of Stacks 0EK5 and Stacks 0EK6

Work in the local Lefschetz situation of Tag 0BLF: `(A, 𝔪)` is a Noetherian local ring, `f ∈ 𝔪`,
`X = Spec A` and `X₀ = V(f)`. Stacks 0EK5 and Stacks 0EK6 both assume, besides a dualizing
complex on `A` and henselianness of the pair `(A, (f))`, that one of

* (c)(i) `A_f` is `(S₂)` and every irreducible component of `X` not contained in `X₀` has
  dimension `≥ 3`, or
* (c)(ii) `depth(A_𝔭) + dim(A/𝔭) > 2` for every prime `𝔭 ⊂ A` with `f ∉ 𝔭`

holds. This file proves that (c)(i) implies (c)(ii), in exactly the form in which
`AlgebraicGeometry.LocalLefschetzSituation.fullyFaithful_finiteEtaleRestriction_of_depth` and
`AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_extension_of_depth_add_dim` take
it, so that either branch may be fed to the carriers of Stacks 0EK5 and Stacks 0EK6. The file
imports neither carrier, so that both may import it.

## Main results

* `AlgebraicGeometry.LocalLefschetzSituation.two_lt_depth_add_ringKrullDim_of_propertySkRing_away`
  — branch (c)(i) implies branch (c)(ii).

## The argument

Let `𝔭` be a prime of `A` with `f ∉ 𝔭`. Since `A` has a dualizing complex it is universally
catenary ([Stacks, Tag 0A80]), hence catenary in the saturated sense. The localization `A_𝔭` is a
localization of `A_f`, so `(S₂)` for `A_f` bounds `depth(A_𝔭)` below by `min(2, dim A_𝔭)`, and
`𝔭` is not the maximal ideal — which contains `f` — so `dim(A/𝔭) ≥ 1`. A prime of `A_f` minimal
over the annihilator of `A_f` contracts to a minimal prime of `A` avoiding `f`, which is an
irreducible component of `X` not contained in `X₀`, so its quotient has dimension `≥ 3`. Running
through the chain-in-the-support argument of
`Stacks.Algebraization.two_lt_depth_add_ringKrullDim_of_propertySkModule_away` — the step that
[Stacks, Tag 0EJC] leaves implicit, proved there for an arbitrary finite module — then gives
`depth(A_𝔭) + dim(A/𝔭) ≥ 3`, which is the strict bound `> 2` of branch (c)(ii).

That general step asks for its dimension bound at every *associated* prime of the localized
module, not only at the minimal ones. Serre's condition `(S₂)` implies `(S₁)`, and over an `(S₁)`
ring the associated primes of the ring itself are exactly its minimal primes
(`mem_minimalPrimes_of_isAssociatedPrimeStacks_self`); that is what turns the hypothesis on the
irreducible components into the hypothesis the general step takes.

## Implementation notes

The module is `A` itself: with `M = A` the general step's conclusion is literally the `hdepth`
hypothesis of the two carriers, including its spelling of the localized module as
`LocalizedModule 𝔭.primeCompl A` and of the two quantities inside `EInt` through
`Stacks.Algebraization.enatToEInt` and `Stacks.Algebraization.krullDimToEInt`.

Branch (c)(i) is stated in the two vocabularies the library already has for its two halves, and
no new predicate is introduced. `(S₂)` for `A_f` is `PropertySkRing (Localization.Away f) 2`,
Serre's condition of [Stacks, Tag 031P] for a ring. "Every irreducible component of `X` not
contained in `X₀` has dimension `≥ 3`" is spelled on minimal primes: the components of
`Spec A` are the `V(𝔮)` for `𝔮` a minimal prime, `V(𝔮) ⊆ V(f)` says `f ∈ 𝔮`, and the dimension
of `V(𝔮)` is `ringKrullDim (A ⧸ 𝔮)`.

Two spellings of Serre's condition occur. `PropertySkRing` of [Stacks, Tag 031P] measures depth
with `ringDepth` and truncates the dimension of the localization to `ℕ∞`;
`HasSerreCondition`, which `mem_minimalPrimes_of_isAssociatedPrimeStacks_self` is stated in,
measures depth with `Module.depth` along the maximal ideal and compares inside `WithBot ℕ∞`. The
two agree, by `ringDepth_eq_depth_maximalIdeal`, and the private lemma below passes from `(S₂)`
in the first to `(S₁)` in the second.

## References

* [Stacks Project, Tag 0EK5](https://stacks.math.columbia.edu/tag/0EK5)
* [Stacks Project, Tag 0EK6](https://stacks.math.columbia.edu/tag/0EK6)
* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80), universal catenarity.
* [Stacks Project, Tag 031P](https://stacks.math.columbia.edu/tag/031P), Serre's conditions.
* [Stacks Project, Tag 031Q](https://stacks.math.columbia.edu/tag/031Q), `(S₁)` and the
  associated primes.
* [Stacks Project, Tag 0EJC](https://stacks.math.columbia.edu/tag/0EJC), the general step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.Algebraization (enatToEInt krullDimToEInt)

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- Serre's condition `(S₂)` in the `PropertySkRing` spelling of [Stacks, Tag 031P] gives `(S₁)`
in the `HasSerreCondition` spelling. The bound `min(k, dim)` is monotone in `k`, the depth of a
local ring is its depth as a module over itself along its maximal ideal
(`ringDepth_eq_depth_maximalIdeal`), and the dimension of `Localization.AtPrime p` is either `⊥`,
where the bound is vacuous, or a value of `ℕ∞` that the truncation `WithBot.unbotD 0` returns
unchanged. -/
@[ega "IV 5.7.3" "special case"]
private theorem hasSerreCondition_one_of_propertySkRing_two (R : Type u) [CommRing R]
    [IsNoetherianRing R] (h : PropertySkRing R 2) : HasSerreCondition R 1 := by
  intro p hp
  have hd : min (1 : ℕ∞) ((ringKrullDim (Localization.AtPrime p)).unbotD 0) ≤
      Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) := by
    rw [← ringDepth_eq_depth_maximalIdeal]
    exact le_trans (min_le_min_right _ (by norm_num)) (h p)
  cases hdim : ringKrullDim (Localization.AtPrime p) with
  | bot => simp
  | coe d =>
      rw [hdim, WithBot.unbotD_coe] at hd
      exact_mod_cast hd

namespace LocalLefschetzSituation

/-- **Branch (c)(i) of the hypotheses of [Stacks, Tag 0EK5] and [Stacks, Tag 0EK6] implies
branch (c)(ii).** In the local Lefschetz situation assume that `A` has a dualizing complex, that
`A_f` satisfies Serre's condition `(S₂)`, and that every irreducible component of `X = Spec A`
not contained in `X₀ = V(f)` — that is, `V(𝔮)` for a minimal prime `𝔮` of `A` with `f ∉ 𝔮` — has
dimension at least `3`. Then

`depth(A_𝔭) + dim(A/𝔭) > 2`

for every prime `𝔭 ⊂ A` with `f ∉ 𝔭`.

The conclusion is verbatim the `hdepth` hypothesis of
`fullyFaithful_finiteEtaleRestriction_of_depth_add_dim` (the case (c)(ii) of Stacks 0EK5) and of
`exists_finiteEtale_extension_of_depth_add_dim` (Stacks 0EK6), so either branch of hypothesis (c)
feeds both. -/
public theorem two_lt_depth_add_ringKrullDim_of_propertySkRing_away
    (S : LocalLefschetzSituation.{u})
    (omega : DerivedCategory (ModuleCat.{u} S.A))
    (homega : Dualizing.IsDualizingComplex (A := S.A) (K := omega))
    (hS₂ : PropertySkRing (Localization.Away S.f) 2)
    (hcomponents : ∀ q : Ideal S.A, q ∈ minimalPrimes S.A → S.f ∉ q →
      (3 : WithBot ℕ∞) ≤ ringKrullDim (S.A ⧸ q)) :
    ∀ p : PrimeSpectrum S.A, S.f ∉ p.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl S.A)) +
        krullDimToEInt (ringKrullDim (S.A ⧸ p.asIdeal)) > ((2 : ℤ) : EInt) := by
  have hcat : IsCatenaryRingSaturated S.A :=
    isCatenaryRingSaturated_of_isCatenary
      (Dualizing.isUniversallyCatenary_of_isDualizingComplex homega S.A)
  let e : LocalizedModule.Away S.f S.A ≃ₗ[Localization.Away S.f] Localization.Away S.f :=
    localizedModuleSelfEquivLocalization (Submonoid.powers S.f)
  have hS₂mod : PropertySkModule (Localization.Away S.f) (LocalizedModule.Away S.f S.A) 2 :=
    propertySkModule_of_linearEquiv e 2 ((propertySkModule_self_iff_propertySkRing 2).mpr hS₂)
  have hbound : ∀ q : Ideal (Localization.Away S.f),
      IsAssociatedPrimeStacks (Localization.Away S.f) (LocalizedModule.Away S.f S.A) q →
      (3 : WithBot ℕ∞) ≤
        ringKrullDim (S.A ⧸ q.comap (algebraMap S.A (Localization.Away S.f))) := by
    intro q hq
    have hqmem : q ∈ associatedPrimes (Localization.Away S.f)
        (LocalizedModule.Away S.f S.A) := by
      rwa [← Stacks.RingTheory.AssociatedPrimeStacks.assStacks_eq_associatedPrimes]
    rw [LinearEquiv.AssociatedPrimes.eq e] at hqmem
    have hqself : IsAssociatedPrimeStacks (Localization.Away S.f) (Localization.Away S.f) q := by
      rwa [← Stacks.RingTheory.AssociatedPrimeStacks.assStacks_eq_associatedPrimes] at hqmem
    have hmap := IsLocalization.minimalPrimes_map (Submonoid.powers S.f)
      (Localization.Away S.f) (⊥ : Ideal S.A)
    rw [Ideal.map_bot] at hmap
    have hcontr : q.comap (algebraMap S.A (Localization.Away S.f)) ∈ minimalPrimes S.A := by
      have hq' : q ∈ (⊥ : Ideal (Localization.Away S.f)).minimalPrimes :=
        mem_minimalPrimes_of_isAssociatedPrimeStacks_self
          (hasSerreCondition_one_of_propertySkRing_two _ hS₂) q hqself
      rwa [hmap] at hq'
    exact hcomponents _ hcontr fun hf => hqself.1.ne_top (Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_comap.mp hf)
      (IsLocalization.map_units (Localization.Away S.f) ⟨S.f, Submonoid.mem_powers S.f⟩))
  exact Stacks.Algebraization.two_lt_depth_add_ringKrullDim_of_propertySkModule_away hcat S.f
    S.f_mem_maximalIdeal S.A hS₂mod hbound

end LocalLefschetzSituation

end AlgebraicGeometry

end
