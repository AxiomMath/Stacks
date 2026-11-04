module

public import Mathlib.RingTheory.Ideal.Height
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksFrontier.RingTheory.LocalCohomology.CatenaryEquidimensional
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Catenary.Saturated

/-!
# Depth of a localization against the codimension of the prime

Let `A` be a Noetherian local ring which is catenary and satisfies Serre's condition `(S₂)`.
Being catenary and `(S₂)` makes `Spec(A)` equidimensional, so the dimension of `A` splits at
every prime `𝔭` as

`dim(A) = height(𝔭) + dim(A ⧸ 𝔭)`,

and `height(𝔭) = dim(A_𝔭)`. Serre's condition therefore gives
`min(2, dim(A) - dim(A ⧸ 𝔭)) ≤ depth(A_𝔭)`: in a ring of dimension at least four the
localization at a prime whose quotient has dimension two has depth at least two.

A Noetherian ring admitting a dualizing complex is catenary, so the hypotheses of the last
assertion of [Stacks, Tag 0F2B] -- a dualizing complex, Serre's condition `(S₂)` and dimension
at least four -- do give depth at least two at every such prime.

## Main results

* `ringKrullDim_eq_height_add_ringKrullDim_quotient_of_equidimensional`: the dimension of a
  catenary Noetherian local ring with equidimensional spectrum splits at every prime as the height
  plus the dimension of the quotient.
* `ringKrullDim_eq_height_add_ringKrullDim_quotient`: the same for a catenary `(S₂)` Noetherian
  local ring.
* `two_le_ringDepth_localization_of_two_le_height`: an `(S₂)` Noetherian ring has depth at least
  two at every prime of height at least two.
* `two_le_ringDepth_localization_of_isCatenary`: a catenary `(S₂)` Noetherian local ring of
  dimension at least four has depth at least two at every prime whose quotient has dimension two.
* `two_le_ringDepth_localization_of_isDualizingComplex`: the same conclusion from a dualizing
  complex in place of catenarity, which is the last assertion of [Stacks, Tag 0F2B].

## Implementation notes

Serre's condition is `PropertySkRing A 2`, that is `min(2, dim A_𝔭) ≤ depth(A_𝔭)` at every prime,
with the dimension of the localization truncated to a natural number by `WithBot.unbotD 0` and
the depth measured by `ringDepth`; the conclusions below are stated with the same `ringDepth`.

Equidimensionality of `Spec(A)` is used through `SpecEquidimensional`, the statement that all
minimal primes have quotients of equal dimension, which is what the height formula
`FlatLocalCatenary.height_add_coheight_eq` consumes; the topological form produced from
catenarity and `(S₂)` is converted once by `specEquidimensional_iff_equidimensional`.

Catenarity enters only through `coheight_covby_of_catenary`, stated for the saturated-chain
spelling `IsCatenaryRingSaturated`, so `Ring.IsCatenary` is translated into that spelling first.

The source states its last assertion for the primes containing a nonzerodivisor `f` under
hypotheses on the depth of `A` and of `A ⧸ fA`; neither `f` nor those hypotheses enter the
argument, so the statement here is for every prime whose quotient has dimension two.

## References

* [Stacks Project, Tag 0F2B](https://stacks.math.columbia.edu/tag/0F2B)
* [Stacks Project, Tag 0FIW](https://stacks.math.columbia.edu/tag/0FIW)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
* [Stacks Project, Tag 031P](https://stacks.math.columbia.edu/tag/031P)
-/

@[expose] public section

open CategoryTheory IsLocalRing PrimeSpectrum TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Serre.LocalizationDepth

/-- **The dimension of a catenary equidimensional Noetherian local ring splits at every prime**
as the height of the prime plus the dimension of the quotient by it. On an equidimensional
spectrum `height(𝔭) + dim(A ⧸ 𝔭)` is the common dimension of the quotients by the minimal primes
(catenarity makes the coheight drop by one along every cover), which is the dimension of `A`
because the maximal ideal has height `dim(A)` and coheight zero. -/
@[ega "0 16.1.4" "Noetherian local rings"]
theorem ringKrullDim_eq_height_add_ringKrullDim_quotient_of_equidimensional (A : Type u)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (hcat : Ring.IsCatenary A)
    (hequi' : Equidimensional (PrimeSpectrum A)) (p : Ideal A) [p.IsPrime] :
    ringKrullDim A = (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) := by
  obtain ⟨r, hr, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := p) bot_le
  let rSpec : PrimeSpectrum A := ⟨r, hr.1.1⟩
  have hcov := coheight_covby_of_catenary (_root_.isCatenaryRingSaturated_of_isCatenary hcat)
  have hequi : SpecEquidimensional A := specEquidimensional_iff_equidimensional.mpr hequi'
  have hsum : ∀ q : PrimeSpectrum A,
      q.asIdeal.height + Order.coheight q = Order.coheight rSpec := fun q => by
    simpa only [← PrimeSpectrum.height_eq_orderHeight] using
      FlatLocalCatenary.height_add_coheight_eq hcov hequi q rSpec hr
  have hdimMax : ringKrullDim A = (Order.coheight rSpec : WithBot ℕ∞) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    have h := hsum ⊤
    simp only [Order.coheight_top, add_zero] at h
    exact_mod_cast h
  have hsumP' := hsum ⟨p, inferInstance⟩
  calc
    ringKrullDim A = (Order.coheight rSpec : WithBot ℕ∞) := hdimMax
    _ = ((p.height + Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum A) : ℕ∞)
          : WithBot ℕ∞) := by exact_mod_cast hsumP'.symm
    _ = (p.height : WithBot ℕ∞)
          + (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum A) : WithBot ℕ∞) := by
          rw [WithBot.coe_add]
    _ = (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) := by
          rw [coheight_eq_ringKrullDim_quotient]

/-- **The dimension of a catenary `(S₂)` Noetherian local ring splits at every prime** as the
height of the prime plus the dimension of the quotient by it. Catenarity and `(S₂)` make
`Spec(A)` equidimensional (Stacks 0FIW), and on an equidimensional catenary local spectrum the
dimension splits by `ringKrullDim_eq_height_add_ringKrullDim_quotient_of_equidimensional`. -/
@[ega "0 16.1.4" "special case", ega "IV 5.10.9" "more general", sga "2 III 3.9" "special case"]
theorem ringKrullDim_eq_height_add_ringKrullDim_quotient (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hcat : Ring.IsCatenary A)
    (hS₂ : PropertySkRing A 2) (p : Ideal A) [p.IsPrime] :
    ringKrullDim A = (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) :=
  ringKrullDim_eq_height_add_ringKrullDim_quotient_of_equidimensional A hcat
    (Stacks.Equidimensional.equidimensional_of_isCatenary_of_propertySkRing_two A hcat hS₂) p

/-- **An `(S₂)` Noetherian ring has depth at least two at every prime of height at least two.**
The height of the prime is the dimension of the localization, so Serre's condition reads
`min(2, dim A_𝔭) = 2 ≤ depth(A_𝔭)` there. -/
theorem two_le_ringDepth_localization_of_two_le_height (A : Type u) [CommRing A]
    [IsNoetherianRing A] (hS₂ : PropertySkRing A 2) (p : Ideal A) [p.IsPrime]
    (hheight : 2 ≤ p.height) :
    2 ≤ ringDepth (Localization.AtPrime p) := by
  have hdimloc : (2 : ℕ∞) ≤ (ringKrullDim (Localization.AtPrime p)).unbotD 0 :=
    WithBot.le_unbotD (by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
      exact WithBot.coe_le_coe.mpr hheight)
  simpa [min_eq_left hdimloc] using hS₂ p

/-- **A catenary `(S₂)` Noetherian local ring of dimension at least four has depth at least two
at every prime whose quotient has dimension two.** Splitting the dimension at the prime turns
`dim(A) ≥ 4` and `dim(A ⧸ 𝔭) = 2` into `height(𝔭) ≥ 2`, and Serre's condition converts that
height into depth. -/
theorem two_le_ringDepth_localization_of_isCatenary (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hcat : Ring.IsCatenary A)
    (hS₂ : PropertySkRing A 2) (hdim : 4 ≤ ringKrullDim A) (p : Ideal A) [p.IsPrime]
    (hp : ringKrullDim (A ⧸ p) = 2) :
    2 ≤ ringDepth (Localization.AtPrime p) := by
  have hsum := ringKrullDim_eq_height_add_ringKrullDim_quotient A hcat hS₂ p
  rw [hp] at hsum
  have h4 : (4 : ℕ∞) ≤ p.height + 2 := by
    apply WithBot.coe_le_coe.mp
    simpa [WithBot.coe_add, hsum] using hdim
  have hheight : (2 : ℕ∞) ≤ p.height :=
    (ENat.add_le_add_iff_right (show (2 : ℕ∞) ≠ ⊤ by simp)).mp
      (by simpa [show (4 : ℕ∞) = 2 + 2 by norm_num, add_comm] using h4)
  exact two_le_ringDepth_localization_of_two_le_height A hS₂ p hheight

/-- **The last assertion of [Stacks, Tag 0F2B].** Let `A` be a Noetherian local ring admitting a
dualizing complex, satisfying Serre's condition `(S₂)` and of dimension at least four. Then the
localization of `A` at a prime whose quotient has dimension two has depth at least two, which is
the fourth hypothesis of that source's proposition.

A ring with a dualizing complex is universally catenary, hence catenary, so this is the
preceding statement. The source restricts the primes to those containing an element `f` which it
assumes to be a nonzerodivisor with `depth(A ⧸ fA) ≥ 2`; neither `f` nor those two hypotheses
enter the argument. -/
@[stacks 0F2B "the last assertion: (S₂) and dimension at least four give hypothesis (4)"]
theorem two_le_ringDepth_localization_of_isDualizingComplex (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {K : DerivedCategory (ModuleCat.{u} A)}
    (hK : Dualizing.IsDualizingComplex K) (hS₂ : PropertySkRing A 2)
    (hdim : 4 ≤ ringKrullDim A) :
    ∀ p : PrimeSpectrum A, ringKrullDim (A ⧸ p.asIdeal) = 2 →
      2 ≤ ringDepth (Localization.AtPrime p.asIdeal) := fun p hp =>
  two_le_ringDepth_localization_of_isCatenary A
    (Dualizing.isUniversallyCatenary_of_isDualizingComplex hK A) hS₂ hdim p.asIdeal hp

end Stacks.Serre.LocalizationDepth

end
