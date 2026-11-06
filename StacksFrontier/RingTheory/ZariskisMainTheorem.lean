module

public import Mathlib.Algebra.Lie.OfAssociative
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RingHom.Surjective
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.ZariskisMainTheorem
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Integrality over `R` after subtracting a polynomial

Let `R` be a ring, let `φ : R[x] → S` be a ring map and let `t ∈ S`. If `t` is integral over
`R[x]` and `t · φ p` lies in the image of `φ` for some monic `p ∈ R[x]`, then there is a
`q ∈ R[x]` such that `t - φ q` is integral over `R`, integrality over `R` being integrality with
respect to `φ.comp Polynomial.C`.

## Main results

* `Stacks.RingTheory.IntegralSubPolynomial.solution`: the statement above, for a ring map
  `φ : R[X] →+* S`.

## References

* [Stacks Project, Tag 00PT](https://stacks.math.columbia.edu/tag/00PT)
-/

@[expose] public section

namespace Stacks.RingTheory.IntegralSubPolynomial

open Polynomial

/-- Reinterpret a ring map `φ : A →+* S` out of an `R`-algebra `A` as an `R`-algebra
homomorphism, for the `R`-algebra structure on `S` transported along `φ`, whose structure map is
`φ.comp (algebraMap R A)`. -/
private def toAlgHom (R : Type*) {A S : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [CommSemiring S] (φ : A →+* S) :
    letI := (φ.comp (algebraMap R A)).toAlgebra
    A →ₐ[R] S :=
  letI := (φ.comp (algebraMap R A)).toAlgebra
  { φ with commutes' := fun _ ↦ rfl }

/-- Let `R` be a ring, let `φ : R[x] → S` be a ring map and let `t ∈ S`. If `t` is integral over
`R[x]` and `φ p * t` lies in the image of `φ` for some monic `p ∈ R[x]`, then there is a `q ∈ R[x]`
such that `t - φ q` is integral over `R`, integrality over `R` being integrality with respect to
`φ.comp Polynomial.C`. -/
public theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (φ : R[X] →+* S) (t : S) (p : R[X])
    (ht : φ.IsIntegralElem t) (hpm : p.Monic) (hp : φ p * t ∈ φ.range) :
    ∃ q : R[X], (φ.comp (C : R →+* R[X])).IsIntegralElem (t - φ q) := by
  let _ : Algebra R S := (φ.comp (C : R →+* R[X])).toAlgebra
  exact exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range (toAlgHom R φ) t p ht hpm hp

end Stacks.RingTheory.IntegralSubPolynomial

end

/-!
# Integrality over `R` after subtracting a polynomial

Let `R` be a ring, let `φ : R[x] → S` be a ring map and let `t ∈ S`. If `t` is integral over
`R[x]` and `t · φ p` lies in the image of `φ` for some monic `p ∈ R[x]`, then there is a
`q ∈ R[x]` with `t - φ q` integral over `R`.

## Main results

* `RingHom.exists_isIntegralElem_sub_of_isIntegralElem_of_mul_mem_range`: the statement above.

## References

* [Stacks Project, Tag 00PT](https://stacks.math.columbia.edu/tag/00PT)
-/

@[expose] public section

open Polynomial

/-- Let `R` be a ring, let `φ : R[x] → S` be a ring map and let `t ∈ S`. If `t` is integral over
`R[x]` and `φ p * t` lies in the image of `φ` for some monic `p ∈ R[x]`, then there is a `q ∈ R[x]`
such that `t - φ q` is integral over `R`, integrality over `R` being integrality with respect to
`φ.comp Polynomial.C`. -/
public alias RingHom.exists_isIntegralElem_sub_of_isIntegralElem_of_mul_mem_range :=
    Stacks.RingTheory.IntegralSubPolynomial.solution

end

/-!
# Leading coefficients modulo the conductor of a finite map from a polynomial ring

Let `R` be a ring, let `φ : R[x] → S` be a finite ring map whose subring `A = φ(R)` of images of
the constants is integrally closed in `S`, and let `J = {g ∈ S | g S ⊆ Im φ}` be the conductor
ideal of `φ`, that is, the largest ideal of `S` contained in the image of `φ`, spelled as the
conductor of `φ x` over `A`. If `u ∈ S` and `p ∈ R[x]` satisfy `φ p * u ∈ J`, then
`φ a ^ m * u ∈ J` for some `m ≥ 0`, where `a` is the leading coefficient of `p`.

## Main results

* `Stacks.RingTheory.ConductorLeadingCoeff.solution`: the statement above, for a ring map
  `φ : R[X] →+* S`.

## References

* [Stacks Project, Tag 00PX](https://stacks.math.columbia.edu/tag/00PX)
-/

@[expose] public section

namespace Stacks.RingTheory.ConductorLeadingCoeff

open Polynomial

/-- Reinterpret a ring map `φ : A →+* S` out of an `R`-algebra `A` as an `R`-algebra
homomorphism, for the `R`-algebra structure on `S` transported along `φ`, whose structure map is
`φ.comp (algebraMap R A)`. -/
private def toAlgHom (R : Type*) {A S : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [CommSemiring S] (φ : A →+* S) :
    letI := (φ.comp (algebraMap R A)).toAlgebra
    A →ₐ[R] S :=
  letI := (φ.comp (algebraMap R A)).toAlgebra
  { φ with commutes' := fun _ ↦ rfl }

/-- If the image of a base ring `A` in `S` is exactly the image `φ(R)` of the constants under a
ring map `φ : R[x] → S`, then the `A`-subalgebra of `S` generated by `φ x` is the image of `φ`:
every `A`-polynomial expression in `φ x` is of the form `φ q`, and conversely. -/
private lemma coe_adjoin_singleton_map_X_eq_range {R S A : Type*} [CommSemiring R] [CommSemiring A]
    [Semiring S] [Algebra A S] (φ : R[X] →+* S)
    (h : Set.range (algebraMap A S) = Set.range (φ.comp (C : R →+* R[X]))) :
    (Algebra.adjoin A {φ X} : Set S) = Set.range φ := by
  have hconst : ∀ a : A, algebraMap A S a ∈ φ.rangeS := fun a ↦ by
    obtain ⟨r, hr⟩ := h.le (Set.mem_range_self a); exact ⟨C r, hr⟩
  refine Set.Subset.antisymm
    (Algebra.adjoin_le (S := { φ.rangeS with algebraMap_mem' := hconst })
      (Set.singleton_subset_iff.mpr ⟨X, rfl⟩)) ?_
  rintro z ⟨q, rfl⟩
  rw [SetLike.mem_coe]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using add_mem hp hq
  | monomial n a =>
      obtain ⟨b, hb⟩ := h.ge (Set.mem_range_self a)
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow,
        show φ (C a) = algebraMap A S b from hb.symm]
      exact mul_mem (Subalgebra.algebraMap_mem _ _)
        (pow_mem (Algebra.self_mem_adjoin_singleton A (φ X)) n)

/-- The conductor of `x : S` depends on its base ring only through the subset of `S` that the base
generates together with `x`: two bases with the same `Algebra.adjoin _ {x}` have the same
conductor at `x`. -/
private lemma conductor_eq_of_coe_adjoin_eq {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A S] [Algebra B S] {x : S}
    (h : (Algebra.adjoin A {x} : Set S) = (Algebra.adjoin B {x} : Set S)) :
    conductor A x = conductor B x :=
  Ideal.ext fun y ↦ by
    simp only [mem_conductor_iff]
    exact forall_congr' fun b ↦ Set.ext_iff.mp h (y * b)

/-- If the image of `R` in `S` is integrally closed in `S`, then every element of `S` integral over
`R` already lies in that image: the integral closure of `R` in `S` is `⊥`. -/
private lemma integralClosure_eq_bot_of_isIntegrallyClosedIn_range {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (h : IsIntegrallyClosedIn (algebraMap R S).range S) :
    integralClosure R S = ⊥ := by
  have hle := (Subring.integralClosure_le_iff (T := (algebraMap R S).range)).mpr
    fun r ↦ RingHom.mem_range.mpr ⟨r, rfl⟩
  exact eq_bot_iff.mpr fun x hx ↦ Algebra.mem_bot.mpr (hle hx)

/-- Let `R` be a ring, let `φ : R[x] → S` be a finite ring map whose subring `φ(R)` of images of
the constants is integrally closed in `S`, and let `J` be the conductor ideal
`{g ∈ S | g * S ⊆ Im φ}` of `φ`, spelled as the conductor of `φ x` over `φ(R)`. If `u ∈ S` and
`p ∈ R[x]` satisfy `φ p * u ∈ J`, then `φ a ^ m * u ∈ J` for some `m ≥ 0`, where `a` is the leading
coefficient of `p`. -/
public theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (φ : R[X] →+* S) (u : S) (p : R[X])
    (hRS : IsIntegrallyClosedIn (φ.comp C).range S) (hφ : φ.Finite)
    (hu : φ p * u ∈ conductor (φ.comp C).range (φ X)) :
    ∃ m : ℕ, (φ.comp C) p.leadingCoeff ^ m * u ∈ conductor (φ.comp C).range (φ X) := by
  let _ : Algebra R S := (φ.comp (C : R →+* R[X])).toAlgebra
  have hcond : conductor R (φ X) = conductor (φ.comp C).range (φ X) :=
    conductor_eq_of_coe_adjoin_eq <| by
      rw [coe_adjoin_singleton_map_X_eq_range φ rfl,
        coe_adjoin_singleton_map_X_eq_range φ
          (by rw [Algebra.coe_algebraMap_ofSubsemiring, Subtype.range_val, RingHom.coe_range])]
  obtain ⟨m, hm⟩ := exists_leadingCoeff_pow_smul_mem_conductor (toAlgHom R φ) u p
    (integralClosure_eq_bot_of_isIntegrallyClosedIn_range hRS) hφ (hcond ▸ hu)
  rw [Algebra.smul_def, map_pow] at hm
  exact ⟨m, hcond ▸ hm⟩

end Stacks.RingTheory.ConductorLeadingCoeff

end

/-!
# Leading coefficients modulo the conductor ideal of a finite map from a polynomial ring

Let `R` be a ring, let `φ : R[x] → S` be a finite ring map whose subring `φ(R)` of images of the
constants is integrally closed in `S`, and let `J = {g ∈ S | g * S ⊆ im φ}` be the conductor ideal
of `φ`, that is, the largest ideal of `S` contained in the image of `φ`. If `u ∈ S` and
`p = a₀ + a₁x + ⋯ + a_k x ^ k` satisfy `φ p * u ∈ J`, then `φ a_k ^ m * u ∈ J` for some `m ≥ 0`.

## Main results

* `RingHom.exists_leadingCoeff_pow_mul_mem_conductor`: the statement above.

## References

* [Stacks Project, Tag 00PX](https://stacks.math.columbia.edu/tag/00PX)
-/

@[expose] public section

open Polynomial

/-- Let `R` be a ring, let `φ : R[x] → S` be a finite ring map whose subring `φ(R)` of images of
the constants is integrally closed in `S`, and let `J` be the conductor ideal
`{g ∈ S | g * S ⊆ im φ}` of `φ`, spelled as the conductor of `φ x` over `φ(R)`. If `u ∈ S` and
`p ∈ R[x]` satisfy `φ p * u ∈ J`, then `φ a ^ m * u ∈ J` for some `m ≥ 0`, where `a` is the leading
coefficient of `p`. -/
public alias RingHom.exists_leadingCoeff_pow_mul_mem_conductor :=
    Stacks.RingTheory.ConductorLeadingCoeff.solution

end

/-!
# All coefficients modulo the radical of the conductor of a finite map from a polynomial ring

Let `R` be a ring, let `φ : R[x] → S` be a finite ring map whose subring `A = φ(R)` of images of
the constants is integrally closed in `S`, and let `J = {g ∈ S | g S ⊆ Im φ}` be the conductor
ideal of `φ`, spelled as the conductor of `φ x` over `A`. If `u ∈ S` and
`p = a₀ + a₁x + ⋯ + a_k x ^ k` satisfy `φ p * u ∈ √J`, then `φ a_i * u ∈ √J` for every `i`.

## Main results

* `Stacks.RingTheory.ConductorRadicalCoeffs.solution`: the statement above, for a ring map
  `φ : R[X] →+* S`.

## References

* [Stacks Project, Tag 00PY](https://stacks.math.columbia.edu/tag/00PY)
-/

@[expose] public section

namespace Stacks.RingTheory.ConductorRadicalCoeffs

open Polynomial

open Stacks.RingTheory.ConductorLeadingCoeff

/-- Let `R` be a ring, let `φ : R[x] → S` be a finite ring map whose subring `φ(R)` of images of
the constants is integrally closed in `S`, and let `J` be the conductor ideal
`{g ∈ S | g * S ⊆ Im φ}` of `φ`, spelled as the conductor of `φ x` over `φ(R)`. If `u ∈ S` and
`p ∈ R[x]` satisfy `φ p * u ∈ √J`, then `φ a * u ∈ √J` for every coefficient `a` of `p`. -/
public theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (φ : R[X] →+* S) (u : S) (p : R[X])
    (hRS : IsIntegrallyClosedIn (φ.comp C).range S) (hφ : φ.Finite)
    (hu : φ p * u ∈ (conductor (φ.comp C).range (φ X)).radical) (i : ℕ) :
    (φ.comp C) (p.coeff i) * u ∈ (conductor (φ.comp C).range (φ X)).radical := by
  let _ : Algebra R S := (φ.comp (C : R →+* R[X])).toAlgebra
  have hcond : conductor R (φ X) = conductor (φ.comp C).range (φ X) :=
    conductor_eq_of_coe_adjoin_eq <| by
      rw [coe_adjoin_singleton_map_X_eq_range φ rfl,
        coe_adjoin_singleton_map_X_eq_range φ
          (by rw [Algebra.coe_algebraMap_ofSubsemiring, Subtype.range_val, RingHom.coe_range])]
  have hm := exists_leadingCoeff_pow_smul_mem_radical_conductor (toAlgHom R φ) u p
    (integralClosure_eq_bot_of_isIntegrallyClosedIn_range hRS) hφ (hcond ▸ hu) i
  simpa only [Algebra.smul_def] using hcond ▸ hm

end Stacks.RingTheory.ConductorRadicalCoeffs

end

/-!
# All coefficients modulo the radical of the conductor ideal of a finite map from a polynomial ring

Let `R` be a ring, let `φ : R[x] → S` be a finite ring map whose subring `φ(R)` of images of the
constants is integrally closed in `S`, and let `J = {g ∈ S | g * S ⊆ im φ}` be the conductor ideal
of `φ`. If `u ∈ S` and `p ∈ R[x]` satisfy `φ p * u ∈ √J`, then `φ a * u ∈ √J` for every coefficient
`a` of `p`.

## Main results

* `RingHom.coeff_mul_mem_radical_conductor`: the statement above.

## References

* [Stacks Project, Tag 00PY](https://stacks.math.columbia.edu/tag/00PY)
-/

@[expose] public section

open Polynomial

/-- Let `R` be a ring, let `φ : R[x] → S` be a finite ring map whose subring `φ(R)` of images of
the constants is integrally closed in `S`, and let `J` be the conductor ideal
`{g ∈ S | g * S ⊆ Im φ}` of `φ`, spelled as the conductor of `φ x` over `φ(R)`. If `u ∈ S` and
`p ∈ R[x]` satisfy `φ p * u ∈ √J`, then `φ a * u ∈ √J` for every coefficient `a` of `p`. -/
public alias RingHom.coeff_mul_mem_radical_conductor :=
    Stacks.RingTheory.ConductorRadicalCoeffs.solution

end

end

/-!
# Zariski's Main Theorem: the integral closure of a quasi-finite algebra

Let `R → S` be a finite type ring map with `S` quasi-finite over `R`, and let `S' ⊆ S` be the
integral closure of `R` in `S`. Then:

1. the map `Spec(S) → Spec(S')` induced by the inclusion `S' ↪ S` is a homeomorphism of `Spec(S)`
   onto an open subset of `Spec(S')`;
2. for every `g ∈ S'` such that `D(g) ⊆ Spec(S')` is contained in the image of the map in (1), the
   natural map `S'_g → S_g` is an isomorphism;
3. there is an `R`-subalgebra `S'' ⊆ S'` that is finite as an `R`-module such that (1) and (2) hold
   with `S'` replaced by `S''`.

## Main results

* `isOpenEmbedding_comap_of_forall_exists_awayMap_bijective`: if every point of `Spec B` lies in a
  basic open `D(f g)` with `A_g → B_g` bijective, then `comap f` is an open embedding.
* `awayMap_bijective_of_basicOpen_subset_range`: for such an injective `f`, `A_g → B_g` is
  bijective whenever `D(g)` lies in the image of `comap f`.
* `exists_awayMap_integralClosure_bijective`: for every prime `q` of `S` there is `g ∈ S'` with
  `g ∉ q` and `S'_g → S_g` bijective.
* `quasiFinite_comap_integralClosure_isOpenEmbedding`: statement (1).
* `quasiFinite_awayMap_integralClosure_bijective`: statement (2).
* `quasiFinite_exists_finite_subalgebra`: statement (3).

## References

* [Stacks Project, Tag 00QB](https://stacks.math.columbia.edu/tag/00QB)
-/

@[expose] public section

open Topology

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If the away-localization map of a ring hom `f : A →+* B` at `g : A` is bijective, then the
restriction of `comap f` to the basic open `D(f g) ⊆ Spec B` is an open topological embedding
(onto `D(g) ⊆ Spec A`). -/
private theorem restrict_comap_isOpenEmbedding {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (g : A)
    (hbij : Function.Bijective (Localization.awayMap f g)) :
    IsOpenEmbedding
      ((PrimeSpectrum.basicOpen (f g) : Set (PrimeSpectrum B)).domRestrict
        (PrimeSpectrum.comap f)) := by
  set A' := Localization.Away g
  set B' := Localization.Away (f g)
  set U : Set (PrimeSpectrum B) := (PrimeSpectrum.basicOpen (f g) : Set (PrimeSpectrum B))
  set e := PrimeSpectrum.comap (algebraMap B B') with he
  have he_emb : IsOpenEmbedding e := PrimeSpectrum.localization_away_isOpenEmbedding B' (f g)
  have he_range : Set.range e = U := PrimeSpectrum.localization_away_comap_range B' (f g)
  set i := PrimeSpectrum.comap (algebraMap A A') with hi
  set h := PrimeSpectrum.comap (Localization.awayMap f g) with hh
  have hi_emb : IsOpenEmbedding i := PrimeSpectrum.localization_away_isOpenEmbedding A' g
  let eqv : A' ≃+* B' := RingEquiv.ofBijective (Localization.awayMap f g) hbij
  have hh_emb : IsOpenEmbedding h := (PrimeSpectrum.homeomorphOfRingEquiv eqv).symm.isOpenEmbedding
  have hsq : (PrimeSpectrum.comap f) ∘ e = i ∘ h := by
    rw [he, hi, hh, ← PrimeSpectrum.comap_comp, ← PrimeSpectrum.comap_comp]
    congr 1
    unfold Localization.awayMap IsLocalization.Away.map
    rw [IsLocalization.map_comp]
  let hom : PrimeSpectrum B' ≃ₜ ↥U :=
    (he_emb.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr he_range)
  have heq : U.domRestrict (PrimeSpectrum.comap f) = (i ∘ h) ∘ hom.symm := by
    ext x : 1
    obtain ⟨b, rfl⟩ := hom.surjective x
    rw [Function.comp_apply, hom.symm_apply_apply]
    exact congrFun hsq b
  rw [heq]
  exact (hi_emb.comp hh_emb).comp hom.symm.isOpenEmbedding

/-- If every point of `Spec B` lies in a basic open `D(f g)` with `A_g → B_g` bijective, then
`comap f : Spec B → Spec A` is an open embedding. -/
theorem isOpenEmbedding_comap_of_forall_exists_awayMap_bijective {A B : Type*} [CommRing A]
    [CommRing B] (f : A →+* B)
    (H : ∀ q : PrimeSpectrum B, ∃ g : A, f g ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap f g)) :
    IsOpenEmbedding (PrimeSpectrum.comap f) := by
  refine IsLocalHomeomorph.isOpenEmbedding_of_injective ?_ fun q₁ q₂ heq ↦ ?_
  · rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
    intro q
    obtain ⟨g, hg, hgb⟩ := H q
    exact ⟨_, PrimeSpectrum.isOpen_basicOpen.mem_nhds hg, restrict_comap_isOpenEmbedding f g hgb⟩
  · obtain ⟨g, hg, hgb⟩ := H q₁
    have hg₂ : f g ∉ q₂.asIdeal := fun hc ↦
      hg (show g ∈ (PrimeSpectrum.comap f q₁).asIdeal by rw [heq]; exact hc)
    exact Subtype.ext_iff.mp
      ((restrict_comap_isOpenEmbedding f g hgb).injective (a₁ := ⟨q₁, hg⟩) (a₂ := ⟨q₂, hg₂⟩) heq)

/-- If `A_g → B_g` is surjective, then for every `x : B` there are `y : A` and `K M : ℕ` with
`f g ^ K * x = f g ^ M * f y`. -/
theorem exists_pow_mul_eq_of_awayMap_surjective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (g : A) (hsurj : Function.Surjective (Localization.awayMap f g)) (x : B) :
    ∃ (y : A) (K M : ℕ), f g ^ K * x = f g ^ M * f y := by
  obtain ⟨z, hz⟩ := hsurj (algebraMap B (Localization.Away (f g)) x)
  obtain ⟨k, y, hky⟩ := IsLocalization.Away.surj g z
  have hcompat : ∀ w : A, Localization.awayMap f g (algebraMap A (Localization.Away g) w) =
      algebraMap B (Localization.Away (f g)) (f w) := fun w ↦ by
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have happ := congrArg (Localization.awayMap f g) hky
  rw [map_mul, map_pow, hcompat, hcompat, hz, ← map_pow, ← map_mul] at happ
  obtain ⟨⟨_, j, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f g)) _).mp happ
  exact ⟨y, j + k, j, by rw [pow_add]; linear_combination hc⟩

/-- A linear map `l` induces a surjection on localizations at `T` as soon as every element of the
target is, up to a unit of `T`, in the image of `l`. -/
theorem LocalizedModule.map_surjective_of_forall_exists_smul_eq {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (T : Submonoid R)
    (l : M →ₗ[R] N) (h : ∀ b : N, ∃ (a : M) (t : T), (t : R) • b = l a) :
    Function.Surjective (LocalizedModule.map T l) := by
  intro y
  induction y using LocalizedModule.induction_on with
  | _ b s =>
    obtain ⟨a, t, ht⟩ := h b
    refine ⟨LocalizedModule.mk a (s * t), ?_⟩
    rw [LocalizedModule.map_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    have key : (s * t : T) • b = (s : T) • l a := by
      rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul, ← ht]; rfl
    simpa using key.symm

/-- Let `f : A →+* B` be injective and suppose every point of `Spec B` lies in a basic open
`D(f r)` with `A_r → B_r` bijective. If `D(g) ⊆ Spec A` lies in the image of `comap f`, then
`A_g → B_g` is bijective. -/
theorem awayMap_bijective_of_basicOpen_subset_range {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f)
    (H : ∀ q : PrimeSpectrum B, ∃ r : A, f r ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap f r))
    (g : A) (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
      Set.range (PrimeSpectrum.comap f)) :
    Function.Bijective (Localization.awayMap f g) := by
  set φ := Localization.awayMap f g with hφ
  let : Algebra (Localization.Away g) (Localization.Away (f g)) := φ.toAlgebra
  set A' := Localization.Away g
  set B' := Localization.Away (f g)
  set algA := algebraMap A A' with halgA
  have hcompat : ∀ w : A, φ (algA w) = algebraMap B B' (f w) := fun w ↦ by
    rw [hφ, halgA, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have hφ_inj : Function.Injective φ := by
    rw [hφ]
    unfold Localization.awayMap IsLocalization.Away.map
    exact IsLocalization.map_injective_of_injective _ _ _ hf
  show Function.Bijective (Algebra.linearMap A' B')
  apply bijective_of_localized_maximal
  intro J hJ
  refine ⟨LocalizedModule.map_injective J.primeCompl _ hφ_inj,
    LocalizedModule.map_surjective_of_forall_exists_smul_eq _ _ fun b ↦ ?_⟩
  have := hJ.isPrime
  have hgJ : algA g ∉ J := fun hc ↦
    hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ hc (IsLocalization.Away.algebraMap_isUnit g))
  obtain ⟨Q, hQ⟩ := hg (show (⟨J.comap algA, Ideal.IsPrime.comap algA⟩ : PrimeSpectrum A) ∈
    PrimeSpectrum.basicOpen g from hgJ)
  obtain ⟨g', hg'Q, hg'bij⟩ := H Q
  have hg'J : algA g' ∉ J := fun hc ↦
    hg'Q (show g' ∈ (PrimeSpectrum.comap f Q).asIdeal by rw [hQ]; exact hc)
  obtain ⟨n, x, hbeq⟩ := IsLocalization.Away.surj (f g) b
  obtain ⟨y, K, M, hy⟩ := exists_pow_mul_eq_of_awayMap_surjective f g' hg'bij.surjective x
  refine ⟨algA g' ^ M * algA y,
    ⟨algA g' ^ K * algA g ^ n, J.primeCompl.mul_mem (pow_mem hg'J K) (pow_mem hgJ n)⟩, ?_⟩
  show φ (algA g' ^ K * algA g ^ n) * b = φ (algA g' ^ M * algA y)
  have hy' := congrArg (algebraMap B B') hy
  simp only [map_mul, map_pow, hcompat] at hy' ⊢
  linear_combination algebraMap B B' (f g') ^ K * hbeq + hy'

/-- For every prime `q` of `S` there is `g` in the integral closure `S'` with `g ∉ q` and
`S'_g → S_g` bijective. -/
theorem exists_awayMap_integralClosure_bijective [Algebra.FiniteType R S]
    [Algebra.QuasiFinite R S] (q : PrimeSpectrum S) :
    ∃ g : integralClosure R S, (g : S) ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom g) :=
  have : Algebra.QuasiFiniteAt R q.asIdeal :=
    Algebra.QuasiFinite.instLocalization q.asIdeal.primeCompl
  Algebra.ZariskisMainProperty.of_finiteType (R := R) q.asIdeal

/-- The map on spectra `Spec(S) → Spec(S')` induced by the inclusion `S' ↪ S` is an open
topological embedding: a homeomorphism of `Spec(S)` onto an open subset of `Spec(S')`. -/
@[stacks 00QB "(1)"]
theorem quasiFinite_comap_integralClosure_isOpenEmbedding
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] :
    IsOpenEmbedding (PrimeSpectrum.comap (integralClosure R S).val.toRingHom) :=
  isOpenEmbedding_comap_of_forall_exists_awayMap_bijective _
    exists_awayMap_integralClosure_bijective

/-- For every `g ∈ S'` such that the basic open `D(g) ⊆ Spec(S')` is contained in the image of
`Spec(S) → Spec(S')`, the natural ring homomorphism `S'_g → S_g` induced by `S' ↪ S` is
bijective. -/
@[stacks 00QB "(2)"]
theorem quasiFinite_awayMap_integralClosure_bijective
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S]
    (g : integralClosure R S)
    (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (integralClosure R S)))
      ⊆ Set.range (PrimeSpectrum.comap (integralClosure R S).val.toRingHom)) :
    Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom g) :=
  awayMap_bijective_of_basicOpen_subset_range _ Subtype.val_injective
    exists_awayMap_integralClosure_bijective g hg

/-- If `S''` contains `gi` and for every algebra generator `s` of `S` there are `y ∈ S''` and
`K M` with `gi^K s = gi^M y` in `S`, then the away map `S''_{gi} → S_{gi}` is surjective. -/
private theorem st2_surj_lemma (S'' : Subalgebra R S) (gi : S'')
    (gens : Finset S) (hgens : Algebra.adjoin R (gens : Set S) = ⊤)
    (hwit : ∀ s ∈ gens, ∃ (y : S'') (K M : ℕ),
        (gi : S) ^ K * s = (gi : S) ^ M * (y : S)) :
    Function.Surjective (Localization.awayMap S''.val.toRingHom gi) := by
  set Sgi := Localization.Away (S''.val.toRingHom gi)
  set φ := Localization.awayMap S''.val.toRingHom gi with hφ
  have hcompat : ∀ w : S'', φ (algebraMap S'' (Localization.Away gi) w)
      = algebraMap S Sgi (w : S) := fun w ↦ by
    rw [hφ, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]; rfl
  have mem : ∀ a ∈ S'', algebraMap S Sgi a ∈ φ.range := fun a ha ↦ ⟨_, hcompat ⟨a, ha⟩⟩
  set u := φ (IsLocalization.Away.invSelf (S := Localization.Away gi) gi)
  have hu : u * algebraMap S Sgi (gi : S) = 1 := by
    rw [mul_comm, ← hcompat, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hu_mem : u ∈ φ.range := ⟨_, rfl⟩
  have key : ∀ a : S, algebraMap S Sgi a ∈ φ.range := by
    intro a
    have ha : a ∈ Algebra.adjoin R (gens : Set S) := by rw [hgens]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem s hs =>
      obtain ⟨y, K, M, hy⟩ := hwit s hs
      have hy' := congrArg (algebraMap S Sgi) hy
      simp only [map_mul, map_pow] at hy'
      have huK : (u * algebraMap S Sgi gi) ^ K = 1 := by rw [hu, one_pow]
      have : algebraMap S Sgi s = u ^ K * (algebraMap S Sgi gi ^ M * algebraMap S Sgi y) := by
        linear_combination -algebraMap S Sgi s * huK + u ^ K * hy'
      rw [this]
      exact mul_mem (pow_mem hu_mem K) (mul_mem (pow_mem (mem _ gi.2) M) (mem _ y.2))
    | algebraMap r => exact mem _ (S''.algebraMap_mem r)
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  intro b
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj (S''.val.toRingHom gi) b
  change b * algebraMap S Sgi (gi : S) ^ n = _ at hna
  have hb : b = algebraMap S Sgi a * u ^ n := by
    rw [← hna, mul_assoc, ← mul_pow, mul_comm (algebraMap S Sgi (gi : S)), hu, one_pow, mul_one]
  exact hb ▸ mul_mem (key a) (pow_mem hu_mem n)

/-- There are finitely many `t ∈ S'` with `S'_t → S_t` bijective whose basic opens `D(t)` cover
`Spec S`. -/
theorem exists_finset_awayMap_integralClosure_bijective [Algebra.FiniteType R S]
    [Algebra.QuasiFinite R S] :
    ∃ T : Finset (integralClosure R S),
      (∀ t ∈ T, Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom t)) ∧
      ∀ q : PrimeSpectrum S, ∃ t ∈ T, (t : S) ∉ q.asIdeal := by
  classical
  choose G hGq hGbij using exists_awayMap_integralClosure_bijective (R := R) (S := S)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun q ↦ (PrimeSpectrum.basicOpen (G q : S) : Set (PrimeSpectrum S)))
    (fun _ ↦ PrimeSpectrum.isOpen_basicOpen) fun q _ ↦ Set.mem_iUnion.2 ⟨q, hGq q⟩
  refine ⟨t.image G, Finset.forall_mem_image.2 fun q _ ↦ hGbij q, fun q ↦ ?_⟩
  obtain ⟨p, hp, hq⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
  exact ⟨G p, Finset.mem_image_of_mem G hp, hq⟩

/-- Given finitely many `t ∈ S'` with `S'_t → S_t` bijective, there is a module-finite
`R`-subalgebra `S'' ⊆ S'` containing every `t` with `S''_t → S_t` still bijective. -/
theorem exists_finite_subalgebra_awayMap_bijective [Algebra.FiniteType R S]
    (T : Finset (integralClosure R S))
    (hT : ∀ t ∈ T,
      Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom t)) :
    ∃ S'' : Subalgebra R S, S'' ≤ integralClosure R S ∧ Module.Finite R S'' ∧
      ∀ t ∈ T, ∃ ht : (t : S) ∈ S'',
        Function.Bijective (Localization.awayMap S''.val.toRingHom ⟨t, ht⟩) := by
  classical
  obtain ⟨gens, hgens⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R S).FG)
  choose y K M hy using fun (t : T) (s : gens) ↦
    exists_pow_mul_eq_of_awayMap_surjective _ _ (hT t t.2).surjective (s : S)
  set gset : Set S := Set.range (fun t : T ↦ ((t : integralClosure R S) : S)) ∪
    Set.range (fun p : T × gens ↦ (y p.1 p.2 : S))
  have hint : gset ⊆ integralClosure R S := by
    rintro x (⟨t, rfl⟩ | ⟨p, rfl⟩) <;> exact SetLike.coe_mem _
  refine ⟨Algebra.adjoin R gset, Algebra.adjoin_le hint,
    Algebra.finite_adjoin_of_finite_of_isIntegral ((Set.finite_range _).union (Set.finite_range _))
      hint, fun t ht ↦ ⟨Algebra.subset_adjoin (Or.inl ⟨⟨t, ht⟩, rfl⟩), ?_, ?_⟩⟩
  · unfold Localization.awayMap IsLocalization.Away.map
    exact IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective
  · exact st2_surj_lemma _ _ gens hgens fun s hs ↦
      ⟨⟨y ⟨t, ht⟩ ⟨s, hs⟩, Algebra.subset_adjoin (Or.inr ⟨(⟨t, ht⟩, ⟨s, hs⟩), rfl⟩)⟩,
        K ⟨t, ht⟩ ⟨s, hs⟩, M ⟨t, ht⟩ ⟨s, hs⟩, hy ⟨t, ht⟩ ⟨s, hs⟩⟩

/-- There is an `R`-subalgebra `S''` of `S`, contained in the integral closure `S'` and finite as
an `R`-module, such that `Spec(S) → Spec(S'')` is an open topological embedding and
`S''_g → S_g` is bijective for every `g ∈ S''` whose basic open `D(g)` lies in the image of that
map. -/
@[stacks 00QB "(3)",
  ega "III 4.4.3" "affine case, X=X'",
  ega "IV 8.12.6" "affine case",
  ega "IV 18.12.13" "affine case",
  ega "III 4.4.6" "special case",
  ega "IV 8.12.9" "Affine case",
  sga "1 VIII 6.4" "affine case"]
theorem quasiFinite_exists_finite_subalgebra
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] :
    ∃ S'' : Subalgebra R S, S'' ≤ integralClosure R S ∧ Module.Finite R S'' ∧
      IsOpenEmbedding (PrimeSpectrum.comap S''.val.toRingHom) ∧
      ∀ g : S'', (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S'')) ⊆
          Set.range (PrimeSpectrum.comap S''.val.toRingHom) →
        Function.Bijective (Localization.awayMap S''.val.toRingHom g) := by
  obtain ⟨T, hTbij, hTcov⟩ := exists_finset_awayMap_integralClosure_bijective (R := R) (S := S)
  obtain ⟨S'', hle, hfin, hS''⟩ := exists_finite_subalgebra_awayMap_bijective T hTbij
  have H : ∀ q : PrimeSpectrum S, ∃ r : S'', S''.val.toRingHom r ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap S''.val.toRingHom r) := fun q ↦ by
    obtain ⟨t, htT, htq⟩ := hTcov q
    obtain ⟨ht, hbij⟩ := hS'' t htT
    exact ⟨⟨t, ht⟩, htq, hbij⟩
  exact ⟨S'', hle, hfin, isOpenEmbedding_comap_of_forall_exists_awayMap_bijective _ H,
    awayMap_bijective_of_basicOpen_subset_range _ Subtype.val_injective H⟩

end
