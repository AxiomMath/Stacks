module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# A Frobenius splitting extends to the fraction field and preserves localizations

Let `A` be a domain with fraction field `K` and `θ : A → A` an additive map with
`θ(aᵖ z) = a θ(z)`. Then `θ` extends to an additive map `θ_K : K → K` with the same property,
given by `θ_K(z / s) = θ(z s^{p-1}) / s`. The formula shows that `θ_K` maps every localization
`S⁻¹A ⊆ K` into itself; in particular it preserves the local rings `A_𝔭`.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_frobeniusSplitting_fractionRing`: the extension `θ_K`,
  with its value on fractions.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public section

namespace Stacks.ResolutionOfSurfaces

variable {p : ℕ} {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- **Extension of a `p⁻¹`-linear map to the fraction field.** An additive `θ : A → A` with
`θ(aᵖ z) = a θ(z)` extends to an additive `θ_K : K → K` with `θ_K(aᵖ x) = a θ_K(x)` and
`θ_K(z / s) = θ(z s^{p-1}) / s` for `s ≠ 0`. -/
theorem exists_frobeniusSplitting_fractionRing (hp : 1 ≤ p) (θ : A →+ A)
    (hθ : ∀ a z, θ (a ^ p * z) = a * θ z) :
    ∃ θK : K →+ K, (∀ a x, θK (a ^ p * x) = a * θK x) ∧
      ∀ z s : A, s ≠ 0 →
        θK (algebraMap A K z / algebraMap A K s) =
          algebraMap A K (θ (z * s ^ (p - 1))) / algebraMap A K s := by
  classical
  have hinj := IsFractionRing.injective A K
  have hs0 : ∀ s : A, s ≠ 0 → algebraMap A K s ≠ 0 := fun s hs h =>
    hs (hinj (by rw [h, map_zero]))
  have hpow : ∀ s : A, s ^ (p - 1) * s = s ^ p := fun s => by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have key : ∀ z s z' s' : A, s ≠ 0 → s' ≠ 0 → z * s' = z' * s →
      s' * θ (z * s ^ (p - 1)) = s * θ (z' * s' ^ (p - 1)) := by
    intro z s z' s' _ _ h
    rw [← hθ, ← hθ]
    congr 1
    calc s' ^ p * (z * s ^ (p - 1)) = (z * s') * (s' ^ (p - 1) * s ^ (p - 1)) := by
          rw [← hpow s']; ring
      _ = (z' * s) * (s' ^ (p - 1) * s ^ (p - 1)) := by rw [h]
      _ = s ^ p * (z' * s' ^ (p - 1)) := by rw [← hpow s]; ring
  have hrep : ∀ x : K, ∃ zs : A × A, zs.2 ≠ 0 ∧
      x = algebraMap A K zs.1 / algebraMap A K zs.2 := fun x => by
    obtain ⟨z, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    exact ⟨(z, s), nonZeroDivisors.ne_zero hs, rfl⟩
  choose rep hrep0 hrepx using hrep
  let F : K → K := fun x =>
    algebraMap A K (θ ((rep x).1 * (rep x).2 ^ (p - 1))) / algebraMap A K (rep x).2
  have hF : ∀ z s : A, s ≠ 0 → F (algebraMap A K z / algebraMap A K s) =
      algebraMap A K (θ (z * s ^ (p - 1))) / algebraMap A K s := by
    intro z s hs
    set x := algebraMap A K z / algebraMap A K s with hxdef
    have hs' := hrep0 x
    have h1 : algebraMap A K z / algebraMap A K s =
        algebraMap A K (rep x).1 / algebraMap A K (rep x).2 := hrepx x
    rw [div_eq_div_iff (hs0 _ hs) (hs0 _ hs')] at h1
    have heq : (rep x).1 * s = z * (rep x).2 :=
      hinj (by rw [map_mul, map_mul]; exact h1.symm)
    have hk := key _ _ _ _ hs' hs heq
    show algebraMap A K (θ ((rep x).1 * (rep x).2 ^ (p - 1))) / algebraMap A K (rep x).2 = _
    rw [div_eq_div_iff (hs0 _ hs') (hs0 _ hs), ← map_mul, ← map_mul]
    congr 1
    rw [mul_comm, hk, mul_comm]
  have hmul : ∀ z s t : A, algebraMap A K t ≠ 0 →
      algebraMap A K z / algebraMap A K s = algebraMap A K (z * t) / algebraMap A K (s * t) :=
    fun z s t ht => by rw [map_mul, map_mul, mul_div_mul_right _ _ ht]
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    rw [hrepx x, hrepx y]
    set z := (rep x).1; set s := (rep x).2; set z' := (rep y).1; set s' := (rep y).2
    have hs := hrep0 x; have hs' := hrep0 y
    have hss : s * s' ≠ 0 := mul_ne_zero hs hs'
    have e1 := hmul z s s' (hs0 _ hs')
    have e2 : algebraMap A K z' / algebraMap A K s' =
        algebraMap A K (z' * s) / algebraMap A K (s * s') := by
      rw [hmul z' s' s (hs0 _ hs), mul_comm s' s]
    rw [e1, e2, ← add_div, ← map_add, hF _ _ hss, hF _ _ hss, hF _ _ hss, ← add_div, ← map_add,
      add_mul, map_add]
  have hzero : F 0 = 0 := by simpa using hF 0 1 one_ne_zero
  refine ⟨⟨⟨F, hzero⟩, hadd⟩, fun a x => ?_, hF⟩
  show F (a ^ p * x) = a * F x
  obtain ⟨z, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) a
  have hs1 := nonZeroDivisors.ne_zero hs
  rw [hrepx x]
  set w := (rep x).1; set t := (rep x).2
  have ht := hrep0 x
  have hst : s ^ p * t ≠ 0 := mul_ne_zero (pow_ne_zero _ hs1) ht
  have e : (algebraMap A K z / algebraMap A K s) ^ p * (algebraMap A K w / algebraMap A K t) =
      algebraMap A K (z ^ p * w) / algebraMap A K (s ^ p * t) := by
    simp only [map_mul, map_pow, div_pow]; rw [div_mul_div_comm]
  rw [e, hF _ _ hst, hF _ _ ht]
  have e2 : z ^ p * w * (s ^ p * t) ^ (p - 1) = (z * s ^ (p - 1)) ^ p * (w * t ^ (p - 1)) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm p (p - 1)]; ring
  have hsK := hs0 _ hs1
  have htK := hs0 _ ht
  rw [e2, hθ, ← hpow s]
  simp only [map_mul, map_pow]
  field_simp
  rw [mul_div_assoc, show algebraMap A K (rep x).2 / algebraMap A K t = 1 from div_self htK,
    mul_one]

end Stacks.ResolutionOfSurfaces

end
