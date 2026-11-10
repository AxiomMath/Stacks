module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Transporting annihilated primes along ring isomorphisms

Let `C` be a local ring with an element `t` and `e : C ≃+* D` a ring isomorphism. Pulling an
ideal back along `e` transports the following two configurations from `(D, e t)` to `(C, t)`:

* a prime `𝔨` with `t ∉ 𝔨`, `t 𝔨 = 0` and `𝔪_C ⊆ √(𝔨 + (t))`;
* an ideal `𝔨` with `t 𝔨 = 0` and `C ⧸ 𝔨` regular local of dimension at least `d`.

## Main results

* `Stacks.AnnihilatedPrime.exists_prime_of_ringEquiv`: the first configuration transports along
  a ring isomorphism.
* `Stacks.AnnihilatedPrime.exists_regular_quotient_of_ringEquiv`: the second configuration
  transports along a ring isomorphism.
-/

@[expose] public section

open IsLocalRing

namespace Stacks.AnnihilatedPrime

variable {C D : Type*} [CommRing C] [CommRing D] [IsLocalRing C] [IsLocalRing D]

/-- If `e t` annihilates `𝔨`, then `t` annihilates the pullback of `𝔨` along `e`. -/
private theorem comap_annihilated {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (t : R)
    (𝔨 : Ideal S) (hann : ∀ k ∈ 𝔨, e t * k = 0) : ∀ k ∈ 𝔨.comap e, t * k = 0 :=
  fun k hk ↦ e.injective (by rw [map_mul, map_zero]; exact hann _ hk)

/-- Let `e : C ≃+* D` be a ring isomorphism of local rings and `t ∈ C`. If `D` has a prime `𝔨`
with `e t ∉ 𝔨`, `e t 𝔨 = 0` and `𝔪_D ⊆ √(𝔨 + (e t))`, then `C` has a prime `𝔨'` with `t ∉ 𝔨'`,
`t 𝔨' = 0` and `𝔪_C ⊆ √(𝔨' + (t))`. -/
theorem exists_prime_of_ringEquiv (e : C ≃+* D) (t : C) (𝔨 : Ideal D) [𝔨.IsPrime]
    (ht : e t ∉ 𝔨) (hann : ∀ k ∈ 𝔨, e t * k = 0)
    (hrad : maximalIdeal D ≤ (𝔨 ⊔ Ideal.span {e t}).radical) :
    ∃ 𝔨' : Ideal C, 𝔨'.IsPrime ∧ t ∉ 𝔨' ∧ (∀ k ∈ 𝔨', t * k = 0) ∧
      maximalIdeal C ≤ (𝔨' ⊔ Ideal.span {t}).radical := by
  refine ⟨𝔨.comap e, Ideal.comap_isPrime _ _, ht,
    comap_annihilated e t 𝔨 hann, fun x hx ↦ ?_⟩
  have hx' : e x ∈ maximalIdeal D := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu ↦ hx ((isUnit_map_iff e x).mp hu)
  obtain ⟨n, hn⟩ := hrad hx'
  refine ⟨n, ?_⟩
  have hle : (𝔨 ⊔ Ideal.span {e t}).comap (e : C →+* D) ≤ 𝔨.comap e ⊔ Ideal.span {t} := by
    intro y hy
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (show e y ∈ 𝔨 ⊔ Ideal.span {e t} from hy)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    refine Submodule.mem_sup.mpr ⟨y - e.symm c * t, ?_, e.symm c * t,
      Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t), by ring⟩
    change e (y - e.symm c * t) ∈ 𝔨
    rw [map_sub, map_mul, e.apply_symm_apply, ← hab]
    simpa using ha
  exact hle (by simpa [Ideal.mem_comap] using hn)

omit [IsLocalRing C] [IsLocalRing D] in
/-- Let `e : C ≃+* D` be a ring isomorphism and `t ∈ C`. If `D` has an ideal `𝔨` with
`e t 𝔨 = 0` and `D ⧸ 𝔨` regular local of dimension at least `d`, then `C` has an ideal `𝔨'` with
`t 𝔨' = 0` and `C ⧸ 𝔨'` regular local of dimension at least `d`. -/
theorem exists_regular_quotient_of_ringEquiv (e : C ≃+* D) (t : C) (𝔨 : Ideal D) (d : WithBot ℕ∞)
    (hann : ∀ k ∈ 𝔨, e t * k = 0) (hreg : IsRegularLocalRing (D ⧸ 𝔨))
    (hdim : d ≤ ringKrullDim (D ⧸ 𝔨)) :
    ∃ 𝔨' : Ideal C, (∀ k ∈ 𝔨', t * k = 0) ∧ IsRegularLocalRing (C ⧸ 𝔨') ∧
      d ≤ ringKrullDim (C ⧸ 𝔨') := by
  let e' : C ⧸ 𝔨.comap (e : C →+* D) ≃+* D ⧸ 𝔨 :=
    Ideal.quotientEquiv _ _ e (Ideal.map_comap_of_surjective _ e.surjective 𝔨).symm
  exact ⟨𝔨.comap (e : C →+* D),
    comap_annihilated e t 𝔨 hann,
    IsRegularLocalRing.of_ringEquiv e'.symm, hdim.trans_eq (ringKrullDim_eq_of_ringEquiv e').symm⟩

end Stacks.AnnihilatedPrime

end
