module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import StacksFrontier.RingTheory.AdicCompletion.Comparison

/-!
# Maps of adic completions induced by a homomorphism shifting powers

Let `R` and `S` be algebras over a commutative ring `A`, let `I ⊆ R` and `J ⊆ S` be ideals,
and let `f : R →ₐ[A] S` be a homomorphism with `(I ^ a) · S ⊆ J` for some `a`.  Then
`I ^ (a * n) · S ⊆ J ^ n` for every `n`, so the maps `R̂_I → S / J ^ n` obtained by reducing
modulo `I ^ (a * n)` and applying `f` form a compatible family and assemble into an
`A`-algebra map `R̂_I → Ŝ_J`.

## Main definitions

* `AdicCompletion.componentOfMapPowLe` — the level-`n` reduction `R̂_I → S / J ^ n`.
* `AdicCompletion.algHomOfMapPowLe` — the induced map `R̂_I → Ŝ_J`.

## Main results

* `AdicCompletion.evalₐ_algHomOfMapPowLe` — the defining identity on level-`n` reductions.
* `AdicCompletion.algHomOfMapPowLe_of` — compatibility with the canonical maps from `R`
  and `S`.
* `AdicCompletion.algHomOfMapPowLe_comp` — functoriality in `f`.
* `AdicCompletion.exists_sub_mem_map_pow` — every element of `R̂_I` agrees modulo `I ^ m` with
  an element of `R`.
* `AdicCompletion.algHom_ext_of_of` — a map of adic completions is determined by its values on
  the uncompleted ring, as soon as the underlying map of rings shifts powers as above.

## References

* [Stacks Project, Tag 0AL5](https://stacks.math.columbia.edu/tag/0AL5)
-/

@[expose] public noncomputable section

namespace AdicCompletion

universe u v w

variable (A : Type u) [CommRing A] {R : Type v} [CommRing R] [Algebra A R]
  {S : Type w} [CommRing S] [Algebra A S]

section

variable {I : Ideal R} {J : Ideal S} {a : ℕ}

/-- If `f` carries `I ^ a` into `J`, it carries `I ^ (a * n)` into `J ^ n`. -/
public theorem map_pow_mul_le_pow (f : R →ₐ[A] S) (ha : (I ^ a).map f ≤ J) (n : ℕ) :
    (I ^ (a * n)).map f ≤ J ^ n := by
  rw [pow_mul, Ideal.map_pow]
  exact Ideal.pow_right_mono ha n

/-- If `f` carries `I ^ a` into `J`, then `I ^ (a * n)` is contained in the preimage of
`J ^ n`. -/
public theorem pow_mul_le_comap_pow (f : R →ₐ[A] S) (ha : (I ^ a).map f ≤ J) (n : ℕ) :
    I ^ (a * n) ≤ (J ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (map_pow_mul_le_pow A f ha n)

/-- The level-`n` component of the map of adic completions induced by `f`: reduce modulo
`I ^ (a * n)` and apply `f`. -/
public def componentOfMapPowLe (f : R →ₐ[A] S) (ha : (I ^ a).map f ≤ J) (n : ℕ) :
    AdicCompletion I R →ₐ[A] S ⧸ J ^ n :=
  (Ideal.quotientMapₐ (R₁ := A) (J ^ n) f (pow_mul_le_comap_pow A f ha n)).comp
    ((evalₐ I (a * n)).restrictScalars A)

/-- `componentOfMapPowLe A f ha n x` is the image under `f` of the reduction of `x` modulo
`I ^ (a * n)`. -/
public theorem componentOfMapPowLe_apply (f : R →ₐ[A] S) (ha : (I ^ a).map f ≤ J) (n : ℕ)
    (x : AdicCompletion I R) :
    componentOfMapPowLe A f ha n x =
      Ideal.quotientMapₐ (R₁ := A) (J ^ n) f (pow_mul_le_comap_pow A f ha n)
        (evalₐ I (a * n) x) :=
  rfl

/-- The level-`n` components are compatible with the reductions of the `J`-adic tower. -/
public theorem factorₐ_comp_componentOfMapPowLe (f : R →ₐ[A] S) (ha : (I ^ a).map f ≤ J)
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp
        (componentOfMapPowLe A f ha n) = componentOfMapPowLe A f ha m := by
  ext x
  have heval : Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.mul_le_mul_left a hle))
      (evalₐ I (a * n) x) = evalₐ I (a * m) x := factor_evalₐ I (Nat.mul_le_mul_left a hle) x
  simp only [componentOfMapPowLe_apply, AlgHom.comp_apply, Ideal.Quotient.factorₐ_apply]
  rw [← heval]
  induction evalₐ I (a * n) x using Quotient.inductionOn' with
  | _ z => rfl

/-- The map of adic completions `R̂_I → Ŝ_J` induced by an `A`-algebra map `f : R → S`
carrying `I ^ a` into `J`. -/
public def algHomOfMapPowLe (f : R →ₐ[A] S) (ha : (I ^ a).map f ≤ J) :
    AdicCompletion I R →ₐ[A] AdicCompletion J S :=
  liftAlgHom J (componentOfMapPowLe A f ha) (factorₐ_comp_componentOfMapPowLe A f ha)

/-- The level-`n` reduction of `algHomOfMapPowLe A f ha x` is the image under `f` of the
reduction of `x` modulo `I ^ (a * n)`. -/
@[simp]
public theorem evalₐ_algHomOfMapPowLe (f : R →ₐ[A] S) (ha : (I ^ a).map f ≤ J) (n : ℕ)
    (x : AdicCompletion I R) :
    evalₐ J n (algHomOfMapPowLe A f ha x) =
      Ideal.quotientMapₐ (R₁ := A) (J ^ n) f (pow_mul_le_comap_pow A f ha n)
        (evalₐ I (a * n) x) :=
  evalₐ_liftAlgHom _ _ _ _ _

/-- The induced map is compatible with the canonical maps from the uncompleted rings. -/
@[simp]
public theorem algHomOfMapPowLe_of (f : R →ₐ[A] S) (ha : (I ^ a).map f ≤ J) (x : R) :
    algHomOfMapPowLe A f ha (of I R x) = of J S (f x) := by
  refine ext_evalₐ fun n ↦ ?_
  rw [evalₐ_algHomOfMapPowLe, evalₐ_of, evalₐ_of]
  rfl

/-- The induced map is compatible with the algebra maps from the uncompleted rings. -/
public theorem algHomOfMapPowLe_algebraMap (f : R →ₐ[A] S) (ha : (I ^ a).map f ≤ J) (x : R) :
    algHomOfMapPowLe A f ha (algebraMap R (AdicCompletion I R) x) =
      algebraMap S (AdicCompletion J S) (f x) :=
  algHomOfMapPowLe_of A f ha x

end

section

variable {T : Type*} [CommRing T] [Algebra A T]
  {I : Ideal R} {J : Ideal S} {K : Ideal T} {a b : ℕ}

/-- The induced maps compose. -/
public theorem algHomOfMapPowLe_comp (f : R →ₐ[A] S) (g : S →ₐ[A] T)
    (ha : (I ^ a).map f ≤ J) (hb : (J ^ b).map g ≤ K)
    (hab : (I ^ (a * b)).map (g.comp f) ≤ K) :
    (algHomOfMapPowLe A g hb).comp (algHomOfMapPowLe A f ha) =
      algHomOfMapPowLe A (g.comp f) hab := by
  refine AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ ?_
  induction x using AdicCompletion.induction_on with
  | h y => simp [mul_assoc]

end

section Approximation

variable {R : Type v} [CommRing R]

/-- Every element of the `I`-adic completion of `R` agrees, modulo `I ^ m`, with an element
of `R`, where `I ^ m` means the ideal it generates in the completion. -/
public theorem exists_sub_mem_map_pow (I : Ideal R) (hI : I.FG) (m : ℕ)
    (x : AdicCompletion I R) :
    ∃ p : R, x - algebraMap R (AdicCompletion I R) p ∈
      (I ^ m).map (algebraMap R (AdicCompletion I R)) := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (evalₐ I m x)
  refine ⟨p, ?_⟩
  have hofp : algebraMap R (AdicCompletion I R) p = of I R p := by
    rw [algebraMap_apply, Algebra.algebraMap_self_apply]
  have h0 : evalₐ I m (x - algebraMap R (AdicCompletion I R) p) = 0 := by
    rw [map_sub, hofp, evalₐ_of, ← hp, sub_self]
  have h1 : eval I R m (x - algebraMap R (AdicCompletion I R) p) = 0 := by
    rw [← factor_evalₐ_eq_eval I _ (by simp), h0]
    simp
  have h2 : x - algebraMap R (AdicCompletion I R) p ∈
      (I ^ m) • (⊤ : Submodule R (AdicCompletion I R)) := by
    rw [pow_smul_top_eq_ker_eval hI]
    exact h1
  rw [Ideal.smul_top_eq_map] at h2
  exact (Submodule.restrictScalars_mem R _ _).mp h2

end Approximation

section Uniqueness

/-- The level-`n` reduction kills the ideal generated by `I ^ n` in the completion. -/
public theorem evalₐ_eq_zero_of_mem_map_pow (I : Ideal R) (n : ℕ) {x : AdicCompletion I R}
    (hx : x ∈ (I ^ n).map (algebraMap R (AdicCompletion I R))) :
    evalₐ I n x = 0 := by
  have hle : (I ^ n).map (algebraMap R (AdicCompletion I R)) ≤
      RingHom.ker (evalₐ I n).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    show evalₐ I n (of I R c) = 0
    rw [evalₐ_of]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hc
  exact RingHom.mem_ker.mp (hle hx)

/-- A map of adic completions is determined by its values on the uncompleted ring: if `I` is
finitely generated, `f : R →ₐ[A] S` carries `I ^ a` into `J`, and two `A`-algebra maps
`R̂_I → Ŝ_J` both agree with `f` on the canonical image of `R`, then they are equal. -/
public theorem algHom_ext_of_of (I : Ideal R) (hI : I.FG) (J : Ideal S) {a : ℕ}
    (f : R →ₐ[A] S) (ha : (I ^ a).map f ≤ J)
    (φ₁ φ₂ : AdicCompletion I R →ₐ[A] AdicCompletion J S)
    (h₁ : ∀ p : R, φ₁ (of I R p) = of J S (f p))
    (h₂ : ∀ p : R, φ₂ (of I R p) = of J S (f p)) :
    φ₁ = φ₂ := by
  have key : ∀ φ : AdicCompletion I R →ₐ[A] AdicCompletion J S,
      (∀ p : R, φ (of I R p) = of J S (f p)) →
      ∀ (n : ℕ) (x : AdicCompletion I R),
        x ∈ (I ^ (a * n)).map (algebraMap R (AdicCompletion I R)) →
        evalₐ J n (φ x) = 0 := by
    intro φ hφ n x hx
    have hcomp : ((φ : AdicCompletion I R →+* AdicCompletion J S)).comp
        (algebraMap R (AdicCompletion I R)) =
        (algebraMap S (AdicCompletion J S)).comp (f : R →+* S) :=
      RingHom.ext fun p ↦ hφ p
    have h : φ x ∈ ((I ^ (a * n)).map f).map (algebraMap S (AdicCompletion J S)) := by
      have hmem := Ideal.mem_map_of_mem (φ : AdicCompletion I R →+* AdicCompletion J S) hx
      rwa [Ideal.map_map, hcomp, ← Ideal.map_map] at hmem
    exact evalₐ_eq_zero_of_mem_map_pow J n (Ideal.map_mono (map_pow_mul_le_pow A f ha n) h)
  refine AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ ?_
  obtain ⟨p, hp⟩ := exists_sub_mem_map_pow I hI (a * n) x
  have e : ∀ φ : AdicCompletion I R →ₐ[A] AdicCompletion J S,
      (∀ p : R, φ (of I R p) = of J S (f p)) →
      evalₐ J n (φ x) = evalₐ J n (φ (of I R p)) := fun φ hφ ↦ by
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact key φ hφ n _ hp
  rw [e φ₁ h₁, e φ₂ h₂, h₁, h₂]

end Uniqueness

end AdicCompletion

end
