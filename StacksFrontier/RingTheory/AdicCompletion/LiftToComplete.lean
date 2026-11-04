module

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import StacksFrontier.RingTheory.AdicCompletion.MapOfPowLe

/-!
# Factoring an algebra map through an adic completion

Let `R` and `T` be algebras over a commutative ring `A`, let `I ⊆ R` and `J ⊆ T` be ideals and
let `T` be `J`-adically complete. An `A`-algebra map `R → T` carrying `I` into `J` extends to
the `I`-adic completion of `R`: the maps `R ⧸ Iⁿ → T ⧸ Jⁿ` it induces, precomposed with the
projections of `R^∧`, form a compatible family, and the universal property of a complete ring
turns that family into an `A`-algebra map `R^∧ → T`.

A ring is adically complete along a nilpotent ideal; this is how the hypothesis on `T` is met
when `T` is a nilpotent thickening of a complete ring.

The extension is unique when `I` is finitely generated and `T` is `J`-adically Hausdorff: two
such maps agree on the image of `R`, which is dense for the `I`-adic topology, and the
difference of their values lies in every power of `J`.

## Main results

* `IsAdicComplete.of_isNilpotent`: a ring is adically complete along a nilpotent ideal.
* `AdicCompletion.factorₐ_evalₐ`: the projections of an adic completion form a compatible
  family.
* `AdicCompletion.exists_algHom_of_isAdicComplete`: an `A`-algebra map `R → T` carrying `I`
  into `J`, with `T` `J`-adically complete, extends to the `I`-adic completion of `R`.
* `AdicCompletion.algHom_ext_of_isHausdorff`: two maps out of an adic completion which agree
  on the image of `R` and carry `I` into an ideal of Hausdorffness are equal.
-/

@[expose] public noncomputable section

/-- A ring is adically complete along a nilpotent ideal: the filtration is eventually zero, so
every adic Cauchy sequence is eventually constant and only zero is infinitely divisible. -/
theorem IsAdicComplete.of_isNilpotent {R : Type*} [CommRing R] (I : Ideal R)
    (hI : IsNilpotent I) : IsAdicComplete I R := by
  obtain ⟨k, hk⟩ := hI
  have hbot : (I ^ k • (⊤ : Submodule R R)) = ⊥ := by
    rw [show I ^ k = ⊥ from le_antisymm hk.le bot_le]
    simp
  have hzero : ∀ {x y : R}, x ≡ y [SMOD (I ^ k • ⊤ : Submodule R R)] → x = y := by
    intro x y h
    rwa [hbot, SModEq.bot] at h
  have hh : IsHausdorff I R := ⟨fun x hx => hzero (hx k)⟩
  have hp : IsPrecomplete I R := by
    refine ⟨fun f hf => ⟨f k, fun n => ?_⟩⟩
    rcases le_or_gt n k with hn | hn
    · exact hf hn
    · rw [hzero (hf hn.le)]
  exact ⟨⟩

namespace AdicCompletion

private theorem factorₐ_mk {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    {I J : Ideal R} (hIJ : I ≤ J) (x : R) :
    Ideal.Quotient.factorₐ A hIJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x := rfl

/-- In a `J`-adically Hausdorff ring, elements whose difference lies in every power of `J` are
equal. -/
private theorem eq_of_sub_mem_pow {T : Type*} [CommRing T] (J : Ideal T) [IsHausdorff J T]
    {x y : T} (h : ∀ n : ℕ, x - y ∈ J ^ n) : x = y :=
  sub_eq_zero.mp (IsHausdorff.haus ‹_› _ fun n => by
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact h n)

/-- The projections of an adic completion form a compatible family for the transition maps on
the quotients by the powers of the ideal. -/
theorem factorₐ_evalₐ {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn) (evalₐ I n x) = evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h a =>
    rw [evalₐ_mk, evalₐ_mk, factorₐ_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      ← Submodule.neg_mem_iff, neg_sub]
    simpa using SModEq.sub_mem.mp (a.property hmn)

/-- An `A`-algebra map `R → T` carrying an ideal `I` of `R` into an ideal `J` of `T`, with `T`
`J`-adically complete, extends to an `A`-algebra map from the `I`-adic completion of `R`. -/
theorem exists_algHom_of_isAdicComplete {A R T : Type*} [CommRing A] [CommRing R] [CommRing T]
    [Algebra A R] [Algebra A T] (I : Ideal R) (J : Ideal T) [IsAdicComplete J T]
    (h : R →ₐ[A] T) (hIJ : I.map h ≤ J) :
    ∃ H : AdicCompletion I R →ₐ[A] T, ∀ x : R, H (of I R x) = h x := by
  have hle : ∀ n : ℕ, I ^ n ≤ Ideal.comap h (J ^ n) := by
    intro n
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hIJ n
  set q : (n : ℕ) → (R ⧸ I ^ n) →ₐ[A] (T ⧸ J ^ n) := fun n =>
    Ideal.quotientMapₐ (J ^ n) h (hle n)
  set fam : (n : ℕ) → AdicCompletion I R →ₐ[A] (T ⧸ J ^ n) := fun n =>
    (q n).comp ((evalₐ I n).restrictScalars A)
  have hsq : ∀ (m n : ℕ) (hmn : m ≤ n) (w : R ⧸ I ^ n),
      Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn) (q n w) =
        q m (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn) w) := by
    intro m n hmn w
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective w
    rfl
  have hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp (fam n) = fam m := by
    intro m n hmn
    refine AlgHom.ext fun z => ?_
    have h1 : fam n z = q n (evalₐ I n z) := rfl
    have h2 : fam m z = q m (evalₐ I m z) := rfl
    rw [AlgHom.comp_apply, h1, h2, hsq m n hmn, factorₐ_evalₐ I hmn]
  refine ⟨IsAdicComplete.liftAlgHom J fam hcompat, fun x => ?_⟩
  have hmk : ∀ n : ℕ, Ideal.Quotient.mk (J ^ n)
      (IsAdicComplete.liftAlgHom J fam hcompat (of I R x)) =
      Ideal.Quotient.mk (J ^ n) (h x) := by
    intro n
    have hn := AlgHom.congr_fun (IsAdicComplete.mkₐ_comp_liftAlgHom J fam hcompat n) (of I R x)
    have h2 : fam n (of I R x) = Ideal.Quotient.mk (J ^ n) (h x) := by
      have h3 : fam n (of I R x) = q n (evalₐ I n (of I R x)) := rfl
      rw [h3, evalₐ_of]
      rfl
    exact hn.trans h2
  have hhaus : IsHausdorff J T := IsAdicComplete.toIsHausdorff
  refine eq_of_sub_mem_pow J fun n => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hmk n, sub_self]

/-- Two `A`-algebra maps out of the `I`-adic completion of `R`, for `I` finitely generated, are
equal as soon as they agree on the image of `R` and carry `I` into an ideal `J` along which the
target is Hausdorff. -/
theorem algHom_ext_of_isHausdorff {A R T : Type*} [CommRing A] [CommRing R] [CommRing T]
    [Algebra A R] [Algebra A T] (I : Ideal R) (hI : I.FG) (J : Ideal T) [IsHausdorff J T]
    (f g : AdicCompletion I R →ₐ[A] T) (hfg : ∀ x : R, f (of I R x) = g (of I R x))
    (hfJ : ∀ x ∈ I, f (of I R x) ∈ J) :
    f = g := by
  have hof : ∀ x : R, algebraMap R (AdicCompletion I R) x = of I R x := fun x => by
    rw [algebraMap_apply, Algebra.algebraMap_self_apply]
  have key : ∀ φ : AdicCompletion I R →ₐ[A] T, (∀ x ∈ I, φ (of I R x) ∈ J) →
      ∀ (n : ℕ) (z : AdicCompletion I R),
        z ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) → φ z ∈ J ^ n := by
    intro φ hφ n z hz
    have hbase : Ideal.map (φ.toRingHom.comp (algebraMap R (AdicCompletion I R))) I ≤ J := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.comp_apply, hof]
      exact hφ x hx
    have h1 : φ z ∈ Ideal.map φ.toRingHom
        ((I ^ n).map (algebraMap R (AdicCompletion I R))) :=
      Ideal.mem_map_of_mem _ hz
    rw [Ideal.map_map, Ideal.map_pow] at h1
    exact pow_le_pow_left' hbase n h1
  refine AlgHom.ext fun z => eq_of_sub_mem_pow J fun n => ?_
  obtain ⟨p, hp⟩ := exists_sub_mem_map_pow I hI n z
  have hfz : f (z - algebraMap R (AdicCompletion I R) p) ∈ J ^ n := key f hfJ n _ hp
  have hgz : g (z - algebraMap R (AdicCompletion I R) p) ∈ J ^ n :=
    key g (fun x hx => hfg x ▸ hfJ x hx) n _ hp
  have hsub := Submodule.sub_mem (J ^ n : Ideal T) hfz hgz
  rwa [map_sub, map_sub, hof p, hfg p, sub_sub_sub_cancel_right] at hsub

end AdicCompletion

end
