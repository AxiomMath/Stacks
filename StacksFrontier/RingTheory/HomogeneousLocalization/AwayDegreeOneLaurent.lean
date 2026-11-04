module

public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayDegreeZeroBaseChange
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Polynomial.Quotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The localization at an element of degree one is a Laurent extension of its degree-zero part

Let `S = ⨁_{d ≥ 0} S_d` be a graded ring, graded by a family of additive subgroups, and `f ∈ S_1`.
Write `S₍f₎` for the degree-zero part of `S_f`. The integer powers of `f` form a basis of `S_f`
over `S₍f₎`, so that `S_f = S₍f₎[f, f⁻¹]` is a Laurent extension of `S₍f₎`. Consequently:

* `S_f` is free, hence flat, over `S₍f₎`, and `S₍f₎` is Noetherian when `S` is;
* for a prime `𝔮` of `S₍f₎`, the extension `𝔮 S_f` is prime, and an element of `S_f` lies in it
  exactly when all its coordinates in the basis of powers of `f` lie in `𝔮`.

## Main results

* `Stacks.GradedLocalization.awayZpowBasis`: the basis of `S_f` over `S₍f₎`.
* `Stacks.GradedLocalization.isNoetherianRing_away`.
* `Stacks.GradedLocalization.isPrime_map_algebraMap_away`.
* `Stacks.GradedLocalization.awayZpowBasis_repr_mem_of_mem_map`.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 01ML](https://stacks.math.columbia.edu/tag/01ML)
-/

@[expose] public noncomputable section

open DirectSum Stacks.GradedLaurent HomogeneousLocalization TensorProduct

namespace Stacks.GradedLocalization

variable {S : Type*} {σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : S}

/-- A finite sum of homogeneous elements of pairwise distinct degrees vanishes only if every
summand vanishes. -/
theorem eq_zero_of_sum_eq_zero_of_injOn' {ι : Type*} {s : Finset ι} {g : ι → ℕ}
    (hg : Set.InjOn g s) {w : ι → S} (hw : ∀ n ∈ s, w n ∈ 𝒜 (g n)) (h : ∑ n ∈ s, w n = 0)
    {n₀ : ι} (hn₀ : n₀ ∈ s) : w n₀ = 0 := by
  classical
  have key : GradedRing.proj 𝒜 (g n₀) (∑ n ∈ s, w n) = w n₀ := by
    rw [map_sum]
    refine (Finset.sum_eq_single_of_mem n₀ hn₀ fun b hb hne => ?_).trans ?_
    · rw [GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne 𝒜 (hw b hb) fun hcon => hne (hg hb hn₀ hcon)
    · rw [GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_same 𝒜 (hw n₀ hn₀)
  rwa [h, map_zero, eq_comm] at key

/-- **The integer powers of an element of degree one are linearly independent over the degree-zero
localization.** -/
@[ega "II 2.2.1" "special case"]
theorem linearIndependent_awayUnit_zpow (hf : f ∈ 𝒜 1) :
    LinearIndependent (Away 𝒜 f)
      (fun k : ℤ => ((awayUnit f ^ k : (Localization.Away f)ˣ) : Localization.Away f)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum n₀ hn₀
  choose jj num hnum hmk using fun n : ℤ => Away.mk_surjective 𝒜 hf (c n)
  simp only [smul_eq_mul, mul_one] at hnum
  set J : ℕ := s.sup jj with hJdef
  set N : ℕ := s.sup fun n => (-n).toNat with hNdef
  have hjJ : ∀ n ∈ s, jj n ≤ J := fun n hn => Finset.le_sup hn
  have hnN : ∀ n ∈ s, (0 : ℤ) ≤ n + N := by
    intro n hn
    have h : ((-n).toNat : ℤ) ≤ (N : ℤ) :=
      Int.ofNat_le.mpr (Finset.le_sup (f := fun n : ℤ => (-n).toNat) hn)
    omega
  set a : ℤ → ℕ := fun n => (n + N).toNat with hadef
  have ha : ∀ n ∈ s, (a n : ℤ) = n + N := fun n hn => Int.toNat_of_nonneg (hnN n hn)
  have hterm : ∀ n ∈ s, c n • ((awayUnit f ^ n : (Localization.Away f)ˣ) : Localization.Away f)
      * algebraMap S (Localization.Away f) (f ^ J)
      * ((awayUnit f ^ (N : ℤ) : (Localization.Away f)ˣ) : Localization.Away f)
      = algebraMap S (Localization.Away f) (num n * f ^ (J - jj n) * f ^ a n) := by
    intro n hn
    rw [show ∀ (c : Away 𝒜 f) (z : Localization.Away f), c • z = c.val * z from fun _ _ => rfl,
      ← hmk n, Away.val_mk]
    exact mk_mul_zpow_mul f (num n) (hjJ n hn) (ha n hn)
  have hzero : algebraMap S (Localization.Away f)
      (∑ n ∈ s, num n * f ^ (J - jj n) * f ^ a n) = 0 := by
    rw [map_sum, ← Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_mul, hsum,
      zero_mul, zero_mul]
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)] at hzero
  obtain ⟨t, hp⟩ := hzero
  obtain ⟨p, hpt⟩ := t.2
  rw [← hpt, Finset.mul_sum] at hp
  have hdeg : ∀ n ∈ s, f ^ p * (num n * f ^ (J - jj n) * f ^ a n) ∈ 𝒜 (p + J + a n) := by
    intro n hn
    have hmem := SetLike.mul_mem_graded (SetLike.pow_mem_graded p hf)
      (SetLike.mul_mem_graded
        (SetLike.mul_mem_graded (hnum n) (SetLike.pow_mem_graded (J - jj n) hf))
        (SetLike.pow_mem_graded (a n) hf))
    have hcan : jj n + (J - jj n) = J := Nat.add_sub_cancel' (hjJ n hn)
    have hidx : p • 1 + (jj n + (J - jj n) • 1 + a n • 1) = p + J + a n := by
      simp only [smul_eq_mul, mul_one]
      omega
    rwa [hidx] at hmem
  have hinj : Set.InjOn (fun n => p + J + a n) s := by
    intro n hn n' hn' hEq
    simp only at hEq
    have h2 := ha n hn
    have h3 := ha n' hn'
    omega
  have hvanish := eq_zero_of_sum_eq_zero_of_injOn' 𝒜 hinj hdeg hp hn₀
  have hnumzero : algebraMap S (Localization.Away f) (num n₀) = 0 := by
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)]
    refine ⟨⟨f ^ (p + (J - jj n₀) + a n₀), p + (J - jj n₀) + a n₀, rfl⟩, ?_⟩
    calc f ^ (p + (J - jj n₀) + a n₀) * num n₀
        = f ^ p * (num n₀ * f ^ (J - jj n₀) * f ^ a n₀) := by rw [pow_add, pow_add]; ring
      _ = 0 := hvanish
  rw [← hmk n₀, ← HomogeneousLocalization.val_injective (Submonoid.powers f) |>.eq_iff,
    HomogeneousLocalization.val_zero, Away.val_mk, mk_eq_algebraMap_mul, hnumzero, zero_mul]

/-- **`S_f` is free over `S₍f₎` on the integer powers of `f`**, for `f` of degree one. -/
def awayZpowBasis (hf : f ∈ 𝒜 1) : Module.Basis ℤ (Away 𝒜 f) (Localization.Away f) :=
  Module.Basis.mk (linearIndependent_awayUnit_zpow 𝒜 hf) fun z _ => by
    obtain ⟨s, c, rfl⟩ := exists_sum_zpow_eq 𝒜 hf z
    exact Submodule.sum_mem _ fun n _ =>
      Submodule.smul_mem _ (c n) (Submodule.subset_span ⟨n, rfl⟩)

/-- The `k`-th vector of `awayZpowBasis` is `f ^ k` in `S_f`. -/
@[simp]
theorem awayZpowBasis_apply (hf : f ∈ 𝒜 1) (k : ℤ) :
    awayZpowBasis 𝒜 hf k = ((awayUnit f ^ k : (Localization.Away f)ˣ) : Localization.Away f) := by
  rw [awayZpowBasis, Module.Basis.mk_apply]

/-- **The degree-zero localization at an element of degree one of a Noetherian graded ring is
Noetherian.** -/
@[ega "II 2.2.6" "special case"]
theorem isNoetherianRing_away [IsNoetherianRing S] (hf : f ∈ 𝒜 1) :
    IsNoetherianRing (Away 𝒜 f) := by
  rcases subsingleton_or_nontrivial (Localization.Away f) with hst | hnt
  · have : Subsingleton (Away 𝒜 f) :=
      Function.Injective.subsingleton (HomogeneousLocalization.val_injective (Submonoid.powers f))
    exact isNoetherian_of_finite _ _
  · have : Module.Free (Away 𝒜 f) (Localization.Away f) := Module.Free.of_basis (awayZpowBasis 𝒜 hf)
    have h : IsNoetherian (Localization.Away f)
        ((Localization.Away f) ⊗[Away 𝒜 f] (Away 𝒜 f)) :=
      isNoetherian_of_linearEquiv
        (TensorProduct.AlgebraTensorModule.rid (Away 𝒜 f) (Localization.Away f)
          (Localization.Away f)).symm
    exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (A := Localization.Away f) h

/-- If `z` lies in the extension of an ideal `Q` of `S₍f₎` to `S_f`, then every coordinate of `z`
in `awayZpowBasis` lies in `Q`. -/
theorem awayZpowBasis_repr_mem_of_mem_map (hf : f ∈ 𝒜 1) (Q : Ideal (Away 𝒜 f))
    {z : Localization.Away f} (hz : z ∈ Q.map (algebraMap (Away 𝒜 f) (Localization.Away f)))
    (k : ℤ) : (awayZpowBasis 𝒜 hf).repr z k ∈ Q := by
  have hz' : z ∈ Q • (⊤ : Submodule (Away 𝒜 f) (Localization.Away f)) := by
    rwa [Ideal.smul_top_eq_map]
  refine Submodule.smul_induction_on hz' (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Q.mul_mem_right _ ha
  · rw [map_add, Finsupp.add_apply]
    exact Q.add_mem hy hy'

/-- The ring map `S₍f₎[T, T⁻¹] → S_f`, `T ↦ f`. -/
def awayLaurentHom (f : S) : LaurentPolynomial (Away 𝒜 f) →+* Localization.Away f :=
  LaurentPolynomial.eval₂ (algebraMap (Away 𝒜 f) (Localization.Away f)) (awayUnit f)

/-- `awayLaurentHom` sends `T ^ k` to `f ^ k`. -/
theorem awayLaurentHom_T (k : ℤ) :
    awayLaurentHom 𝒜 f (LaurentPolynomial.T k)
      = ((awayUnit f ^ k : (Localization.Away f)ˣ) : Localization.Away f) :=
  LaurentPolynomial.eval₂_T _ _ k

/-- `awayLaurentHom` sends a constant `a` to its image `a.val` in `S_f`. -/
theorem awayLaurentHom_C (a : Away 𝒜 f) :
    awayLaurentHom 𝒜 f (LaurentPolynomial.C a) = a.val :=
  LaurentPolynomial.eval₂_C _ _ a

/-- **The Laurent identification `S₍f₎[T, T⁻¹] ≅ S_f`**, for `f` of degree one. -/
def awayLaurentEquiv (hf : f ∈ 𝒜 1) : LaurentPolynomial (Away 𝒜 f) ≃+* Localization.Away f := by
  refine RingEquiv.ofBijective (awayLaurentHom 𝒜 f) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro p hp
    have hsum : ∑ n ∈ (AddMonoidAlgebra.coeff p).support, AddMonoidAlgebra.coeff p n •
        ((awayUnit f ^ n : (Localization.Away f)ˣ) : Localization.Away f)
        = awayLaurentHom 𝒜 f p := by
      conv_rhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
      rw [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [LaurentPolynomial.single_eq_C_mul_T, map_mul, awayLaurentHom_C, awayLaurentHom_T]
      rfl
    have hli := linearIndependent_iff'.mp (linearIndependent_awayUnit_zpow 𝒜 hf)
      (AddMonoidAlgebra.coeff p).support (AddMonoidAlgebra.coeff p) (hsum.trans hp)
    refine LaurentPolynomial.ext_iff.mpr fun k => ?_
    by_cases hk : k ∈ (AddMonoidAlgebra.coeff p).support
    · exact hli k hk
    · simpa using hk
  · intro z
    have hz : z ∈ Submodule.span (Away 𝒜 f) (Set.range fun k : ℤ =>
        ((awayUnit f ^ k : (Localization.Away f)ˣ) : Localization.Away f)) := by
      rw [← funext (awayZpowBasis_apply 𝒜 hf)]
      exact (awayZpowBasis 𝒜 hf).mem_span z
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨LaurentPolynomial.T k, awayLaurentHom_T 𝒜 k⟩
    | zero => exact ⟨0, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨px, rfl⟩ := hx
      obtain ⟨py, rfl⟩ := hy
      exact ⟨px + py, map_add _ _ _⟩
    | smul c x _ hx =>
      obtain ⟨px, rfl⟩ := hx
      exact ⟨LaurentPolynomial.C c * px, by rw [map_mul, awayLaurentHom_C]; rfl⟩

/-- `awayLaurentEquiv` sends a constant `a` to its image `a.val` in `S_f`. -/
theorem awayLaurentEquiv_C (hf : f ∈ 𝒜 1) (a : Away 𝒜 f) :
    awayLaurentEquiv 𝒜 hf (LaurentPolynomial.C a) = a.val :=
  awayLaurentHom_C 𝒜 a

/-- **The extension of a prime of `S₍f₎` to `S_f` is prime**, for `f` of degree one. -/
theorem isPrime_map_algebraMap_away (hf : f ∈ 𝒜 1) (Q : Ideal (Away 𝒜 f)) [Q.IsPrime] :
    (Q.map (algebraMap (Away 𝒜 f) (Localization.Away f))).IsPrime := by
  set R := Away 𝒜 f
  have hP : (Q.map (Polynomial.C : R →+* Polynomial R)).IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hdisj : Disjoint (↑(Submonoid.powers (Polynomial.X : Polynomial R)) : Set (Polynomial R))
      ↑(Q.map (Polynomial.C : R →+* Polynomial R)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    have h1 := (Ideal.mem_map_C_iff.1 hn) n
    rw [Polynomial.coeff_X_pow_self] at h1
    exact hP.ne_top' (Q.eq_top_of_isUnit_mem h1 isUnit_one ▸ Ideal.map_top _)
  have hL := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers Polynomial.X)
    (LaurentPolynomial R) _ hP hdisj
  have hmap : ((Q.map (Polynomial.C : R →+* Polynomial R)).map
      (algebraMap (Polynomial R) (LaurentPolynomial R))).map
        ((awayLaurentEquiv 𝒜 hf : LaurentPolynomial R →+* Localization.Away f)) =
      Q.map (algebraMap R (Localization.Away f)) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_C, RingHom.coe_coe]
    exact awayLaurentEquiv_C 𝒜 hf a
  rw [← hmap]
  exact Ideal.map_isPrime_of_equiv (awayLaurentEquiv 𝒜 hf)

end Stacks.GradedLocalization

end
