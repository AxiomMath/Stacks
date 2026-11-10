module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.IntegralClosure

/-!
# Valuations and subrings of a common fraction field

Surjectivity of the multiplication map `A ⊗[ℤ] B → K` forces the subring `A` to contain an
element of valuation greater than one at every place where `B` is contained in the valuation
ring: otherwise the whole image of the tensor product would be bounded by one. Combining
finitely many such places produces a single element of `A` large at all of them, whose inverse
is then small enough to lie in the Jacobson radical of the integral closure.

## Main results

* `WithZero.exists_lt_pow`: powers of an element greater than one are cofinal.
* `Valuation.exists_ne_zero_forall_one_lt`: a single element of a subring is large at every
  member of a finite family of places at which some element is large.
* `Valuation.exists_one_lt_of_tensorProduct_surjective`: surjectivity of the multiplication map
  produces an element of the first subring of valuation greater than one.
* `Ring.exists_mem_jacobson_of_valuation_lt_one`: an element of small valuation at every height
  one prime of a Dedekind domain lies in its Jacobson radical.
* `Ring.exists_pos_pow_mem_jacobson`: a positive power of an element of the Jacobson radical of
  the integral closure comes from the Jacobson radical of the base.

## Implementation notes

The value group is written multiplicatively as `WithZero Γ`, matching Mathlib's adic valuations
on a Dedekind domain. The finite family of places is indexed by a `Finset`, and the inductive
step replaces a witness `x` by `x ^ N + y` for `N` large, which is large at the old places
because the valuation of the sum is that of the dominant term.

## References

* [Stacks Project, Tag 09N5](https://stacks.math.columbia.edu/tag/09N5)
-/

@[expose] public section

namespace WithZero

/-- In a multiplicatively archimedean linearly ordered group with zero adjoined, the powers of
an element greater than one are cofinal. -/
public lemma exists_lt_pow {Γ : Type*} [CommGroup Γ] [LinearOrder Γ]
    [IsOrderedMonoid Γ] [MulArchimedean Γ] {a : WithZero Γ} (ha : 1 < a)
    (b : WithZero Γ) : ∃ n : ℕ, b < a ^ n := by
  obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.mp (ne_of_gt (zero_lt_one.trans ha))
  induction b using WithZero.recZeroCoe with
  | zero => exact ⟨0, by simp⟩
  | coe b =>
    obtain ⟨n, hn⟩ := _root_.exists_lt_pow (WithZero.coe_lt_coe.mp ha) b
    exact ⟨n, by simpa only [← WithZero.coe_pow, WithZero.coe_lt_coe] using hn⟩

end WithZero

namespace Valuation

/-- Given a finite family of valuations at each of which some element of a subring has value
greater than one, a single nonzero element of the subring has value greater than one at all of
them. -/
public lemma exists_ne_zero_forall_one_lt {K : Type*} [CommRing K] [Nontrivial K]
    {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ] [MulArchimedean Γ]
    {ι : Type*} (A : Subring K) (v : ι → Valuation K (WithZero Γ))
    (s : Finset ι) (h : ∀ i ∈ s, ∃ x : A, 1 < v i x) :
    ∃ x : A, x ≠ 0 ∧ ∀ i ∈ s, 1 < v i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨x, hx, hxs⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    by_cases hxi : 1 < v i x
    · exact ⟨x, hx, by simpa only [Finset.mem_insert, forall_eq_or_imp] using And.intro hxi hxs⟩
    obtain ⟨y, hy⟩ := h i (Finset.mem_insert_self _ _)
    choose n hn using fun j : s => WithZero.exists_lt_pow (hxs j j.property) (v j y)
    let N := s.attach.sup n + 1
    have hdom (j : ι) (hj : j ∈ s) : v j y < v j x ^ N :=
      (hn ⟨j, hj⟩).trans_le
        (pow_le_pow_right₀ (hxs j hj).le
          ((Finset.le_sup (f := n) (Finset.mem_attach s ⟨j, hj⟩)).trans (Nat.le_succ _)))
    have hval : v i ((x : K) ^ N + y) = v i y := by
      apply (v i).map_add_eq_of_lt_right
      rw [map_pow]
      exact (pow_le_one₀ zero_le (le_of_not_gt hxi)).trans_lt hy
    refine ⟨x ^ N + y, ?_, ?_⟩
    · intro hz
      rw [show (x : K) ^ N + y = 0 from congrArg Subtype.val hz, map_zero] at hval
      exact (ne_of_gt (zero_lt_one.trans hy)) hval.symm
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [Subring.coe_add, Subring.coe_pow, hval] using hy
      · change 1 < v j ((x : K) ^ N + y)
        rw [(v j).map_add_eq_of_lt_left (by simpa only [map_pow] using hdom j hj), map_pow]
        exact one_lt_pow₀ (hxs j hj) (by simp [N])

/-- If the multiplication map from `A ⊗[ℤ] B` is surjective and the valuation is bounded by one
on `B` but not on the whole field, then some element of `A` has valuation greater than one. -/
public lemma exists_one_lt_of_tensorProduct_surjective {K : Type*} [CommRing K]
    {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]
    (A B : Subring K) (v : Valuation K (WithZero Γ))
    (hv : ∃ z, 1 < v z) (hB : ∀ b : B, v b ≤ 1)
    (h_surj : Function.Surjective
      (Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
        B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    ∃ x : A, 1 < v x := by
  by_contra! h
  obtain ⟨z, hz⟩ := hv
  have hbound (t : TensorProduct ℤ A B) :
      v (Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
        B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _) t) ≤ 1 := by
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      simpa using (mul_le_mul_of_nonneg_right (h a) zero_le).trans (by simpa using hB b)
    | add t u ht hu =>
      simpa only [map_add] using (v.map_add _ _).trans (max_le ht hu)
  obtain ⟨t, rfl⟩ := h_surj z
  exact hz.not_ge (hbound t)

end Valuation

namespace Ring

/-- An element of the fraction field of a Dedekind domain whose valuation is less than one at
every height one prime lies in the Jacobson radical of the domain. -/
public lemma exists_mem_jacobson_of_valuation_lt_one
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (hR : ¬ IsField R) {x : K}
    (hx : ∀ p : IsDedekindDomain.HeightOneSpectrum R, p.valuation K x < 1) :
    ∃ y : R, algebraMap R K y = x ∧ y ∈ Ring.jacobson R := by
  obtain ⟨y, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    K x (fun p => (hx p).le)
  refine ⟨y, rfl, ?_⟩
  rw [← Ideal.jacobson_bot, Ideal.jacobson, Ideal.mem_sInf]
  intro m hm
  let p : IsDedekindDomain.HeightOneSpectrum R :=
    ⟨m, hm.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm.2 hR⟩
  exact (p.valuation_lt_one_iff_mem y).mp (hx p)

/-- A positive power of a nonzero element of the Jacobson radical of the integral closure is
the image of an element of the Jacobson radical of the base. -/
public lemma exists_pos_pow_mem_jacobson
    {R K C : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] [Finite (MaximalSpectrum R)] [Field K]
    [Algebra R K] [IsFractionRing R K] [CommRing C]
    [Algebra R C] [Algebra C K] [IsScalarTower R C K] [IsIntegralClosure C R K]
    (x : C) (hx : x ≠ 0) (hxj : x ∈ Ring.jacobson C) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ y : R,
      algebraMap R C y = x ^ n ∧ y ∈ Ideal.jacobson (⊥ : Ideal R) := by
  have := IsIntegralClosure.isIntegral_algebra R K (A := C)
  obtain ⟨n, y, hy⟩ := IsIntegralClosure.exists_pow_mul_mem_range R K C x hx hxj x
  refine ⟨n + 1, Nat.succ_ne_zero _, y, ?_, ?_⟩
  · simpa only [pow_succ] using hy
  · apply mem_jacobson_of_algebraMap_mem (S := C) (fun a b hab =>
      IsFractionRing.injective R K (by
        simp only [IsScalarTower.algebraMap_apply R C K, hab]))
    rw [hy, Ideal.jacobson_bot]
    exact (Ring.jacobson C).mul_mem_left _ hxj

end Ring
