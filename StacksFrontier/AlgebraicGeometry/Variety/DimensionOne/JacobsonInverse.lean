module

public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.Valuation
public import StacksCore.Tactic.StacksAttribute

/-!
# An element whose inverse lies in several Jacobson radicals

Let `A` and finitely many rings `B i` be subrings of a common field which is their fraction
field, each `B i` a Noetherian one-dimensional semilocal domain. If each multiplication map
`A ⊗[ℤ] B i → K` is surjective, then some nonzero element of `A` has its inverse in the
Jacobson radical of every `B i`. The element is produced by making its valuation large at
every height one prime of every integral closure at once.

## Main results

* `Ring.exists_ne_zero_inverse_mem_jacobson_of_tensorProduct_surjective` produces the required
  element of `A`.

## Implementation notes

The finite list in the source is represented by an arbitrary finite index type. Rings contained
in the common fraction field are represented literally as subrings, so the tensor-product map is
the canonical multiplication map. The conclusion explicitly records that the chosen element is
nonzero, as is required by the proof and by the usual meaning of its reciprocal.

The passage from the integral closure back to `B i` costs a power: the inverse lies in the
Jacobson radical of the closure, and only a positive power of it is the image of an element of
the Jacobson radical of `B i`. Raising the chosen element to the product of these exponents
makes a single element work for every index.

## References

* [Stacks Project, Tag 09N5](https://stacks.math.columbia.edu/tag/09N5)
-/

@[expose] public section

namespace Ring

universe u v

/-- For finitely many Noetherian one-dimensional semilocal subrings of a common
fraction field, surjectivity of the corresponding multiplication maps produces
a nonzero element whose reciprocal belongs to all their Jacobson radicals. -/
@[stacks 09N5]
public theorem exists_ne_zero_inverse_mem_jacobson_of_tensorProduct_surjective
    {K : Type u} [Field K] {ι : Type v} [Finite ι]
    (A : Subring K) (B : ι → Subring K)
    [IsFractionRing A K] [∀ i, IsFractionRing (B i) K]
    [∀ i, IsNoetherianRing (B i)] [∀ i, Finite (MaximalSpectrum (B i))]
    (h_dim : ∀ i, ringKrullDim (B i) = 1)
    (h_surj : ∀ i, Function.Surjective
      (Algebra.TensorProduct.lift (B := B i) A.subtype.toIntAlgHom
        (B i).subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    ∃ x : A, x ≠ 0 ∧ ∀ i, ∃ y : B i,
      (y : K) = (x : K)⁻¹ ∧ y ∈ Ideal.jacobson (⊥ : Ideal (B i)) := by
  classical
  let C (i : ι) := integralClosure (B i) K
  have hdimOne (i : ι) : Ring.DimensionLEOne (B i) := by
    have : Ring.KrullDimLE 1 (B i) :=
      Ring.krullDimLE_iff.mpr (by simp only [h_dim i, Nat.cast_one, le_refl])
    exact ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have hBnf (i : ι) : ¬ IsField (B i) := fun h =>
    one_ne_zero ((h_dim i).symm.trans (ringKrullDim_eq_zero_of_isField h))
  have hDedekind (i : ι) : IsDedekindDomain (C i) :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      (B i) K K (C i)).1
  have hFrac (i : ι) : IsFractionRing (C i) K :=
    integralClosure.isFractionRing_of_finite_extension K K
  have hFinite (i : ι) : Finite (MaximalSpectrum (C i)) :=
    IsIntegralClosure.finite_maximalSpectrum (B i) K (C i)
  have hCnf (i : ι) : ¬ IsField (C i) :=
    mt (isField_of_isIntegral_of_isField (R := B i) (S := C i)
      (fun a b hab => Subtype.ext (congrArg (fun z : C i => (z : K)) hab))) (hBnf i)
  have hFinitePrimes (i : ι) : Finite (IsDedekindDomain.HeightOneSpectrum (C i)) :=
    Finite.of_equiv (MaximalSpectrum (C i))
      (IsDedekindDomain.HeightOneSpectrum.equivMaximalSpectrum (hCnf i)).symm
  let J := (i : ι) × IsDedekindDomain.HeightOneSpectrum (C i)
  let v : J → Valuation K (WithZero (Multiplicative ℤ)) := fun j => j.2.valuation K
  have hwitness (j : J) : ∃ x : A, 1 < v j x := by
    refine Valuation.exists_one_lt_of_tensorProduct_surjective A (B j.1) (v j) ?_
      (fun b => j.2.valuation_le_one (algebraMap (B j.1) (C j.1) b)) (h_surj j.1)
    obtain ⟨z, hz⟩ := j.2.valuation_surjective K (WithZero.exp (1 : ℤ))
    refine ⟨z, ?_⟩
    change 1 < j.2.valuation K z
    rw [hz]
    exact WithZero.exp_lt_exp.mpr (by decide : (0 : ℤ) < 1)
  let _ := Fintype.ofFinite J
  obtain ⟨x, hx, hxv⟩ :=
    Valuation.exists_ne_zero_forall_one_lt A v Finset.univ (fun j _ => hwitness j)
  have hnorm (i : ι) : ∃ z : C i, algebraMap (C i) K z = (x : K)⁻¹ ∧
      z ∈ Ring.jacobson (C i) := by
    apply exists_mem_jacobson_of_valuation_lt_one (hCnf i)
    intro p
    rw [Valuation.map_inv]
    have hp : 1 < p.valuation K x := hxv ⟨i, p⟩ (Finset.mem_univ _)
    exact (inv_lt_one₀ (zero_lt_one.trans hp)).mpr hp
  choose z hz hzj using hnorm
  have hz0 (i : ι) : z i ≠ 0 := fun h => hx (by simpa [h] using (hz i).symm)
  have hpow (i : ι) : ∃ n ≠ 0, ∃ y : B i,
      (y : K) = (x : K)⁻¹ ^ n ∧ y ∈ Ideal.jacobson (⊥ : Ideal (B i)) := by
    obtain ⟨n, hn, y, hy, hyj⟩ :=
      exists_pos_pow_mem_jacobson (R := B i) (K := K) (z i) (hz0 i) (hzj i)
    refine ⟨n, hn, y, ?_, hyj⟩
    change algebraMap (B i) K y = _
    rw [IsScalarTower.algebraMap_apply (B i) (C i) K, hy, map_pow, hz i]
  choose n hn y hy hyj using hpow
  let _ := Fintype.ofFinite ι
  refine ⟨x ^ ∏ i, n i, pow_ne_zero _ hx, fun i => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  have hk0 : k ≠ 0 := fun h =>
    Finset.prod_ne_zero_iff.mpr (fun i _ => hn i) (by simpa [h] using hk)
  refine ⟨y i ^ k, ?_, (Ideal.jacobson ⊥).pow_mem_of_mem (hyj i) k (Nat.pos_of_ne_zero hk0)⟩
  simp only [Subring.coe_pow, hy i, ← pow_mul, ← hk, inv_pow]

end Ring
