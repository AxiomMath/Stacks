module

public import StacksFrontier.RingTheory.Blowup.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Adjoin.FG

/-!
# Finitely generated subalgebras of a fraction field are affine blowup algebras

Let `A` be a domain with fraction field `K`. Every finitely generated `A`-subalgebra `D` of `K` is
an affine blowup algebra `A[J/t]`: writing the generators of `D` over a common denominator
`t ≠ 0` as `aᵢ / t`, the ideal `J = (t, a₁, …, aₙ)` has `A[J/t] = A[a₁/t, …, aₙ/t] = D`.

## Main definitions

* `Stacks.Blowup.awayToFractionField`: the embedding `A_t ⟶ K` for `t ≠ 0`.

## Main results

* `Stacks.Blowup.awayToFractionField_injective`: that embedding is injective.
* `Stacks.Blowup.exists_algEquiv_affineBlowup_of_fg`: a finitely generated `A`-subalgebra of `K`
  is isomorphic, as an `A`-algebra, to an affine blowup algebra `A[J/t]` with `t ∈ J`, `t ≠ 0`.

## References

* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
* [Stacks Project, Tag 052Q](https://stacks.math.columbia.edu/tag/052Q)
-/

@[expose] public noncomputable section

namespace Stacks.Blowup

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- The embedding of the localization `A_t` into the fraction field, for `t ≠ 0`. -/
def awayToFractionField (t : A) (ht : t ≠ 0) : Localization.Away t →ₐ[A] K :=
  IsLocalization.liftAlgHom (M := Submonoid.powers t) (f := Algebra.ofId A K) (fun y => by
    obtain ⟨_, n, rfl⟩ := y
    exact Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (pow_ne_zero n ht)))

/-- `Stacks.Blowup.awayToFractionField` sends `x / y` in `A_t` to `x / y` in `K`. -/
theorem awayToFractionField_mk (t : A) (ht : t ≠ 0) (x : A) (y : Submonoid.powers t) :
    awayToFractionField (K := K) t ht (Localization.mk x y) =
      algebraMap A K x / algebraMap A K y := by
  have hy : algebraMap A K y ≠ 0 := by
    obtain ⟨_, n, rfl⟩ := y
    exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (pow_ne_zero n ht)
  rw [eq_div_iff hy]
  have h : Localization.mk x y * algebraMap A (Localization.Away t) y =
      algebraMap A (Localization.Away t) x := by
    rw [Localization.mk_eq_mk', IsLocalization.mk'_spec]
  have h' := congrArg (awayToFractionField (K := K) t ht) h
  rwa [map_mul, AlgHom.commutes, AlgHom.commutes] at h'

/-- The embedding `A_t ⟶ K` is injective. -/
theorem awayToFractionField_injective (t : A) (ht : t ≠ 0) :
    Function.Injective (awayToFractionField (K := K) t ht) := by
  change Function.Injective (IsLocalization.lift _)
  rw [IsLocalization.lift_injective_iff]
  exact fun x y => ⟨fun h => by
    rw [IsLocalization.injective (Localization.Away t)
      (powers_le_nonZeroDivisors_of_noZeroDivisors ht) h],
    fun h => by rw [IsFractionRing.injective A K h]⟩

/-- **A finitely generated subalgebra of the fraction field is an affine blowup algebra.** For a
finitely generated `A`-subalgebra `D` of `K` there are an ideal `J` and `t ∈ J`, `t ≠ 0`, with
`D ≅ A[J/t]` as `A`-algebras. -/
theorem exists_algEquiv_affineBlowup_of_fg (D : Subalgebra A K) (hD : D.FG) :
    ∃ (J : Ideal A) (t : A), t ∈ J ∧ t ≠ 0 ∧ Nonempty (D ≃ₐ[A] affineBlowup J t) := by
  classical
  obtain ⟨s, hs⟩ := hD
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) s
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  choose a ha using fun y (hy : y ∈ s) => hint y hy
  let gens : Set A := insert b (Set.range fun y : s => a y.1 y.2)
  let J : Ideal A := Ideal.span gens
  have hbJ : b ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  refine ⟨J, b, hbJ, hb0, ?_⟩
  let Φ := awayToFractionField (K := K) b hb0
  have hbK : algebraMap A K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb0
  have hay : ∀ y (hy : y ∈ s), algebraMap A K (a y hy) / algebraMap A K b = y := fun y hy => by
    rw [ha y hy, Algebra.smul_def, mul_div_cancel_left₀ _ hbK]
  have himage : Φ '' affineBlowupGenSet J b =
      (fun j => algebraMap A K j / algebraMap A K b) '' (J : Set A) := by
    rw [affineBlowupGenSet, Set.image_image]
    exact Set.image_congr fun j _ =>
      awayToFractionField_mk (K := K) b hb0 j ⟨b, Submonoid.mem_powers b⟩
  have hmap : (affineBlowup J b).map Φ = D := by
    rw [affineBlowup, AlgHom.map_adjoin, himage, ← hs]
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨j, hj, rfl⟩
      refine Submodule.span_induction (p := fun j _ =>
        algebraMap A K j / algebraMap A K b ∈ Algebra.adjoin A (s : Set K)) ?_ ?_ ?_ ?_ hj
      · rintro x (rfl | ⟨⟨y, hy⟩, rfl⟩)
        · rw [div_self hbK]
          exact Subalgebra.one_mem _
        · simp only [hay]
          exact Algebra.subset_adjoin hy
      · simp
      · intro x y _ _ hx hy
        rw [map_add, add_div]
        exact Subalgebra.add_mem _ hx hy
      · intro r x _ hx
        rw [smul_eq_mul, map_mul, mul_div_assoc]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) hx
    · rw [Algebra.adjoin_le_iff]
      intro y hy
      exact Algebra.subset_adjoin
        ⟨a y hy, Ideal.subset_span (Set.mem_insert_of_mem _ ⟨⟨y, hy⟩, rfl⟩), hay y hy⟩
  exact ⟨(Subalgebra.equivOfEq _ _ hmap).symm.trans
    (Subalgebra.equivMapOfInjective _ Φ (awayToFractionField_injective b hb0)).symm⟩

end Stacks.Blowup

end
