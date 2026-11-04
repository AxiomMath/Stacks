module

public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalPointed
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalSectionSmooth

/-!
# Lifting a free `d`-dimensional structure through a nilpotent reduction

Let `R' → R` be a surjection of commutative rings with nilpotent kernel `I`, let `A'` be a flat
`R'`-algebra and let `φ : A' → A` be a surjection onto an `R`-algebra with kernel `I A'`,
compatible with the base rings. If `A` is the algebra of a free `d`-dimensional structure `m`
over `R`, then `A'` is the algebra of a free `d`-dimensional structure `m'` over `R'` whose
extension of scalars along `R' → R` is `m`, and the identification of `A'` with the algebra of
`m'` is compatible with `φ` coordinate by coordinate.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.exists_structure_lift_of_nilpotent_ker`: the lift.

## References

* [Stacks Project, Tag 051F](https://stacks.math.columbia.edu/tag/051F)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {R' R A' A : Type u} [CommRing R'] [CommRing R] [CommRing A'] [CommRing A]
  [Algebra R' R] [Algebra R' A'] [Algebra R A] {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The coordinates of the image of an element under a reduction compatible with two bases are
the images of its coordinates. -/
private theorem repr_of_basis_lift (φ : A' →+* A)
    (hcompat : ∀ c : R', φ (algebraMap R' A' c) = algebraMap R A (algebraMap R' R c))
    (b' : Module.Basis (Fin d) R' A') (b : Module.Basis (Fin d) R A)
    (hb : ∀ i, φ (b' i) = b i) (z : A') (k : Fin d) :
    b.repr (φ z) k = algebraMap R' R (b'.repr z k) := by
  classical
  have hz : φ z = ∑ l, algebraMap R' R (b'.repr z l) • b l :=
    calc
      φ z = φ (∑ l, b'.repr z l • b' l) := by rw [b'.sum_repr]
      _ = ∑ l, φ (b'.repr z l • b' l) := map_sum φ _ _
      _ = ∑ l, algebraMap R' R (b'.repr z l) • b l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcompat, hb]
  rw [hz]
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ k) h)]
  simp [Algebra.algebraMap_eq_smul_one]

/-- **Lifting a free `d`-dimensional structure through a nilpotent reduction.** Let `R' → R` be
surjective with nilpotent kernel `I`, let `A'` be a flat `R'`-algebra and let `φ : A' → A` be a
surjection onto an `R`-algebra with kernel `I A'`, compatible with the base rings. If `A` is the
algebra of a free `d`-dimensional structure `m` over `R`, then `A'` is the algebra of a free
`d`-dimensional structure `m'` over `R'` extending to `m`, compatibly with `φ`. -/
theorem exists_structure_lift_of_nilpotent_ker [Module.Flat R' A']
    (hsurj : Function.Surjective (algebraMap R' R))
    (hnil : IsNilpotent (RingHom.ker (algebraMap R' R)))
    (φ : A' →+* A) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.map (algebraMap R' A') (RingHom.ker (algebraMap R' R)))
    (hcompat : ∀ c : R', φ (algebraMap R' A' c) = algebraMap R A (algebraMap R' R c))
    (m : FiniteFreeAlgebra R d) (e : A ≃ₐ[R] Carrier m) :
    ∃ (m' : FiniteFreeAlgebra R' d) (e' : A' ≃ₐ[R'] Carrier m'),
      map (algebraMap R' R) m' = m ∧
        ∀ (z : A') (k : Fin d), algebraMap R' R (e' z k) = e (φ z) k := by
  classical
  let b : Module.Basis (Fin d) R A := (Carrier.basis m).map e.toLinearEquiv.symm
  have hbapply : ∀ i, b i = e.symm (Carrier.basis m i) := fun i => by
    simp [b, Module.Basis.map_apply]
  have hb0 : b 0 = 1 := by
    rw [hbapply, Carrier.basis_zero, map_one]
  have hbe : ∀ i, e (b i) = Carrier.basis m i := fun i => by
    rw [hbapply, e.apply_symm_apply]
  obtain ⟨b', hb'0, hb'φ⟩ :=
    Algebra.exists_basis_lift_of_nilpotent_ker hsurj hnil φ hφ hker hcompat b hb0
  refine ⟨ofBasis b' hb'0, algEquivCarrierOfBasis b' hb'0, ?_, ?_⟩
  · refine (ofBasis_map (algebraMap R' R) φ hcompat b' hb'0 b hb0 hb'φ).trans ?_
    refine (ofBasis_eq_of_algEquiv e b (Carrier.basis m) hb0 (Carrier.basis_zero m) hbe).trans ?_
    exact ofBasis_carrierBasis m
  · intro z k
    have hrepr : ∀ w : A, b.repr w k = e w k := by
      intro w
      have hw : b.repr w = (Carrier.basis m).repr (e w) := by
        simp [b]
      rw [hw, Carrier.basis_repr_apply]
    change algebraMap R' R (b'.repr z k) = e (φ z) k
    rw [← repr_of_basis_lift φ hcompat b' b hb'φ z k, hrepr]

end AlgebraicGeometry.FiniteFreeAlgebra

end
