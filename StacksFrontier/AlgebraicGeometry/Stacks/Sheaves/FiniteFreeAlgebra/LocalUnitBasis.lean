module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.OfBasis

/-!
# Trivialising the unit of a free algebra over a standard open cover

Let `A` be a commutative algebra over a commutative ring `R` which is free of rank `d > 0` as an
`R`-module, on a basis `b`. The coordinates of `1` in `b` generate the unit ideal of `R`, so the
standard opens they cut out cover `Spec R`; and after any base change in which one of those
coordinates becomes invertible, the base changed algebra is free on a basis whose first vector is
the unit, hence is the algebra of a free `d`-dimensional structure. Over each member of that
cover `Spec A` is therefore the spectrum of a free `d`-dimensional structure.

## Main definitions

* `Module.Basis.updateOfIsUnit`: the basis obtained from `b` by replacing its `i`-th vector by an
  element whose `i`-th coordinate is invertible.
* `AlgebraicGeometry.FiniteFreeAlgebra.basisOne` and
  `AlgebraicGeometry.FiniteFreeAlgebra.basisOneOfIsUnit`: a basis whose first vector is the unit,
  of the algebra itself and of a base change of it.
* `AlgebraicGeometry.FiniteFreeAlgebra.structureOne` and
  `AlgebraicGeometry.FiniteFreeAlgebra.structureOfIsUnit`: the free `d`-dimensional structures
  their structure constants form.

## Main results

* `Module.Basis.det_update`: the determinant of a basis at an updated family is the coordinate of
  the new vector at the updated index.
* `AlgebraicGeometry.FiniteFreeAlgebra.span_range_repr_one_eq_top`: the coordinates of the unit
  generate the unit ideal.
* `AlgebraicGeometry.FiniteFreeAlgebra.algEquivCarrierOne` and
  `AlgebraicGeometry.FiniteFreeAlgebra.algEquivCarrierOfIsUnit`: the algebra, respectively its
  base change, is the algebra of that structure, and
  `AlgebraicGeometry.FiniteFreeAlgebra.specOverIsoSpecCoverOfIsUnit` says the same for spectra.
* `AlgebraicGeometry.FiniteFreeAlgebra.exists_basis_one_of_isLocalRing`: over a local ring such a
  basis always exists.
* `AlgebraicGeometry.FiniteFreeAlgebra.isUnit_algebraMap_localizationAway_repr_one` and
  `AlgebraicGeometry.FiniteFreeAlgebra.exists_structure_algEquiv_localizationAway`: the base
  change along the localization at one coordinate of the unit meets that hypothesis, so over each
  member of the standard open cover the algebra is the algebra of a free structure.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

namespace Module.Basis

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι]

/-- The determinant, in a basis `b`, of the family obtained from `b` by replacing its `i`-th
vector by `x` is the `i`-th coordinate of `x`. -/
theorem det_update (b : Basis ι R M) (i : ι) (x : M) :
    b.det (Function.update (b : ι → M) i x) = b.repr x i := by
  rw [Basis.det_apply, Basis.toMatrix_update, Basis.toMatrix_self]
  have h : (fun k => ∑ j, (b.repr x) j • (1 : Matrix ι ι R) k j) = ⇑(b.repr x) := by
    funext k
    simp [Matrix.one_apply]
  conv_lhs => rw [← h]
  rw [Matrix.det_updateCol_sum, Matrix.det_one, smul_eq_mul, mul_one]

/-- The basis obtained from `b` by replacing its `i`-th vector by an element whose `i`-th
coordinate is invertible. -/
noncomputable def updateOfIsUnit (b : Basis ι R M) (i : ι) (x : M)
    (hx : IsUnit (b.repr x i)) : Basis ι R M :=
  Basis.mk (v := Function.update (b : ι → M) i x)
    (b.is_basis_iff_det.mpr (by rwa [det_update])).1
    (b.is_basis_iff_det.mpr (by rwa [det_update])).2.ge

/-- The updated basis is the updated family. -/
theorem updateOfIsUnit_apply (b : Basis ι R M) (i : ι) (x : M) (hx : IsUnit (b.repr x i))
    (j : ι) : updateOfIsUnit b i x hx j = Function.update (b : ι → M) i x j :=
  Basis.mk_apply _ _ _

/-- The `i`-th vector of the updated basis is the new vector. -/
theorem updateOfIsUnit_self (b : Basis ι R M) (i : ι) (x : M) (hx : IsUnit (b.repr x i)) :
    updateOfIsUnit b i x hx i = x := by
  rw [updateOfIsUnit_apply, Function.update_self]

end Module.Basis

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ} [NeZero d]

/-- The coordinates of the unit of a commutative algebra free of positive rank generate the unit
ideal of the base. -/
theorem span_range_repr_one_eq_top (b : Module.Basis (Fin d) R A) :
    Ideal.span (Set.range fun i => b.repr 1 i) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : b 0 = ∑ i, b.repr 1 i • (b 0 * b i) := by
    conv_lhs => rw [← mul_one (b 0), ← b.sum_repr (1 : A)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
  have h2 : b.repr (b 0) 0 = ∑ i, b.repr 1 i * b.repr (b 0 * b i) 0 := by
    conv_lhs => rw [h1]
    simp
  have h3 : (1 : R) = ∑ i, b.repr 1 i * b.repr (b 0 * b i) 0 := by simpa using h2
  rw [h3]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- A basis whose first vector is the unit, available as soon as one coordinate of the unit is
invertible: replace the vector at that index by the unit and transpose that index with `0`. -/
noncomputable def basisOne (b : Module.Basis (Fin d) R A) (i : Fin d)
    (hi : IsUnit (b.repr 1 i)) : Module.Basis (Fin d) R A :=
  (b.updateOfIsUnit i 1 hi).reindex (Equiv.swap 0 i)

/-- The first vector of `AlgebraicGeometry.FiniteFreeAlgebra.basisOne` is the unit. -/
theorem basisOne_zero (b : Module.Basis (Fin d) R A) (i : Fin d) (hi : IsUnit (b.repr 1 i)) :
    basisOne b i hi 0 = 1 := by
  rw [basisOne, Module.Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left,
    Module.Basis.updateOfIsUnit_self]

/-- The free `d`-dimensional algebra structure formed by the structure constants of
`AlgebraicGeometry.FiniteFreeAlgebra.basisOne`. -/
noncomputable def structureOne (b : Module.Basis (Fin d) R A) (i : Fin d)
    (hi : IsUnit (b.repr 1 i)) : FiniteFreeAlgebra R d :=
  ofBasis (basisOne b i hi) (basisOne_zero b i hi)

/-- A commutative algebra free of positive rank in which one coordinate of the unit is
invertible is the algebra of a free `d`-dimensional structure. -/
noncomputable def algEquivCarrierOne (b : Module.Basis (Fin d) R A) (i : Fin d)
    (hi : IsUnit (b.repr 1 i)) : A ≃ₐ[R] Carrier (structureOne b i hi) :=
  algEquivCarrierOfBasis (basisOne b i hi) (basisOne_zero b i hi)

/-- Over a local ring, a commutative algebra free of positive rank has a basis whose first
vector is the unit. -/
theorem exists_basis_one_of_isLocalRing [IsLocalRing R] (b : Module.Basis (Fin d) R A) :
    ∃ c : Module.Basis (Fin d) R A, c 0 = 1 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin d, IsUnit (b.repr 1 i) := by
    by_contra! hc
    have hle : Ideal.span (Set.range fun i => b.repr 1 i) ≤ IsLocalRing.maximalIdeal R :=
      Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i =>
        not_not.mp fun h => hc i (IsLocalRing.notMem_maximalIdeal.mp h))
    rw [span_range_repr_one_eq_top b, top_le_iff] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle
  exact ⟨basisOne b i hi, basisOne_zero b i hi⟩

variable (S : Type u) [CommRing S] [Algebra R S]

omit [NeZero d] in
/-- The coordinates of the unit of a base changed algebra, in the base changed basis, are the
images of the coordinates of the unit. -/
theorem baseChange_repr_one (b : Module.Basis (Fin d) R A) (i : Fin d) :
    (b.baseChange S).repr (1 : S ⊗[R] A) i = algebraMap R S (b.repr 1 i) := by
  rw [Algebra.TensorProduct.one_def, Module.Basis.baseChange_repr_tmul]
  exact (Algebra.algebraMap_eq_smul_one _).symm

/-- A basis of the base changed algebra whose first vector is the unit, available as soon as one
coordinate of the unit becomes invertible in the new base. -/
noncomputable def basisOneOfIsUnit (b : Module.Basis (Fin d) R A) (i : Fin d)
    (hi : IsUnit (algebraMap R S (b.repr 1 i))) : Module.Basis (Fin d) S (S ⊗[R] A) :=
  basisOne (b.baseChange S) i (by rwa [baseChange_repr_one])

/-- The first vector of `AlgebraicGeometry.FiniteFreeAlgebra.basisOneOfIsUnit` is the unit. -/
theorem basisOneOfIsUnit_zero (b : Module.Basis (Fin d) R A) (i : Fin d)
    (hi : IsUnit (algebraMap R S (b.repr 1 i))) : basisOneOfIsUnit S b i hi 0 = 1 :=
  basisOne_zero _ i _

/-- The free `d`-dimensional algebra structure over the new base formed by the structure
constants of `AlgebraicGeometry.FiniteFreeAlgebra.basisOneOfIsUnit`. -/
noncomputable def structureOfIsUnit (b : Module.Basis (Fin d) R A) (i : Fin d)
    (hi : IsUnit (algebraMap R S (b.repr 1 i))) : FiniteFreeAlgebra S d :=
  structureOne (b.baseChange S) i (by rwa [baseChange_repr_one])

/-- If one coordinate of the unit becomes invertible in `S`, the base changed algebra `S ⊗[R] A` is
the algebra of a free `d`-dimensional structure over `S`. -/
@[stacks 05YQ "clause (b) of the proof over an affine base: inverting one coordinate of the unit \
presents the algebra as the algebra of a free `d`-dimensional structure"]
noncomputable def algEquivCarrierOfIsUnit (b : Module.Basis (Fin d) R A) (i : Fin d)
    (hi : IsUnit (algebraMap R S (b.repr 1 i))) :
    (S ⊗[R] A) ≃ₐ[S] Carrier (structureOfIsUnit S b i hi) :=
  algEquivCarrierOfBasis (basisOneOfIsUnit S b i hi) (basisOneOfIsUnit_zero S b i hi)

/-- The spectrum of the base changed algebra is the spectrum of a free `d`-dimensional structure,
as a scheme over the spectrum of the new base. -/
noncomputable def specOverIsoSpecCoverOfIsUnit (b : Module.Basis (Fin d) R A) (i : Fin d)
    (hi : IsUnit (algebraMap R S (b.repr 1 i))) :
    specOver S (S ⊗[R] A) ≅ specCover (structureOfIsUnit S b i hi) :=
  specOverIsoSpecCoverOfBasis (basisOneOfIsUnit S b i hi) (basisOneOfIsUnit_zero S b i hi)

omit [NeZero d] in
/-- In the localization of `R` at a coordinate of the unit, that coordinate is invertible. -/
theorem isUnit_algebraMap_localizationAway_repr_one (b : Module.Basis (Fin d) R A) (i : Fin d) :
    IsUnit (algebraMap R (Localization.Away (b.repr 1 i)) (b.repr 1 i)) :=
  IsLocalization.map_units (Localization.Away (b.repr 1 i))
    ⟨b.repr 1 i, Submonoid.mem_powers _⟩

/-- Over each member of the standard open cover of `Spec R` cut out by the coordinates of the unit,
the algebra is the algebra of a free `d`-dimensional structure. -/
@[stacks 05YQ "clause (b) of the proof over an affine base, on the standard open cover cut out \
by the coordinates of the unit"]
theorem exists_structure_algEquiv_localizationAway (b : Module.Basis (Fin d) R A) (i : Fin d) :
    ∃ m : FiniteFreeAlgebra (Localization.Away (b.repr 1 i)) d,
      Nonempty ((Localization.Away (b.repr 1 i) ⊗[R] A) ≃ₐ[Localization.Away (b.repr 1 i)]
        Carrier m) :=
  ⟨_, ⟨algEquivCarrierOfIsUnit _ b i (isUnit_algebraMap_localizationAway_repr_one b i)⟩⟩

end AlgebraicGeometry.FiniteFreeAlgebra

end
