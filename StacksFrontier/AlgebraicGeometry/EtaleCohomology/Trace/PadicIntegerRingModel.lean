module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.IntegralModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsLinearEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficients

/-!
# Models over the ring of integers of representations over a finite extension of `ℚ_ℓ`

Let `E` be a finite extension of `ℚ_ℓ` with a basis `b`, `O_E` its ring of integers and
`σ : G → GL_m(E)` a representation of a compact group whose restriction of scalars `Res_b σ` is
continuous. The `O_E`-span of the image in `E^m` of a `Res_b σ`-stable `ℤ_ℓ`-lattice of `ℚ_ℓ^{md}`
is a `σ`-stable `O_E`-lattice, free of rank `m` because `O_E` is a principal ideal domain. In a
basis of it `σ` has entries in `O_E`: this is a representation `σ' : G → GL_m(O_E)` with the same
traces as `σ`, and restriction of scalars along a `ℤ_ℓ`-basis of `O_E` carries it to a conjugate
of `Res_b σ` by a matrix which also conjugates `Res_b(e · 1_m)` to the restriction of scalars of
`e · 1_m` for every `e ∈ E`.

## Main definitions

All names are in the namespace `Stacks.EtaleCohomology`.

* `modelLattice`: the `σ`-stable `O_E`-lattice of `E^m`.
* `modelRep`: the model `σ' : G → GL_m(O_E)` of `σ`.
* `modelConjMatrix`: the matrix conjugating `Res_b σ` to the restriction of scalars of `σ'`.

## Main results

* `isLattice_padicIntegerRingSpan`: the `O_E`-span of the image of a lattice of `ℚ_ℓ^{md}` is an
  `O_E`-lattice of `E^m`.
* `trace_map_modelRep_pow`: `σ'` has the traces of `σ`.
* `modelConjMatrix_mul_rep`, `modelConjMatrix_mul_scalar`: the conjugation identities.
* `continuous_modelRestrictScalarsRep`: the restriction of scalars of `σ'` is continuous.
-/

@[expose] public noncomputable section

open Module Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

attribute [local instance] padicIntAlgebraOfRat

local notation "𝒪" => integralClosure ℤ_[ℓ] E

section Lattice

variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

omit [IsDomain R] in
/-- The coordinates in the extended basis of a lattice vector are the images of its integral
coordinates. -/
public theorem repr_extendOfIsLattice_coe' {ι : Type*} [Finite ι]
    {L : Submodule R V} [Submodule.IsLattice K L] (c : Basis ι R L) (x : L) (i : ι) :
    (c.extendOfIsLattice K).repr (x : V) i = algebraMap R K (c.repr x i) := by
  classical
  have := Fintype.ofFinite ι
  set bK := c.extendOfIsLattice K
  have hx : (x : V) = ∑ j, (algebraMap R K (c.repr x j)) • bK j := by
    conv_lhs => rw [← c.sum_repr x]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul_of_tower, Basis.extendOfIsLattice_apply, algebraMap_smul]
  rw [hx, ← bK.equivFun_apply, map_sum]
  simp only [map_smul, Basis.equivFun_self, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

end Lattice

variable (ℓ) in
/-- The image in `E^m` of a `ℤ_ℓ`-submodule of `ℚ_ℓ^{md}` along `ℚ_ℓ^{md} ≅ E^m`. -/
public abbrev latticeImage {d : ℕ} (b : Basis (Fin d) ℚ_[ℓ] E) (m : ℕ)
    (L : Submodule ℤ_[ℓ] (Fin (m * d) → ℚ_[ℓ])) : Submodule ℤ_[ℓ] (Fin m → E) :=
  L.map ((restrictScalarsEquiv b m).toLinearMap.restrictScalars ℤ_[ℓ])

/-- The `O_E`-span of a `ℤ_ℓ`-lattice of `E^m`. -/
public abbrev padicIntegerRingSpan {m : ℕ} (L : Submodule ℤ_[ℓ] (Fin m → E)) :
    Submodule 𝒪 (Fin m → E) :=
  Submodule.span 𝒪 (L : Set (Fin m → E))

/-- `E` is the fraction field of `O_E`. -/
public instance isFractionRing_padicIntegerRing : IsFractionRing 𝒪 E :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[ℓ] E

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **The `O_E`-span of the image of a lattice of `ℚ_ℓ^{md}` is an `O_E`-lattice of `E^m`.** -/
public theorem isLattice_padicIntegerRingSpan {d : ℕ} (b : Basis (Fin d) ℚ_[ℓ] E) (m : ℕ)
    (L : Submodule ℤ_[ℓ] (Fin (m * d) → ℚ_[ℓ])) [Submodule.IsLattice ℚ_[ℓ] L] :
    Submodule.IsLattice E (padicIntegerRingSpan (latticeImage ℓ b m L)) where
  fg := by
    classical
    obtain ⟨S, hS⟩ := (Submodule.IsLattice.fg (A := ℚ_[ℓ]) (M := L))
    refine ⟨S.image (restrictScalarsEquiv b m), ?_⟩
    rw [Finset.coe_image, padicIntegerRingSpan, latticeImage, ← hS, Submodule.map_span,
      Submodule.span_span_of_tower]
    rfl
  span_eq_top := by
    have hL := Submodule.IsLattice.span_eq_top (A := ℚ_[ℓ]) (M := L)
    refine eq_top_iff.2 fun v _ => ?_
    have hv : v ∈ Submodule.span ℚ_[ℓ] ((latticeImage ℓ b m L : Submodule ℤ_[ℓ] (Fin m → E)) :
        Set (Fin m → E)) := by
      have h := Submodule.map_span (restrictScalarsEquiv b m).toLinearMap (L : Set _)
      rw [hL, Submodule.map_top, LinearEquiv.range] at h
      rw [latticeImage, Submodule.map_coe]
      exact h ▸ Submodule.mem_top
    exact Submodule.span_le_restrictScalars ℚ_[ℓ] E _
      (Submodule.span_mono Submodule.subset_span hv)

section Model

variable {G : Type*} [Group G] [TopologicalSpace G] {d m : ℕ} (b : Basis (Fin d) ℚ_[ℓ] E)
  (σ : G →* GL (Fin m) E)

/-- **The `σ`-stable `O_E`-lattice**: the `O_E`-span of the image of the `Res_b σ`-stable
lattice. -/
public abbrev modelLattice : Submodule 𝒪 (Fin m → E) :=
  padicIntegerRingSpan (latticeImage ℓ b m (stableLattice (restrictScalarsRep b σ)))

omit [FiniteDimensional ℚ_[ℓ] E] [TopologicalSpace G] in
/-- `σ` stabilises the model lattice. -/
public theorem mulVec_mem_modelLattice (g : G) {v : Fin m → E} (hv : v ∈ modelLattice b σ) :
    (σ g).val *ᵥ v ∈ modelLattice b σ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨u, hu, rfl⟩ := hv
      refine Submodule.subset_span ⟨(restrictScalarsRep b σ g).val *ᵥ u,
        mulVec_mem_stableLattice _ g hu, ?_⟩
      show restrictScalarsEquiv b m (restrictScalarsMatrix b (σ g).val *ᵥ u) = _
      rw [restrictScalarsEquiv_mulVec]
      rfl
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add v w _ _ hv hw => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hv hw
  | smul a v _ hv =>
      have h : (σ g).val *ᵥ (a • v) = a • ((σ g).val *ᵥ v) := by
        show (σ g).val *ᵥ ((a : E) • v) = (a : E) • ((σ g).val *ᵥ v)
        rw [Matrix.mulVec_smul]
      rw [h]
      exact Submodule.smul_mem _ a hv

variable [IsTopologicalGroup G] [CompactSpace G]

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- The model lattice is an `O_E`-lattice of `E^m`. -/
public theorem isLattice_modelLattice (hσ : Continuous (restrictScalarsRep b σ)) :
    Submodule.IsLattice E (modelLattice b σ) :=
  have := isLattice_stableLattice (restrictScalarsRep b σ) hσ
  isLattice_padicIntegerRingSpan b m _

/-- The model lattice is free of rank `m`. -/
public theorem finrank_modelLattice (hσ : Continuous (restrictScalarsRep b σ)) :
    haveI := isPrincipalIdealRing_padicIntegerRing ℓ E
    haveI := isLattice_modelLattice b σ hσ
    Module.finrank 𝒪 (modelLattice b σ) = m := by
  have := isPrincipalIdealRing_padicIntegerRing ℓ E
  have := isLattice_modelLattice b σ hσ
  rw [Submodule.IsLattice.finrank_of_pi E, Fintype.card_fin]

/-- **A basis of the model lattice.** -/
public def modelBasis (hσ : Continuous (restrictScalarsRep b σ)) :
    Basis (Fin m) 𝒪 (modelLattice b σ) :=
  haveI := isPrincipalIdealRing_padicIntegerRing ℓ E
  haveI := isLattice_modelLattice b σ hσ
  haveI : Module.Finite 𝒪 (modelLattice b σ) :=
    Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (A := E))
  Module.finBasisOfFinrankEq _ _ (finrank_modelLattice b σ hσ)

/-- The basis of the model lattice, as a basis of `E^m`. -/
public def modelBasisE (hσ : Continuous (restrictScalarsRep b σ)) : Basis (Fin m) E (Fin m → E) :=
  haveI := isLattice_modelLattice b σ hσ
  (modelBasis b σ hσ).extendOfIsLattice E

/-- The vectors of `modelBasisE` are those of the basis of the model lattice. -/
public theorem modelBasisE_apply (hσ : Continuous (restrictScalarsRep b σ)) (i : Fin m) :
    modelBasisE b σ hσ i = (modelBasis b σ hσ i : Fin m → E) := by
  have := isLattice_modelLattice b σ hσ
  exact Basis.extendOfIsLattice_apply _ _ _

/-- The matrix of `σ(g)` in the basis of the model lattice, with entries in `O_E`. -/
public def modelMatrix (hσ : Continuous (restrictScalarsRep b σ)) (g : G) :
    Matrix (Fin m) (Fin m) 𝒪 :=
  Matrix.of fun i j => (modelBasis b σ hσ).repr ⟨(σ g).val *ᵥ (modelBasis b σ hσ j : Fin m → E),
    mulVec_mem_modelLattice b σ g (modelBasis b σ hσ j).2⟩ i

/-- The model matrix is the matrix of `σ(g)` in the extended basis. -/
public theorem map_modelMatrix (hσ : Continuous (restrictScalarsRep b σ)) (g : G) :
    (modelMatrix b σ hσ g).map (algebraMap 𝒪 E) =
      LinearMap.toMatrix (modelBasisE b σ hσ) (modelBasisE b σ hσ) (Matrix.toLin' (σ g).val) := by
  have := isLattice_modelLattice b σ hσ
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, Matrix.toLin'_apply, modelBasisE_apply]
  exact (repr_extendOfIsLattice_coe' (modelBasis b σ hσ) _ i).symm

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- Matrices over `O_E` are determined by their images over `E`. -/
public theorem map_algebraMap_padicIntegerRing_injective {n : Type*} :
    Function.Injective fun M : Matrix n n 𝒪 => M.map (algebraMap 𝒪 E) :=
  fun _ _ h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)

/-- **The model of `σ` with coefficients in `O_E`.** -/
public def modelRep (hσ : Continuous (restrictScalarsRep b σ)) : G →* GL (Fin m) 𝒪 :=
  MonoidHom.toHomUnits
    { toFun := modelMatrix b σ hσ
      map_one' := by
        apply map_algebraMap_padicIntegerRing_injective
        change (modelMatrix b σ hσ 1).map (algebraMap 𝒪 E) = (1 : Matrix (Fin m) (Fin m) 𝒪).map
          (algebraMap 𝒪 E)
        rw [map_modelMatrix, map_one, Units.val_one, Matrix.toLin'_one, LinearMap.toMatrix_id,
          Matrix.map_one _ (map_zero _) (map_one _)]
      map_mul' := fun g h => by
        apply map_algebraMap_padicIntegerRing_injective
        change (modelMatrix b σ hσ (g * h)).map (algebraMap 𝒪 E) =
          (modelMatrix b σ hσ g * modelMatrix b σ hσ h).map (algebraMap 𝒪 E)
        rw [Matrix.map_mul, map_modelMatrix, map_modelMatrix, map_modelMatrix, map_mul,
          Units.val_mul, Matrix.toLin'_mul, LinearMap.toMatrix_comp (modelBasisE b σ hσ)
          (modelBasisE b σ hσ) (modelBasisE b σ hσ)] }

/-- The image over `E` of `σ'(g)` is the matrix of `σ(g)` in the basis of the model lattice. -/
public theorem map_modelRep (hσ : Continuous (restrictScalarsRep b σ)) (g : G) :
    (modelRep b σ hσ g).val.map (algebraMap 𝒪 E) =
      LinearMap.toMatrix (modelBasisE b σ hσ) (modelBasisE b σ hσ) (Matrix.toLin' (σ g).val) :=
  map_modelMatrix b σ hσ g

/-- **The model of `σ` has the traces of `σ`.** -/
public theorem trace_map_modelRep_pow (hσ : Continuous (restrictScalarsRep b σ)) (g : G) (n : ℕ) :
    (((modelRep b σ hσ g).val ^ n).map (algebraMap 𝒪 E)).trace = ((σ g).val ^ n).trace := by
  rw [← Units.val_pow_eq_pow_val, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, map_modelRep,
    ← LinearMap.trace_eq_matrix_trace, Matrix.trace_toLin'_eq]

end Model

section Basis

variable {d : ℕ} (b : Basis (Fin d) ℚ_[ℓ] E)

omit [FiniteDimensional ℚ_[ℓ] E] in
include b in
/-- The dimension of `E` over `ℚ_ℓ` is the size of the basis `b`. -/
public theorem finrank_eq_of_basis : Module.finrank ℚ_[ℓ] E = d := by
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

/-- A `ℤ_ℓ`-basis of `O_E` indexed like `b`. -/
public def padicIntegerRingBasisOf : Basis (Fin d) ℤ_[ℓ] 𝒪 :=
  (padicIntegerRingBasis ℓ E).reindex (finCongr (finrank_eq_of_basis b))

/-- The basis of `O_E` indexed like `b`, as a `ℚ_ℓ`-basis of `E`. -/
public def padicIntegerRingBasisRatOf : Basis (Fin d) ℚ_[ℓ] E :=
  (padicIntegerRingBasisRat ℓ E).reindex (finCongr (finrank_eq_of_basis b))

/-- The `ℚ_ℓ`-basis of `E` consists of the elements of the `ℤ_ℓ`-basis of `O_E`. -/
public theorem padicIntegerRingBasisRatOf_apply (i : Fin d) :
    padicIntegerRingBasisRatOf b i = (padicIntegerRingBasisOf b i : E) := by
  rw [padicIntegerRingBasisRatOf, padicIntegerRingBasisOf, Basis.reindex_apply,
    Basis.reindex_apply, padicIntegerRingBasisRat_apply]

/-- The coordinates of an element of `O_E` in the `ℚ_ℓ`-basis of `E` are its coordinates in the
`ℤ_ℓ`-basis of `O_E`. -/
public theorem padicIntegerRingBasisRatOf_repr (x : 𝒪) (i : Fin d) :
    (padicIntegerRingBasisRatOf b).repr (x : E) i =
      ((padicIntegerRingBasisOf b).repr x i : ℚ_[ℓ]) := by
  rw [padicIntegerRingBasisRatOf, padicIntegerRingBasisOf, Basis.repr_reindex_apply,
    Basis.repr_reindex_apply, padicIntegerRingBasisRat_repr]

/-- **Restriction of scalars of an `O_E`-matrix along the basis of `O_E`, over `ℚ_ℓ`**: restricting
scalars of its image over `E` gives the image over `ℚ_ℓ` of its restriction of scalars to `ℤ_ℓ`. -/
public theorem restrictScalarsMatrix_map_padicIntegerRing {m : ℕ} (M : Matrix (Fin m) (Fin m) 𝒪) :
    restrictScalarsMatrix (padicIntegerRingBasisRatOf b) (M.map (algebraMap 𝒪 E)) =
      (coefficientMatrixRingHom (padicIntegerRingBasisOf b) m M).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
  ext p q
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [restrictScalarsMatrix_apply, Matrix.map_apply, Matrix.map_apply,
    coefficientMatrixRingHom_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, padicIntegerRingBasisRatOf_apply]
  show (padicIntegerRingBasisRatOf b).repr ((M i j * padicIntegerRingBasisOf b l' : 𝒪) : E) l = _
  rw [padicIntegerRingBasisRatOf_repr]
  rfl

end Basis


section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {d m : ℕ} (b : Basis (Fin d) ℚ_[ℓ] E) (σ : G →* GL (Fin m) E)
  (hσ : Continuous (restrictScalarsRep b σ))

/-- The restriction of scalars of the model of `σ` along the basis of `O_E`. -/
public abbrev modelRestrictScalarsRep : G →* GL (Fin (m * d)) ℤ_[ℓ] :=
  (Units.map (coefficientMatrixRingHom (padicIntegerRingBasisOf b) m).toMonoidHom).comp
    (modelRep b σ hσ)

/-- **`ℚ_ℓ^{md} ≅ E^m ≅ E^m ≅ ℚ_ℓ^{md}`** through the basis of the model lattice. -/
public def modelEquiv : (Fin (m * d) → ℚ_[ℓ]) ≃ₗ[ℚ_[ℓ]] (Fin (m * d) → ℚ_[ℓ]) :=
  ((restrictScalarsEquiv b m).trans ((modelBasisE b σ hσ).equivFun.restrictScalars ℚ_[ℓ])).trans
    (restrictScalarsEquiv (padicIntegerRingBasisRatOf b) m).symm

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- The inverse of `ℚ_ℓ^{md} ≅ E^m` intertwines a matrix `N` over `E` with its restriction of
scalars. -/
theorem restrictScalarsEquiv_symm_mulVec {d' : ℕ} (b' : Basis (Fin d') ℚ_[ℓ] E)
    (N : Matrix (Fin m) (Fin m) E) (y : Fin m → E) :
    (restrictScalarsEquiv b' m).symm (N *ᵥ y) =
      restrictScalarsMatrix b' N *ᵥ (restrictScalarsEquiv b' m).symm y := by
  apply (restrictScalarsEquiv b' m).injective
  rw [LinearEquiv.apply_symm_apply, restrictScalarsEquiv_mulVec, LinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- The scalar matrix `e · 1_m` acts on `E^m` as multiplication by `e`. -/
theorem padicModel_scalar_mulVec_eq_smul (e : E) (v : Fin m → E) :
    Matrix.scalar (Fin m) e *ᵥ v = e • v := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]

/-- **The identification carries `Res_b σ` to the restriction of scalars of the model.** -/
public theorem modelEquiv_mulVec_rep (g : G) (w : Fin (m * d) → ℚ_[ℓ]) :
    modelEquiv b σ hσ ((restrictScalarsRep b σ g).val *ᵥ w) =
      ((modelRestrictScalarsRep b σ hσ g).val.map (algebraMap ℤ_[ℓ] ℚ_[ℓ])) *ᵥ
        modelEquiv b σ hσ w := by
  have h1 : restrictScalarsEquiv b m ((restrictScalarsRep b σ g).val *ᵥ w) =
      (σ g).val *ᵥ restrictScalarsEquiv b m w := restrictScalarsEquiv_mulVec b _ w
  have h2 : ∀ x, (modelBasisE b σ hσ).equivFun ((σ g).val *ᵥ x) =
      ((modelRep b σ hσ g).val.map (algebraMap 𝒪 E)) *ᵥ (modelBasisE b σ hσ).equivFun x := by
    intro x
    rw [map_modelRep, Basis.equivFun_apply, Basis.equivFun_apply, ← Matrix.toLin'_apply,
      LinearMap.toMatrix_mulVec_repr]
  show (restrictScalarsEquiv (padicIntegerRingBasisRatOf b) m).symm
      ((modelBasisE b σ hσ).equivFun (restrictScalarsEquiv b m
        ((restrictScalarsRep b σ g).val *ᵥ w))) = _
  rw [h1, h2, restrictScalarsEquiv_symm_mulVec, restrictScalarsMatrix_map_padicIntegerRing]
  rfl

/-- **The identification carries `Res_b(e · 1_m)` to the restriction of scalars of `e · 1_m`
along the basis of `O_E`.** -/
public theorem modelEquiv_mulVec_scalar (e : E) (w : Fin (m * d) → ℚ_[ℓ]) :
    modelEquiv b σ hσ (restrictScalarsMatrix b (Matrix.scalar (Fin m) e) *ᵥ w) =
      restrictScalarsMatrix (padicIntegerRingBasisRatOf b) (Matrix.scalar (Fin m) e) *ᵥ
        modelEquiv b σ hσ w := by
  show (restrictScalarsEquiv (padicIntegerRingBasisRatOf b) m).symm
      ((modelBasisE b σ hσ).equivFun (restrictScalarsEquiv b m
        (restrictScalarsMatrix b (Matrix.scalar (Fin m) e) *ᵥ w))) = _
  rw [restrictScalarsEquiv_mulVec, padicModel_scalar_mulVec_eq_smul, map_smul,
    ← padicModel_scalar_mulVec_eq_smul, restrictScalarsEquiv_symm_mulVec]
  rfl

/-- The matrix of the identification. -/
public abbrev modelConjMatrix : Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ] :=
  LinearMap.toMatrix' (modelEquiv b σ hσ).toLinearMap

/-- The matrix of the inverse identification. -/
public abbrev modelConjMatrixInv : Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ] :=
  LinearMap.toMatrix' (modelEquiv b σ hσ).symm.toLinearMap

/-- The matrix of the inverse identification is a left inverse. -/
public theorem modelConjMatrixInv_mul : modelConjMatrixInv b σ hσ * modelConjMatrix b σ hσ = 1 := by
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  exact LinearMap.ext fun w => (modelEquiv b σ hσ).symm_apply_apply w

/-- The matrix of the inverse identification is a right inverse. -/
public theorem modelConjMatrix_mul_inv :
    modelConjMatrix b σ hσ * modelConjMatrixInv b σ hσ = 1 := by
  exact mul_eq_one_comm.1 (modelConjMatrixInv_mul b σ hσ)

/-- If the identification intertwines `A` with `B`, then `modelConjMatrix` conjugates them. -/
private theorem modelConjMatrix_mul_eq_of_mulVec (A B : Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ])
    (h : ∀ w, modelEquiv b σ hσ (A *ᵥ w) = B *ᵥ modelEquiv b σ hσ w) :
    modelConjMatrix b σ hσ * A = B * modelConjMatrix b σ hσ := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  exact LinearMap.ext h

/-- **The model is conjugate to `Res_b σ`**: `T Res_b σ(g) = Res(σ'(g)) T`. -/
public theorem modelConjMatrix_mul_rep (g : G) :
    modelConjMatrix b σ hσ * (restrictScalarsRep b σ g).val =
      (modelRestrictScalarsRep b σ hσ g).val.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) *
        modelConjMatrix b σ hσ := by
  exact modelConjMatrix_mul_eq_of_mulVec b σ hσ _ _ (modelEquiv_mulVec_rep b σ hσ g)

/-- **The conjugation carries `Res_b(e · 1_m)` to the restriction of scalars of `e · 1_m`.** -/
public theorem modelConjMatrix_mul_scalar (e : E) :
    modelConjMatrix b σ hσ * restrictScalarsMatrix b (Matrix.scalar (Fin m) e) =
      restrictScalarsMatrix (padicIntegerRingBasisRatOf b) (Matrix.scalar (Fin m) e) *
        modelConjMatrix b σ hσ := by
  exact modelConjMatrix_mul_eq_of_mulVec b σ hσ _ _ (modelEquiv_mulVec_scalar b σ hσ e)

/-- **The restriction of scalars of the model of `σ` is continuous.** -/
public theorem continuous_modelRestrictScalarsRep :
    Continuous (modelRestrictScalarsRep b σ hσ) := by
  have hconj : ∀ g, (modelRestrictScalarsRep b σ hσ g).val.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) =
      modelConjMatrix b σ hσ * (restrictScalarsRep b σ g).val * modelConjMatrixInv b σ hσ := by
    intro g
    rw [modelConjMatrix_mul_rep, Matrix.mul_assoc, modelConjMatrix_mul_inv, Matrix.mul_one]
  have hR : Continuous fun g => (restrictScalarsRep b σ g).val := Units.continuous_val.comp hσ
  have hemb : Topology.IsEmbedding ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) := isometry_subtype_coe.isEmbedding
  have hval : Continuous fun g => (modelRestrictScalarsRep b σ hσ g).val := by
    refine continuous_matrix fun p q => hemb.continuous_iff.2 ?_
    have h := ((continuous_const.matrix_mul hR).matrix_mul continuous_const).matrix_elem p q
      (A := fun g => modelConjMatrix b σ hσ * (restrictScalarsRep b σ g).val *
        modelConjMatrixInv b σ hσ)
    refine h.congr fun g => ?_
    rw [← hconj]
    rfl
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have h := hval.comp continuous_inv
  refine h.congr fun g => ?_
  simp only [Function.comp_apply, map_inv]

end Conj

end Stacks.EtaleCohomology

end
