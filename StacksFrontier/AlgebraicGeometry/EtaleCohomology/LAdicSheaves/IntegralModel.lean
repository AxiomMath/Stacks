module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Instances.Matrix

/-!
# Integral models of continuous `ℓ`-adic representations of compact groups

A continuous representation `ρ : G → GL_r(ℚ_ℓ)` of a compact group stabilises a `ℤ_ℓ`-lattice
in `ℚ_ℓ^r`, so after a change of basis it takes values in `GL_r(ℤ_ℓ)`.  This is the first step
of the passage from a continuous representation of `π₁(X, x̄)` to the lisse sheaf `ℱ_ρ` of the
notation preceding [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): the reductions of the
integral model modulo `ℓ^{n+1}` are the finite continuous `π₁`-modules whose locally constant
sheaves are the levels of `ℱ_ρ`.

## Main definitions

* `Stacks.EtaleCohomology.integralStabiliser`: the open subgroup of `G` of elements `g` for
  which `ρ g` and its inverse have integral entries.
* `Stacks.EtaleCohomology.stableLattice`: the `ℤ_ℓ`-span of the translates `ρ(g) ℤ_ℓ^r`.
* `Stacks.EtaleCohomology.integralLift`: a representation into `GL_r(ℚ_ℓ)` with integral
  values, as one into `GL_r(ℤ_ℓ)`.
* `Stacks.EtaleCohomology.integralModel`: a continuous `G →* GL_r(ℤ_ℓ)` conjugate over `ℚ_ℓ`
  to `ρ`.

## Main results

* `Stacks.EtaleCohomology.isLattice_stableLattice`: the stable lattice is a lattice; it is
  finitely generated because the integral stabiliser has finite index.
* `Stacks.EtaleCohomology.exists_conj_integral`: some conjugate of `ρ` by `GL_r(ℚ_ℓ)` has
  integral entries everywhere.
* `Stacks.EtaleCohomology.map_integralModel`: the integral model is that conjugate.
* `Stacks.EtaleCohomology.continuous_integralModel`: the integral model is continuous.
* `Stacks.EtaleCohomology.charpoly_integralModel`: it has the characteristic polynomials of `ρ`,
  so the Frobenius data of the conjecture preceding Tag 03VH is unchanged.
-/

@[expose] public noncomputable section

open Matrix Module

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

/-- The standard lattice `ℤ_ℓ^r ⊆ ℚ_ℓ^r`. -/
public abbrev standardLattice (ℓ r : ℕ) [Fact ℓ.Prime] : Submodule ℤ_[ℓ] (Fin r → ℚ_[ℓ]) :=
  Submodule.span ℤ_[ℓ] (Set.range (Pi.basisFun ℚ_[ℓ] (Fin r)))

/-- A vector lies in the standard lattice exactly when its coordinates are integral. -/
public theorem mem_standardLattice_iff {v : Fin r → ℚ_[ℓ]} :
    v ∈ standardLattice ℓ r ↔ ∀ i, ‖v i‖ ≤ 1 := by
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      by_cases h : i = j <;> simp [h]
    | zero => simp
    | add x y _ _ hx hy =>
      intro i
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) (hy i))
    | smul a x _ hx =>
      intro i
      rw [Pi.smul_apply, Algebra.smul_def, PadicInt.algebraMap_apply, norm_mul]
      exact mul_le_one₀ a.norm_le_one (norm_nonneg _) (hx i)
  · obtain ⟨a, ha⟩ : ∃ a : Fin r → ℤ_[ℓ], ∀ i, (a i : ℚ_[ℓ]) = v i :=
      ⟨fun i => ⟨v i, hv i⟩, fun i => rfl⟩
    have : v = ∑ i, a i • Pi.basisFun ℚ_[ℓ] (Fin r) i := by
      ext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp [Algebra.smul_def, ha]
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The set of matrices with integral entries. -/
public def IsIntegralMatrix (A : Matrix (Fin r) (Fin r) ℚ_[ℓ]) : Prop := ∀ i j, ‖A i j‖ ≤ 1

/-- A matrix is integral exactly when it maps the standard lattice into itself. -/
public theorem isIntegralMatrix_iff_mulVec {A : Matrix (Fin r) (Fin r) ℚ_[ℓ]} :
    IsIntegralMatrix A ↔ ∀ v ∈ standardLattice ℓ r, A *ᵥ v ∈ standardLattice ℓ r := by
  refine ⟨fun hA v hv => ?_, fun h i j => ?_⟩
  · rw [mem_standardLattice_iff] at hv ⊢
    intro i
    rw [Matrix.mulVec, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hA i j) (norm_nonneg _) (hv j)
  · have hj := h (Pi.single j 1) (mem_standardLattice_iff.2 fun k => by
      by_cases hk : k = j <;> simp [hk])
    rw [mem_standardLattice_iff] at hj
    simpa [Matrix.mulVec_single] using hj i

/-- Integral matrices are closed under multiplication. -/
public theorem IsIntegralMatrix.mul {A B : Matrix (Fin r) (Fin r) ℚ_[ℓ]}
    (hA : IsIntegralMatrix A) (hB : IsIntegralMatrix B) : IsIntegralMatrix (A * B) := by
  rw [isIntegralMatrix_iff_mulVec] at hA hB ⊢
  intro v hv
  rw [← Matrix.mulVec_mulVec]
  exact hA _ (hB v hv)

/-- The identity matrix is integral. -/
public theorem isIntegralMatrix_one : IsIntegralMatrix (1 : Matrix (Fin r) (Fin r) ℚ_[ℓ]) := by
  rw [isIntegralMatrix_iff_mulVec]
  intro v hv
  simpa using hv

variable {G : Type*} [Group G] [TopologicalSpace G] (ρ : G →* GL (Fin r) ℚ_[ℓ])

/-- The integral stabiliser: the subgroup of `g` with `ρ g` and `ρ g⁻¹` integral. -/
public def integralStabiliser : Subgroup G where
  carrier := {g | IsIntegralMatrix (ρ g).val ∧ IsIntegralMatrix (ρ g)⁻¹.val}
  one_mem' := by simp [isIntegralMatrix_one]
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · rw [map_mul, Units.val_mul]
      exact ha.1.mul hb.1
    · rw [map_mul, _root_.mul_inv_rev, Units.val_mul]
      exact hb.2.mul ha.2
  inv_mem' {a} ha := by
    refine ⟨?_, ?_⟩
    · rw [map_inv]; exact ha.2
    · rw [map_inv, inv_inv]; exact ha.1

/-- The integral stabiliser of a continuous representation is open. -/
public theorem isOpen_integralStabiliser (hρ : Continuous ρ) :
    IsOpen (integralStabiliser ρ : Set G) := by
  have hball : IsOpen {x : ℚ_[ℓ] | ‖x‖ ≤ 1} := by
    simpa [Metric.closedBall, dist_zero_right] using
      IsUltrametricDist.isOpen_closedBall (0 : ℚ_[ℓ]) one_ne_zero
  have h1 : Continuous fun g => (ρ g).val := Units.continuous_val.comp hρ
  have h2 : Continuous fun g => (ρ g)⁻¹.val := Units.continuous_coe_inv.comp hρ
  have : (integralStabiliser ρ : Set G) =
      (⋂ i, ⋂ j, (fun g => (ρ g).val i j) ⁻¹' {x | ‖x‖ ≤ 1}) ∩
        ⋂ i, ⋂ j, (fun g => (ρ g)⁻¹.val i j) ⁻¹' {x | ‖x‖ ≤ 1} := by
    ext g
    simp [integralStabiliser, IsIntegralMatrix]
  rw [this]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact hball.preimage (h1.matrix_elem i j)
  · exact hball.preimage (h2.matrix_elem i j)

/-- The `ℤ_ℓ`-linear map `ℚ_ℓ^r → ℚ_ℓ^r` given by `ρ g`. -/
public abbrev reprLinear (g : G) : (Fin r → ℚ_[ℓ]) →ₗ[ℤ_[ℓ]] (Fin r → ℚ_[ℓ]) :=
  ((ρ g).val.mulVecLin).restrictScalars ℤ_[ℓ]

/-- The stable lattice: the `ℤ_ℓ`-span of all the translates `ρ(g) ℤ_ℓ^r`. -/
public def stableLattice : Submodule ℤ_[ℓ] (Fin r → ℚ_[ℓ]) :=
  ⨆ g, (standardLattice ℓ r).map (reprLinear ρ g)

/-- `reprLinear` turns products into compositions. -/
private theorem reprLinear_mul {H : Type*} [Group H] (ρ : H →* GL (Fin r) ℚ_[ℓ]) (g h : H) :
    reprLinear ρ (g * h) = (reprLinear ρ g).comp (reprLinear ρ h) := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  rw [← Units.val_mul, ← map_mul]

omit [TopologicalSpace G] in
/-- The stable lattice is stable under `ρ`. -/
public theorem mulVec_mem_stableLattice (g : G) {v : Fin r → ℚ_[ℓ]}
    (hv : v ∈ stableLattice ρ) : (ρ g).val *ᵥ v ∈ stableLattice ρ := by
  have : (stableLattice ρ).map (reprLinear ρ g) ≤ stableLattice ρ := by
    rw [stableLattice, Submodule.map_iSup]
    refine iSup_le fun h => ?_
    rw [← Submodule.map_comp, ← reprLinear_mul]
    exact le_iSup (fun g => (standardLattice ℓ r).map (reprLinear ρ g)) (g * h)
  exact this ⟨v, hv, rfl⟩

omit [TopologicalSpace G] in
/-- The standard lattice lies in the stable lattice. -/
public theorem standardLattice_le_stableLattice : standardLattice ℓ r ≤ stableLattice ρ := by
  intro v hv
  refine (le_iSup (fun g => (standardLattice ℓ r).map (reprLinear ρ g)) 1) ⟨v, hv, ?_⟩
  simp

/-- **The stable lattice is a lattice.**  It is finitely generated: it is the finite sum of the
translates by representatives of the cosets of the open, hence finite-index, integral
stabiliser, each of which is finitely generated; and it contains `ℤ_ℓ^r`, which spans. -/
public theorem isLattice_stableLattice [IsTopologicalGroup G] [CompactSpace G]
    (hρ : Continuous ρ) : Submodule.IsLattice ℚ_[ℓ] (stableLattice ρ) where
  fg := by
    have hfin : Finite (G ⧸ integralStabiliser ρ) :=
      Subgroup.quotient_finite_of_isOpen _ (isOpen_integralStabiliser ρ hρ)
    have hle : stableLattice ρ ≤
        ⨆ q : G ⧸ integralStabiliser ρ, (standardLattice ℓ r).map (reprLinear ρ q.out) := by
      refine iSup_le fun g => ?_
      set q : G ⧸ integralStabiliser ρ := QuotientGroup.mk g
      have hmem : q.out⁻¹ * g ∈ integralStabiliser ρ := by
        rw [← QuotientGroup.eq]
        exact q.out_eq
      have hg : g = q.out * (q.out⁻¹ * g) := by group
      have hsub : (standardLattice ℓ r).map (reprLinear ρ (q.out⁻¹ * g)) ≤
          standardLattice ℓ r := by
        rintro _ ⟨v, hv, rfl⟩
        exact (isIntegralMatrix_iff_mulVec.1 hmem.1) v hv
      refine le_trans ?_ (le_iSup _ q)
      rw [hg, reprLinear_mul, Submodule.map_comp]
      exact Submodule.map_mono hsub
    refine Submodule.FG.of_le (Submodule.fg_iSup _ fun q => ?_) hle
    exact (Submodule.fg_span (Set.finite_range _)).map _
  span_eq_top := by
    refine eq_top_iff.2 (le_trans ?_ (Submodule.span_mono (standardLattice_le_stableLattice ρ)))
    rw [Submodule.span_span_of_tower, (Pi.basisFun ℚ_[ℓ] (Fin r)).span_eq]

/-- The coordinates in the extended basis of a lattice vector are the images of its integral
coordinates. -/
public theorem repr_extendOfIsLattice_coe {L : Submodule ℤ_[ℓ] (Fin r → ℚ_[ℓ])}
    [Submodule.IsLattice ℚ_[ℓ] L] (b : Basis (Fin r) ℤ_[ℓ] L) (m : L) (i : Fin r) :
    (b.extendOfIsLattice ℚ_[ℓ]).repr (m : Fin r → ℚ_[ℓ]) i = (b.repr m i : ℚ_[ℓ]) := by
  set bK := b.extendOfIsLattice ℚ_[ℓ]
  have hm : (m : Fin r → ℚ_[ℓ]) = ∑ j, ((b.repr m j : ℤ_[ℓ]) : ℚ_[ℓ]) • bK j := by
    conv_lhs => rw [← b.sum_repr m]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul_of_tower, Basis.extendOfIsLattice_apply, ← PadicInt.algebraMap_apply,
      algebraMap_smul]
  rw [hm, ← bK.equivFun_apply, map_sum]
  simp only [map_smul, Basis.equivFun_self, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

/-- **Integral conjugates.**  A continuous representation `ρ : G → GL_r(ℚ_ℓ)` of a compact
group is conjugate, by some `P ∈ GL_r(ℚ_ℓ)`, to one with integral entries: take for the columns
of `P` a `ℤ_ℓ`-basis of the stable lattice, which is free of rank `r` because `ℤ_ℓ` is a
principal ideal domain. -/
public theorem exists_conj_integral [IsTopologicalGroup G] [CompactSpace G] (hρ : Continuous ρ) :
    ∃ P : GL (Fin r) ℚ_[ℓ], ∀ g, IsIntegralMatrix (P⁻¹ * ρ g * P).val := by
  have := isLattice_stableLattice ρ hρ
  have hrank : finrank ℤ_[ℓ] (stableLattice ρ) = r := by
    rw [Submodule.IsLattice.finrank_of_pi ℚ_[ℓ], Fintype.card_fin]
  let b : Basis (Fin r) ℤ_[ℓ] (stableLattice ρ) := Module.finBasisOfFinrankEq _ _ hrank
  let bK := b.extendOfIsLattice ℚ_[ℓ]
  let e := Pi.basisFun ℚ_[ℓ] (Fin r)
  let P : GL (Fin r) ℚ_[ℓ] :=
    ⟨e.toMatrix bK, bK.toMatrix e, Basis.toMatrix_mul_toMatrix_flip _ _,
      Basis.toMatrix_mul_toMatrix_flip _ _⟩
  refine ⟨P, fun g i j => ?_⟩
  have hconj : (P⁻¹ * ρ g * P).val =
      LinearMap.toMatrix bK bK (Matrix.toLin' (ρ g).val) := by
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bK e bK e,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    rfl
  rw [hconj, LinearMap.toMatrix_apply, Matrix.toLin'_apply, Basis.extendOfIsLattice_apply]
  have hmem : (ρ g).val *ᵥ (b j : Fin r → ℚ_[ℓ]) ∈ stableLattice ρ :=
    mulVec_mem_stableLattice ρ g (b j).2
  have := repr_extendOfIsLattice_coe b ⟨_, hmem⟩ i
  simp only at this
  rw [this]
  exact (b.repr ⟨_, hmem⟩ i).norm_le_one

/-- The lift to `ℤ_ℓ` of a matrix with integral entries. -/
public def IsIntegralMatrix.lift {A : Matrix (Fin r) (Fin r) ℚ_[ℓ]} (hA : IsIntegralMatrix A) :
    Matrix (Fin r) (Fin r) ℤ_[ℓ] :=
  Matrix.of fun i j => ⟨A i j, hA i j⟩

/-- Mapping the lift of an integral matrix back to `ℚ_ℓ` recovers the matrix. -/
@[simp]
public theorem IsIntegralMatrix.mapMatrix_lift {A : Matrix (Fin r) (Fin r) ℚ_[ℓ]}
    (hA : IsIntegralMatrix A) : (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix hA.lift = A := by
  ext i j
  rfl

/-- Mapping integral matrices to `ℚ_ℓ` is injective. -/
public theorem mapMatrix_padicInt_injective :
    Function.Injective ((PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (m := Fin r)) :=
  Matrix.map_injective fun _ _ => PadicInt.ext

/-- The lift of a product of integral matrices is the product of the lifts. -/
public theorem IsIntegralMatrix.lift_mul {A B : Matrix (Fin r) (Fin r) ℚ_[ℓ]}
    (hA : IsIntegralMatrix A) (hB : IsIntegralMatrix B) (hAB : IsIntegralMatrix (A * B)) :
    hAB.lift = hA.lift * hB.lift := by
  apply mapMatrix_padicInt_injective
  simp only [map_mul, IsIntegralMatrix.mapMatrix_lift]

/-- The lift of the identity matrix is the identity. -/
public theorem IsIntegralMatrix.lift_one
    (h : IsIntegralMatrix (1 : Matrix (Fin r) (Fin r) ℚ_[ℓ])) : h.lift = 1 := by
  apply mapMatrix_padicInt_injective
  rw [map_one, IsIntegralMatrix.mapMatrix_lift]

/-- The unit of `GL_r(ℤ_ℓ)` lifting an integral value `σ g` of a representation. -/
public def integralLiftUnit (σ : G →* GL (Fin r) ℚ_[ℓ]) (hσ : ∀ g, IsIntegralMatrix (σ g).val)
    (g : G) : GL (Fin r) ℤ_[ℓ] :=
  ⟨(hσ g).lift, (hσ g⁻¹).lift,
    by
      apply mapMatrix_padicInt_injective
      rw [map_mul, IsIntegralMatrix.mapMatrix_lift, IsIntegralMatrix.mapMatrix_lift, map_one,
        ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one],
    by
      apply mapMatrix_padicInt_injective
      rw [map_mul, IsIntegralMatrix.mapMatrix_lift, IsIntegralMatrix.mapMatrix_lift, map_one,
        ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]⟩

omit [TopologicalSpace G] in
/-- Over `ℚ_ℓ` the unit `integralLiftUnit σ hσ g` is `σ g`. -/
public theorem mapMatrix_integralLiftUnit (σ : G →* GL (Fin r) ℚ_[ℓ])
    (hσ : ∀ g, IsIntegralMatrix (σ g).val) (g : G) :
    (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralLiftUnit σ hσ g).val = (σ g).val :=
  IsIntegralMatrix.mapMatrix_lift _

/-- A representation `σ : G →* GL_r(ℚ_ℓ)` with integral values, as a representation into
`GL_r(ℤ_ℓ)`. -/
public def integralLift (σ : G →* GL (Fin r) ℚ_[ℓ]) (hσ : ∀ g, IsIntegralMatrix (σ g).val) :
    G →* GL (Fin r) ℤ_[ℓ] where
  toFun := integralLiftUnit σ hσ
  map_one' := by
    apply Units.ext
    apply mapMatrix_padicInt_injective
    rw [mapMatrix_integralLiftUnit, Units.val_one, map_one, map_one, Units.val_one]
  map_mul' g h := by
    apply Units.ext
    apply mapMatrix_padicInt_injective
    rw [Units.val_mul, map_mul, mapMatrix_integralLiftUnit, mapMatrix_integralLiftUnit,
      mapMatrix_integralLiftUnit, map_mul, Units.val_mul]

omit [TopologicalSpace G] in
/-- Over `ℚ_ℓ` the matrix of `integralLift σ hσ g` is that of `σ g`. -/
public theorem mapMatrix_integralLift (σ : G →* GL (Fin r) ℚ_[ℓ])
    (hσ : ∀ g, IsIntegralMatrix (σ g).val) (g : G) :
    (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralLift σ hσ g).val = (σ g).val :=
  mapMatrix_integralLiftUnit σ hσ g

omit [TopologicalSpace G] in
/-- Over `ℚ_ℓ` the inverse of `integralLift σ hσ g` is the inverse of `σ g`. -/
public theorem mapMatrix_integralLift_inv (σ : G →* GL (Fin r) ℚ_[ℓ])
    (hσ : ∀ g, IsIntegralMatrix (σ g).val) (g : G) :
    (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralLift σ hσ g)⁻¹.val = (σ g)⁻¹.val := by
  rw [← map_inv, ← map_inv]
  exact mapMatrix_integralLift σ hσ g⁻¹

omit [TopologicalSpace G] in
/-- The entries of `integralLift σ hσ g`, viewed in `ℚ_ℓ`, are those of `σ g`. -/
public theorem integralLift_val (σ : G →* GL (Fin r) ℚ_[ℓ]) (hσ : ∀ g, IsIntegralMatrix (σ g).val)
    (g : G) (i j : Fin r) : (((integralLift σ hσ g).val i j : ℤ_[ℓ]) : ℚ_[ℓ]) = (σ g).val i j :=
  congrArg (fun M : Matrix (Fin r) (Fin r) ℚ_[ℓ] => M i j) (mapMatrix_integralLift σ hσ g)

omit [TopologicalSpace G] in
/-- The entries of the inverse of `integralLift σ hσ g`, viewed in `ℚ_ℓ`, are those of
`(σ g)⁻¹`. -/
public theorem integralLift_inv_val (σ : G →* GL (Fin r) ℚ_[ℓ])
    (hσ : ∀ g, IsIntegralMatrix (σ g).val) (g : G) (i j : Fin r) :
    (((integralLift σ hσ g)⁻¹.val i j : ℤ_[ℓ]) : ℚ_[ℓ]) = (σ g)⁻¹.val i j :=
  congrArg (fun M : Matrix (Fin r) (Fin r) ℚ_[ℓ] => M i j) (mapMatrix_integralLift_inv σ hσ g)

omit [TopologicalSpace G] in
/-- Over `ℚ_ℓ` the integral lift is the original representation. -/
public theorem map_integralLift (σ : G →* GL (Fin r) ℚ_[ℓ])
    (hσ : ∀ g, IsIntegralMatrix (σ g).val) (g : G) :
    Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ)) (integralLift σ hσ g) = σ g := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact integralLift_val σ hσ g i j

/-- The integral lift of a continuous representation is continuous. -/
public theorem continuous_integralLift {σ : G →* GL (Fin r) ℚ_[ℓ]}
    (hσ : ∀ g, IsIntegralMatrix (σ g).val) (hc : Continuous σ) :
    Continuous (integralLift σ hσ) := by
  have hind : Topology.IsInducing ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) :=
    PadicInt.isOpenEmbedding_coe.isInducing
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => hind.continuous_iff.2 ?_
    exact ((Units.continuous_val.comp hc).matrix_elem i j).congr fun g =>
      (integralLift_val σ hσ g i j).symm
  · refine continuous_pi fun i => continuous_pi fun j => hind.continuous_iff.2 ?_
    exact ((Units.continuous_coe_inv.comp hc).matrix_elem i j).congr fun g =>
      (integralLift_inv_val σ hσ g i j).symm

/-- The conjugate `g ↦ P⁻¹ ρ(g) P` of a representation. -/
public abbrev conjRepr (P : GL (Fin r) ℚ_[ℓ]) : G →* GL (Fin r) ℚ_[ℓ] :=
  (MulAut.conj P⁻¹).toMonoidHom.comp ρ

omit [TopologicalSpace G] in
/-- The conjugate representation sends `g` to `P⁻¹ * ρ g * P`. -/
public theorem conjRepr_apply (P : GL (Fin r) ℚ_[ℓ]) (g : G) :
    conjRepr ρ P g = P⁻¹ * ρ g * P := by
  simp [conjRepr]

/-- **The integral model** of a continuous representation `ρ : G → GL_r(ℚ_ℓ)` of a compact
group: a continuous representation `G →* GL_r(ℤ_ℓ)` which over `ℚ_ℓ` is the conjugate
`P⁻¹ ρ P` of `ρ` by the matrix `P` of `Stacks.EtaleCohomology.exists_conj_integral`. -/
public def integralModel [IsTopologicalGroup G] [CompactSpace G] (hρ : Continuous ρ) :
    G →* GL (Fin r) ℤ_[ℓ] :=
  integralLift (conjRepr ρ (exists_conj_integral ρ hρ).choose) fun g => by
    rw [conjRepr_apply]
    exact (exists_conj_integral ρ hρ).choose_spec g

/-- Over `ℚ_ℓ` the integral model is the conjugate of `ρ` by the matrix chosen in
`Stacks.EtaleCohomology.exists_conj_integral`. -/
public theorem map_integralModel [IsTopologicalGroup G] [CompactSpace G] (hρ : Continuous ρ)
    (g : G) :
    Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ)) (integralModel ρ hρ g) =
      (exists_conj_integral ρ hρ).choose⁻¹ * ρ g * (exists_conj_integral ρ hρ).choose := by
  rw [integralModel, map_integralLift, conjRepr_apply]

/-- The integral model of a continuous representation is continuous. -/
public theorem continuous_integralModel [IsTopologicalGroup G] [CompactSpace G]
    (hρ : Continuous ρ) : Continuous (integralModel ρ hρ) := by
  refine continuous_integralLift _ ?_
  have : (conjRepr ρ (exists_conj_integral ρ hρ).choose : G → GL (Fin r) ℚ_[ℓ]) =
      fun g => (exists_conj_integral ρ hρ).choose⁻¹ * ρ g * (exists_conj_integral ρ hρ).choose :=
    funext (conjRepr_apply ρ _)
  rw [this]
  exact (continuous_const.mul hρ).mul continuous_const

/-- The characteristic polynomial of the integral model, mapped to `ℚ_ℓ`, is that of `ρ`. -/
public theorem charpoly_integralModel [IsTopologicalGroup G] [CompactSpace G]
    (hρ : Continuous ρ) (g : G) :
    ((integralModel ρ hρ g).val.charpoly).map (PadicInt.Coe.ringHom (p := ℓ)) =
      (ρ g).val.charpoly := by
  rw [← Matrix.charpoly_map, ← RingHom.mapMatrix_apply, integralModel, mapMatrix_integralLift,
    conjRepr_apply, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' _ _

end Stacks.EtaleCohomology

end
