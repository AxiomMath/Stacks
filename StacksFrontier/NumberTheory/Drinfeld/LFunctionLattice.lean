module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.QuasiFinite.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficients
public import StacksFrontier.NumberTheory.Drinfeld.EqualCharacteristicObstruction

/-!
# Integral models over `O_E` of continuous representations

Let `E` be a finite extension of `ℚ_ℓ`, with its module topology, and `O = O_E` the integral
closure of `ℤ_ℓ` in `E`. A continuous representation `ρ : G → GL_r(E)` of a compact group
stabilises an `O`-lattice in `E^r`, so after a change of basis by some `P ∈ GL_r(E)` it takes
values in `GL_r(O)`. Restricting scalars along a `ℤ_ℓ`-basis of `O` turns this model into a
continuous `ℤ_ℓ`-representation of rank `r · [E : ℚ_ℓ]` commuting with `O`, whose sheaf is the
`O`-sheaf `ℱ_ρ` (`Stacks.EtaleCohomology.coefficientRepresentationSheaf`). The same holds for a
continuous character `χ : G → Eˣ`, whose values are units of `O`. This is the first step of
Drinfeld's proof of [Tag 03VU](https://stacks.math.columbia.edu/tag/03VU): the sheaf of
`ρ ⊗ χ` is an `ℓ`-adic sheaf with an action of `O`.

## Main definitions

* `Stacks.Drinfeld.HasIntegralEntries`: a matrix over the fraction field `K` of `R` with entries
  in `R`.
* `Stacks.Drinfeld.integralVectors`: the `R`-lattice `R^r ⊆ K^r`.
* `Stacks.Drinfeld.integralEntriesStabiliser`, `Stacks.Drinfeld.integralStableLattice`: the
  open subgroup of `g` with `ρ g` integral, and the `R`-span of the translates `ρ(g) R^r`.
* `Stacks.Drinfeld.integralEntriesLift`: a representation with integral values, as one into
  `GL_r(R)`.
* `Stacks.Drinfeld.integralClosureBasis`: a `ℤ_ℓ`-basis of `O_E` indexed by `Fin [E : ℚ_ℓ]`.
* `Stacks.Drinfeld.integralClosureModel`, `Stacks.Drinfeld.integralClosureModelConj`: the model
  `ρ_O : G →* GL_r(O_E)` of `ρ` and the matrix `P` with `ρ_O = P ρ P⁻¹`.
* `Stacks.Drinfeld.integralClosureCharacter`: a continuous character `G → Eˣ` as one into
  `O_Eˣ`.

## Main results

* `Stacks.Drinfeld.isPrincipalIdealRing_integralClosure`,
  `Stacks.Drinfeld.finrank_integralClosure`: `O_E` is a principal ideal domain, free of rank
  `[E : ℚ_ℓ]` over `ℤ_ℓ`.
* `Stacks.Drinfeld.isOpen_integralClosure`: `O_E` is open in `E`.
* `Stacks.Drinfeld.isLattice_integralStableLattice`,
  `Stacks.Drinfeld.exists_conj_hasIntegralEntries`: the stable lattice is a lattice, so some
  conjugate of `ρ` is integral.
* `Stacks.Drinfeld.map_integralClosureModel`: `ρ_O = P ρ P⁻¹` over `E`; and
  `Stacks.Drinfeld.map_characterTwist_integralClosureModel`: `ρ_O ⊗ χ_O = P (ρ ⊗ χ) P⁻¹`.
* `Stacks.Drinfeld.continuous_restrictScalars_integralClosureModel`: the restriction of scalars
  of `ρ_O` along any `ℤ_ℓ`-basis of `O_E` is continuous, the hypothesis of
  `Stacks.EtaleCohomology.coefficientRepresentationSheaf`; likewise
  `Stacks.Drinfeld.continuous_restrictScalars_characterTwist_integralClosureModel` for the twist
  `ρ_O ⊗ χ_O`.

## References

* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
-/

@[expose] public noncomputable section

open Matrix Module

namespace Stacks.Drinfeld

/-! ### Lattices over a principal ideal domain -/

section Lattice

variable (R : Type*) {K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {r : ℕ}

/-- A matrix over `K` *has integral entries* if all its entries lie in the image of `R`. -/
public def HasIntegralEntries (A : Matrix (Fin r) (Fin r) K) : Prop :=
  ∀ i j, A i j ∈ (algebraMap R K).range

/-- The standard lattice `R^r ⊆ K^r`. -/
public def integralVectors (K : Type*) [Field K] [Algebra R K] (r : ℕ) :
    Submodule R (Fin r → K) :=
  LinearMap.range ((Algebra.linearMap R K).compLeft (Fin r))

variable {R} in
omit [IsDomain R] [IsFractionRing R K] in
/-- A vector lies in the standard lattice exactly when its coordinates lie in `R`. -/
public theorem mem_integralVectors {v : Fin r → K} :
    v ∈ integralVectors R K r ↔ ∀ i, v i ∈ (algebraMap R K).range := by
  constructor
  · rintro ⟨w, rfl⟩ i
    exact ⟨w i, rfl⟩
  · intro h
    choose w hw using h
    exact ⟨w, funext hw⟩

/-- The standard basis vectors lie in the standard lattice. -/
private theorem single_one_mem_integralVectors {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    {r : ℕ} (i : Fin r) : Pi.single i (1 : K) ∈ integralVectors R K r :=
  mem_integralVectors.2 fun k => by
    rcases eq_or_ne k i with rfl | hk
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hk]⟩

omit [IsDomain R] [IsFractionRing R K] in
/-- The standard lattice is finitely generated. -/
public theorem fg_integralVectors : (integralVectors R K r).FG := by
  rw [integralVectors, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

variable {R} in
omit [IsDomain R] [IsFractionRing R K] in
/-- A matrix has integral entries exactly when it maps the standard lattice into itself. -/
public theorem hasIntegralEntries_iff_mulVec {A : Matrix (Fin r) (Fin r) K} :
    HasIntegralEntries R A ↔ ∀ v ∈ integralVectors R K r, A *ᵥ v ∈ integralVectors R K r := by
  refine ⟨fun hA v hv => mem_integralVectors.2 fun i => ?_, fun h i j => ?_⟩
  · rw [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (mem_integralVectors.1 hv j)
  · have hj := h _ (single_one_mem_integralVectors j)
    simpa [Matrix.mulVec_single] using mem_integralVectors.1 hj i

variable {R} in
omit [IsDomain R] [IsFractionRing R K] in
/-- Matrices with integral entries are closed under multiplication. -/
public theorem HasIntegralEntries.mul {A B : Matrix (Fin r) (Fin r) K}
    (hA : HasIntegralEntries R A) (hB : HasIntegralEntries R B) :
    HasIntegralEntries R (A * B) := by
  rw [hasIntegralEntries_iff_mulVec] at hA hB ⊢
  intro v hv
  rw [← Matrix.mulVec_mulVec]
  exact hA _ (hB v hv)

omit [IsDomain R] [IsFractionRing R K] in
/-- The identity matrix has integral entries. -/
public theorem hasIntegralEntries_one :
    HasIntegralEntries R (1 : Matrix (Fin r) (Fin r) K) := by
  rw [hasIntegralEntries_iff_mulVec]
  intro v hv
  simpa using hv

variable {G : Type*} [Group G] (ρ : G →* GL (Fin r) K)

/-- The subgroup of `g` with `ρ g` and `ρ g⁻¹` integral. -/
public def integralEntriesStabiliser : Subgroup G where
  carrier := {g | HasIntegralEntries R (ρ g).val ∧ HasIntegralEntries R (ρ g)⁻¹.val}
  one_mem' := by simp [hasIntegralEntries_one]
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

omit [IsDomain R] [IsFractionRing R K] in
/-- If `R` is open in `K`, the integral stabiliser of a continuous representation is open. -/
public theorem isOpen_integralEntriesStabiliser [TopologicalSpace K] [TopologicalSpace G]
    [IsTopologicalGroup G] (hR : IsOpen ((algebraMap R K).range : Set K))
    (hρ : Continuous fun g => (ρ g : Matrix (Fin r) (Fin r) K)) :
    IsOpen (integralEntriesStabiliser R ρ : Set G) := by
  have h2 : Continuous fun g => ((ρ g)⁻¹ : GL (Fin r) K).val := by
    simp_rw [← map_inv]
    exact hρ.comp continuous_inv
  have : (integralEntriesStabiliser R ρ : Set G) =
      (⋂ i, ⋂ j, (fun g => (ρ g).val i j) ⁻¹' ((algebraMap R K).range : Set K)) ∩
        ⋂ i, ⋂ j, (fun g => (ρ g)⁻¹.val i j) ⁻¹' ((algebraMap R K).range : Set K) := by
    ext g
    simp [integralEntriesStabiliser, HasIntegralEntries]
  rw [this]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact hR.preimage (hρ.matrix_elem i j)
  · exact hR.preimage (h2.matrix_elem i j)

/-- The `R`-linear map `K^r → K^r` given by `ρ g`. -/
public abbrev integralReprLinear (g : G) : (Fin r → K) →ₗ[R] (Fin r → K) :=
  ((ρ g).val.mulVecLin).restrictScalars R

/-- The stable lattice: the `R`-span of all the translates `ρ(g) R^r`. -/
public def integralStableLattice : Submodule R (Fin r → K) :=
  ⨆ g, (integralVectors R K r).map (integralReprLinear R ρ g)

/-- The linear map of a product is the composite of the linear maps. -/
private theorem integralReprLinear_mul (R : Type*) {K : Type*} [CommRing R] [Field K]
    [Algebra R K] {r : ℕ} {G : Type*} [Group G] (ρ : G →* GL (Fin r) K) (g h : G) :
    integralReprLinear R ρ (g * h) =
      (integralReprLinear R ρ g).comp (integralReprLinear R ρ h) := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  rw [← Units.val_mul, ← map_mul]

omit [IsDomain R] [IsFractionRing R K] in
/-- The stable lattice is stable under `ρ`. -/
public theorem mulVec_mem_integralStableLattice (g : G) {v : Fin r → K}
    (hv : v ∈ integralStableLattice R ρ) : (ρ g).val *ᵥ v ∈ integralStableLattice R ρ := by
  have : (integralStableLattice R ρ).map (integralReprLinear R ρ g) ≤
      integralStableLattice R ρ := by
    rw [integralStableLattice, Submodule.map_iSup]
    refine iSup_le fun h => ?_
    rw [← Submodule.map_comp, ← integralReprLinear_mul]
    exact le_iSup (fun g => (integralVectors R K r).map (integralReprLinear R ρ g)) (g * h)
  exact this ⟨v, hv, rfl⟩

omit [IsDomain R] [IsFractionRing R K] in
/-- The standard lattice lies in the stable lattice. -/
public theorem integralVectors_le_integralStableLattice :
    integralVectors R K r ≤ integralStableLattice R ρ := by
  intro v hv
  refine (le_iSup (fun g => (integralVectors R K r).map (integralReprLinear R ρ g)) 1)
    ⟨v, hv, ?_⟩
  simp

omit [IsDomain R] [IsFractionRing R K] in
/-- **The stable lattice is a lattice**, when `R` is open in `K` and `G` is compact: it is the
finite sum of the translates by representatives of the cosets of the open, hence finite-index,
integral stabiliser, and it contains `R^r`, which spans `K^r`. -/
public theorem isLattice_integralStableLattice [IsNoetherianRing R] [TopologicalSpace K]
    [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (hR : IsOpen ((algebraMap R K).range : Set K))
    (hρ : Continuous fun g => (ρ g : Matrix (Fin r) (Fin r) K)) :
    Submodule.IsLattice K (integralStableLattice R ρ) where
  fg := by
    have hfin : Finite (G ⧸ integralEntriesStabiliser R ρ) :=
      Subgroup.quotient_finite_of_isOpen _ (isOpen_integralEntriesStabiliser R ρ hR hρ)
    have hle : integralStableLattice R ρ ≤ ⨆ q : G ⧸ integralEntriesStabiliser R ρ,
        (integralVectors R K r).map (integralReprLinear R ρ q.out) := by
      refine iSup_le fun g => ?_
      set q : G ⧸ integralEntriesStabiliser R ρ := QuotientGroup.mk g
      have hmem : q.out⁻¹ * g ∈ integralEntriesStabiliser R ρ := by
        rw [← QuotientGroup.eq]
        exact q.out_eq
      have hsub : (integralVectors R K r).map (integralReprLinear R ρ (q.out⁻¹ * g)) ≤
          integralVectors R K r := by
        rintro _ ⟨v, hv, rfl⟩
        exact (hasIntegralEntries_iff_mulVec.1 hmem.1) v hv
      have hcomp := integralReprLinear_mul R ρ q.out (q.out⁻¹ * g)
      rw [mul_inv_cancel_left] at hcomp
      refine le_trans ?_ (le_iSup _ q)
      rw [hcomp, Submodule.map_comp]
      exact Submodule.map_mono hsub
    exact Submodule.FG.of_le (Submodule.fg_iSup _ fun q => (fg_integralVectors R).map _) hle
  span_eq_top := by
    refine eq_top_iff.2 (le_trans ?_
      (Submodule.span_mono (integralVectors_le_integralStableLattice R ρ)))
    rw [← (Pi.basisFun K (Fin r)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    simpa using single_one_mem_integralVectors (R := R) (K := K) i

omit [IsDomain R] in
/-- The coordinates in the extended basis of a lattice vector are the images of its integral
coordinates. -/
public theorem repr_extendOfIsLattice_coe {L : Submodule R (Fin r → K)}
    [Submodule.IsLattice K L] (b : Basis (Fin r) R L) (m : L) (i : Fin r) :
    (b.extendOfIsLattice K).repr (m : Fin r → K) i = algebraMap R K (b.repr m i) := by
  set bK := b.extendOfIsLattice K
  have hm : (m : Fin r → K) = ∑ j, algebraMap R K (b.repr m j) • bK j := by
    conv_lhs => rw [← b.sum_repr m]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul_of_tower, Basis.extendOfIsLattice_apply, algebraMap_smul]
  rw [hm, ← bK.equivFun_apply, map_sum]
  simp only [map_smul, Basis.equivFun_self, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

/-- **Integral conjugates.** If `R` is a principal ideal domain open in its fraction field `K`, a
continuous representation `ρ : G → GL_r(K)` of a compact group is conjugate, by some
`P ∈ GL_r(K)`, to one with integral entries: the rows of `P` are the coordinates in an
`R`-basis of the stable lattice, which is free of rank `r`. -/
public theorem exists_conj_hasIntegralEntries [IsPrincipalIdealRing R] [TopologicalSpace K]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (hR : IsOpen ((algebraMap R K).range : Set K))
    (hρ : Continuous fun g => (ρ g : Matrix (Fin r) (Fin r) K)) :
    ∃ P : GL (Fin r) K, ∀ g, HasIntegralEntries R (P * ρ g * P⁻¹).val := by
  have := isLattice_integralStableLattice R ρ hR hρ
  have hrank : finrank R (integralStableLattice R ρ) = r := by
    rw [Submodule.IsLattice.finrank_of_pi K, Fintype.card_fin]
  let b : Basis (Fin r) R (integralStableLattice R ρ) := Module.finBasisOfFinrankEq _ _ hrank
  let bK := b.extendOfIsLattice K
  let e := Pi.basisFun K (Fin r)
  let P : GL (Fin r) K :=
    ⟨e.toMatrix bK, bK.toMatrix e, Basis.toMatrix_mul_toMatrix_flip _ _,
      Basis.toMatrix_mul_toMatrix_flip _ _⟩
  refine ⟨P⁻¹, fun g i j => ?_⟩
  have hconj : (P⁻¹ * ρ g * P⁻¹⁻¹).val =
      LinearMap.toMatrix bK bK (Matrix.toLin' (ρ g).val) := by
    rw [inv_inv, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bK e bK e,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    rfl
  rw [hconj, LinearMap.toMatrix_apply, Matrix.toLin'_apply, Basis.extendOfIsLattice_apply]
  have hmem : (ρ g).val *ᵥ (b j : Fin r → K) ∈ integralStableLattice R ρ :=
    mulVec_mem_integralStableLattice R ρ g (b j).2
  have := repr_extendOfIsLattice_coe R b ⟨_, hmem⟩ i
  simp only at this
  rw [this]
  exact ⟨_, rfl⟩

/-- The lift to `R` of a matrix with integral entries. -/
public def HasIntegralEntries.lift {A : Matrix (Fin r) (Fin r) K} (hA : HasIntegralEntries R A) :
    Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i j => (hA i j).choose

omit [IsDomain R] [IsFractionRing R K] in
/-- The lift to `R` of a matrix with integral entries maps back to the matrix. -/
@[simp]
public theorem HasIntegralEntries.mapMatrix_lift {A : Matrix (Fin r) (Fin r) K}
    (hA : HasIntegralEntries R A) : (algebraMap R K).mapMatrix hA.lift = A := by
  ext i j
  exact (hA i j).choose_spec

variable (K) in
omit [IsDomain R] in
/-- Mapping matrices over `R` to `K` is injective. -/
public theorem mapMatrix_algebraMap_injective :
    Function.Injective ((algebraMap R K).mapMatrix (m := Fin r)) :=
  Matrix.map_injective (IsFractionRing.injective R K)

/-- The unit of `GL_r(R)` lifting an integral value `σ g` of a representation. -/
public def integralEntriesLiftUnit (σ : G →* GL (Fin r) K)
    (hσ : ∀ g, HasIntegralEntries R (σ g).val) (g : G) : GL (Fin r) R :=
  ⟨(hσ g).lift, (hσ g⁻¹).lift,
    by
      apply mapMatrix_algebraMap_injective R K
      rw [map_mul, HasIntegralEntries.mapMatrix_lift, HasIntegralEntries.mapMatrix_lift, map_one,
        ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one],
    by
      apply mapMatrix_algebraMap_injective R K
      rw [map_mul, HasIntegralEntries.mapMatrix_lift, HasIntegralEntries.mapMatrix_lift, map_one,
        ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]⟩

omit [IsDomain R] in
/-- The unit `integralEntriesLiftUnit R σ hσ g` maps back to `σ g` over `K`. -/
public theorem mapMatrix_integralEntriesLiftUnit (σ : G →* GL (Fin r) K)
    (hσ : ∀ g, HasIntegralEntries R (σ g).val) (g : G) :
    (algebraMap R K).mapMatrix (integralEntriesLiftUnit R σ hσ g).val = (σ g).val :=
  HasIntegralEntries.mapMatrix_lift R _

/-- A representation `σ : G →* GL_r(K)` with integral values, as a representation into
`GL_r(R)`. -/
public def integralEntriesLift (σ : G →* GL (Fin r) K)
    (hσ : ∀ g, HasIntegralEntries R (σ g).val) : G →* GL (Fin r) R where
  toFun := integralEntriesLiftUnit R σ hσ
  map_one' := by
    apply Units.ext
    apply mapMatrix_algebraMap_injective R K
    rw [mapMatrix_integralEntriesLiftUnit, Units.val_one, map_one, map_one, Units.val_one]
  map_mul' g h := by
    apply Units.ext
    apply mapMatrix_algebraMap_injective R K
    rw [Units.val_mul, map_mul, mapMatrix_integralEntriesLiftUnit,
      mapMatrix_integralEntriesLiftUnit, mapMatrix_integralEntriesLiftUnit, map_mul,
      Units.val_mul]

omit [IsDomain R] in
/-- Over `K` the integral lift is the original representation. -/
public theorem map_integralEntriesLift (σ : G →* GL (Fin r) K)
    (hσ : ∀ g, HasIntegralEntries R (σ g).val) (g : G) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (integralEntriesLift R σ hσ g) = σ g := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrArg (fun M : Matrix (Fin r) (Fin r) K => M i j)
    (mapMatrix_integralEntriesLiftUnit R σ hσ g)

end Lattice

/-! ### The ring of integers of a finite extension of `ℚ_ℓ` -/

section Ring

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E] [Algebra ℤ_[ℓ] E] [IsScalarTower ℤ_[ℓ] ℚ_[ℓ] E]

/-- `E` is the fraction field of `O_E`. -/
public instance isFractionRing_integralClosure :
    IsFractionRing (integralClosure ℤ_[ℓ] E) E :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[ℓ] E

/-- `O_E` is a Dedekind domain. -/
public instance isDedekindDomain_integralClosure :
    IsDedekindDomain (integralClosure ℤ_[ℓ] E) :=
  integralClosure.isDedekindDomain ℤ_[ℓ] ℚ_[ℓ] E

/-- `O_E` is a finite `ℤ_ℓ`-module. -/
public instance finite_integralClosure : Module.Finite ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) :=
  haveI : Module.IsTorsionFree ℤ_[ℓ] E := .trans_faithfulSMul ℤ_[ℓ] ℚ_[ℓ] E
  IsIntegralClosure.finite ℤ_[ℓ] ℚ_[ℓ] E (integralClosure ℤ_[ℓ] E)

/-- `O_E` is a free `ℤ_ℓ`-module. -/
public instance free_integralClosure : Module.Free ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) :=
  haveI : Module.IsTorsionFree ℤ_[ℓ] E := .trans_faithfulSMul ℤ_[ℓ] ℚ_[ℓ] E
  IsIntegralClosure.module_free ℤ_[ℓ] ℚ_[ℓ] E (integralClosure ℤ_[ℓ] E)

/-- The `ℤ_ℓ`-rank of `O_E` is `[E : ℚ_ℓ]`. -/
public theorem finrank_integralClosure :
    finrank ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) = finrank ℚ_[ℓ] E :=
  have : Module.IsTorsionFree ℤ_[ℓ] E := .trans_faithfulSMul ℤ_[ℓ] ℚ_[ℓ] E
  IsIntegralClosure.rank ℤ_[ℓ] ℚ_[ℓ] E (integralClosure ℤ_[ℓ] E)

/-- **`O_E` is a principal ideal domain**: it is a Dedekind domain with finitely many primes,
those over the two primes `0` and `(ℓ)` of `ℤ_ℓ`, of which there are finitely many since `O_E` is
finite over `ℤ_ℓ`. -/
public instance isPrincipalIdealRing_integralClosure :
    IsPrincipalIdealRing (integralClosure ℤ_[ℓ] E) := by
  refine IsPrincipalIdealRing.of_finite_primes ?_
  have h1 := Algebra.QuasiFinite.finite_primesOver (R := ℤ_[ℓ])
    (S := integralClosure ℤ_[ℓ] E) ⊥
  have h2 := Algebra.QuasiFinite.finite_primesOver (R := ℤ_[ℓ])
    (S := integralClosure ℤ_[ℓ] E) (IsLocalRing.maximalIdeal ℤ_[ℓ])
  refine (h1.union h2).subset fun P (hP : P.IsPrime) => ?_
  have hu : (P.under ℤ_[ℓ]).IsPrime := Ideal.IsPrime.under _ _
  rcases eq_or_ne (P.under ℤ_[ℓ]) ⊥ with h | h
  · exact Or.inl ⟨hP, ⟨h.symm⟩⟩
  · exact Or.inr ⟨hP, ⟨(IsLocalRing.eq_maximalIdeal (hu.isMaximal h)).symm⟩⟩

/-- A `ℤ_ℓ`-basis of `O_E` indexed by `Fin [E : ℚ_ℓ]`. -/
public def integralClosureBasis :
    Basis (Fin (finrank ℚ_[ℓ] E)) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) :=
  Module.finBasisOfFinrankEq _ _ (finrank_integralClosure ℓ E)

/-- `E` is the localisation of `O_E` at the nonzero elements of `ℤ_ℓ`. -/
public instance isLocalization_integralClosure :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ_[ℓ] E) (nonZeroDivisors ℤ_[ℓ]))
      E :=
  IsIntegralClosure.isLocalization ℤ_[ℓ] ℚ_[ℓ] E (integralClosure ℤ_[ℓ] E)

variable {ℓ E} {ι : Type*} [Fintype ι]

/-- The `ℚ_ℓ`-basis of `E` given by a `ℤ_ℓ`-basis of `O_E`. -/
public abbrev rationalBasis (b : Basis ι ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)) : Basis ι ℚ_[ℓ] E :=
  b.localizationLocalization ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ]) E

omit [Fintype ι] in
/-- The rational coordinates of an element of `O_E` are its integral coordinates. -/
public theorem rationalBasis_repr_coe (b : Basis ι ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))
    (y : integralClosure ℤ_[ℓ] E) (i : ι) :
    (rationalBasis b).repr (y : E) i = (b.repr y i : ℚ_[ℓ]) :=
  b.localizationLocalization_repr_algebraMap ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ]) E y i

omit [Fintype ι] in
/-- An element of `E` lies in `O_E` exactly when its coordinates in a basis coming from `O_E` are
`ℓ`-adic integers. -/
public theorem mem_integralClosure_iff_repr [Finite ι]
    (b : Basis ι ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)) (y : E) : y ∈ integralClosure ℤ_[ℓ] E ↔
      ∀ i, (rationalBasis b).repr y i ∈ Set.range ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) := by
  have := Fintype.ofFinite ι
  refine ⟨fun hy i => ⟨_, (rationalBasis_repr_coe b ⟨y, hy⟩ i).symm⟩, fun h => ?_⟩
  have h' : ∀ i, ∃ a : ℤ_[ℓ], (a : ℚ_[ℓ]) = (rationalBasis b).repr y i := h
  choose a ha using h'
  rw [← (rationalBasis b).sum_repr y]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [← ha i, Basis.localizationLocalization_apply]
  change (algebraMap ℤ_[ℓ] ℚ_[ℓ] (a i)) • ((b i : integralClosure ℤ_[ℓ] E) : E) ∈ _
  rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] E]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (b i).2

variable [TopologicalSpace E] [IsModuleTopology ℚ_[ℓ] E]

variable (ℓ E) in
/-- **`O_E` is open in `E`**: in the coordinates of a basis coming from `O_E` it is `ℤ_ℓ^d`. -/
public theorem isOpen_integralClosure : IsOpen (integralClosure ℤ_[ℓ] E : Set E) := by
  let b := integralClosureBasis ℓ E
  have : (integralClosure ℤ_[ℓ] E : Set E) =
      ⋂ i, (fun y => (rationalBasis b).repr y i) ⁻¹' Set.range ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) := by
    ext y
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
    exact mem_integralClosure_iff_repr b y
  rw [this]
  refine isOpen_iInter_of_finite fun i => PadicInt.isOpenEmbedding_coe.isOpen_range.preimage ?_
  exact IsModuleTopology.continuous_of_linearMap ((rationalBasis b).coord i)

variable (ℓ E) in
/-- The image of `O_E` in `E` is open. -/
public theorem isOpen_range_algebraMap_integralClosure :
    IsOpen ((algebraMap (integralClosure ℤ_[ℓ] E) E).range : Set E) := by
  convert isOpen_integralClosure ℓ E
  ext y
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩

/-! ### The integral model of a representation over `O_E` -/

variable {r : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (ρ : G →* GL (Fin r) E)
  (hρ : Continuous fun g => (ρ g : Matrix (Fin r) (Fin r) E))

variable (ℓ) in
/-- **The matrix `P ∈ GL_r(E)` conjugating `ρ` into `GL_r(O_E)`**
(`Stacks.Drinfeld.exists_conj_hasIntegralEntries`). -/
public def integralClosureModelConj : GL (Fin r) E :=
  (exists_conj_hasIntegralEntries (integralClosure ℤ_[ℓ] E) ρ
    (isOpen_range_algebraMap_integralClosure ℓ E) hρ).choose

/-- The conjugate `g ↦ P ρ(g) P⁻¹` of a representation. -/
public abbrev conjRepresentation (P : GL (Fin r) E) : G →* GL (Fin r) E :=
  (MulAut.conj P).toMonoidHom.comp ρ

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TopologicalSpace E] in
/-- The value of the conjugate representation at `g` is `P ρ(g) P⁻¹`. -/
public theorem conjRepresentation_apply (P : GL (Fin r) E) (g : G) :
    conjRepresentation ρ P g = P * ρ g * P⁻¹ := by
  simp [conjRepresentation]

variable (ℓ) in
/-- **The integral model `ρ_O : G →* GL_r(O_E)`** of a continuous representation
`ρ : G → GL_r(E)` of a compact group: over `E` it is the conjugate `P ρ P⁻¹` by
`P = Stacks.Drinfeld.integralClosureModelConj ℓ ρ hρ`. -/
public def integralClosureModel : G →* GL (Fin r) (integralClosure ℤ_[ℓ] E) :=
  integralEntriesLift (integralClosure ℤ_[ℓ] E)
    (conjRepresentation ρ (integralClosureModelConj ℓ ρ hρ)) fun g => by
      rw [conjRepresentation_apply]
      exact (exists_conj_hasIntegralEntries (integralClosure ℤ_[ℓ] E) ρ
        (isOpen_range_algebraMap_integralClosure ℓ E) hρ).choose_spec g

/-- **Over `E`, the integral model is `P ρ P⁻¹`.** -/
public theorem map_integralClosureModel (g : G) :
    Matrix.GeneralLinearGroup.map (algebraMap (integralClosure ℤ_[ℓ] E) E)
        (integralClosureModel ℓ ρ hρ g) =
      integralClosureModelConj ℓ ρ hρ * ρ g * (integralClosureModelConj ℓ ρ hρ)⁻¹ := by
  rw [integralClosureModel, map_integralEntriesLift, conjRepresentation_apply]

/-- The entries of the integral model are those of `P ρ P⁻¹`. -/
public theorem integralClosureModel_apply (g : G) (i j : Fin r) :
    (((integralClosureModel ℓ ρ hρ g).val i j : integralClosure ℤ_[ℓ] E) : E) =
      (integralClosureModelConj ℓ ρ hρ * ρ g * (integralClosureModelConj ℓ ρ hρ)⁻¹).val i j := by
  rw [← map_integralClosureModel ρ hρ g, Matrix.GeneralLinearGroup.map_apply]
  rfl

/-! ### Continuity after restriction of scalars -/

omit [CompactSpace G] in
/-- **Restriction of scalars of a continuous `O_E`-representation is continuous**: if
`σ : G →* GL_r(O_E)` is continuous as a map into `M_r(E)`, its restriction of scalars along any
`ℤ_ℓ`-basis `b` of `O_E` is a continuous map into `GL_{rd}(ℤ_ℓ)`. -/
public theorem continuous_restrictScalars_of_continuous_map {d : ℕ}
    (b : Basis (Fin d) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))
    (σ : G →* GL (Fin r) (integralClosure ℤ_[ℓ] E))
    (hσ : Continuous fun g =>
      (Matrix.GeneralLinearGroup.map (algebraMap (integralClosure ℤ_[ℓ] E) E) (σ g)).val) :
    Continuous ((Units.map (Stacks.EtaleCohomology.coefficientMatrixRingHom b r).toMonoidHom).comp
      σ) := by
  have : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[ℓ] E
  set φ := (Units.map (Stacks.EtaleCohomology.coefficientMatrixRingHom b r).toMonoidHom).comp σ
  have hind : Topology.IsInducing ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) :=
    PadicInt.isOpenEmbedding_coe.isInducing
  have hval : Continuous fun g => (φ g).val := by
    refine continuous_pi fun p => continuous_pi fun q => hind.continuous_iff.2 ?_
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective q
    have heq : ∀ g, (((φ g).val (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) : ℤ_[ℓ]) :
        ℚ_[ℓ]) = (rationalBasis b).repr
          ((Matrix.GeneralLinearGroup.map (algebraMap (integralClosure ℤ_[ℓ] E) E) (σ g)).val
            i j * (b l : E)) k := by
      intro g
      change ((Stacks.EtaleCohomology.coefficientMatrixRingHom b r (σ g).val
        (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) : ℤ_[ℓ]) : ℚ_[ℓ]) = _
      rw [Stacks.EtaleCohomology.coefficientMatrixRingHom_apply,
        Algebra.leftMulMatrix_eq_repr_mul, ← rationalBasis_repr_coe,
        Matrix.GeneralLinearGroup.map_apply]
      rfl
    exact ((IsModuleTopology.continuous_of_linearMap ((rationalBasis b).coord k)).comp
      ((hσ.matrix_elem i j).mul continuous_const)).congr fun g => (heq g).symm
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have : (fun g => ((φ g)⁻¹ : GL (Fin (r * d)) ℤ_[ℓ]).val) = fun g => (φ g⁻¹).val := by
    funext g
    rw [map_inv]
  rw [this]
  exact hval.comp continuous_inv

/-- **The restriction of scalars of the integral model is continuous**, for any `ℤ_ℓ`-basis `b`
of `O_E`: this is the continuity hypothesis of
`Stacks.EtaleCohomology.coefficientRepresentationSheaf`. -/
public theorem continuous_restrictScalars_integralClosureModel {d : ℕ}
    (b : Basis (Fin d) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)) :
    Continuous ((Units.map (Stacks.EtaleCohomology.coefficientMatrixRingHom b r).toMonoidHom).comp
      (integralClosureModel ℓ ρ hρ)) := by
  have : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[ℓ] E
  refine continuous_restrictScalars_of_continuous_map b _ ?_
  simp_rw [map_integralClosureModel, Units.val_mul]
  exact (continuous_const.mul hρ).mul continuous_const

/-! ### Characters -/

variable (χ : G →* Eˣ) (hχ : Continuous fun g => (χ g : E))

omit [IsTopologicalGroup G] in
include hχ in
/-- The values of a continuous character of a compact group are integral over `ℤ_ℓ`. -/
public theorem mem_integralClosure_character (g : G) : (χ g : E) ∈ integralClosure ℤ_[ℓ] E := by
  have hC : IsCompact (Set.range fun g => (χ g : E)) := isCompact_range hχ
  exact isIntegral_of_pow_mem_of_isCompact hC fun n => ⟨g ^ n, by simp⟩

variable (ℓ) in
/-- **A continuous character `χ : G → Eˣ` of a compact group takes values in `O_Eˣ`.** -/
public def integralClosureCharacter : G →* (integralClosure ℤ_[ℓ] E)ˣ where
  toFun g := ⟨⟨χ g, mem_integralClosure_character χ hχ g⟩,
    ⟨χ g⁻¹, mem_integralClosure_character χ hχ g⁻¹⟩,
    Subtype.ext (by simp),
    Subtype.ext (by simp)⟩
  map_one' := Units.ext (Subtype.ext (by simp))
  map_mul' g h := Units.ext (Subtype.ext (by simp))

omit [IsTopologicalGroup G] in
/-- The value of `integralClosureCharacter` at `g`, as an element of `E`, is `χ g`. -/
public theorem coe_integralClosureCharacter (g : G) :
    (((integralClosureCharacter ℓ χ hχ g : integralClosure ℤ_[ℓ] E)) : E) = χ g :=
  rfl

/-- **The twist `ρ_O ⊗ χ_O` of the integral model by the integral character is, over `E`,
`χ · P ρ P⁻¹`.** -/
public theorem characterTwist_integralClosureModel_val (g : G) :
    (Matrix.GeneralLinearGroup.map (algebraMap (integralClosure ℤ_[ℓ] E) E)
        (Stacks.EtaleCohomology.characterTwist (O := integralClosure ℤ_[ℓ] E)
          (integralClosureModel ℓ ρ hρ) (integralClosureCharacter ℓ χ hχ) g)).val =
      (χ g : E) •
        (integralClosureModelConj ℓ ρ hρ * ρ g * (integralClosureModelConj ℓ ρ hρ)⁻¹).val := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Stacks.EtaleCohomology.characterTwist_val,
    Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
    ← integralClosureModel_apply ρ hρ g i j]
  rfl

/-- **Over `E` the twist `ρ_O ⊗ χ_O` is `P (ρ ⊗ χ) P⁻¹`**, `P` the matrix of the integral model
of `ρ`. -/
public theorem map_characterTwist_integralClosureModel (g : G) :
    Matrix.GeneralLinearGroup.map (algebraMap (integralClosure ℤ_[ℓ] E) E)
        (Stacks.EtaleCohomology.characterTwist (integralClosureModel ℓ ρ hρ)
          (integralClosureCharacter ℓ χ hχ) g) =
      integralClosureModelConj ℓ ρ hρ * Stacks.EtaleCohomology.characterTwist ρ χ g *
        (integralClosureModelConj ℓ ρ hρ)⁻¹ := by
  apply Units.ext
  rw [characterTwist_integralClosureModel_val, Units.val_mul, Units.val_mul, Units.val_mul,
    Units.val_mul, Stacks.EtaleCohomology.characterTwist_val, Matrix.mul_smul, Matrix.smul_mul]

/-- **The restriction of scalars of the twist `ρ_O ⊗ χ_O` is continuous**, for any
`ℤ_ℓ`-basis `b` of `O_E`. -/
public theorem continuous_restrictScalars_characterTwist_integralClosureModel {d : ℕ}
    (b : Basis (Fin d) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)) :
    Continuous ((Units.map (Stacks.EtaleCohomology.coefficientMatrixRingHom b r).toMonoidHom).comp
      (Stacks.EtaleCohomology.characterTwist (O := integralClosure ℤ_[ℓ] E)
        (integralClosureModel ℓ ρ hρ) (integralClosureCharacter ℓ χ hχ))) := by
  have : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[ℓ] E
  refine continuous_restrictScalars_of_continuous_map b _ ?_
  simp_rw [characterTwist_integralClosureModel_val, Units.val_mul]
  exact hχ.smul ((continuous_const.mul hρ).mul continuous_const)

end Ring

end Stacks.Drinfeld

end
