module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChange
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChangeHomotopyInverse.CartanRemainder

/-!
# The decomposition `Ω' = (B' ⊗_B Ω) ⊕ B' dz` and the integrating homotopy

The decomposition `Crystalline.DzDecomposition` of the one-forms of `B'` (assumption (2) of
Stacks, Tag 07Q1), with the components `d₁` and `∂_z` of the differential; the induced maps on
the terms `M ⊗_B Ω^p` and `(B' ⊗_B M) ⊗_{B'} (Ω')^p` of the two de Rham complexes and their
rank-one projections; the integrating homotopy built from `θ`; the induction principle over
the generators of the decomposition; and the injectivity of the base change map `c_M^•` when
`B → B'` is universally injective. Part of the proof of Stacks, Tag 07Q7.
-/

@[expose] public section

open scoped TensorProduct DirectSum


universe u u' w

namespace Crystalline

open Stacks.DeRham.DifferentialDescent


variable {A B Omega : Type u} {A' B' Omega' : Type u'} {M : Type w}
variable
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
  [AddCommGroup Omega] [Module B Omega]
  [AddCommGroup Omega'] [Module B' Omega']
  [AddCommGroup M] [Module B M]

/-- Assumption (2) of Section 60.25: the decomposition `Ω' = (B' ⊗_B Ω) ⊕ B' dz`, where
`dz = d z` for the chosen element `z ∈ B'`.  The isomorphism is required to be the canonical
map `b' ⊗ ω ↦ b' ψ(ω)` on the first summand and `c ↦ c dz` on the second, which determines
it. -/
public structure DzDecomposition (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B') where
  /-- The decomposition of the one-forms of `B'` into the base change of those of `B` and the
  free piece spanned by `dz`. -/
  equiv : ((B' ⊗[B] Omega) × B') ≃ₗ[B'] Omega'
  /-- On the first summand the decomposition is the canonical map induced by `ψ`. -/
  equiv_tmul : ∀ (b' : B') (omega : Omega), equiv (b' ⊗ₜ[B] omega, 0) = b' • psi omega
  /-- On the second summand the decomposition is multiplication of `dz` by a scalar. -/
  equiv_dz : ∀ b' : B', equiv (0, b') = b' • SourceDeRham.targetD pi' z

namespace DzDecomposition

variable {pi' : Ω[B'⁄A'] →ₗ[B'] Omega'} {psi : Omega →ₛₗ[algebraMap B B'] Omega'} {z : B'}

/-- The component `d₁(f) ∈ B' ⊗_B Ω` of `d f` in the first summand of the decomposition. -/
public noncomputable def dOne (dec : DzDecomposition pi' psi z) (f : B') : B' ⊗[B] Omega :=
  (dec.equiv.symm (SourceDeRham.targetD pi' f)).1

/-- The coefficient `∂_z(f) ∈ B'` of `dz` in `d f`. -/
public noncomputable def partialZ (dec : DzDecomposition pi' psi z) (f : B') : B' :=
  (dec.equiv.symm (SourceDeRham.targetD pi' f)).2

omit [SMulCommClass A' B B'] in
/-- The defining decomposition `d(f) = d₁(f) + ∂_z(f) dz` of the differential of an element of
`B'`. -/
public theorem dOne_add_partialZ_smul (dec : DzDecomposition pi' psi z) (f : B') :
    dec.equiv (dec.dOne f, 0) + dec.partialZ f • SourceDeRham.targetD pi' z =
      SourceDeRham.targetD pi' f := by
  rw [← dec.equiv_dz, ← map_add]
  have : ((dec.dOne f, 0) + (0, dec.partialZ f) : (B' ⊗[B] Omega) × B') =
      dec.equiv.symm (SourceDeRham.targetD pi' f) :=
    Prod.ext (by simp [dOne]) (by simp [partialZ])
  rw [this, LinearEquiv.apply_symm_apply]

end DzDecomposition

/-- The inclusion of the base-change summand in the one-form decomposition. -/
noncomputable def baseFormInclusion
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z) :
    (B' ⊗[B] Omega) →ₗ[B'] Omega' where
  toFun x := dec.equiv (x, 0)
  map_add' x y := by
    simpa using dec.equiv.map_add (x, 0) (y, 0)
  map_smul' c x := by
    simpa using dec.equiv.map_smul c (x, 0)

/-- Projection onto the base-change summand in the one-form decomposition. -/
private noncomputable def baseFormProjection
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z) :
    Omega' →ₗ[B'] (B' ⊗[B] Omega) where
  toFun x := (dec.equiv.symm x).1
  map_add' x y := by simp
  map_smul' c x := by simp

omit [SMulCommClass A' B B'] in
/-- The projection is a retraction of the base-form inclusion. -/
private theorem baseFormProjection_comp_baseFormInclusion
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z) :
    (baseFormProjection pi' psi z dec).comp
      (baseFormInclusion pi' psi z dec) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (dec.equiv.symm (dec.equiv (x, 0))).1 = x
  simp

/-- Extract the component containing exactly one factor from the distinguished rank-one summand
in the exterior power of a direct product. It is defined using the graded product equivalence for
exterior algebras, so it is valid over an arbitrary commutative ring. -/
noncomputable def exteriorPower_extractRankOne
    (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] (n : ℕ) :
    (⋀[R]^(n + 1) (W × R)) →ₗ[R] ⋀[R]^n W := by
  let qW : (⨁ i : ℕ, ⋀[R]^i W) →ₗ[R] ⋀[R]^n W :=
    DirectSum.component R ℕ (fun i : ℕ => ⋀[R]^i W) n
  let qR : (⨁ i : ℕ, ⋀[R]^i R) →ₗ[R] ⋀[R]^1 R :=
    DirectSum.component R ℕ (fun i : ℕ => ⋀[R]^i R) 1
  let qTensor :
      ((⨁ i : ℕ, ⋀[R]^i W) ⊗[R] (⨁ i : ℕ, ⋀[R]^i R)) →ₗ[R]
        (⋀[R]^n W) ⊗[R] (⋀[R]^1 R) :=
    TensorProduct.map qW qR
  let qOne : (⋀[R]^n W) ⊗[R] (⋀[R]^1 R) →ₗ[R] ⋀[R]^n W :=
    (TensorProduct.rid R (⋀[R]^n W)).toLinearMap.comp
      (TensorProduct.map (LinearMap.id (R := R)) (exteriorPower.oneEquiv R R).toLinearMap)
  exact qOne.comp (qTensor.comp ((GradedTensorProduct.auxEquiv R _ _).toLinearMap.comp
    ((ExteriorAlgebra.prodEquivTensor R W R).toLinearMap.comp
      (Submodule.subtype (⋀[R]^(n + 1) (W × R))))))

/-- The graded product equivalence sends a wedge of `inl`/`inr` images to the tensor of the
two wedges. -/
private theorem prodEquivTensor_ιMulti_append
    (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] (a b : ℕ)
    (v : Fin a → W) (w : Fin b → R) :
    (ExteriorAlgebra.prodEquivTensor R W R)
        (ExteriorAlgebra.ιMulti R (a + b)
          (Fin.append (LinearMap.inl R W R ∘ v) (LinearMap.inr R W R ∘ w))) =
      (ExteriorAlgebra.ιMulti R a v) ᵍ⊗ₜ[R] (ExteriorAlgebra.ιMulti R b w) := by
  rw [← ExteriorAlgebra.prodEquivTensor_symm_apply_tmul_ιMulti, AlgEquiv.apply_symm_apply]

/-- The degree-`n` component of a wedge of degree `k` is the wedge itself if `k = n`, else zero. -/
private theorem component_decompose_ιMulti
    (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] (k n : ℕ) (v : Fin k → W) :
    (DirectSum.component R ℕ (fun i : ℕ => ⋀[R]^i W) n)
        (DirectSum.decompose (fun i : ℕ => ⋀[R]^i W) (ExteriorAlgebra.ιMulti R k v)) =
      if h : k = n then Eq.recOn h (exteriorPower.ιMulti R k v) else 0 := by
  rw [← exteriorPower.ιMulti_apply_coe, DirectSum.decompose_coe,
    ← DirectSum.lof_eq_of R, DirectSum.component.of]

/-- The graded product equivalence sends a base wedge to the corresponding wedge in the first
factor and the degree-zero element in the rank-one factor. -/
private theorem exteriorPower_prodEquivTensor_inl_ιMulti
    (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] (n : ℕ)
    (v : Fin (n + 1) → W) :
    (ExteriorAlgebra.prodEquivTensor R W R)
        (ExteriorAlgebra.ιMulti R (n + 1) (LinearMap.inl R W R ∘ v)) =
      (ExteriorAlgebra.ιMulti R (n + 1) v) ᵍ⊗ₜ[R]
        (ExteriorAlgebra.ιMulti R 0 Fin.elim0) := by
  have h := prodEquivTensor_ιMulti_append R W (n + 1) 0 v Fin.elim0
  rwa [Fin.append_right_nil _ _ rfl] at h

/-- The rank-one extractor vanishes on wedges made entirely from the first summand. -/
private theorem exteriorPower_extractRankOne_zero_on_inl
    (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] (n : ℕ) :
    (exteriorPower_extractRankOne R W n).comp
      (exteriorPower.map (n + 1) (LinearMap.inl R W R)) = 0 := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span R
      (Set.range (exteriorPower.ιMulti R (n + 1) :
        (Fin (n + 1) → W) → ⋀[R]^(n + 1) W)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨v, rfl⟩ := hv
      simp only [exteriorPower_extractRankOne, LinearMap.comp_apply,
        exteriorPower.map_apply_ιMulti, Submodule.subtype_apply,
        exteriorPower.ιMulti_apply_coe]
      rw [AlgEquiv.toLinearMap_apply,
        exteriorPower_prodEquivTensor_inl_ιMulti R W n v]
      simp only [LinearEquiv.coe_toLinearMap, GradedTensorProduct.auxEquiv_tmul,
        TensorProduct.map_tmul, component_decompose_ιMulti]
      simp
  | zero => simp
  | add x y hx hy ihx ihy =>
      change (exteriorPower_extractRankOne R W n ∘ₗ
        exteriorPower.map (n + 1) (LinearMap.inl R W R)) (x + y) = 0
      rw [map_add, ihx, ihy]
      simp
  | smul a x hx ih => simp [ih]

/-- Removing a single distinguished rank-one factor from a pure wedge leaves its base wedge. -/
private theorem exteriorPower_extractRankOne_inl_append_inr_one
    (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] (n : ℕ)
    (v : Fin n → W) :
    exteriorPower_extractRankOne R W n
      (exteriorPower.ιMulti R (n + 1)
        (Fin.append (LinearMap.inl R W R ∘ v)
          (LinearMap.inr R W R ∘ fun _ : Fin 1 => (1 : R)))) =
      exteriorPower.ιMulti R n v := by
  simp only [exteriorPower_extractRankOne, LinearMap.comp_apply,
    Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe, AlgEquiv.toLinearMap_apply]
  rw [prodEquivTensor_ιMulti_append R W n 1 v (fun _ : Fin 1 => (1 : R))]
  simp only [LinearEquiv.coe_toLinearMap, GradedTensorProduct.auxEquiv_tmul,
    TensorProduct.map_tmul, component_decompose_ιMulti]
  simp [exteriorPower.oneEquiv_ιMulti, TensorProduct.rid_tmul]

private theorem exteriorPower_extractRankOne_cons_inr_one
    (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] (n : ℕ)
    (v : Fin n → W) :
    exteriorPower_extractRankOne R W n
      (exteriorPower.ιMulti R (n + 1)
        (Fin.cons (0, 1) (LinearMap.inl R W R ∘ v))) =
      (-1 : R) ^ n • exteriorPower.ιMulti R n v := by
  have hw : exteriorPower.ιMulti R (n + 1)
      (Fin.cons (0, 1) (LinearMap.inl R W R ∘ v)) =
      (-1 : R) ^ n • exteriorPower.ιMulti R (n + 1)
        (Fin.append (LinearMap.inl R W R ∘ v)
          (LinearMap.inr R W R ∘ fun _ : Fin 1 => (1 : R))) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, exteriorPower.ιMulti_apply_coe]
    rw [← ExteriorAlgebra.ιMulti_mul_ιMulti, ExteriorAlgebra.ιMulti_succ_apply]
    change ExteriorAlgebra.ι R (0, 1) *
      ExteriorAlgebra.ιMulti R n (LinearMap.inl R W R ∘ v) = _
    have h := ExteriorAlgebra.ι_mul_ιMulti_anticomm (R := R) (0, 1)
      (LinearMap.inl R W R ∘ v)
    simpa [ExteriorAlgebra.ιMulti_apply, Units.smul_def, ← Int.cast_smul_eq_zsmul R]
      using h
  rw [hw, map_smul, exteriorPower_extractRankOne_inl_append_inr_one]

/-- Conjugating a retraction `F ∘ G = id` by a linear equivalence gives a retraction. -/
private theorem symm_comp_comp_comp_equiv
    {R X Y Z : Type*} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] (e : X ≃ₗ[R] Y) (F : Z →ₗ[R] Y) (G : Y →ₗ[R] Z)
    (h : F.comp G = LinearMap.id) :
    (e.symm.toLinearMap.comp F).comp (G.comp e.toLinearMap) = LinearMap.id := by
  rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ F, h, LinearMap.id_comp]
  exact e.symm_comp

section CoefficientMaps

variable (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
  (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
  (dec : DzDecomposition pi' psi z)

noncomputable def formBaseInclusion (p : ℕ) :
    B' ⊗[B] (⋀[B]^p Omega) →ₗ[B'] (⋀[B']^p Omega') :=
  (exteriorPower.map p (baseFormInclusion pi' psi z dec)).comp
    (exteriorScalarEquiv B B' Omega p).toLinearMap

private noncomputable def formBaseProjection (p : ℕ) :
    (⋀[B']^p Omega') →ₗ[B'] B' ⊗[B] (⋀[B]^p Omega) :=
  (exteriorScalarEquiv B B' Omega p).symm.toLinearMap.comp
    (exteriorPower.map p (baseFormProjection pi' psi z dec))

omit [SMulCommClass A' B B'] in
private theorem formBaseProjection_comp_inclusion (p : ℕ) :
    (formBaseProjection pi' psi z dec p).comp (formBaseInclusion pi' psi z dec p) =
      LinearMap.id := by
  refine symm_comp_comp_comp_equiv _ _ _ ?_
  rw [← exteriorPower.map_comp, baseFormProjection_comp_baseFormInclusion,
    exteriorPower.map_id]

omit [SMulCommClass A' B B'] in
private theorem formBaseInclusion_tmul_ιMulti (p : ℕ) (f : B') (v : Fin p → Omega) :
    formBaseInclusion pi' psi z dec p (f ⊗ₜ[B] exteriorPower.ιMulti B p v) =
      f • exteriorPower.ιMulti B' p (psi ∘ v) := by
  simp only [formBaseInclusion, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    exteriorScalarEquiv_tmul_ιMulti, map_smul, exteriorPower.map_apply_ιMulti]
  congr 2
  funext i
  exact (dec.equiv_tmul 1 (v i)).trans (one_smul _ _)

noncomputable def coefficientInclusion (p : ℕ) :
    B' ⊗[B] (M ⊗[B] (⋀[B]^p Omega)) →ₗ[B']
      (B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega') :=
  (TensorProduct.map LinearMap.id (formBaseInclusion pi' psi z dec p)).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange B B' M (⋀[B]^p Omega)).toLinearMap

private noncomputable def coefficientProjection (p : ℕ) :
    (B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega') →ₗ[B']
      B' ⊗[B] (M ⊗[B] (⋀[B]^p Omega)) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange B B' M (⋀[B]^p Omega)).symm.toLinearMap.comp
    (TensorProduct.map LinearMap.id (formBaseProjection pi' psi z dec p))

omit [SMulCommClass A' B B'] in
private theorem coefficientProjection_comp_inclusion (p : ℕ) :
    (coefficientProjection pi' psi z dec (M := M) p).comp
      (coefficientInclusion pi' psi z dec p) = LinearMap.id := by
  refine symm_comp_comp_comp_equiv _ _ _ ?_
  rw [← TensorProduct.map_comp, formBaseProjection_comp_inclusion, LinearMap.id_comp,
    TensorProduct.map_id]

omit [SMulCommClass A' B B'] in
theorem coefficientInclusion_tmul_ιMulti (p : ℕ) (f : B') (m : M)
    (v : Fin p → Omega) :
    coefficientInclusion pi' psi z dec p
      (f ⊗ₜ[B] (m ⊗ₜ[B] exteriorPower.ιMulti B p v)) =
      (f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ v) := by
  simp [coefficientInclusion, formBaseInclusion_tmul_ιMulti,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

noncomputable def formRankOneProjection (p : ℕ) :
    (⋀[B']^(p + 1) Omega') →ₗ[B'] B' ⊗[B] (⋀[B]^p Omega) :=
  (exteriorScalarEquiv B B' Omega p).symm.toLinearMap.comp
    ((((-1 : B') ^ p) • exteriorPower_extractRankOne B' (B' ⊗[B] Omega) p).comp
      (exteriorPower.map (p + 1) dec.equiv.symm.toLinearMap))

noncomputable def coefficientRankOneProjection (p : ℕ) :
    (B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega') →ₗ[B']
      B' ⊗[B] (M ⊗[B] (⋀[B]^p Omega)) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange B B' M (⋀[B]^p Omega)).symm.toLinearMap.comp
    (TensorProduct.map LinearMap.id (formRankOneProjection pi' psi z dec p))

end CoefficientMaps

omit [SMulCommClass A' B B'] in
private theorem decomposition_symm_psi
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z) (w : Omega) :
    dec.equiv.symm (psi w) = (1 ⊗ₜ[B] w, 0) := by
  apply dec.equiv.injective
  rw [LinearEquiv.apply_symm_apply, dec.equiv_tmul, one_smul]

omit [SMulCommClass A' B B'] in
private theorem decomposition_symm_dz
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z) :
    dec.equiv.symm (SourceDeRham.targetD pi' z) = (0, 1) := by
  apply dec.equiv.injective
  rw [LinearEquiv.apply_symm_apply, dec.equiv_dz, one_smul]

omit [SMulCommClass A' B B'] in
private theorem formRankOneProjection_ιMulti_psi
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z) (p : ℕ) (v : Fin (p + 1) → Omega) :
    formRankOneProjection pi' psi z dec p
      (exteriorPower.ιMulti B' (p + 1) (psi ∘ v)) = 0 := by
  have heq : dec.equiv.symm.toLinearMap ∘ (psi ∘ v) =
      LinearMap.inl B' (B' ⊗[B] Omega) B' ∘ (fun i => 1 ⊗ₜ[B] v i) := by
    funext i
    exact decomposition_symm_psi pi' psi z dec (v i)
  have hz := LinearMap.congr_fun
    (exteriorPower_extractRankOne_zero_on_inl B' (B' ⊗[B] Omega) p)
      (exteriorPower.ιMulti B' (p + 1) (fun i => 1 ⊗ₜ[B] v i))
  simp only [LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
    LinearMap.zero_apply] at hz
  simp only [formRankOneProjection, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
    heq, LinearMap.smul_apply, hz, smul_zero, map_zero]

omit [SMulCommClass A' B B'] in
private theorem formRankOneProjection_ιMulti_cons_dz
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z) (p : ℕ) (v : Fin p → Omega) :
    formRankOneProjection pi' psi z dec p
      (exteriorPower.ιMulti B' (p + 1)
        (Fin.cons (SourceDeRham.targetD pi' z) (psi ∘ v))) =
      1 ⊗ₜ[B] exteriorPower.ιMulti B p v := by
  have heq : dec.equiv.symm.toLinearMap ∘
      Fin.cons (SourceDeRham.targetD pi' z) (psi ∘ v) =
      Fin.cons (0, 1) (LinearMap.inl B' (B' ⊗[B] Omega) B' ∘
        (fun i => 1 ⊗ₜ[B] v i)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact decomposition_symm_dz pi' psi z dec
    · exact decomposition_symm_psi pi' psi z dec (v j)
  simp only [formRankOneProjection, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
    heq, LinearMap.smul_apply, exteriorPower_extractRankOne_cons_inr_one]
  rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  apply (exteriorScalarEquiv B B' Omega p).injective
  simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
    exteriorScalarEquiv_tmul_ιMulti, one_smul]

omit [SMulCommClass A' B B'] in
theorem coefficientRankOneProjection_base
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z) (p : ℕ) (f : B') (m : M)
    (v : Fin (p + 1) → Omega) :
    coefficientRankOneProjection pi' psi z dec p
      ((f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' (p + 1) (psi ∘ v)) = 0 := by
  simp [coefficientRankOneProjection, formRankOneProjection_ιMulti_psi]

omit [SMulCommClass A' B B'] in
theorem coefficientRankOneProjection_dz
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z) (p : ℕ) (f : B') (m : M)
    (v : Fin p → Omega) :
    coefficientRankOneProjection pi' psi z dec p
      ((f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' (p + 1)
        (Fin.cons (SourceDeRham.targetD pi' z) (psi ∘ v))) =
      f ⊗ₜ[B] (m ⊗ₜ[B] exteriorPower.ιMulti B p v) := by
  simp [coefficientRankOneProjection, formRankOneProjection_ιMulti_cons_dz,
    TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]

noncomputable def integratingHomotopy
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z) (theta : B' →ₗ[B] B') (p : ℕ) :
    RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega')) →ₗ[A]
      RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')) where
  toFun x := coefficientInclusion pi' psi z dec p
    (TensorProduct.map theta LinearMap.id (coefficientRankOneProjection pi' psi z dec p x))
  map_add' x y := by
    change (B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega') at x y
    change coefficientInclusion pi' psi z dec p
      (TensorProduct.map theta LinearMap.id
        (coefficientRankOneProjection pi' psi z dec p (x + y))) =
      coefficientInclusion pi' psi z dec p
        (TensorProduct.map theta LinearMap.id (coefficientRankOneProjection pi' psi z dec p x)) +
      coefficientInclusion pi' psi z dec p
        (TensorProduct.map theta LinearMap.id (coefficientRankOneProjection pi' psi z dec p y))
    simp only [map_add]
  map_smul' r x := by
    change (B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega') at x
    change coefficientInclusion pi' psi z dec p
      (TensorProduct.map theta LinearMap.id
        (coefficientRankOneProjection pi' psi z dec p (algebraMap A B' r • x))) =
      algebraMap A B' r • coefficientInclusion pi' psi z dec p
        (TensorProduct.map theta LinearMap.id (coefficientRankOneProjection pi' psi z dec p x))
    rw [map_smul, IsScalarTower.algebraMap_eq A B B', RingHom.comp_apply,
      IsScalarTower.algebraMap_smul, map_smul,
      ← IsScalarTower.algebraMap_smul B' (algebraMap A B r), map_smul]

private theorem alternatingMap_mem_of_base_and_cons
    {R V N : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup N] [Module R N] (p : ℕ) (F : V [⋀^Fin (p + 1)]→ₗ[R] N)
    (K : AddSubgroup N) (s : Set V) (z : V)
    (hbase : ∀ v : Fin (p + 1) → V, Set.range v ⊆ s → F v ∈ K)
    (hcons : ∀ v : Fin p → V, Set.range v ⊆ s → F (Fin.cons z v) ∈ K)
    (v : Fin (p + 1) → V) (hv : Set.range v ⊆ s ∪ {z}) : F v ∈ K := by
  classical
  by_cases hb : ∀ i, v i ∈ s
  · exact hbase v (Set.range_subset_iff.mpr hb)
  push Not at hb
  obtain ⟨i, hi⟩ := hb
  have hi' : v i = z := by simpa using (hv (Set.mem_range_self i)).resolve_left hi
  by_cases hr : ∃ j, j ≠ i ∧ v j = z
  · obtain ⟨j, hji, hj⟩ := hr
    rw [F.map_eq_zero_of_eq v (hj.trans hi'.symm) hji]
    exact K.zero_mem
  have hs : ∀ j, j ≠ i → v j ∈ s := by
    intro j hji
    rcases hv (Set.mem_range_self j) with hj | hj
    · exact hj
    · exact False.elim (hr ⟨j, hji, by simpa using hj⟩)
  let σ : Equiv.Perm (Fin (p + 1)) := Equiv.swap 0 i
  let w : Fin p → V := fun j => v (σ j.succ)
  have hw : Set.range w ⊆ s := by
    rintro _ ⟨j, rfl⟩
    apply hs
    intro heq
    exact Fin.succ_ne_zero j (σ.injective (heq.trans (Equiv.swap_apply_left 0 i).symm))
  have heq : v = (Fin.cons z w) ∘ σ := by
    funext j
    have hh : Fin.cons z w = v ∘ σ := by
      funext k
      refine Fin.cases ?_ (fun k => rfl) k
      simpa [σ] using hi'.symm
    rw [hh]
    simp [σ]
  rw [heq, F.map_perm]
  simpa only [Units.smul_def] using K.zsmul_mem (hcons w hw) (σ.sign : ℤ)

omit [SMulCommClass A' B B'] in
private theorem decomposition_span
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z) :
    Submodule.span B' (Set.range psi ∪ {SourceDeRham.targetD pi' z}) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  rw [← dec.equiv.apply_symm_apply x]
  obtain ⟨w, f⟩ := dec.equiv.symm x
  have hx : dec.equiv (w, f) = dec.equiv (w, 0) + dec.equiv (0, f) := by
    rw [← map_add]
    simp
  rw [hx, dec.equiv_dz]
  clear hx
  apply Submodule.add_mem
  · induction w using TensorProduct.inductionOn with
    | tmul f w =>
      rw [dec.equiv_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨w, rfl⟩))
    | add x y hx hy =>
      have heq : dec.equiv (x + y, 0) = dec.equiv (x, 0) + dec.equiv (y, 0) := by
        rw [← map_add]
        simp
      rw [heq]
      exact Submodule.add_mem _ hx hy
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr (Set.mem_singleton _)))

omit [SMulCommClass A' B B'] in
theorem tensorExterior_dz_induction
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z)
    (H : ∀ p, AddSubgroup ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')))
    (hbase : ∀ p (f : B') (m : M) (v : Fin p → Omega),
      (f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ v) ∈ H p)
    (hdz : ∀ p (f : B') (m : M) (v : Fin p → Omega),
      (f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' (p + 1)
        (Fin.cons (SourceDeRham.targetD pi' z) (psi ∘ v)) ∈ H (p + 1)) :
    ∀ p x, x ∈ H p := by
  intro p
  let K : Submodule B' (⋀[B']^p Omega') := {
    carrier := {w | ∀ f : B', ∀ m : M, (f ⊗ₜ[B] m) ⊗ₜ[B'] w ∈ H p}
    zero_mem' := by simp
    add_mem' := by
      intro w w' hw hw' f m
      simpa only [TensorProduct.tmul_add] using (H p).add_mem (hw f m) (hw' f m)
    smul_mem' := by
      intro g w hw f m
      simpa only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul]
        using hw (g * f) m }
  have hK : K = ⊤ := by
    apply top_unique
    rw [← exteriorPower.ιMulti_span_of_span B' p Omega' (decomposition_span pi' psi z dec),
      Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    change ∀ f m, _
    intro f m
    let F := (TensorProduct.mk B' (B' ⊗[B] M) (⋀[B']^p Omega') (f ⊗ₜ[B] m)).compAlternatingMap
      (exteriorPower.ιMulti B' p)
    have hbase' : ∀ v : Fin p → Omega', Set.range v ⊆ Set.range psi → F v ∈ H p := by
      intro v hv
      obtain ⟨w, rfl⟩ := Set.range_subset_range_iff_exists_comp.mp hv
      exact hbase p f m w
    cases p with
    | zero => exact hbase' v (Set.range_subset_iff.mpr fun i => Fin.elim0 i)
    | succ p =>
      apply alternatingMap_mem_of_base_and_cons p F (H (p + 1)) (Set.range psi)
        (SourceDeRham.targetD pi' z) hbase' ?_ v hv
      intro v hv
      obtain ⟨w, rfl⟩ := Set.range_subset_range_iff_exists_comp.mp hv
      exact hdz p f m w
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact (H p).add_mem hx hy
  | tmul m w =>
    have hw : w ∈ K := hK ▸ Submodule.mem_top
    induction m using TensorProduct.inductionOn with
    | tmul f m => exact hw f m
    | add x y hx hy => simpa only [TensorProduct.add_tmul] using (H p).add_mem hx hy

theorem tensorExterior_induction_of_span
    {R W N I : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    [AddCommGroup N] [Module R N] (g : I → W)
    (hg : Submodule.span R (Set.range g) = ⊤) (p : ℕ)
    (P : N ⊗[R] (⋀[R]^p W) → Prop)
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hwedge : ∀ m v, P (m ⊗ₜ[R] exteriorPower.ιMulti R p (g ∘ v)))
    (x : N ⊗[R] (⋀[R]^p W)) : P x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact hadd x y hx hy
  | tmul m w =>
    have hw : w ∈ Submodule.span R (exteriorPower.ιMulti R p ''
        {v : Fin p → W | Set.range v ⊆ Set.range g}) := by
      rw [exteriorPower.ιMulti_span_of_span R p W hg]
      exact Submodule.mem_top
    induction hw using Submodule.span_induction generalizing m with
    | mem w hw =>
      obtain ⟨v, hv, rfl⟩ := hw
      obtain ⟨a, rfl⟩ := Set.range_subset_range_iff_exists_comp.mp hv
      exact hwedge m a
    | zero => simpa using hzero
    | add x y _ _ hx hy => simpa [TensorProduct.tmul_add] using hadd _ _ (hx m) (hy m)
    | smul r x _ hx =>
      simpa only [TensorProduct.tmul_smul, TensorProduct.smul_tmul'] using hx (r • m)

theorem tensorExterior_induction
    {R W N : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    [AddCommGroup N] [Module R N] (p : ℕ) (P : N ⊗[R] (⋀[R]^p W) → Prop)
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hwedge : ∀ m v, P (m ⊗ₜ[R] exteriorPower.ιMulti R p v))
    (x : N ⊗[R] (⋀[R]^p W)) : P x :=
  tensorExterior_induction_of_span id (by simp) p P hzero hadd (by simpa using hwedge) x

omit [Algebra A A'] [IsScalarTower A B B'] [IsScalarTower A A' B'] in
omit [SMulCommClass A' B B'] in
theorem baseChangeMap_eq_coefficientInclusion
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z)
    (p : ℕ)
    (c : RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
      RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')))
    (hc : ∀ (m : M) (v : Fin p → Omega),
      c (m ⊗ₜ[B] exteriorPower.ιMulti B p v) =
        (1 ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ v))
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    c x = coefficientInclusion pi' psi z dec p (1 ⊗ₜ[B] x) := by
  induction x using tensorExterior_induction p with
  | hzero =>
    simp only [TensorProduct.tmul_zero, map_zero]
    exact c.map_zero
  | hadd x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add]
    exact (c.map_add x y).trans (congrArg₂ (· + ·) hx hy)
  | hwedge m v => rw [hc, coefficientInclusion_tmul_ιMulti]

omit [Algebra A A'] [IsScalarTower A B B'] [IsScalarTower A A' B'] in
omit [SMulCommClass A' B B'] in
theorem baseChangeMap_injective
    (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
    (dec : DzDecomposition pi' psi z)
    (huniv :
      Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{max u w}
        (Algebra.linearMap B B')) (p : ℕ)
    (c : RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
      RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')))
    (hc : ∀ (m : M) (v : Fin p → Omega),
      c (m ⊗ₜ[B] exteriorPower.ιMulti B p v) =
        (1 ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ v)) :
    Function.Injective c := by
  intro x y hxy
  change M ⊗[B] (⋀[B]^p Omega) at x y
  have h := congrArg (coefficientProjection pi' psi z dec p) hxy
  rw [baseChangeMap_eq_coefficientInclusion pi' psi z dec p c hc x,
    baseChangeMap_eq_coefficientInclusion pi' psi z dec p c hc y] at h
  have hcomp := coefficientProjection_comp_inclusion pi' psi z dec (M := M) p
  have hxy' : (1 : B') ⊗ₜ[B] x = (1 : B') ⊗ₜ[B] y := by
    simpa only [← LinearMap.comp_apply, hcomp, LinearMap.id_apply] using h
  have h' : (Algebra.linearMap B B').rTensor (M ⊗[B] (⋀[B]^p Omega))
      (1 ⊗ₜ[B] x) = (Algebra.linearMap B B').rTensor (M ⊗[B] (⋀[B]^p Omega))
      (1 ⊗ₜ[B] y) := by simpa using hxy'
  have hh := huniv (M ⊗[B] (⋀[B]^p Omega)) h'
  change (x : M ⊗[B] (⋀[B]^p Omega)) = y
  simpa using congrArg (TensorProduct.lid B (M ⊗[B] (⋀[B]^p Omega))) hh

end Crystalline

end
