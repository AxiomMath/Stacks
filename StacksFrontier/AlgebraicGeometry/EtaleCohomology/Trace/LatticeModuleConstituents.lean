module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingRestrictConstituents
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseRepresentation
public import Mathlib.RepresentationTheory.Basic

/-!
# Constituents modulo `ℓ` of lattices of a restricted representation

Let `ρₘ : Γ → GL_r(ℤ_ℓ)` and `φ : G' → Γ` be group homomorphisms, and let
`ρ_f : G' → GL_r(ℤ_ℓ)` be conjugate to `ρₘ ∘ φ` over `ℚ_ℓ`. Write `ℤ_ℓ^r` with `G` acting through
`ρ` as the `ℤ[G]`-module `Stacks.EtaleCohomology.LatticeModule ρ`, and
`Stacks.EtaleCohomology.latticeReduction ρₘ` for its reduction modulo `ℓ`.

If `Γ`, `G'`, `φ` are as in `Stacks.EtaleCohomology.exists_isCompl_comp_of_normal_factor` (a
normal subgroup `N ◁ Γ` on which `ρₘ` only depends on `π : Γ → P`, `π ∘ φ = ι ∘ π'` with `π'`
surjective and `ι` of normal range, `[G' : φ⁻¹ N]` prime to `ℓ`), then every simple subquotient
of `latticeReduction ρₘ` stays semisimple along `φ`
(`Stacks.EtaleCohomology.isSemisimpleModule_groupRingRestrict_latticeReduction`), and every
`ℤ_ℓ^r / ℓᵏ` with `G'` acting through `ρ_f` has its constituents in the restrictions of these
simple subquotients (`Stacks.EtaleCohomology.hasConstituentsIn_latticeModule_restrict`). This is
Brauer–Nesbitt for the two lattices `ℤ_ℓ^r` and `Q ℤ_ℓ^r` of `ρₘ ∘ φ ⊗ ℚ_ℓ`, after scaling one
into the other (`Stacks.EtaleCohomology.exists_latticeIntertwiners`).

## Main definitions

* `Stacks.EtaleCohomology.LatticeModule`, `Stacks.EtaleCohomology.latticeReduction`.

## Main results

* `Stacks.EtaleCohomology.exists_latticeIntertwiners`.
* `Stacks.EtaleCohomology.HasConstituentsIn.latticeModule_of_conj`.
* `Stacks.EtaleCohomology.isSemisimpleModule_groupRingRestrict_latticeReduction`.
* `Stacks.EtaleCohomology.hasConstituentsIn_latticeModule_restrict`.
-/

@[expose] public noncomputable section

universe v

open scoped Matrix

namespace Stacks.EtaleCohomology

open MonoidAlgebra

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

section Lattice

variable {G : Type*} [Group G]

/-- `ℤ_ℓ^r` with `G` acting through `ρ`, as a representation over `ℤ`. -/
def latticeRepresentation (ρ : G →* GL (Fin r) ℤ_[ℓ]) : Representation ℤ G (Fin r → ℤ_[ℓ]) where
  toFun g := (Matrix.mulVecLin (ρ g).val).restrictScalars ℤ
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    simp [Matrix.mulVec_mulVec]

/-- **The lattice `ℤ_ℓ^r` of `ρ`**, as a `ℤ[G]`-module. -/
abbrev LatticeModule (ρ : G →* GL (Fin r) ℤ_[ℓ]) : Type :=
  (latticeRepresentation ρ).asModule

/-- The identification of the lattice module with `ℤ_ℓ^r`. -/
abbrev latticeModuleEquiv (ρ : G →* GL (Fin r) ℤ_[ℓ]) : LatticeModule ρ ≃ₗ[ℤ] (Fin r → ℤ_[ℓ]) :=
  (latticeRepresentation ρ).asModuleEquiv

/-- The action of `of ℤ G g` on the lattice module is multiplication by the matrix `ρ g`. -/
theorem latticeModule_of_smul (ρ : G →* GL (Fin r) ℤ_[ℓ]) (g : G) (v : LatticeModule ρ) :
    latticeModuleEquiv ρ (of ℤ G g • v) = (ρ g).val *ᵥ latticeModuleEquiv ρ v := by
  rw [MonoidAlgebra.of_apply, Representation.single_smul, one_smul]
  rfl

/-- The `ℤ[G]`-linear map `ℤ_ℓ^r → ℤ_ℓ^r` given by an intertwining matrix. -/
def latticeModuleHom (ρ₁ ρ₂ : G →* GL (Fin r) ℤ_[ℓ]) (C : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hC : ∀ g, C * (ρ₂ g).val = (ρ₁ g).val * C) :
    LatticeModule ρ₂ →ₗ[MonoidAlgebra ℤ G] LatticeModule ρ₁ :=
  groupRingLinearMap ((latticeModuleEquiv ρ₁).symm.toLinearMap.toAddMonoidHom.comp
      ((Matrix.mulVecLin C).toAddMonoidHom.comp
        (latticeModuleEquiv ρ₂).toLinearMap.toAddMonoidHom)) fun g v => by
    apply (latticeModuleEquiv ρ₁).injective
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply,
      latticeModule_of_smul, Matrix.mulVec_mulVec, hC]

/-- The map `latticeModuleHom ρ₁ ρ₂ C hC` is multiplication by `C` on `ℤ_ℓ^r`. -/
theorem latticeModuleHom_apply (ρ₁ ρ₂ : G →* GL (Fin r) ℤ_[ℓ]) (C : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hC : ∀ g, C * (ρ₂ g).val = (ρ₁ g).val * C) (v : LatticeModule ρ₂) :
    latticeModuleEquiv ρ₁ (latticeModuleHom ρ₁ ρ₂ C hC v) = C *ᵥ latticeModuleEquiv ρ₂ v := by
  simp [latticeModuleHom]

/-- **Integral intertwiners of two rationally conjugate lattices**: if `ρ₂ = Q⁻¹ ρ₁ Q` over
`ℚ_ℓ`, then `C = ℓᵃ Q` and `D = ℓᵇ Q⁻¹` are integral for large `a`, `b`, intertwine `ρ₂` with `ρ₁`
and `ρ₁` with `ρ₂`, and `C D = D C = ℓᵃ⁺ᵇ`. -/
theorem exists_latticeIntertwiners (ρ₁ ρ₂ : G →* GL (Fin r) ℤ_[ℓ]) (Q : GL (Fin r) ℚ_[ℓ])
    (hQ : ∀ g, Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ)) (ρ₂ g) =
      Q⁻¹ * Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ)) (ρ₁ g) * Q) :
    ∃ (C D : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (n : ℕ),
      C * D = ((ℓ : ℤ_[ℓ]) ^ n) • 1 ∧ D * C = ((ℓ : ℤ_[ℓ]) ^ n) • 1 ∧
      (∀ g, C * (ρ₂ g).val = (ρ₁ g).val * C) ∧ (∀ g, D * (ρ₁ g).val = (ρ₂ g).val * D) := by
  obtain ⟨a, ha⟩ := exists_isIntegralMatrix_pow_smul (ℓ := ℓ) Q.val
  obtain ⟨b, hb⟩ := exists_isIntegralMatrix_pow_smul (ℓ := ℓ) (Q⁻¹ : GL (Fin r) ℚ_[ℓ]).val
  have hval : ∀ g, (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (ρ₂ g).val =
      (Q⁻¹ : GL (Fin r) ℚ_[ℓ]).val * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (ρ₁ g).val *
        Q.val := fun g => congrArg Units.val (hQ g)
  have hQQ'' : ∀ X : Matrix (Fin r) (Fin r) ℚ_[ℓ],
      Q.val * ((Q⁻¹ : GL (Fin r) ℚ_[ℓ]).val * X) = X :=
    fun X => by rw [← Matrix.mul_assoc, Q.mul_inv, Matrix.one_mul]
  have hsc : (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (((ℓ : ℤ_[ℓ]) ^ (a + b)) • 1) =
      ((ℓ : ℚ_[ℓ]) ^ a * (ℓ : ℚ_[ℓ]) ^ b) • (1 : Matrix (Fin r) (Fin r) ℚ_[ℓ]) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, pow_add]
  refine ⟨ha.lift, hb.lift, a + b, ?_, ?_, fun g => ?_, fun g => ?_⟩ <;>
    apply mapMatrix_padicInt_injective <;>
    simp only [map_mul, IsIntegralMatrix.mapMatrix_lift, hval, hsc, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, Q.mul_inv, Q.inv_mul, hQQ'', Matrix.mul_one,
      smul_smul, mul_comm]

variable {ι : Type*} {𝓜 : ι → Type} [∀ i, AddCommGroup (𝓜 i)]
  [∀ i, Module (MonoidAlgebra ℤ G) (𝓜 i)]

/-- **Brauer–Nesbitt for rationally conjugate integral representations**: if `ρ₂` is conjugate
to `ρ₁` over `ℚ_ℓ` and `ℤ_ℓ^r / ℓ` with `G` acting through `ρ₁` has its constituents in `𝓜`, so
has every `ℤ_ℓ^r / ℓᵏ` with `G` acting through `ρ₂`. -/
theorem HasConstituentsIn.latticeModule_of_conj (ρ₁ ρ₂ : G →* GL (Fin r) ℤ_[ℓ])
    (Q : GL (Fin r) ℚ_[ℓ])
    (hQ : ∀ g, Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ)) (ρ₂ g) =
      Q⁻¹ * Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ)) (ρ₁ g) * Q)
    (h : HasConstituentsIn (MonoidAlgebra ℤ G) 𝓜
      (LatticeModule ρ₁ ⧸ powSMulRange (MonoidAlgebra ℤ G) ℓ (LatticeModule ρ₁) 1)) (k : ℕ) :
    HasConstituentsIn (MonoidAlgebra ℤ G) 𝓜
      (LatticeModule ρ₂ ⧸ powSMulRange (MonoidAlgebra ℤ G) ℓ (LatticeModule ρ₂) k) := by
  obtain ⟨C, D, n, hCD, hDC, hC, hD⟩ := exists_latticeIntertwiners ρ₁ ρ₂ Q hQ
  have hpow : ∀ (E : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (v : Fin r → ℤ_[ℓ]),
      E = ((ℓ : ℤ_[ℓ]) ^ n) • 1 → E *ᵥ v = ℓ ^ n • v := by
    rintro E v rfl
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine h.of_isogeny (latticeModuleHom ρ₁ ρ₂ C hC) (latticeModuleHom ρ₂ ρ₁ D hD) n
    (fun x => ?_) (fun y => ?_) (fun y hy => ?_) k
  · apply (latticeModuleEquiv ρ₁).injective
    rw [latticeModuleHom_apply, latticeModuleHom_apply, Matrix.mulVec_mulVec, hpow _ _ hCD,
      map_nsmul]
  · apply (latticeModuleEquiv ρ₂).injective
    rw [latticeModuleHom_apply, latticeModuleHom_apply, Matrix.mulVec_mulVec, hpow _ _ hDC,
      map_nsmul]
  · apply (latticeModuleEquiv ρ₂).injective
    have hy' := congrArg (latticeModuleEquiv ρ₂) hy
    rw [map_nsmul, map_zero] at hy'
    rw [map_zero]
    funext i
    have hi := congrFun hy' i
    rw [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply, mul_eq_zero] at hi
    exact hi.resolve_left (Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero))

/-- **The reduction modulo `ℓ` of the lattice of `ρ`.** -/
abbrev latticeReduction (ρ : G →* GL (Fin r) ℤ_[ℓ]) : Type :=
  LatticeModule ρ ⧸ powSMulRange (MonoidAlgebra ℤ G) ℓ (LatticeModule ρ) 1

/-- The reduction modulo `ℓ` of a lattice is killed by `ℓ`. -/
theorem latticeReduction_nsmul_eq_zero (ρ : G →* GL (Fin r) ℤ_[ℓ]) (x : latticeReduction ρ) :
    ℓ • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact mem_powSMulRange.2 ⟨y, by rw [pow_one]⟩

/-- If `ρ g₁ = ρ g₂`, then `g₁` and `g₂` act in the same way on the reduction modulo `ℓ` of the
lattice of `ρ`. -/
theorem latticeReduction_of_smul_eq (ρ : G →* GL (Fin r) ℤ_[ℓ]) {g₁ g₂ : G} (h : ρ g₁ = ρ g₂)
    (x : latticeReduction ρ) : of ℤ G g₁ • x = of ℤ G g₂ • x := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
    congr 1
    apply (latticeModuleEquiv ρ).injective
    rw [latticeModule_of_smul, latticeModule_of_smul, h]

/-- The reduction modulo `ℓ` of a lattice is finite. -/
instance instFiniteLatticeReduction (ρ : G →* GL (Fin r) ℤ_[ℓ]) : Finite (latticeReduction ρ) := by
  refine Finite.of_surjective (fun x : Fin r → ZMod ℓ =>
    Submodule.Quotient.mk (p := powSMulRange (MonoidAlgebra ℤ G) ℓ (LatticeModule ρ) 1)
      ((latticeModuleEquiv ρ).symm fun i => (((x i).val : ℕ) : ℤ_[ℓ]))) ?_
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    refine ⟨fun i => PadicInt.toZMod (latticeModuleEquiv ρ v i), ?_⟩
    have hker : ∀ i, latticeModuleEquiv ρ v i -
        (((PadicInt.toZMod (latticeModuleEquiv ρ v i)).val : ℕ) : ℤ_[ℓ]) ∈
          Ideal.span {(ℓ : ℤ_[ℓ])} := by
      intro i
      rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub,
        map_natCast, ZMod.natCast_zmod_val, sub_self]
    choose c hc using fun i => Ideal.mem_span_singleton'.1 (hker i)
    refine ((Submodule.Quotient.eq _).2 (mem_powSMulRange.2
      ⟨(latticeModuleEquiv ρ).symm c, ?_⟩)).symm
    apply (latticeModuleEquiv ρ).injective
    rw [map_nsmul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, pow_one]
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul, mul_comm, hc i, Pi.sub_apply]

end Lattice

section Restrict

variable {Γ G' : Type*} [Group Γ] [Group G']

/-- The restriction along `φ` of the lattice of `ρ` is the lattice of `ρ ∘ φ`. -/
def groupRingRestrictLatticeModuleEquiv (ρ : Γ →* GL (Fin r) ℤ_[ℓ]) (φ : G' →* Γ) :
    GroupRingRestrict φ (LatticeModule ρ) ≃ₗ[MonoidAlgebra ℤ G'] LatticeModule (ρ.comp φ) :=
  LinearEquiv.ofLinear
    (groupRingLinearMap ((latticeModuleEquiv (ρ.comp φ)).symm.toLinearMap.toAddMonoidHom.comp
        ((latticeModuleEquiv ρ).toLinearMap.toAddMonoidHom.comp
          (toGroupRingRestrict φ).symm.toAddMonoidHom)) fun g x => by
      apply (latticeModuleEquiv (ρ.comp φ)).injective
      rw [groupRingRestrict_of_smul]
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, AddEquiv.coe_toAddMonoidHom,
        AddEquiv.symm_apply_apply, latticeModule_of_smul]
      rfl)
    (groupRingLinearMap ((toGroupRingRestrict φ).toAddMonoidHom.comp
        ((latticeModuleEquiv ρ).symm.toLinearMap.toAddMonoidHom.comp
          (latticeModuleEquiv (ρ.comp φ)).toLinearMap.toAddMonoidHom)) fun g x => by
      rw [groupRingRestrict_of_smul]
      apply congrArg (toGroupRingRestrict φ)
      apply (latticeModuleEquiv ρ).injective
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, AddEquiv.coe_toAddMonoidHom,
        AddEquiv.symm_apply_apply, latticeModule_of_smul]
      rfl)
    (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl)

omit [Fact ℓ.Prime] in
/-- The restriction along `φ` of the submodule `ℓᵏ M` is the submodule `ℓᵏ` of the restriction
of `M`. -/
theorem groupRingRestrictSubmodule_powSMulRange (φ : G' →* Γ) (M : Type*) [AddCommGroup M]
    [Module (MonoidAlgebra ℤ Γ) M] (k : ℕ) :
    groupRingRestrictSubmodule φ (powSMulRange (MonoidAlgebra ℤ Γ) ℓ M k) =
      powSMulRange (MonoidAlgebra ℤ G') ℓ (GroupRingRestrict φ M) k := by
  ext x
  rw [mem_groupRingRestrictSubmodule, mem_powSMulRange, mem_powSMulRange]
  rfl

/-- `(ℤ_ℓ^r, ρ ∘ φ) / ℓ` is the restriction along `φ` of `(ℤ_ℓ^r, ρ) / ℓ`. -/
def latticeReductionRestrictEquiv (ρ : Γ →* GL (Fin r) ℤ_[ℓ]) (φ : G' →* Γ) :
    (LatticeModule (ρ.comp φ) ⧸
        powSMulRange (MonoidAlgebra ℤ G') ℓ (LatticeModule (ρ.comp φ)) 1) ≃ₗ[MonoidAlgebra ℤ G']
      GroupRingRestrict φ (latticeReduction ρ) :=
  (Submodule.Quotient.equiv _ _ (groupRingRestrictLatticeModuleEquiv ρ φ).symm
      (powSMulRange_map_linearEquiv _ 1)).trans
    ((Submodule.quotEquivOfEq _ _ (groupRingRestrictSubmodule_powSMulRange φ _ 1).symm).trans
      (groupRingRestrictQuotientEquiv φ _))

variable {P P' : Type*} [Group P] [Group P']

/-- If `a` and `b` act in the same way on `M`, they act in the same way on every simple
subquotient of `M`. -/
theorem simpleSubquotient_smul_eq {A : Type*} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]
    (a b : A) (h : ∀ x : M, a • x = b • x) (j : SimpleSubquotientIndex A M)
    (x : simpleSubquotient A M j) : a • x = b • x := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (by rw [Submodule.coe_smul, Submodule.coe_smul, h])

/-- If `n` kills `M`, then `n` kills every simple subquotient of `M`. -/
theorem simpleSubquotient_nsmul_eq_zero {A : Type*} [Ring A] {M : Type v} [AddCommGroup M]
    [Module A M] (n : ℕ) (h : ∀ x : M, n • x = 0) (j : SimpleSubquotientIndex A M)
    (x : simpleSubquotient A M j) : n • x = 0 := by
  have h' := simpleSubquotient_smul_eq (n : A) 0
    (fun y => by rw [Nat.cast_smul_eq_nsmul, h, zero_smul]) j x
  rwa [Nat.cast_smul_eq_nsmul, zero_smul] at h'

/-- Every simple subquotient of a finite module is finite. -/
instance instFiniteSimpleSubquotient {A : Type*} [Ring A] {M : Type v} [AddCommGroup M]
    [Module A M] [Finite M] (j : SimpleSubquotientIndex A M) :
    Finite (simpleSubquotient A M j) :=
  Finite.of_surjective _ (Submodule.Quotient.mk_surjective j.2.1)

/-- **The simple subquotients of the reduction modulo `ℓ` of `ρₘ` stay semisimple along `φ`.** -/
theorem isSemisimpleModule_groupRingRestrict_latticeReduction (ρₘ : Γ →* GL (Fin r) ℤ_[ℓ])
    (φ : G' →* Γ) (π : Γ →* P) (π' : G' →* P') (hπ' : Function.Surjective π') (ι : P' →* P)
    [ι.range.Normal] (hcomm : ∀ g, π (φ g) = ι (π' g)) (N : Subgroup Γ) [N.Normal]
    (hfac : ∀ n₁ ∈ N, ∀ n₂ ∈ N, π n₁ = π n₂ → ρₘ n₁ = ρₘ n₂) [(N.comap φ).FiniteIndex]
    (hidx : ((N.comap φ).index : ZMod ℓ) ≠ 0)
    (j : SimpleSubquotientIndex (MonoidAlgebra ℤ Γ) (latticeReduction ρₘ)) :
    IsSemisimpleModule (MonoidAlgebra ℤ G')
      (GroupRingRestrict φ (simpleSubquotient _ _ j)) := by
  let : Module (ZMod ℓ) (simpleSubquotient _ _ j) := AddCommGroup.zmodModule
    (simpleSubquotient_nsmul_eq_zero ℓ (latticeReduction_nsmul_eq_zero ρₘ) j)
  exact isSemisimpleModule_groupRingRestrict_of_isSimpleModule ℓ φ π π' hπ' ι hcomm N
    (fun n₁ h₁ n₂ h₂ he x => simpleSubquotient_smul_eq _ _
      (latticeReduction_of_smul_eq ρₘ (hfac n₁ h₁ n₂ h₂ he)) j x) hidx

/-- **Constituents of a lattice conjugate to a restricted one**: if `ρ_f` is conjugate to `ρₘ ∘ φ`
over `ℚ_ℓ` and `Γ`, `G'`, `φ` are as in
`Stacks.EtaleCohomology.exists_isCompl_comp_of_normal_factor`, every `ℤ_ℓ^r / ℓᵏ` with `G'` acting
through `ρ_f` has its constituents in the restrictions along `φ` of the simple subquotients of the
reduction modulo `ℓ` of `ρₘ`. -/
theorem hasConstituentsIn_latticeModule_restrict (ρₘ : Γ →* GL (Fin r) ℤ_[ℓ])
    (ρf : G' →* GL (Fin r) ℤ_[ℓ]) (φ : G' →* Γ) (Q : GL (Fin r) ℚ_[ℓ])
    (hQ : ∀ g, Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ)) (ρf g) =
      Q⁻¹ * Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ)) (ρₘ (φ g)) * Q)
    (π : Γ →* P) (π' : G' →* P') (hπ' : Function.Surjective π') (ι : P' →* P)
    [ι.range.Normal] (hcomm : ∀ g, π (φ g) = ι (π' g)) (N : Subgroup Γ) [N.Normal]
    (hfac : ∀ n₁ ∈ N, ∀ n₂ ∈ N, π n₁ = π n₂ → ρₘ n₁ = ρₘ n₂) [(N.comap φ).FiniteIndex]
    (hidx : ((N.comap φ).index : ZMod ℓ) ≠ 0) (k : ℕ) :
    HasConstituentsIn (MonoidAlgebra ℤ G')
      (fun j : SimpleSubquotientIndex (MonoidAlgebra ℤ Γ) (latticeReduction ρₘ) =>
        GroupRingRestrict φ (simpleSubquotient _ _ j))
      (LatticeModule ρf ⧸ powSMulRange (MonoidAlgebra ℤ G') ℓ (LatticeModule ρf) k) := by
  have h₀ := HasConstituentsIn.groupRingRestrict φ (M := latticeReduction ρₘ)
    (isSemisimpleModule_groupRingRestrict_latticeReduction ρₘ φ π π' hπ' ι hcomm N hfac hidx)
  exact HasConstituentsIn.latticeModule_of_conj (ρₘ.comp φ) ρf Q hQ
    (h₀.of_linearEquiv (latticeReductionRestrictEquiv ρₘ φ).symm) k

end Restrict

end Stacks.EtaleCohomology

end
