module

public import StacksFrontier.RingTheory.Etale.Basic.DiagonalIdeal
public import StacksFrontier.RingTheory.DifferentialOperator.Defs
public import StacksFrontier.RingTheory.TensorProduct.IsBaseChangeSpan
import StacksFrontier.RingTheory.DifferentialOperator.PrincipalParts
import StacksCore.Tactic.StacksAttribute

/-!
# Principal parts under a formally étale extension

Along a formally étale `S → S'` the modules of principal parts base change: for an `S`-module `M`,
`S' ⊗[S] Pᵏ_{S/R}(M) = Pᵏ_{S'/R}(S' ⊗[S] M)`. Equivalently, a differential operator of order at
most `k` out of `M` with values in an `S'`-module extends uniquely to one out of `S' ⊗[S] M` of the
same order. For `M = S` and `k = 1` the module of principal parts is `Ω[S⁄R] × S`, and the first
coordinate of the identification is `KaehlerDifferential.isBaseChange_of_formallyEtale`. The proof
uses the base change of the powers of the diagonal ideal,
`KaehlerDifferential.isBaseChange_quotient_ideal_pow_of_formallyEtale`.

This file was split from `StacksFrontier.RingTheory.Etale.Basic`, which re-exports it.

## Main results

* `LinearMap.IsUniversalDifferentialOperatorOfOrderLE.isBaseChange_of_formallyEtale`: for `S → S'`
  formally étale, a module of principal parts of order `k` of `S' ⊗[S] M` over `R → S'` is the
  base change along `S → S'` of one of `M` over `R → S`, compatibly with the universal
  differential operators.
* `LinearMap.IsUniversalDifferentialOperatorOfOrderLE.existsUnique_isBaseChange_of_formallyEtale`:
  the comparison map exists and is unique.
* `LinearMap.IsUniversalDifferentialOperatorOfOrderLE.existsUnique_extension_of_formallyEtale`:
  a differential operator `M → N` of order at most `l` extends uniquely to a differential
  operator `S' ⊗[S] M → S' ⊗[S] N`, of order at most `l`.
* `LinearMap.IsUniversalDifferentialOperatorOfOrderLE.baseChange_of_formallyEtale`: both
  assertions together, Stacks 0H94.

## Implementation notes

The base change result is stated in the `IsBaseChange` form of
`KaehlerDifferential.isBaseChange_of_formallyEtale`, for an arbitrary base change `M'` of `M`, and
the comparison map `g` is characterised by its compatibility with the universal differential
operators.

## References

* [StacksProject 0H94](https://stacks.math.columbia.edu/tag/0H94)
-/

@[expose] public section

universe u v w x y

open scoped TensorProduct

/-! ### Principal parts under a formally étale extension -/

namespace LinearMap.IsUniversalDifferentialOperatorOfOrderLE

/-! #### Generalities on differential operators of finite order -/

section Order

variable {R S M N N₂ : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [Module S M] [IsScalarTower R S M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] [AddCommGroup N₂] [Module R N₂] [Module S N₂] [IsScalarTower R S N₂]

/-- An operator of order at most `0` is an `S`-linear map; this is that map. -/
private def toLinearMapOfOrderZero {D : M →ₗ[R] N} (hD : D.IsDifferentialOperatorOfOrderLE S 0) :
    M →ₗ[S] N where
  toFun := D
  map_add' := D.map_add
  map_smul' s m := isDifferentialOperatorOfOrderLE_zero_iff.mp hD s m

/-- Postcomposition with an `S`-linear map preserves the order of a differential operator. -/
private lemma orderLE_postcomp (φ : N →ₗ[S] N₂) {k : ℕ} {D : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) :
    (φ.restrictScalars R ∘ₗ D).IsDifferentialOperatorOfOrderLE S k := by
  induction k generalizing D with
  | zero => intro s m; simp [hD s m]
  | succ k ih =>
    rw [isDifferentialOperatorOfOrderLE_succ_iff]
    intro s
    have key : commSMul (φ.restrictScalars R ∘ₗ D) s = φ.restrictScalars R ∘ₗ commSMul D s := by
      ext m; simp [commSMul_apply]
    rw [key]
    exact ih (hD s)

/-- Precomposition with an `S`-linear map preserves the order of a differential operator. -/
private lemma orderLE_precomp {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] [Module S M₂]
    [IsScalarTower R S M₂] (ψ : M₂ →ₗ[S] M) {k : ℕ} {D : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) :
    (D ∘ₗ ψ.restrictScalars R).IsDifferentialOperatorOfOrderLE S k := by
  induction k generalizing D with
  | zero =>
    intro s m
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, map_smul]
    exact hD s (ψ m)
  | succ k ih =>
    rw [isDifferentialOperatorOfOrderLE_succ_iff]
    intro s
    have key : commSMul (D ∘ₗ ψ.restrictScalars R) s = commSMul D s ∘ₗ ψ.restrictScalars R := by
      ext m; simp [commSMul_apply]
    rw [key]
    exact ih (hD s)

/-- The order of a differential operator may be read off after an injective `S`-linear map. -/
private lemma orderLE_of_injective {φ : N →ₗ[S] N₂} (hφ : Function.Injective φ) :
    ∀ {k : ℕ} {D : M →ₗ[R] N}, (φ.restrictScalars R ∘ₗ D).IsDifferentialOperatorOfOrderLE S k →
      D.IsDifferentialOperatorOfOrderLE S k := by
  intro k
  induction k with
  | zero => intro D h s m; exact hφ (by simpa using h s m)
  | succ k ih =>
    intro D h
    rw [isDifferentialOperatorOfOrderLE_succ_iff]
    intro s
    refine ih ?_
    have key : φ.restrictScalars R ∘ₗ commSMul D s = commSMul (φ.restrictScalars R ∘ₗ D) s := by
      ext m; simp [commSMul_apply]
    rw [key]
    exact h s

private lemma commSMul_commSMul_comm (D : M →ₗ[R] N) (a b : S) :
    commSMul (commSMul D a) b = commSMul (commSMul D b) a := by
  ext m
  simp only [commSMul_apply, smul_sub, smul_comm a b]
  abel

end Order

/-! #### The universal property in an arbitrary universe -/

section Universal

variable {R : Type u} {S : Type v} {M : Type w} {P : Type x} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [AddCommGroup P] [Module R P]
  [Module S P] [IsScalarTower R S P]

/-- A universal differential operator generates its target over `S`. -/
private lemma span_range_eq_top {k : ℕ} {D : M →ₗ[R] P}
    (hD : D.IsUniversalDifferentialOperatorOfOrderLE S k) :
    Submodule.span S (Set.range D) = ⊤ := by
  set T := Submodule.span S (Set.range D)
  set u : (P ⧸ T) →ₗ[S] ULift.{max v w} (P ⧸ T) := ULift.moduleEquiv.symm.toLinearMap with hu
  obtain ⟨α, -, huq⟩ := hD.2 (N := ULift.{max v w} (P ⧸ T)) 0
    (LinearMap.zero_isDifferentialOperatorOfOrderLE k)
  have key : u ∘ₗ T.mkQ = 0 :=
    (huq _ fun m => by
        simp [(Submodule.Quotient.mk_eq_zero T).mpr (Submodule.subset_span ⟨m, rfl⟩)]).trans
      (huq 0 fun _ => rfl).symm
  have hinj : Function.Injective u := by rw [hu]; exact ULift.moduleEquiv.symm.injective
  rw [Submodule.eq_top_iff']
  intro p
  refine (Submodule.Quotient.mk_eq_zero T).mp (hinj ?_)
  simpa using LinearMap.congr_fun key p

/-- Two `S`-linear maps out of the target of a universal differential operator agree as soon as
they agree on the values of that operator. -/
private lemma eq_of_comp_eq {k : ℕ} {D : M →ₗ[R] P}
    (hD : D.IsUniversalDifferentialOperatorOfOrderLE S k) {N : Type y} [AddCommGroup N]
    [Module S N] {α β : P →ₗ[S] N} (h : ∀ m : M, α (D m) = β (D m)) : α = β := by
  refine LinearMap.ext_on (span_range_eq_top hD) ?_
  rintro p ⟨m, rfl⟩
  exact h m

/-- The universal property of a universal differential operator holds for test modules in every
universe, not only in the one it quantifies over. -/
private lemma existsUnique_comp_eq {k : ℕ} {D : M →ₗ[R] P}
    (hD : D.IsUniversalDifferentialOperatorOfOrderLE S k) {N : Type y} [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] {E : M →ₗ[R] N}
    (hE : E.IsDifferentialOperatorOfOrderLE S k) :
    ∃! α : P →ₗ[S] N, ∀ m : M, α (D m) = E m := by
  set β : (S ⊗[R] M) →ₗ[S] N := E.liftBaseChange S with hβ
  set K : Submodule S (S ⊗[R] M) := LinearMap.ker β with hK
  set ι : ((S ⊗[R] M) ⧸ K) →ₗ[S] N := K.liftQ β le_rfl with hι
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨z, rfl⟩ := K.mkQ_surjective z
    refine (Submodule.Quotient.mk_eq_zero K).mpr ?_
    have : β z = 0 := by simpa [hι] using hz
    simpa [hK, LinearMap.mem_ker] using this
  have hcomp : ∀ m : M, ι (K.mkQ ((1 : S) ⊗ₜ[R] m)) = E m := fun m => by simp [hι, hβ]
  set Ebar : M →ₗ[R] ((S ⊗[R] M) ⧸ K) :=
    K.mkQ.restrictScalars R ∘ₗ TensorProduct.mk R S M 1 with hEbar
  have hιEbar : ι.restrictScalars R ∘ₗ Ebar = E := by ext m; exact hcomp m
  have hEbarord : Ebar.IsDifferentialOperatorOfOrderLE S k := by
    refine orderLE_of_injective hιinj ?_
    rw [hιEbar]
    exact hE
  set e : ((S ⊗[R] M) ⧸ K) ≃ₗ[S] ULift.{x} ((S ⊗[R] M) ⧸ K) := ULift.moduleEquiv.symm with he
  obtain ⟨α₀, hα₀, -⟩ := hD.2 (N := ULift.{x} ((S ⊗[R] M) ⧸ K))
    (e.toLinearMap.restrictScalars R ∘ₗ Ebar) (orderLE_postcomp e.toLinearMap hEbarord)
  have hα : ∀ m : M, (ι ∘ₗ e.symm.toLinearMap ∘ₗ α₀) (D m) = E m := fun m => by
    have h := hα₀ m
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars] at h ⊢
    rw [h]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hcomp m
  exact ⟨_, hα, fun α₁ h₁ => eq_of_comp_eq hD fun m => (h₁ m).trans (hα m).symm⟩

end Universal

/-! #### The jets of a differential operator -/

section Jets

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [Module S M] [IsScalarTower R S M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- The action of the diagonal algebra `S ⊗[R] S` on `S ⊗[R] M`, given by
`(a ⊗ₜ b) • (t ⊗ₜ m) = a t ⊗ₜ b • m`, as an `R`-algebra map into the `R`-linear endomorphisms:
multiplication in the left factor and the action of the right factor on `M` commute. -/
private noncomputable def diagonalEnd : (S ⊗[R] S) →ₐ[R] Module.End R (S ⊗[R] M) :=
  Algebra.TensorProduct.lift (Algebra.lsmul R R (S ⊗[R] M))
    ((Module.End.lTensorAlgHom R M S).comp (Algebra.lsmul R R M))
    (fun a b => by
      refine LinearMap.ext fun z => ?_
      induction z with
      | tmul t m =>
        simp [Module.End.lTensorAlgHom, LinearMap.lTensorHom, LinearMap.lTensor_tmul,
          TensorProduct.smul_tmul']
      | add x y hx hy => simp_all [Module.End.mul_apply])

private lemma diagonalEnd_tmul_tmul (a b t : S) (m : M) :
    diagonalEnd (R := R) (M := M) (a ⊗ₜ[R] b) (t ⊗ₜ[R] m) = (a * t) ⊗ₜ[R] (b • m) := by
  simp [diagonalEnd, Module.End.lTensorAlgHom, LinearMap.lTensorHom, LinearMap.lTensor_tmul,
    TensorProduct.smul_tmul', smul_eq_mul]

/-- The left factor acts through the `S`-module structure of `S ⊗[R] M`. -/
private lemma diagonalEnd_algebraMap (s : S) (z : S ⊗[R] M) :
    diagonalEnd (R := R) (M := M) (algebraMap S (S ⊗[R] S) s) z = s • z := by
  induction z with
  | tmul t m =>
    rw [Algebra.TensorProduct.algebraMap_apply, diagonalEnd_tmul_tmul]
    simp [TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

/-- The right-hand structure map `S → (S ⊗[R] S) ⧸ J ^ (k + 1)`, `s ↦ class of 1 ⊗ₜ s`, where
`J = Ker(S ⊗[R] S → S)`. It agrees with the left-hand structure map `algebraMap` modulo `J`. -/
private noncomputable def rho (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (k : ℕ) :
    S →ₐ[R] ((S ⊗[R] S) ⧸ KaehlerDifferential.ideal R S ^ (k + 1)) :=
  (Ideal.Quotient.mkₐ R _).comp Algebra.TensorProduct.includeRight

private lemma rho_apply (k : ℕ) (s : S) :
    rho R S k s = Ideal.Quotient.mk _ ((1 : S) ⊗ₜ[R] s) := rfl

/-- **The jets of a differential operator of finite order.** A differential operator
`E : M → N` of order at most `k` relative to `R → S` is the same datum as an `S`-linear map
`u : (S ⊗[R] S) ⧸ J ^ (k + 1) → Hom_R(M, N)` satisfying `u (q ρ s) = u q ∘ (s • ·)`, the operator
being `u 1`: indeed `u (class of (a ⊗ₜ b)) m = a • E (b • m)`, which is well defined precisely
because `E` has order at most `k`. -/
private theorem exists_jet_of_orderLE (k : ℕ) {E : M →ₗ[R] N}
    (hE : E.IsDifferentialOperatorOfOrderLE S k) :
    ∃ u : ((S ⊗[R] S) ⧸ KaehlerDifferential.ideal R S ^ (k + 1)) →ₗ[S] (M →ₗ[R] N),
      (∀ (q : (S ⊗[R] S) ⧸ KaehlerDifferential.ideal R S ^ (k + 1)) (s : S) (m : M),
          u (q * rho R S k s) m = u q (s • m)) ∧
        ∀ m : M, u 1 m = E m := by
  let _inst : Module (S ⊗[R] S) (S ⊗[R] M) :=
    Module.compHom _ (diagonalEnd (R := R) (S := S) (M := M)).toRingHom
  have hact : ∀ (q : S ⊗[R] S) (z : S ⊗[R] M), q • z = diagonalEnd q z := fun _ _ => rfl
  have hsmul : ∀ (a b t : S) (m : M), (a ⊗ₜ[R] b) • (t ⊗ₜ[R] m) = (a * t) ⊗ₜ[R] (b • m) :=
    fun a b t m => (hact _ _).trans (diagonalEnd_tmul_tmul a b t m)
  have : IsScalarTower S (S ⊗[R] S) (S ⊗[R] M) :=
    ⟨fun s q z => by
      change diagonalEnd (s • q) z = s • diagonalEnd q z
      rw [Algebra.smul_def, map_mul, Module.End.mul_apply, diagonalEnd_algebraMap]⟩
  obtain ⟨α, hα, -⟩ := existsUnique_comp_eq
    (LinearMap.isUniversalDifferentialOperatorOfOrderLE_mkQ_comp_mk_one
      (R := R) (S := S) (M := M) hsmul k) hE
  set β : (S ⊗[R] M) →ₗ[S] N := α ∘ₗ ((KaehlerDifferential.ideal R S ^ (k + 1) •
    (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))).restrictScalars S).mkQ with hβdef
  have hβ1 : ∀ m : M, β ((1 : S) ⊗ₜ[R] m) = E m := fun m => hα m
  have hβ0 : ∀ q ∈ KaehlerDifferential.ideal R S ^ (k + 1), ∀ z : S ⊗[R] M, β (q • z) = 0 := by
    intro q hq z
    have hmem : q • z ∈ (KaehlerDifferential.ideal R S ^ (k + 1) •
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))).restrictScalars S :=
      (Submodule.restrictScalars_mem S _ _).mpr (Submodule.smul_mem_smul hq Submodule.mem_top)
    have hmk : ((KaehlerDifferential.ideal R S ^ (k + 1) •
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))).restrictScalars S).mkQ (q • z) = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hmem
    rw [hβdef, LinearMap.comp_apply, hmk, map_zero]
  let w : (S ⊗[R] S) →ₗ[S] (M →ₗ[R] N) :=
    { toFun := fun q => β.restrictScalars R ∘ₗ diagonalEnd q ∘ₗ TensorProduct.mk R S M 1
      map_add' := fun q q' => LinearMap.ext fun m => by
        change β (diagonalEnd (q + q') ((1 : S) ⊗ₜ[R] m)) =
          β (diagonalEnd q ((1 : S) ⊗ₜ[R] m)) + β (diagonalEnd q' ((1 : S) ⊗ₜ[R] m))
        rw [map_add, LinearMap.add_apply, map_add]
      map_smul' := fun s q => LinearMap.ext fun m => by
        change β (diagonalEnd (s • q) ((1 : S) ⊗ₜ[R] m)) = s • β (diagonalEnd q ((1 : S) ⊗ₜ[R] m))
        rw [Algebra.smul_def, map_mul, Module.End.mul_apply, diagonalEnd_algebraMap, map_smul] }
  have hwapp : ∀ (q : S ⊗[R] S) (m : M), w q m = β (diagonalEnd q ((1 : S) ⊗ₜ[R] m)) :=
    fun _ _ => rfl
  have hker : (KaehlerDifferential.ideal R S ^ (k + 1)).restrictScalars S ≤ LinearMap.ker w := by
    intro q hq
    refine LinearMap.ext fun m => ?_
    rw [hwapp, ← hact, hβ0 q ((Submodule.restrictScalars_mem S _ _).mp hq)]
    rfl
  refine ⟨Submodule.liftQ ((KaehlerDifferential.ideal R S ^ (k + 1)).restrictScalars S) w hker,
    ?_, ?_⟩
  · intro q s m
    obtain ⟨q₀, rfl⟩ :=
      Ideal.Quotient.mk_surjective (I := KaehlerDifferential.ideal R S ^ (k + 1)) q
    rw [rho_apply, ← map_mul]
    change w (q₀ * ((1 : S) ⊗ₜ[R] s)) m = w q₀ (s • m)
    rw [hwapp, hwapp, map_mul, Module.End.mul_apply, diagonalEnd_tmul_tmul, one_mul]
  · intro m
    change w 1 m = E m
    rw [hwapp, map_one]
    exact hβ1 m

end Jets

/-! #### The transport of a jet along a formally étale extension -/

section Transport

variable {R S S' M N : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
  [Algebra S S'] [IsScalarTower R S S'] [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M] [AddCommGroup N] [Module R N] [Module S N] [Module S' N]
  [IsScalarTower R S' N] [IsScalarTower S S' N] [IsScalarTower R S N]

/-- The canonical `S`-algebra map `S ⊗[R] S → S' ⊗[R] S'`, `a ⊗ₜ b ↦ a ⊗ₜ b`. -/
private def diagonalMap : (S ⊗[R] S) →ₐ[S] (S' ⊗[R] S') :=
  Algebra.TensorProduct.map (Algebra.ofId S S') (IsScalarTower.toAlgHom R S S')

private lemma diagonalMap_tmul (a b : S) :
    diagonalMap (R := R) (S' := S') (a ⊗ₜ[R] b) =
      algebraMap S S' a ⊗ₜ[R] algebraMap S S' b :=
  Algebra.TensorProduct.map_tmul _ _ _ _

/-- `diagonalMap` commutes with the two multiplication maps. -/
private lemma lmul'_diagonalMap (x : S ⊗[R] S) :
    (Algebra.TensorProduct.lmul' R : (S' ⊗[R] S') →ₐ[R] S') (diagonalMap (S' := S') x) =
      algebraMap S S' (Algebra.TensorProduct.lmul' R x) := by
  induction x with
  | tmul a b =>
    rw [diagonalMap_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `diagonalMap` carries the diagonal ideal of `S` into the diagonal ideal of `S'`. -/
private lemma ideal_map_diagonalMap_le :
    (KaehlerDifferential.ideal R S).map (diagonalMap (R := R) (S' := S')) ≤
      KaehlerDifferential.ideal R S' := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap]
  exact RingHom.mem_ker.mpr (by rw [lmul'_diagonalMap x, RingHom.mem_ker.mp hx, map_zero])

/-- The additive map `S' ⊗[S] M → N`, `b ⊗ₜ m ↦ v (1 ⊗ₜ b) m`, attached to a jet `v`. The
balancing hypothesis on `v` is exactly what makes it well defined over `S`. -/
private def jetAddHom (v : (S' ⊗[R] S') →ₗ[S'] (M →ₗ[R] N))
    (hv : ∀ (q : S' ⊗[R] S') (s : S) (m : M),
      v (q * ((1 : S') ⊗ₜ[R] algebraMap S S' s)) m = v q (s • m)) :
    (S' ⊗[S] M) →+ N :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b : S' => (v ((1 : S') ⊗ₜ[R] b)).toAddMonoidHom)
      (fun a b => by ext m; simp [TensorProduct.tmul_add]))
    (fun s b m => by
      have h1 : (1 : S') ⊗ₜ[R] (s • b) =
          ((1 : S') ⊗ₜ[R] b) * ((1 : S') ⊗ₜ[R] algebraMap S S' s) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def, mul_comm]
      exact (congrArg (fun q => v q m) h1).trans (hv _ s m))

omit [Algebra R S] [IsScalarTower R S S'] [IsScalarTower R S M] [Module S N]
  [IsScalarTower S S' N] [IsScalarTower R S N] in
private lemma jetAddHom_tmul (v : (S' ⊗[R] S') →ₗ[S'] (M →ₗ[R] N))
    (hv : ∀ (q : S' ⊗[R] S') (s : S) (m : M),
      v (q * ((1 : S') ⊗ₜ[R] algebraMap S S' s)) m = v q (s • m)) (b : S') (m : M) :
    jetAddHom v hv (b ⊗ₜ[S] m) = v ((1 : S') ⊗ₜ[R] b) m :=
  TensorProduct.liftAddHom_tmul _ _ _ _

/-- The `R`-linear map `S' ⊗[S] M → N`, `b ⊗ₜ m ↦ v (1 ⊗ₜ b) m`, attached to a jet `v`: the
differential operator that `v` encodes. -/
private def opOfJet (v : (S' ⊗[R] S') →ₗ[S'] (M →ₗ[R] N))
    (hv : ∀ (q : S' ⊗[R] S') (s : S) (m : M),
      v (q * ((1 : S') ⊗ₜ[R] algebraMap S S' s)) m = v q (s • m)) :
    (S' ⊗[S] M) →ₗ[R] N where
  toFun := jetAddHom v hv
  map_add' := (jetAddHom v hv).map_add
  map_smul' r z := by
    simp only [RingHom.id_apply]
    induction z with
    | tmul b m =>
      rw [TensorProduct.smul_tmul', jetAddHom_tmul, jetAddHom_tmul, TensorProduct.tmul_smul,
        ← algebraMap_smul S' r ((1 : S') ⊗ₜ[R] b), map_smul, LinearMap.smul_apply,
        algebraMap_smul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

omit [IsScalarTower R S M] [Module S N] [IsScalarTower S S' N] [IsScalarTower R S N] in
private lemma opOfJet_tmul (v : (S' ⊗[R] S') →ₗ[S'] (M →ₗ[R] N))
    (hv : ∀ (q : S' ⊗[R] S') (s : S) (m : M),
      v (q * ((1 : S') ⊗ₜ[R] algebraMap S S' s)) m = v q (s • m)) (b : S') (m : M) :
    opOfJet v hv (b ⊗ₜ[S] m) = v ((1 : S') ⊗ₜ[R] b) m :=
  jetAddHom_tmul v hv b m

omit [IsScalarTower R S M] [Module S N] [IsScalarTower S S' N] [IsScalarTower R S N] in
private lemma opOfJet_eq_zero (v : (S' ⊗[R] S') →ₗ[S'] (M →ₗ[R] N))
    (hv : ∀ (q : S' ⊗[R] S') (s : S) (m : M),
      v (q * ((1 : S') ⊗ₜ[R] algebraMap S S' s)) m = v q (s • m)) (h : ∀ q, v q = 0) :
    opOfJet v hv = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z with
  | tmul b m => rw [opOfJet_tmul, h]; simp
  | add x y hx hy => rw [map_add, hx, hy]; simp

omit [Algebra R S] [IsScalarTower R S S'] [IsScalarTower R S M] [Module S N]
  [IsScalarTower S S' N] [IsScalarTower R S N] in
/-- Multiplying a jet on the left by a fixed element of `S' ⊗[R] S'` gives a jet. -/
private lemma jet_mulLeft (v : (S' ⊗[R] S') →ₗ[S'] (M →ₗ[R] N))
    (hv : ∀ (q : S' ⊗[R] S') (s : S) (m : M),
      v (q * ((1 : S') ⊗ₜ[R] algebraMap S S' s)) m = v q (s • m)) (a : S' ⊗[R] S') :
    ∀ (q : S' ⊗[R] S') (s : S) (m : M),
      (v ∘ₗ LinearMap.mulLeft S' a) (q * ((1 : S') ⊗ₜ[R] algebraMap S S' s)) m =
        (v ∘ₗ LinearMap.mulLeft S' a) q (s • m) := by
  intro q s m
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, ← mul_assoc]
  exact hv _ s m

omit [IsScalarTower R S M] [Module S N] [IsScalarTower S S' N] [IsScalarTower R S N] in
/-- The commutator of the operator attached to a jet with multiplication by `b : S'` is the
operator attached to the jet multiplied by `1 ⊗ₜ b - b ⊗ₜ 1`, an element of the diagonal
ideal. -/
private lemma commSMul_opOfJet (v : (S' ⊗[R] S') →ₗ[S'] (M →ₗ[R] N))
    (hv : ∀ (q : S' ⊗[R] S') (s : S) (m : M),
      v (q * ((1 : S') ⊗ₜ[R] algebraMap S S' s)) m = v q (s • m)) (b : S') :
    commSMul (opOfJet v hv) b =
      opOfJet (v ∘ₗ LinearMap.mulLeft S' ((1 : S') ⊗ₜ[R] b - b ⊗ₜ[R] (1 : S')))
        (jet_mulLeft v hv _) := by
  refine LinearMap.ext fun z => ?_
  induction z with
  | tmul c m =>
    have hb : v (b ⊗ₜ[R] c) m = b • v ((1 : S') ⊗ₜ[R] c) m := by
      rw [show b ⊗ₜ[R] c = b • ((1 : S') ⊗ₜ[R] c) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, LinearMap.smul_apply]
    rw [commSMul_apply, TensorProduct.smul_tmul', opOfJet_tmul, opOfJet_tmul, opOfJet_tmul]
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, sub_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, map_sub, LinearMap.sub_apply,
      smul_eq_mul]
    rw [hb]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [IsScalarTower R S M] [Module S N] [IsScalarTower S S' N] [IsScalarTower R S N] in
/-- A jet vanishing on the `(j + 1)`-st power of the diagonal ideal of `S'` gives a differential
operator of order at most `j` relative to `R → S'`. -/
private lemma orderLE_opOfJet : ∀ {j : ℕ} (v : (S' ⊗[R] S') →ₗ[S'] (M →ₗ[R] N))
    (hv : ∀ (q : S' ⊗[R] S') (s : S) (m : M),
      v (q * ((1 : S') ⊗ₜ[R] algebraMap S S' s)) m = v q (s • m)),
    (∀ q ∈ KaehlerDifferential.ideal R S' ^ (j + 1), v q = 0) →
      (opOfJet v hv).IsDifferentialOperatorOfOrderLE S' j := by
  intro j
  induction j with
  | zero =>
    intro v hv h b y
    have hzero : commSMul (opOfJet v hv) b = 0 := by
      rw [commSMul_opOfJet]
      refine opOfJet_eq_zero _ _ fun q => ?_
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      refine h _ ?_
      rw [zero_add, pow_one]
      exact Ideal.mul_mem_right q _
        (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b)
    have h1 := LinearMap.congr_fun hzero y
    rw [commSMul_apply] at h1
    simpa using eq_of_sub_eq_zero (by simpa using h1)
  | succ j ih =>
    intro v hv h
    rw [isDifferentialOperatorOfOrderLE_succ_iff]
    intro b
    rw [commSMul_opOfJet]
    refine ih _ _ fun q hq => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    refine h _ ?_
    rw [pow_succ' (KaehlerDifferential.ideal R S') (j + 1)]
    exact Ideal.mul_mem_mul (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b) hq

end Transport

/-! #### Extension of a differential operator along the base change -/

section Extension

variable {R S S' M M' N : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
  [Algebra R S'] [Algebra S S'] [IsScalarTower R S S'] [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M] [AddCommGroup M'] [Module R M'] [Module S M'] [Module S' M']
  [IsScalarTower R S' M'] [IsScalarTower S S' M'] [IsScalarTower R S M'] [AddCommGroup N]
  [Module R N] [Module S N] [Module S' N] [IsScalarTower R S' N] [IsScalarTower S S' N]
  [IsScalarTower R S N]

/-- If `S → S'` is formally unramified then `Ω[S'⁄S] = 0`, so `S'` carries no nonzero
`S`-derivation with values in an `S'`-module. -/
private lemma subsingleton_derivation [Algebra.FormallyUnramified S S'] (V : Type*)
    [AddCommGroup V] [Module S V] [Module S' V] [IsScalarTower S S' V] :
    Subsingleton (Derivation S S' V) := by
  have hΩ : Subsingleton Ω[S'⁄S] := Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have : Subsingleton (Ω[S'⁄S] →ₗ[S'] V) :=
    ⟨fun a b => LinearMap.ext fun x => by rw [hΩ.elim x 0, map_zero, map_zero]⟩
  exact (KaehlerDifferential.linearMapEquivDerivation S S').symm.injective.subsingleton

omit [Algebra R S] [IsScalarTower R S S'] [Module S M'] [IsScalarTower S S' M']
  [IsScalarTower R S M'] [IsScalarTower R S N] in
/-- If `S → S'` is formally unramified, an operator of finite order relative to `R → S'` which
commutes with the scalars coming from `S` is already `S'`-linear. -/
private lemma orderLE_zero_of_commSMul_algebraMap [Algebra.FormallyUnramified S S'] :
    ∀ {k : ℕ} {F : M' →ₗ[R] N}, F.IsDifferentialOperatorOfOrderLE S' k →
      (∀ s : S, commSMul F (algebraMap S S' s) = 0) →
      F.IsDifferentialOperatorOfOrderLE S' 0 := by
  intro k
  induction k with
  | zero => intro F hF _; exact hF
  | succ k ih =>
    intro F hF h0
    have hcomm : ∀ s' : S', (commSMul F s').IsDifferentialOperatorOfOrderLE S' 0 := by
      intro s'
      refine ih (hF s') fun s => ?_
      rw [commSMul_commSMul_comm, h0 s, commSMul_zero_left]
    have hlin : ∀ (s' c : S') (y : M'), commSMul F s' (c • y) = c • commSMul F s' y :=
      fun s' => hcomm s'
    have hleib : ∀ (a b : S') (y : M'),
        commSMul F (a * b) y = a • commSMul F b y + b • commSMul F a y := by
      intro a b y
      rw [commSMul_mul_apply F a b y, hlin a b y]
      abel
    let d : Derivation S S' (M' →ₗ[S'] N) :=
      { toFun := fun s' => toLinearMapOfOrderZero (hcomm s')
        map_add' := by
          intro a b
          ext y
          change commSMul F (a + b) y = commSMul F a y + commSMul F b y
          simp only [commSMul_apply, add_smul, map_add]
          abel
        map_smul' := by
          intro c a
          ext y
          change commSMul F (c • a) y = c • commSMul F a y
          rw [Algebra.smul_def, hleib, h0 c]
          simp [algebraMap_smul]
        map_one_eq_zero' := by
          ext y
          change commSMul F 1 y = 0
          simp [commSMul_apply]
        leibniz' := by
          intro a b
          ext y
          change commSMul F (a * b) y = _
          rw [hleib a b y]
          rfl }
    intro s' y
    have : Subsingleton (Derivation S S' (M' →ₗ[S'] N)) := subsingleton_derivation _
    have h1 : d s' = 0 := by rw [Subsingleton.elim d 0]; simp
    have h2 : commSMul F s' y = 0 := by
      have h := congrArg (fun φ : M' →ₗ[S'] N => φ y) h1
      simp only [LinearMap.zero_apply] at h
      exact h
    rw [commSMul_apply] at h2
    exact eq_of_sub_eq_zero h2

omit [Algebra R S] [Module R M] [IsScalarTower R S M] [IsScalarTower R S S']
  [IsScalarTower R S M'] [IsScalarTower R S N] in
/-- **Uniqueness of the extension.** If `S → S'` is formally unramified, an operator of finite
order relative to `R → S'` vanishing on the image of `M` in the base change `M'` is zero. -/
private lemma eq_zero_of_orderLE_of_comp_eq_zero [Algebra.FormallyUnramified S S']
    {f : M →ₗ[S] M'} (hf : IsBaseChange S' f) :
    ∀ {k : ℕ} {F : M' →ₗ[R] N}, F.IsDifferentialOperatorOfOrderLE S' k →
      (∀ m : M, F (f m) = 0) → F = 0 := by
  have hspan : Submodule.span S' (Set.range f) = ⊤ := IsBaseChange.span_range_eq_top hf
  have base : ∀ {F : M' →ₗ[R] N}, F.IsDifferentialOperatorOfOrderLE S' 0 →
      (∀ m : M, F (f m) = 0) → F = 0 := by
    intro F hF h0
    have hz : toLinearMapOfOrderZero hF = 0 := by
      refine LinearMap.ext_on hspan ?_
      rintro y ⟨m, rfl⟩
      change F (f m) = 0
      exact h0 m
    ext y
    have := congrArg (fun φ : M' →ₗ[S'] N => φ y) hz
    simpa [toLinearMapOfOrderZero] using this
  intro k
  induction k with
  | zero => intro F hF h0; exact base hF h0
  | succ k ih =>
    intro F hF h0
    refine base (orderLE_zero_of_commSMul_algebraMap (S := S) hF fun s => ?_) h0
    refine ih (hF (algebraMap S S' s)) fun m => ?_
    rw [commSMul_apply, algebraMap_smul, ← map_smul f s m, h0, h0, smul_zero, sub_zero]

omit [IsScalarTower R S M] [IsScalarTower R S M'] in
/-- **Extension of a jet.** If `S → S'` is formally étale, a jet `u` over `S` with values in
`Hom_R(M, N)`, for an `S'`-module `N`, gives a differential operator `M' → N` of order at most `k`
relative to `R → S'` which agrees with `u 1` on the image of `M`. -/
private theorem exists_extension_of_jet [Algebra.FormallyEtale S S'] {f : M →ₗ[S] M'}
    (hf : IsBaseChange S' f) (k : ℕ)
    (u : ((S ⊗[R] S) ⧸ KaehlerDifferential.ideal R S ^ (k + 1)) →ₗ[S] (M →ₗ[R] N))
    (hu : ∀ (q : (S ⊗[R] S) ⧸ KaehlerDifferential.ideal R S ^ (k + 1)) (s : S) (m : M),
      u (q * rho R S k s) m = u q (s • m)) :
    ∃ E' : M' →ₗ[R] N, E'.IsDifferentialOperatorOfOrderLE S' k ∧ ∀ m : M, E' (f m) = u 1 m := by
  have hcomap : KaehlerDifferential.ideal R S ^ (k + 1) ≤ Ideal.comap
      (diagonalMap (R := R) (S' := S')) (KaehlerDifferential.ideal R S' ^ (k + 1)) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono ideal_map_diagonalMap_le _
  set φ : ((S ⊗[R] S) ⧸ KaehlerDifferential.ideal R S ^ (k + 1)) →ₐ[S]
      ((S' ⊗[R] S') ⧸ KaehlerDifferential.ideal R S' ^ (k + 1)) :=
    Ideal.quotientMapₐ _ diagonalMap hcomap with hφdef
  have hφmk : ∀ x : S ⊗[R] S, φ (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (diagonalMap (R := R) (S' := S') x) := fun _ => rfl
  have hbc := KaehlerDifferential.isBaseChange_quotient_ideal_pow_of_formallyEtale (k + 1) φ
    (fun a b => by rw [hφmk, diagonalMap_tmul])
  set u' := hbc.lift u with hu'def
  have hlift : ∀ q, u' (φ q) = u q := fun q => hbc.lift_eq u q
  set v : (S' ⊗[R] S') →ₗ[S'] (M →ₗ[R] N) :=
    u' ∘ₗ Submodule.mkQ ((KaehlerDifferential.ideal R S' ^ (k + 1)).restrictScalars S') with hvdef
  have hvapp : ∀ q : S' ⊗[R] S', v q = u' (Ideal.Quotient.mk _ q) := fun _ => rfl
  have hvzero : ∀ q ∈ KaehlerDifferential.ideal R S' ^ (k + 1), v q = 0 := by
    intro q hq
    rw [hvapp, Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
  have hspan : Submodule.span S' (Set.range φ.toLinearMap) = ⊤ :=
    IsBaseChange.span_range_eq_top hbc
  have hkey : ∀ (s : S) (m : M)
      (x : (S' ⊗[R] S') ⧸ KaehlerDifferential.ideal R S' ^ (k + 1)),
      u' (x * φ (rho R S k s)) m = u' x (s • m) := by
    intro s m x
    have hx : x ∈ Submodule.span S' (Set.range φ.toLinearMap) := by
      rw [hspan]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, rfl⟩ := hy
      change u' (φ q * φ (rho R S k s)) m = u' (φ q) (s • m)
      rw [← map_mul φ, hlift, hlift]
      exact hu q s m
    | zero => simp
    | add a b _ _ ha hb =>
      rw [add_mul, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb]
    | smul c a _ ha =>
      have h1 : u' (c • a * φ (rho R S k s)) = c • u' (a * φ (rho R S k s)) := by
        rw [smul_mul_assoc, map_smul]
      rw [h1, map_smul u' c a]
      change c • (u' (a * φ (rho R S k s))) m = c • (u' a) (s • m)
      rw [ha]
  have hvbal : ∀ (q : S' ⊗[R] S') (s : S) (m : M),
      v (q * ((1 : S') ⊗ₜ[R] algebraMap S S' s)) m = v q (s • m) := by
    intro q s m
    have h1 : Ideal.Quotient.mk (KaehlerDifferential.ideal R S' ^ (k + 1))
        ((1 : S') ⊗ₜ[R] algebraMap S S' s) = φ (rho R S k s) := by
      rw [rho_apply, hφmk, diagonalMap_tmul, map_one]
    rw [hvapp, hvapp, map_mul, h1, hkey]
  refine ⟨opOfJet v hvbal ∘ₗ hf.equiv.symm.toLinearMap.restrictScalars R, ?_, ?_⟩
  · exact orderLE_precomp (S := S') hf.equiv.symm.toLinearMap (orderLE_opOfJet v hvbal hvzero)
  · intro m
    have h2 : hf.equiv.symm (f m) = (1 : S') ⊗ₜ[S] m := by
      refine hf.equiv.injective ?_
      rw [LinearEquiv.apply_symm_apply, hf.equiv_tmul, one_smul]
    have h3 : u' 1 = u 1 := by rw [← map_one φ]; exact hlift 1
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [h2, opOfJet_tmul, ← Algebra.TensorProduct.one_def, hvapp, map_one, h3]

omit [IsScalarTower R S M'] in
/-- **Existence of the extension.** If `S → S'` is formally étale then every differential
operator `E : M → N` of order at most `k` relative to `R → S`, with values in an `S'`-module `N`,
extends to a differential operator `M' → N` of order at most `k` relative to `R → S'`. -/
private theorem exists_extension [Algebra.FormallyEtale S S'] {f : M →ₗ[S] M'}
    (hf : IsBaseChange S' f) (k : ℕ) {E : M →ₗ[R] N}
    (hE : E.IsDifferentialOperatorOfOrderLE S k) :
    ∃ E' : M' →ₗ[R] N, E'.IsDifferentialOperatorOfOrderLE S' k ∧ ∀ m : M, E' (f m) = E m := by
  obtain ⟨u, hu, hu1⟩ := exists_jet_of_orderLE k hE
  obtain ⟨E', hord, hcomp⟩ := exists_extension_of_jet hf k u hu
  exact ⟨E', hord, fun m => (hcomp m).trans (hu1 m)⟩

end Extension

/-- The scalar tower `R → S → X` implied by `R → S' → X` and `S → S' → X`. -/
private lemma isScalarTower_of_isScalarTower_left {R S S' X : Type*} [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    [AddCommGroup X] [Module R X] [Module S X] [Module S' X] [IsScalarTower R S' X]
    [IsScalarTower S S' X] : IsScalarTower R S X :=
  IsScalarTower.of_algebraMap_smul fun r m => by
    rw [← IsScalarTower.algebraMap_smul S' ((algebraMap R S) r) m,
      ← IsScalarTower.algebraMap_apply R S S', IsScalarTower.algebraMap_smul]

section PrincipalParts

variable {R S S' M M' P P' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
  [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
  [AddCommGroup M'] [Module R M'] [Module S M'] [Module S' M'] [IsScalarTower R S' M']
  [IsScalarTower S S' M']
  [AddCommGroup P'] [Module R P'] [Module S P'] [Module S' P'] [IsScalarTower R S' P']
  [IsScalarTower S S' P']

/-- Let `R → S → S'` be ring maps with `S → S'` formally étale (for example
étale), let `M` be an `S`-module, let `k : ℕ` and let `M'` be the base change of `M` along
`S → S'`, given by `f`. Let `(P, D)` be a module of principal parts of order `k` of `M`
relative to `R → S` and let `(P', D')` be one of `M'` relative to `R → S'`. Then an `S`-linear map
`g : P → P'` with `g ∘ D = D' ∘ f` exhibits `P'` as the base change of `P` along `S → S'`. Such a
map exists and is unique, by `existsUnique_isBaseChange_of_formallyEtale`; the complete statement
of Stacks 0H94 is `baseChange_of_formallyEtale`. -/
theorem isBaseChange_of_formallyEtale [Algebra.FormallyEtale S S'] (k : ℕ)
    {D : M →ₗ[R] P} (hD : D.IsUniversalDifferentialOperatorOfOrderLE S k)
    {D' : M' →ₗ[R] P'} (hD' : D'.IsUniversalDifferentialOperatorOfOrderLE S' k)
    (f : M →ₗ[S] M') (hf : IsBaseChange S' f) (g : P →ₗ[S] P')
    (hg : ∀ m : M, g (D m) = D' (f m)) :
    IsBaseChange S' g := by
  have : IsScalarTower R S M' := isScalarTower_of_isScalarTower_left (S' := S')
  have : IsScalarTower R S P' := isScalarTower_of_isScalarTower_left (S' := S')
  have : IsScalarTower R S (S' ⊗[S] P) := isScalarTower_of_isScalarTower_left (S' := S')
  obtain ⟨Dt, hDtord, hDt⟩ := exists_extension (N := S' ⊗[S] P) hf k
    (E := (TensorProduct.mk S S' P 1).restrictScalars R ∘ₗ D)
    (orderLE_postcomp (TensorProduct.mk S S' P 1) hD.1)
  have hDt' : ∀ m : M, Dt (f m) = (1 : S') ⊗ₜ[S] D m := hDt
  set η : (S' ⊗[S] P) →ₗ[S'] P' := g.liftBaseChange S' with hη
  have hη1 : ∀ p : P, η ((1 : S') ⊗ₜ[S] p) = g p := fun p => by
    simp [hη, LinearMap.liftBaseChange_tmul]
  obtain ⟨θ, hθ, -⟩ := existsUnique_comp_eq hD' hDtord
  have hηDt : ∀ z : M', η (Dt z) = D' z := by
    have hzero : η.restrictScalars R ∘ₗ Dt - D' = 0 := by
      refine eq_zero_of_orderLE_of_comp_eq_zero hf
        (LinearMap.isDifferentialOperatorOfOrderLE_sub (orderLE_postcomp η hDtord) hD'.1)
        fun m => ?_
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars]
      rw [hDt' m, hη1 (D m), hg m, sub_self]
    exact fun z => LinearMap.congr_fun (sub_eq_zero.mp hzero) z
  have hηθ : η ∘ₗ θ = LinearMap.id := by
    refine eq_of_comp_eq hD' fun z => ?_
    rw [LinearMap.comp_apply, hθ z, hηDt z, LinearMap.id_apply]
  have hθη : θ ∘ₗ η = LinearMap.id := by
    have hres : ((θ ∘ₗ η).restrictScalars S) ∘ₗ TensorProduct.mk S S' P 1 =
        ((LinearMap.id : (S' ⊗[S] P) →ₗ[S'] (S' ⊗[S] P)).restrictScalars S) ∘ₗ
          TensorProduct.mk S S' P 1 := by
      refine eq_of_comp_eq hD fun m => ?_
      change θ (η ((1 : S') ⊗ₜ[S] D m)) = (1 : S') ⊗ₜ[S] D m
      rw [hη1 (D m), hg m, ← hDt' m, hθ (f m)]
    exact (LinearMap.liftBaseChangeEquiv S').symm.injective
      (LinearMap.ext fun p => LinearMap.congr_fun hres p)
  exact IsBaseChange.of_equiv (LinearEquiv.ofLinearMap η θ hηθ hθη) hη1

omit [IsScalarTower R S S'] in
/-- An operator of order at most `k` relative to `R → S'` has order at most `k` relative to
`R → S`, for the `S`-module structures induced along `S → S'`. -/
private lemma orderLE_of_orderLE_algebraMap {X Y : Type*} [AddCommGroup X] [Module R X]
    [Module S X] [Module S' X] [IsScalarTower R S X] [IsScalarTower R S' X] [IsScalarTower S S' X]
    [AddCommGroup Y] [Module R Y] [Module S Y] [Module S' Y] [IsScalarTower R S Y]
    [IsScalarTower R S' Y] [IsScalarTower S S' Y] :
    ∀ {j : ℕ} {F : X →ₗ[R] Y}, F.IsDifferentialOperatorOfOrderLE S' j →
      F.IsDifferentialOperatorOfOrderLE S j := by
  intro j
  induction j with
  | zero =>
    intro F hF s x
    rw [← algebraMap_smul S' s x, hF, algebraMap_smul]
  | succ j ih =>
    intro F hF
    rw [isDifferentialOperatorOfOrderLE_succ_iff]
    intro s
    have key : commSMul F s = commSMul F (algebraMap S S' s) := by
      ext x; simp [commSMul_apply, algebraMap_smul]
    rw [key]
    exact ih (isDifferentialOperatorOfOrderLE_succ_iff.mp hF _)

/-- An operator of order at most `k` has order at most `k + n`. -/
private lemma orderLE_add_right {X Y : Type*} [AddCommGroup X] [Module R X] [Module S' X]
    [IsScalarTower R S' X] [AddCommGroup Y] [Module R Y] [Module S' Y] [IsScalarTower R S' Y]
    {k : ℕ} {F : X →ₗ[R] Y} (hF : F.IsDifferentialOperatorOfOrderLE S' k) :
    ∀ n : ℕ, F.IsDifferentialOperatorOfOrderLE S' (k + n)
  | 0 => hF
  | n + 1 => isDifferentialOperatorOfOrderLE_succ (orderLE_add_right hF n)

/-- **Existence and uniqueness of the comparison map.** In the situation of
`isBaseChange_of_formallyEtale`, there is a unique `S`-linear map `g : P → P'` with
`g ∘ D = D' ∘ f`, and it exhibits `P'` as the base change of `P` along `S → S'`. -/
theorem existsUnique_isBaseChange_of_formallyEtale [Algebra.FormallyEtale S S'] (k : ℕ)
    {D : M →ₗ[R] P} (hD : D.IsUniversalDifferentialOperatorOfOrderLE S k)
    {D' : M' →ₗ[R] P'} (hD' : D'.IsUniversalDifferentialOperatorOfOrderLE S' k)
    (f : M →ₗ[S] M') (hf : IsBaseChange S' f) :
    ∃ g : P →ₗ[S] P', (∀ m : M, g (D m) = D' (f m)) ∧ IsBaseChange S' g ∧
      ∀ g' : P →ₗ[S] P', (∀ m : M, g' (D m) = D' (f m)) → g' = g := by
  have : IsScalarTower R S M' := isScalarTower_of_isScalarTower_left (S' := S')
  have : IsScalarTower R S P' := isScalarTower_of_isScalarTower_left (S' := S')
  obtain ⟨g, hg, huniq⟩ := existsUnique_comp_eq hD (E := D' ∘ₗ f.restrictScalars R)
    (orderLE_precomp f (orderLE_of_orderLE_algebraMap hD'.1))
  exact ⟨g, hg, isBaseChange_of_formallyEtale k hD hD' f hf g hg, fun g' hg' => huniq g' hg'⟩

/-- **Unique extension of a differential operator.** Let `R → S → S'` be ring maps with
`S → S'` formally étale and let `M'` be the base change of the `S`-module `M` along `S → S'`,
given by `f`. Then every differential operator `E : M → N` of order at most `l` relative to
`R → S` has an extension `E' : M' → S' ⊗[S] N`, `E' (f m) = 1 ⊗ E m`, which is a differential
operator of order at most `l` relative to `R → S'`; and any differential operator of finite order
`M' → S' ⊗[S] N` relative to `R → S'` extending `E` equals `E'`. -/
theorem existsUnique_extension_of_formallyEtale [Algebra.FormallyEtale S S'] {N : Type*}
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {f : M →ₗ[S] M'} (hf : IsBaseChange S' f) (l : ℕ) {E : M →ₗ[R] N}
    (hE : E.IsDifferentialOperatorOfOrderLE S l) :
    ∃ E' : M' →ₗ[R] S' ⊗[S] N, E'.IsDifferentialOperatorOfOrderLE S' l ∧
      (∀ m : M, E' (f m) = (1 : S') ⊗ₜ[S] E m) ∧
      ∀ (j : ℕ) (E'' : M' →ₗ[R] S' ⊗[S] N), E''.IsDifferentialOperatorOfOrderLE S' j →
        (∀ m : M, E'' (f m) = (1 : S') ⊗ₜ[S] E m) → E'' = E' := by
  have : IsScalarTower R S M' := isScalarTower_of_isScalarTower_left (S' := S')
  have : IsScalarTower R S (S' ⊗[S] N) := isScalarTower_of_isScalarTower_left (S' := S')
  obtain ⟨E', hord, hext⟩ := exists_extension (N := S' ⊗[S] N) hf l
    (E := (TensorProduct.mk S S' N 1).restrictScalars R ∘ₗ E)
    (orderLE_postcomp (TensorProduct.mk S S' N 1) hE)
  refine ⟨E', hord, hext, fun j E'' hE'' hext'' => ?_⟩
  have hsub : (E'' - E').IsDifferentialOperatorOfOrderLE S' (j + l) :=
    isDifferentialOperatorOfOrderLE_sub (orderLE_add_right hE'' l)
      (by rw [Nat.add_comm]; exact orderLE_add_right hord j)
  have hzero : E'' - E' = 0 := eq_zero_of_orderLE_of_comp_eq_zero hf hsub fun m => by
    rw [LinearMap.sub_apply, hext'' m, hext m]
    simp
  exact sub_eq_zero.mp hzero

/-- Let `R → S → S'` be ring maps with `S → S'` formally étale (for example étale). Let `M` be an
`S`-module and `M' = S' ⊗[S] M`, given as a base change `f : M → M'`. Let `(P, D)` and `(P', D')`
be modules of principal parts of order `k` of `M` over `R → S` and of `M'` over `R → S'`. Then
`S' ⊗[S] Pᵏ_{S/R}(M) = Pᵏ_{S'/R}(M')`: the unique `S`-linear `g : P → P'` with `g ∘ D = D' ∘ f`
exhibits `P'` as the base change of `P`. Moreover, for any `S`-module `N`, every differential
operator `E : M → N` of finite order `l` has a unique extension `E' : M' → S' ⊗[S] N` to a
differential operator, which has order at most `l`. -/
@[stacks 0H94 "The identification `S' ⊗_S Pᵏ_{S/R}(M) = Pᵏ_{S'/R}(M')` is stated in Mathlib's
`IsBaseChange` form, for an arbitrary base change `f : M → M'` and arbitrary modules of principal
parts on both sides (Definition 09CL, constructed in 09CK), via the unique map compatible with the
universal differential operators. The extension is unique among differential operators of any
finite order and has the order of `E`. The source writes `M' = S' ⊗_R M`, a slip for
`S' ⊗_S M`."]
theorem baseChange_of_formallyEtale [Algebra.FormallyEtale S S'] (k : ℕ)
    {D : M →ₗ[R] P} (hD : D.IsUniversalDifferentialOperatorOfOrderLE S k)
    {D' : M' →ₗ[R] P'} (hD' : D'.IsUniversalDifferentialOperatorOfOrderLE S' k)
    (f : M →ₗ[S] M') (hf : IsBaseChange S' f) (N : Type*) [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] :
    (∃ g : P →ₗ[S] P', (∀ m : M, g (D m) = D' (f m)) ∧ IsBaseChange S' g ∧
      ∀ g' : P →ₗ[S] P', (∀ m : M, g' (D m) = D' (f m)) → g' = g) ∧
    ∀ (l : ℕ) (E : M →ₗ[R] N), E.IsDifferentialOperatorOfOrderLE S l →
      ∃ E' : M' →ₗ[R] S' ⊗[S] N, E'.IsDifferentialOperatorOfOrderLE S' l ∧
        (∀ m : M, E' (f m) = (1 : S') ⊗ₜ[S] E m) ∧
        ∀ (j : ℕ) (E'' : M' →ₗ[R] S' ⊗[S] N), E''.IsDifferentialOperatorOfOrderLE S' j →
          (∀ m : M, E'' (f m) = (1 : S') ⊗ₜ[S] E m) → E'' = E' :=
  ⟨existsUnique_isBaseChange_of_formallyEtale k hD hD' f hf,
    fun l _ hE => existsUnique_extension_of_formallyEtale hf l hE⟩

end PrincipalParts

end LinearMap.IsUniversalDifferentialOperatorOfOrderLE

end
