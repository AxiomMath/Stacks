module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.Basic

/-!
# Flatness over `B` from flatness over `A` and flatness of the multiplication map

Let `A → B` be a map of commutative rings and let `μ : B ⊗[A] B → B` be the multiplication
map. If `B` is flat as a `(B ⊗[A] B)`-module via `μ`, then every `B`-module `N` that is flat
over `A` is flat over `B`.

For `B`-modules `N` and `P`, the module `N ⊗[A] P` is a `(B ⊗[A] B)`-module via
`(b₁ ⊗ b₂) • (n ⊗ p) = (b₁ • n) ⊗ (b₂ • p)`, and there is a natural isomorphism
`(N ⊗[A] P) ⊗[B ⊗[A] B] B ≃ N ⊗[B] P`.

The constructions used to build that isomorphism live in the `Stacks.WeaklyEtale.Flat` namespace.

## Main definitions

* `Stacks.WeaklyEtale.Flat.actAlg`: the `A`-algebra map `B ⊗[A] B → Module.End A (N ⊗[A] P)`
  given by the actions of `B` on both factors.
* `Stacks.WeaklyEtale.Flat.moduleBB`: the `(B ⊗[A] B)`-module structure on `N ⊗[A] P` induced by
  `actAlg`.
* `Stacks.WeaklyEtale.Flat.qmap`: the canonical `A`-linear map `N ⊗[A] P → N ⊗[B] P`.
* `Stacks.WeaklyEtale.Flat.phiAdd`, `Stacks.WeaklyEtale.Flat.psiAdd`: the mutually inverse
  additive maps between `(N ⊗[A] P) ⊗[B ⊗[A] B] B` and `N ⊗[B] P`.
* `Stacks.WeaklyEtale.Flat.lTensorBB`: the map `N ⊗[A] N' → N ⊗[A] N''` induced by a `B`-linear
  map `N' → N''`, as a `(B ⊗[A] B)`-linear map.

## Main results

* `Stacks.WeaklyEtale.Flat.lTensor_injective_of_injective`: under the hypotheses above,
  `N ⊗[B] -` preserves injective `B`-linear maps.
* `flat_of_flat_of_mul_flat`: If `μ` is flat and `N` is `A`-flat, then `N` is `B`-flat.

## References

* [Stacks, Tag 092C](https://stacks.math.columbia.edu/tag/092C)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace Stacks.WeaklyEtale.Flat

section Scaffold

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable (N : Type*) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable (P : Type*) [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]

/-- The action of `B` on `N ⊗[A] P` through the factor `N`, as an `A`-algebra homomorphism
`B → Module.End A (N ⊗[A] P)`. -/
noncomputable def actNAlg : B →ₐ[A] Module.End A (N ⊗[A] P) where
  toFun b := LinearMap.rTensor P (Algebra.lsmul A A N b)
  map_one' := by
    refine LinearMap.ext fun t => ?_
    simp only [map_one, Module.End.one_eq_id, LinearMap.rTensor_id, LinearMap.id_coe, id_eq]
  map_mul' x y := by
    refine LinearMap.ext fun t => ?_
    simp only [map_mul, Module.End.mul_eq_comp, LinearMap.rTensor_comp,
      LinearMap.comp_apply]
  map_zero' := by
    refine LinearMap.ext fun t => ?_
    simp only [map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply]
  map_add' x y := by
    refine LinearMap.ext fun t => ?_
    simp only [map_add, LinearMap.rTensor_add, LinearMap.add_apply]
  commutes' a := by
    refine LinearMap.ext fun t => ?_
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      Module.End.one_eq_id, LinearMap.rTensor_smul, LinearMap.rTensor_id,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq]

/-- The action of `B` on `N ⊗[A] P` through the factor `P`, as an `A`-algebra homomorphism
`B → Module.End A (N ⊗[A] P)`. -/
noncomputable def actPAlg : B →ₐ[A] Module.End A (N ⊗[A] P) where
  toFun b := LinearMap.lTensor N (Algebra.lsmul A A P b)
  map_one' := by
    refine LinearMap.ext fun t => ?_
    simp only [map_one, Module.End.one_eq_id, LinearMap.lTensor_id, LinearMap.id_coe, id_eq]
  map_mul' x y := by
    refine LinearMap.ext fun t => ?_
    simp only [map_mul, Module.End.mul_eq_comp, LinearMap.lTensor_comp,
      LinearMap.comp_apply]
  map_zero' := by
    refine LinearMap.ext fun t => ?_
    simp only [map_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]
  map_add' x y := by
    refine LinearMap.ext fun t => ?_
    simp only [map_add, LinearMap.lTensor_add, LinearMap.add_apply]
  commutes' a := by
    refine LinearMap.ext fun t => ?_
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      Module.End.one_eq_id, LinearMap.lTensor_smul, LinearMap.lTensor_id,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq]

/-- The actions `actNAlg` and `actPAlg` commute. -/
lemma actNAlg_commute_actPAlg (x y : B) :
    Commute (actNAlg A B N P x) (actPAlg A B N P y) := by
  show actNAlg A B N P x * actPAlg A B N P y = actPAlg A B N P y * actNAlg A B N P x
  refine LinearMap.ext fun t => ?_
  simp only [actNAlg, actPAlg, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Module.End.mul_apply]
  induction t with
  | tmul n p => simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, Algebra.lsmul_coe]
  | add s t hs ht => simp [hs, ht]

/-- The `A`-algebra map `B ⊗[A] B → Module.End A (N ⊗[A] P)` given by the actions of `B` on
both factors. -/
noncomputable def actAlg : (B ⊗[A] B) →ₐ[A] Module.End A (N ⊗[A] P) :=
  Algebra.TensorProduct.lift (actNAlg A B N P) (actPAlg A B N P)
    (actNAlg_commute_actPAlg A B N P)

/-- The `(B ⊗[A] B)`-module structure on `N ⊗[A] P`.

Mathlib's `TensorProduct.Algebra.module` does not apply: it needs two distinct algebras
acting on the module, whereas here both tensor factors are the same ring `B` acting on
`N ⊗[A] P` through different legs. -/
noncomputable abbrev moduleBB : Module (B ⊗[A] B) (N ⊗[A] P) :=
  Module.compHom (N ⊗[A] P) (actAlg A B N P).toRingHom

/-- The canonical `A`-linear quotient map `N ⊗[A] P → N ⊗[B] P`. -/
noncomputable def qmap : N ⊗[A] P →ₗ[A] N ⊗[B] P :=
  TensorProduct.lift
    { toFun := fun n =>
        { toFun := fun p => n ⊗ₜ[B] p
          map_add' := fun x y => by simp [TensorProduct.tmul_add]
          map_smul' := by
            intro a x
            simp only [RingHom.id_apply]
            rw [← IsScalarTower.algebraMap_smul B a x,
              ← IsScalarTower.algebraMap_smul B a (n ⊗ₜ[B] x),
              ← TensorProduct.smul_tmul, TensorProduct.smul_tmul'] }
      map_add' := fun x y => by
        ext p
        simp [TensorProduct.add_tmul]
      map_smul' := by
        intro a x
        ext p
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
          LinearMap.smul_apply]
        rw [← IsScalarTower.algebraMap_smul B a (x ⊗ₜ[B] p),
          ← IsScalarTower.algebraMap_smul B a x, TensorProduct.smul_tmul'] }

/-- The quotient map `qmap` sends `n ⊗ₜ[A] p` to `n ⊗ₜ[B] p`. -/
@[simp] lemma qmap_tmul (n : N) (p : P) : qmap A B N P (n ⊗ₜ[A] p) = n ⊗ₜ[B] p := rfl

/-- The endomorphism `actAlg (b₁ ⊗ₜ b₂)` sends `n ⊗ₜ p` to `(b₁ • n) ⊗ₜ (b₂ • p)`. -/
@[simp] lemma actAlg_tmul (b₁ b₂ : B) (n : N) (p : P) :
    actAlg A B N P (b₁ ⊗ₜ[A] b₂) (n ⊗ₜ[A] p) = (b₁ • n) ⊗ₜ[A] (b₂ • p) := by
  unfold actAlg
  rw [Algebra.TensorProduct.lift_tmul]
  simp only [Module.End.mul_apply, actNAlg, actPAlg, AlgHom.coe_mk, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
  simp [Algebra.lsmul_coe]

/-- Scalar multiplication for `moduleBB` is the action of `actAlg`. -/
lemma moduleBB_smul (r : B ⊗[A] B) (x : N ⊗[A] P) :
    (letI := moduleBB A B N P; r • x) = actAlg A B N P r x := rfl

/-- For `moduleBB`, the element `b₁ ⊗ₜ b₂` acts on `N ⊗[A] P` factorwise. -/
lemma moduleBB_smul_tmul (b₁ b₂ : B) (n : N) (p : P) :
    (letI := moduleBB A B N P; (b₁ ⊗ₜ[A] b₂) • (n ⊗ₜ[A] p)) = (b₁ • n) ⊗ₜ[A] (b₂ • p) := by
  rw [moduleBB_smul, actAlg_tmul]

/-- For `moduleBB`, `n ⊗ₜ (b • p)` is the action of `1 ⊗ₜ b` on `n ⊗ₜ p`. -/
private lemma tmul_smul_eq_one_tmul_smul (b : B) (n : N) (p : P) :
    letI := moduleBB A B N P; n ⊗ₜ[A] (b • p) = ((1 : B) ⊗ₜ[A] b) • (n ⊗ₜ[A] p) := by
  simpa using (moduleBB_smul_tmul A B N P 1 b n p).symm

end Scaffold

section Maps
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable (alg : Algebra (B ⊗[A] B) B)
variable (hμ : (algebraMap (B ⊗[A] B) B) = (Algebra.TensorProduct.lmul' A).toRingHom)
variable (N : Type*) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable (P : Type*) [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]

/-- The action of `b₁ ⊗ₜ b₂` on `1 : B` through `μ` is `b₁ * b₂`. -/
private lemma tmul_smul_one_eq_mul
    (h : (algebraMap (B ⊗[A] B) B) = (Algebra.TensorProduct.lmul' A).toRingHom) (b₁ b₂ : B) :
    letI := alg; (b₁ ⊗ₜ[A] b₂) • (1 : B) = b₁ * b₂ := by
  rw [Algebra.smul_def, h]
  simp [Algebra.TensorProduct.lmul'_apply_tmul]

include hμ in
/-- The map `qmap` intertwines the action of `r : B ⊗[A] B` on `N ⊗[A] P` with scalar
multiplication by `μ r` on `N ⊗[B] P`. -/
lemma qmap_actAlg (r : B ⊗[A] B) (x : N ⊗[A] P) :
    qmap A B N P (actAlg A B N P r x)
      = (letI := alg; (algebraMap (B ⊗[A] B) B r) • qmap A B N P x) := by
  let := alg
  induction r with
  | add r₁ r₂ h₁ h₂ => simp [map_add, h₁, h₂, add_smul]
  | tmul b₁ b₂ =>
    induction x with
    | add x₁ x₂ hx₁ hx₂ => simp [map_add, hx₁, hx₂, smul_add]
    | tmul n p =>
      rw [actAlg_tmul, qmap_tmul, qmap_tmul, hμ]
      show (b₁ • n) ⊗ₜ[B] (b₂ • p) = (b₁ * b₂) • (n ⊗ₜ[B] p)
      rw [← TensorProduct.smul_tmul' b₁ n (b₂ • p), TensorProduct.tmul_smul b₂ n p,
        smul_smul]

/-- The inner additive map `b ↦ b • qmap x` used to build `phiAdd`, for fixed
`x : N ⊗[A] P`. -/
noncomputable def phiInner (x : N ⊗[A] P) : B →+ (N ⊗[B] P) :=
  AddMonoidHom.mk' (fun b => b • qmap A B N P x) (fun b₁ b₂ => add_smul b₁ b₂ _)

/-- The outer additive map `x ↦ phiInner x` used to build `phiAdd`. -/
noncomputable def phiOuter : (N ⊗[A] P) →+ (B →+ (N ⊗[B] P)) :=
  AddMonoidHom.mk' (fun x => phiInner A B N P x) (by
    intro x y
    ext b
    simp only [phiInner, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, smul_add])

include hμ in
/-- The additive map `phiAdd : (N ⊗[A] P) ⊗[B ⊗[A] B] B → N ⊗[B] P` given by
`(n ⊗ₜ p) ⊗ₜ b ↦ b • (n ⊗ₜ[B] p)`. -/
noncomputable def phiAdd :
    letI := alg; letI := moduleBB A B N P;
    ((N ⊗[A] P) ⊗[B ⊗[A] B] B) →+ (N ⊗[B] P) :=
  letI := alg; letI := moduleBB A B N P;
  TensorProduct.liftAddHom (phiOuter A B N P) (by
    intro r x b
    let := alg
    simp only [phiOuter, phiInner, AddMonoidHom.mk'_apply]
    change b • qmap A B N P (r • x) = (r • b) • qmap A B N P x
    rw [show (r • x) = actAlg A B N P r x from rfl, qmap_actAlg A B alg hμ N P r x]
    rw [Algebra.smul_def, smul_smul, mul_comm b ((algebraMap (B ⊗[A] B) B) r)])

include hμ in
/-- In `(N ⊗[A] P) ⊗[B ⊗[A] B] B`, one has `((b • n) ⊗ p) ⊗ 1 = (n ⊗ (b • p)) ⊗ 1`. -/
lemma smul_tmul_tmul_one (b : B) (n : N) (p : P) :
    letI := alg; letI := moduleBB A B N P;
    (((b • n) ⊗ₜ[A] p) ⊗ₜ[B ⊗[A] B] (1:B))
      = ((n ⊗ₜ[A] (b • p)) ⊗ₜ[B ⊗[A] B] (1:B)) := by
  let := alg; let := moduleBB A B N P
  have h1 : ((b • n) ⊗ₜ[A] p) = (b ⊗ₜ[A] (1:B)) • (n ⊗ₜ[A] p) := by
    simpa using (moduleBB_smul_tmul A B N P b 1 n p).symm
  rw [h1, tmul_smul_eq_one_tmul_smul A B N P, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
    tmul_smul_one_eq_mul A B alg hμ, tmul_smul_one_eq_mul A B alg hμ, mul_one, one_mul]

/-- The inner additive map `p ↦ (n ⊗ₜ p) ⊗ₜ 1` used to build `psiAdd`, for fixed `n : N`. -/
noncomputable def psiInner (n : N) :
    letI := alg; letI := moduleBB A B N P;
    P →+ ((N ⊗[A] P) ⊗[B ⊗[A] B] B) :=
  letI := alg; letI := moduleBB A B N P
  AddMonoidHom.mk' (fun p => (n ⊗ₜ[A] p) ⊗ₜ[B ⊗[A] B] (1:B))
    (fun p₁ p₂ => by
      change (n ⊗ₜ[A] (p₁ + p₂)) ⊗ₜ[B ⊗[A] B] (1:B)
        = (n ⊗ₜ[A] p₁) ⊗ₜ[B ⊗[A] B] (1:B) + (n ⊗ₜ[A] p₂) ⊗ₜ[B ⊗[A] B] (1:B)
      rw [TensorProduct.tmul_add, TensorProduct.add_tmul])

/-- The outer additive map `n ↦ psiInner n` used to build `psiAdd`. -/
noncomputable def psiOuter :
    letI := alg; letI := moduleBB A B N P;
    N →+ (P →+ ((N ⊗[A] P) ⊗[B ⊗[A] B] B)) :=
  letI := alg; letI := moduleBB A B N P
  AddMonoidHom.mk' (fun n => psiInner A B alg N P n)
    (fun n₁ n₂ => by
      ext p
      change (psiInner A B alg N P (n₁ + n₂)) p
        = (psiInner A B alg N P n₁) p + (psiInner A B alg N P n₂) p
      simp only [psiInner, AddMonoidHom.mk'_apply]
      rw [TensorProduct.add_tmul, TensorProduct.add_tmul])

include hμ in
/-- The additive map `psiAdd : N ⊗[B] P → (N ⊗[A] P) ⊗[B ⊗[A] B] B` given by
`n ⊗ₜ[B] p ↦ (n ⊗ₜ p) ⊗ₜ 1`. -/
noncomputable def psiAdd :
    letI := alg; letI := moduleBB A B N P;
    (N ⊗[B] P) →+ ((N ⊗[A] P) ⊗[B ⊗[A] B] B) :=
  letI := alg; letI := moduleBB A B N P
  TensorProduct.liftAddHom (psiOuter A B alg N P) (by
    intro b n p
    change (psiInner A B alg N P (b • n)) p = (psiInner A B alg N P n) (b • p)
    simp only [psiInner, AddMonoidHom.mk'_apply]
    exact smul_tmul_tmul_one A B alg hμ N P b n p)

include hμ in
/-- `phiAdd` sends `x ⊗ b` to `b • qmap x`. -/
lemma phiAdd_tmul (x : N ⊗[A] P) (b : B) :
    (letI := alg; letI := moduleBB A B N P;
      phiAdd A B alg hμ N P (x ⊗ₜ[B ⊗[A] B] b)) = b • qmap A B N P x := by
  let := alg; let := moduleBB A B N P
  rw [phiAdd, TensorProduct.liftAddHom_tmul]
  rfl

include hμ in
/-- `psiAdd` sends `n ⊗ₜ[B] p` to `(n ⊗ₜ[A] p) ⊗ₜ 1`. -/
lemma psiAdd_tmul (n : N) (p : P) :
    (letI := alg; letI := moduleBB A B N P;
      psiAdd A B alg hμ N P (n ⊗ₜ[B] p) = (n ⊗ₜ[A] p) ⊗ₜ[B ⊗[A] B] (1:B)) := by
  let := alg; let := moduleBB A B N P
  rfl

include hμ in
/-- `phiAdd` is a left inverse of `psiAdd`. -/
lemma phiAdd_psiAdd (y : N ⊗[B] P) :
    (letI := alg; letI := moduleBB A B N P;
      phiAdd A B alg hμ N P (psiAdd A B alg hμ N P y)) = y := by
  let := alg; let := moduleBB A B N P
  induction y with
  | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | tmul n p =>
    rw [psiAdd_tmul A B alg hμ N P n p, phiAdd_tmul A B alg hμ N P (n ⊗ₜ[A] p) 1,
      qmap_tmul, one_smul]

include hμ in
/-- `psiAdd` is a left inverse of `phiAdd`. -/
lemma psiAdd_phiAdd (z : (letI := alg; letI := moduleBB A B N P; (N ⊗[A] P) ⊗[B ⊗[A] B] B)) :
    (letI := alg; letI := moduleBB A B N P;
      psiAdd A B alg hμ N P (phiAdd A B alg hμ N P z)) = z := by
  let := alg; let := moduleBB A B N P
  induction z with
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | tmul x b =>
    rw [phiAdd_tmul A B alg hμ N P x b]
    induction x with
    | add x₁ x₂ hx₁ hx₂ =>
      rw [map_add, smul_add, map_add, hx₁, hx₂, ← TensorProduct.add_tmul]
    | tmul n p =>
      rw [qmap_tmul, ← TensorProduct.tmul_smul, psiAdd_tmul A B alg hμ N P n (b • p)]
      rw [tmul_smul_eq_one_tmul_smul A B N P, TensorProduct.smul_tmul]
      show (n ⊗ₜ[A] p) ⊗ₜ[B ⊗[A] B] (((1:B) ⊗ₜ[A] b) • (1:B)) = (n ⊗ₜ[A] p) ⊗ₜ[B ⊗[A] B] b
      rw [tmul_smul_one_eq_mul A B alg hμ, one_mul]

end Maps

section Assembly
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable (N : Type*) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable (N' N'' : Type*) [AddCommGroup N'] [Module B N'] [Module A N'] [IsScalarTower A B N']
  [AddCommGroup N''] [Module B N''] [Module A N''] [IsScalarTower A B N'']
variable (f : N' →ₗ[B] N'')

/-- For a `B`-linear map `f : N' → N''`, the map `N ⊗[A] N' → N ⊗[A] N''` induced by `f`, as a
`(B ⊗[A] B)`-linear map for the `moduleBB` structures. -/
noncomputable def lTensorBB :
    letI := moduleBB A B N N'; letI := moduleBB A B N N'';
    (N ⊗[A] N') →ₗ[B ⊗[A] B] (N ⊗[A] N'') :=
  letI := moduleBB A B N N'; letI := moduleBB A B N N''
  { toFun := LinearMap.lTensor N (f.restrictScalars A)
    map_add' := by intro x y; rw [map_add]
    map_smul' := by
      intro r x
      simp only [RingHom.id_apply]
      change LinearMap.lTensor N (f.restrictScalars A) (actAlg A B N N' r x)
        = actAlg A B N N'' r (LinearMap.lTensor N (f.restrictScalars A) x)
      induction r with
      | add r₁ r₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
      | tmul b₁ b₂ =>
        induction x with
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
        | tmul n n' =>
          rw [actAlg_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
            actAlg_tmul]
          simp only [LinearMap.restrictScalars_apply, map_smul] }

/-- `lTensorBB f` sends `n ⊗ₜ n'` to `n ⊗ₜ f n'`. -/
lemma lTensorBB_tmul (n : N) (n' : N') :
    (letI := moduleBB A B N N'; letI := moduleBB A B N N'';
      lTensorBB A B N N' N'' f (n ⊗ₜ[A] n')) = n ⊗ₜ[A] (f n') := by
  let := moduleBB A B N N'; let := moduleBB A B N N''
  show LinearMap.lTensor N (f.restrictScalars A) (n ⊗ₜ[A] n') = _
  rw [LinearMap.lTensor_tmul]
  rfl

end Assembly

section Final
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable (alg : Algebra (B ⊗[A] B) B)
variable (hμ : (algebraMap (B ⊗[A] B) B) = (Algebra.TensorProduct.lmul' A).toRingHom)
variable (hflat : Module.Flat (B ⊗[A] B) B)
variable (N : Type*) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable (hN : Module.Flat A N)
variable (N' N'' : Type*) [AddCommGroup N'] [Module B N'] [Module A N'] [IsScalarTower A B N']
  [AddCommGroup N''] [Module B N''] [Module A N''] [IsScalarTower A B N'']
variable (f : N' →ₗ[B] N'')

include hμ hflat hN in
/-- If `B` is flat over `B ⊗[A] B` via `μ` and `N` is flat over `A`, then `N ⊗[B] -`
sends an injective `B`-linear map `f : N' → N''` to an injective map. -/
theorem lTensor_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (LinearMap.lTensor N f) := by
  let := alg
  let := moduleBB A B N N'
  let := moduleBB A B N N''
  have hsquare : ∀ y : N ⊗[B] N',
      LinearMap.lTensor N f y
        = phiAdd A B alg hμ N N''
            ((LinearMap.rTensor B (lTensorBB A B N N' N'' f)) (psiAdd A B alg hμ N N' y)) := by
    intro y
    induction y with
    | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
    | tmul n n' =>
      rw [LinearMap.lTensor_tmul, psiAdd_tmul A B alg hμ N N' n n',
        LinearMap.rTensor_tmul, lTensorBB_tmul A B N N' N'' f n n',
        phiAdd_tmul A B alg hμ N N'' (n ⊗ₜ[A] f n') 1, qmap_tmul, one_smul]
  have hpsi : Function.Injective (psiAdd A B alg hμ N N') :=
    Function.LeftInverse.injective (phiAdd_psiAdd A B alg hμ N N')
  have hgInj : Function.Injective (lTensorBB A B N N' N'' f) :=
    Module.Flat.lTensor_preserves_injective_linearMap (f.restrictScalars A) hf
  have hrT : Function.Injective (LinearMap.rTensor B (lTensorBB A B N N' N'' f)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (lTensorBB A B N N' N'' f) hgInj
  have hphi : Function.Injective (phiAdd A B alg hμ N N'') :=
    Function.LeftInverse.injective (psiAdd_phiAdd A B alg hμ N N'')
  intro a b hab
  exact hpsi (hrT (hphi (by rwa [← hsquare a, ← hsquare b])))

end Final

end Stacks.WeaklyEtale.Flat

open TensorProduct in
/-- **Stacks Tag 092C.** Let `A → B` be a ring map such that the multiplication
map `μ : B ⊗_A B → B` makes `B` a flat `(B ⊗_A B)`-module. Let `N` be a
`B`-module. If `N` is flat as an `A`-module, then `N` is flat as a
`B`-module. -/
@[stacks 092C]
theorem flat_of_flat_of_mul_flat
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (hB : Algebra.MulFlat A B)
    (N : Type*) [AddCommGroup N] [Module B N]
    [Module A N] [IsScalarTower A B N]
    (hN : Module.Flat A N) :
    Module.Flat B N := by
  let alg : Algebra (B ⊗[A] B) B :=
    (Algebra.TensorProduct.lmul' A (S := B)).toRingHom.toAlgebra
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N' N'' _ _ _ _ f hf
  let : Module A N' := Module.compHom N' (algebraMap A B)
  let : Module A N'' := Module.compHom N'' (algebraMap A B)
  let : IsScalarTower A B N' := IsScalarTower.of_algebraMap_smul (fun a x => rfl)
  let : IsScalarTower A B N'' := IsScalarTower.of_algebraMap_smul (fun a x => rfl)
  exact Stacks.WeaklyEtale.Flat.lTensor_injective_of_injective A B alg (RingHom.algebraMap_toAlgebra
    _) hB N
    hN N' N'' f hf
