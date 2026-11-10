module

public import StacksFrontier.RingTheory.Descent.SquareZeroGroupoid.Comparison

/-!
# The descent datum on a square-zero invariant ideal

Let `s, t : B ⇉ C` be a groupoid of rings (see
`StacksFrontier.RingTheory.Descent.SquareZeroGroupoid.Comparison`) and `J ⊆ B` an ideal of square
zero whose two extensions to `C` agree, with the reduced groupoid effective over `A₀ → B₀`. The
ideal `J`, a `B₀`-module because `J² = 0`, carries a descent datum relative to `A₀ → B₀`, whose
coaction is restriction along `s` read through the identification `B₀ ⊗[A₀] J ≅ J C` given by
flatness of `t`; the counit axiom comes from the unit `e` and the cocycle axiom from the
composition `m`, both checked after an injective comparison of the triple overlap with
`C ⊗[B] D`.

## Main definitions

* `Module.Descent.SquareZero.coaction`: the coaction of the descent datum on `J`.
* `Module.Descent.SquareZero.datum`: the descent datum on `J`.

## Main results

* `Module.Descent.SquareZero.exists_injective_triple`: the injective comparison on the triple
  overlap.
* `Module.Descent.SquareZero.exists_sub_mem_eqLocus`: the vanishing of `H¹`, used to lift
  elements of `A₀` to the equalizer.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 051C](https://stacks.math.columbia.edu/tag/051C)
-/

@[expose] public section

open TensorProduct

universe u

namespace Module.Descent.SquareZero

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]

variable (s : B →+* C) (J : Ideal B)

/-- If `J ^ 2 = ⊥`, elements of `J` annihilate `J D`. -/
private lemma smul_extJ_eq_zero_of_mem {D : Type u} [CommRing D] [Algebra B D] (hJ : J ^ 2 = ⊥)
    {j : B} (hj : j ∈ J) (w : extJ D J) : j • w = 0 := by
  apply Subtype.ext
  rw [Submodule.coe_smul_of_tower, Submodule.coe_zero, Algebra.smul_def]
  exact mul_eq_zero_of_mem_extJ D J hJ (Ideal.mem_map_of_mem _ hj) w.2

/-! ### The triple overlap -/

section Triple

variable {A₀ : Type u} [CommRing A₀] [Algebra A₀ (B ⧸ J)] [Algebra A₀ (C ⧸ extJ C J)]
  [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)]
  {D : Type u} [CommRing D] [Algebra B D] (σ : C ≃+* D)
  (hσ : ∀ b, σ (s b) = algebraMap B D b)

variable (hJ : J ^ 2 = ⊥) (hinv : J.map s = extJ C J)
  (hcomp : ∀ a : A₀, s₀ s J hinv (algebraMap A₀ (B ⧸ J) a) =
    algebraMap (B ⧸ J) (C ⧸ extJ C J) (algebraMap A₀ (B ⧸ J) a))

omit [Algebra A₀ (B ⧸ J)] [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] in
include hσ hinv in
/-- `σ` carries the ideal `J C` onto `J D`. -/
lemma map_σ_extJ : (extJ C J).map (σ : C →+* D) = extJ D J := by
  rw [← hinv, Ideal.map_map]
  congr 1
  ext b
  exact hσ b

omit [Algebra A₀ (B ⧸ J)] [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] in
include hσ hinv in
/-- If `z ∈ J C` then `σ z ∈ J D`. -/
lemma σ_mem_extJ {z : C} (hz : z ∈ extJ C J) : σ z ∈ extJ D J := by
  rw [← map_σ_extJ s J σ hσ hinv]
  exact Ideal.mem_map_of_mem _ hz

omit [Algebra A₀ (B ⧸ J)] [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] in
include hσ hinv in
/-- If `σ z ∈ J D` then `z ∈ J C`. -/
lemma mem_extJ_of_σ_mem {z : C} (hz : σ z ∈ extJ D J) : z ∈ extJ C J := by
  rw [← map_σ_extJ s J σ hσ hinv] at hz
  obtain ⟨x, hx, hxz⟩ := (Ideal.mem_map_iff_of_surjective (σ : C →+* D) σ.surjective).mp hz
  rwa [← σ.injective hxz]

omit [Algebra A₀ (B ⧸ J)] [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] in
/-- The restriction of `σ` to an identification `J C ≅ J D`. -/
def σJ : extJ C J ≃+ extJ D J where
  toFun z := ⟨σ z, σ_mem_extJ s J σ hσ hinv z.2⟩
  invFun w := ⟨σ.symm w, mem_extJ_of_σ_mem s J σ hσ hinv (by simp)⟩
  left_inv z := by ext; simp
  right_inv w := by ext; simp
  map_add' x y := by ext; simp

omit [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)] in
include hJ in
/-- If `J ^ 2 = ⊥`, the `C`-module `C ⊗[B] J D` is annihilated by `J C`. -/
lemma isTorsionBySet_C_tensor :
    Module.IsTorsionBySet C (C ⊗[B] extJ D J) (extJ C J) := by
  intro x y
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]
  | tmul c w =>
    change ((y : C) * c) ⊗ₜ w = 0
    have key : ∀ z ∈ extJ C J, z ⊗ₜ[B] w = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, hj, rfl⟩ := hx
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
        rw [smul_extJ_eq_zero_of_mem J hJ hj, TensorProduct.tmul_zero]
      | zero => exact TensorProduct.zero_tmul _ _
      | add a b _ _ ha hb => rw [TensorProduct.add_tmul, ha, hb, add_zero]
      | smul c' a _ ha =>
        rw [smul_eq_mul, ← smul_eq_mul, ← TensorProduct.smul_tmul', ha, smul_zero]
    exact key _ (Ideal.mul_mem_right _ _ y.2)

include hσ hJ hinv hcomp in
/-- **The injective comparison on the triple overlap.** Let `P` be an `A₀`-algebra with a map
`σP : P → C₀` making `B₀ ⊗[A₀] P → C₀` bijective. There is an injective additive map
`P ⊗[A₀] J C → C ⊗[B] D` sending `y ⊗ z` to `c ⊗ σ(z)` for any lift `c ∈ C` of `σP y`. -/
lemma exists_injective_triple [Module.Flat B C] {P : Type*} [CommRing P] [Algebra A₀ P]
    (σP : P →+* C ⧸ extJ C J)
    (hP : ∀ a : A₀, σP (algebraMap A₀ P a) =
      algebraMap (B ⧸ J) (C ⧸ extJ C J) (algebraMap A₀ (B ⧸ J) a))
    (hbij : Function.Bijective (cmpP σP hP)) :
    ∃ ι : P ⊗[A₀] extJ C J →+ C ⊗[B] D, Function.Injective ι ∧
      ∀ (y : P) (z : extJ C J) (c : C), Ideal.Quotient.mk (extJ C J) c = σP y →
        ι (y ⊗ₜ z) = c ⊗ₜ σ z := by
  have hTM : Module.IsTorsionBySet B (extJ D J) J := fun w j =>
    smul_extJ_eq_zero_of_mem J hJ j.2 w
  let : Module (B ⧸ J) (extJ D J) := hTM.module
  have : IsScalarTower B (B ⧸ J) (extJ D J) := hTM.isScalarTower
  let : Module A₀ (extJ D J) := Module.compHom _ (algebraMap A₀ (B ⧸ J))
  have : IsScalarTower A₀ (B ⧸ J) (extJ D J) :=
    ⟨fun a b w => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have hTN := isTorsionBySet_C_tensor (C := C) J (D := D) hJ
  let : Module (C ⧸ extJ C J) (C ⊗[B] extJ D J) := hTN.module
  have : IsScalarTower C (C ⧸ extJ C J) (C ⊗[B] extJ D J) := hTN.isScalarTower
  let : Module (B ⧸ J) (C ⊗[B] extJ D J) :=
    Module.compHom _ (algebraMap (B ⧸ J) (C ⧸ extJ C J))
  have : IsScalarTower (B ⧸ J) (C ⧸ extJ C J) (C ⊗[B] extJ D J) :=
    ⟨fun x y z => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have hmkN : ∀ (c : C) (n : C ⊗[B] extJ D J), Ideal.Quotient.mk (extJ C J) c • n = c • n :=
    fun c n => Module.IsTorsionBySet.mk_smul hTN c n
  have : IsScalarTower B (B ⧸ J) (C ⊗[B] extJ D J) := ⟨fun b β n => by
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective β
    change (algebraMap (B ⧸ J) (C ⧸ extJ C J) (b • Ideal.Quotient.mk J b')) • n =
      b • (algebraMap (B ⧸ J) (C ⧸ extJ C J) (Ideal.Quotient.mk J b') • n)
    rw [show b • Ideal.Quotient.mk J b' = Ideal.Quotient.mk J (b * b') from rfl, t₀_mk, t₀_mk,
      hmkN, hmkN, map_mul, mul_smul, algebraMap_smul]⟩
  let : Module A₀ (C ⊗[B] extJ D J) := Module.compHom _ (algebraMap A₀ (C ⧸ extJ C J))
  have : IsScalarTower A₀ (C ⧸ extJ C J) (C ⊗[B] extJ D J) :=
    ⟨fun a y n => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : IsScalarTower A₀ (B ⧸ J) (C ⊗[B] extJ D J) := ⟨fun a β n => by
    change algebraMap (B ⧸ J) (C ⧸ extJ C J) (a • β) • n =
      algebraMap A₀ (C ⧸ extJ C J) a • algebraMap (B ⧸ J) (C ⧸ extJ C J) β • n
    rw [Algebra.smul_def, map_mul, mul_smul, ← IsScalarTower.algebraMap_apply]⟩
  let ℓ : extJ D J →ₗ[B ⧸ J] C ⊗[B] extJ D J :=
    { toFun := fun w => (1 : C) ⊗ₜ w
      map_add' := fun x y => TensorProduct.tmul_add _ _ _
      map_smul' := fun β w => by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
        rw [mk_smul_of_tower, RingHom.id_apply, mk_smul_of_tower, TensorProduct.tmul_smul] }
  let κ' := LinearMap.liftBaseChange (C ⧸ extJ C J) ℓ
  have hκ' : Function.Injective κ' := by
    refine injective_liftBaseChange_quot C J ℓ ?_
    intro x y hxy
    have hid : ∀ z : C ⊗[B] extJ D J,
        LinearMap.liftBaseChange C (ℓ.restrictScalars B) z = z := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul c w =>
        rw [LinearMap.liftBaseChange_tmul]
        change c • ((1 : C) ⊗ₜ[B] w) = c ⊗ₜ w
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add a b ha hb => rw [map_add, ha, hb]
    rwa [hid, hid] at hxy
  let : Algebra P (C ⧸ extJ C J) := σP.toAlgebra
  let ξ : P ⊗[A₀] extJ D J →ₗ[A₀] C ⊗[B] extJ D J :=
    let : Module P (C ⊗[B] extJ D J) := Module.compHom _ σP
    have : IsScalarTower A₀ P (C ⊗[B] extJ D J) := ⟨fun a b n => by
      rw [Algebra.smul_def]
      change σP (algebraMap A₀ P a * b) • n = a • (σP b • n)
      rw [map_mul, mul_smul, hP, ← IsScalarTower.algebraMap_apply, algebraMap_smul]⟩
    let ℓA : extJ D J →ₗ[A₀] C ⊗[B] extJ D J :=
      { toFun := ℓ
        map_add' := map_add ℓ
        map_smul' := fun a w => by
          rw [← algebraMap_smul (B ⧸ J) a w, ℓ.map_smul, RingHom.id_apply, algebraMap_smul] }
    (LinearMap.liftBaseChange P ℓA).restrictScalars A₀
  have hξ : Function.Injective ξ :=
    injective_pushout_comparison (cmpPEquiv J σP hP hbij)
      (fun _ _ => rfl) κ' hκ' ξ (fun b w => by
        change _ = _ • ((1 : C ⧸ extJ C J) • ℓ w)
        rw [one_smul]
        rfl)
  let incl := LinearMap.lTensor C ((extJ D J).subtype.restrictScalars B)
  have hincl : Function.Injective incl :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := C) _ Subtype.val_injective
  let σA : extJ C J ≃ₗ[A₀] extJ D J :=
    { σJ s J σ hσ hinv with
      map_smul' := fun a z => by
        obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (algebraMap A₀ (B ⧸ J) a)
        have hsub : s b - algebraMap B C b ∈ extJ C J := s_sub_t_mem s J hinv (hb ▸ hcomp a)
        have hz := mul_eq_zero_of_mem_extJ C J hJ hsub z.2
        rw [sub_mul, sub_eq_zero] at hz
        have h1 : (a • z : extJ C J) = algebraMap B C b • z := by
          rw [← algebraMap_smul (C ⧸ extJ C J) a z, IsScalarTower.algebraMap_apply A₀ (B ⧸ J),
            ← hb, t₀_mk, mk_smul_extJ, algebraMap_smul]
        have h2 : ∀ w : extJ D J, (a • w : extJ D J) = b • w := fun w => by
          change algebraMap A₀ (B ⧸ J) a • w = _
          rw [← hb, mk_smul_of_tower]
        rw [RingHom.id_apply, h1, h2]
        ext
        change σ ((algebraMap B C b • z : extJ C J) : C) = ((b • σJ s J σ hσ hinv z : extJ D J) : D)
        rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, Algebra.smul_def,
          Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply, ← hz, map_mul, hσ]
        rfl }
  refine ⟨(incl.restrictScalars ℤ).toAddMonoidHom.comp ((ξ.restrictScalars ℤ).toAddMonoidHom.comp
    ((LinearEquiv.lTensor P σA).toLinearMap.restrictScalars ℤ).toAddMonoidHom),
    ?_, ?_⟩
  · exact hincl.comp (hξ.comp (LinearEquiv.lTensor P σA).injective)
  · intro y z c hc
    have h : ξ (y ⊗ₜ σA z) = c ⊗ₜ σA z := by
      change σP y • ((1 : C) ⊗ₜ[B] σA z) = _
      rw [← hc, hmkN, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change incl (ξ (y ⊗ₜ σA z)) = _
    rw [h]
    rfl

end Triple


/-! ### The descent datum on `J` -/

section Descent

variable {A₀ : Type u} [CommRing A₀] [Algebra A₀ (B ⧸ J)] [Algebra A₀ (C ⧸ extJ C J)]
  [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)]
  (hJ : J ^ 2 = ⊥) (hinv : J.map s = extJ C J)
  (hcomp : ∀ a : A₀, s₀ s J hinv (algebraMap A₀ (B ⧸ J) a) =
    algebraMap (B ⧸ J) (C ⧸ extJ C J) (algebraMap A₀ (B ⧸ J) a))
  [Module.Flat B C] (hbij : Function.Bijective (cmp (s₀ s J hinv) A₀ hcomp))

/-- The comparison `α : B₀ ⊗[A₀] J ≅ J C`, as an equivalence. -/
noncomputable abbrev αE : (B ⧸ J) ⊗[A₀] J ≃ₗ[A₀] extJ C J :=
  LinearEquiv.ofBijective (α s J hinv hcomp)
    (α_bijective (s := s) (J := J) (hinv := hinv) (hcomp := hcomp) hbij)

/-- The coaction of the descent datum on `J`: restriction along `s`, read through `α`. -/
noncomputable def coaction : J →ₗ[B ⧸ J] (B ⧸ J) ⊗[A₀] J where
  toFun n := (αE s J hinv hcomp hbij).symm
    (sJ (s := s) (J := J) (hJ := hJ) (hinv := hinv) (hcomp := hcomp) n)
  map_add' x y := by simp
  map_smul' β n := by
    apply (αE s J hinv hcomp hbij).injective
    rw [LinearEquiv.apply_symm_apply, RingHom.id_apply]
    change _ = α s J hinv hcomp (β • (αE s J hinv hcomp hbij).symm _)
    rw [α_smul, sJ_smul]
    congr 1
    exact ((αE s J hinv hcomp hbij).apply_symm_apply _).symm

/-- `α` sends the coaction of `n` to `sJ n`. -/
lemma α_coaction (n : J) :
    α s J hinv hcomp (coaction s J hJ hinv hcomp hbij n) =
      sJ (s := s) (J := J) (hJ := hJ) (hinv := hinv) (hcomp := hcomp) n :=
  (αE s J hinv hcomp hbij).apply_symm_apply _

omit [Module.Flat B C] in
/-- The unit `e : C → B` of the groupoid restricted to `J C → J`, a retraction of `sJ`. -/
def unitRestrict (e : C →+* B) (het : ∀ b, e (algebraMap B C b) = b) : extJ C J →ₗ[A₀] J where
  toFun p := ⟨e p, by
    have h : e p ∈ (J.map (algebraMap B C)).map e := Ideal.mem_map_of_mem e p.2
    rwa [Ideal.map_map, show e.comp (algebraMap B C) = RingHom.id B from
      RingHom.ext het, Ideal.map_id] at h⟩
  map_add' x y := by ext; simp
  map_smul' a p := by
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (algebraMap A₀ (B ⧸ J) a)
    have h := smul_eq_of_lift J hb (C := C)
    rw [RingHom.id_apply, h.1]
    apply Subtype.ext
    change e ((a • p : extJ C J) : C) = b * e p
    rw [h.2 p, Submodule.coe_smul_of_tower, Algebra.smul_def, Algebra.algebraMap_self,
      RingHom.id_apply, map_mul, het]

omit [Module.Flat B C] in
/-- `unitRestrict e het p = e p` as elements of `B`. -/
@[simp]
lemma unitRestrict_apply (e : C →+* B) (het : ∀ b, e (algebraMap B C b) = b) (p : extJ C J) :
    (unitRestrict (A₀ := A₀) J e het p : B) = e p := rfl

/-- **The counit axiom.** The counit of `B₀ ⊗[A₀] J` applied to the coaction of `n` is `n`. -/
lemma counit_coaction (e : C →+* B) (hes : ∀ b, e (s b) = b)
    (het : ∀ b, e (algebraMap B C b) = b) (n : J) :
    Module.Descent.counit A₀ (B ⧸ J) J (coaction s J hJ hinv hcomp hbij n) = n := by
  refine Module.Descent.counit_coaction_of_retraction (coaction s J hJ hinv hcomp hbij)
    (α s J hinv hcomp) (sJ (s := s) (J := J) (hJ := hJ) (hinv := hinv) (hcomp := hcomp))
    (fun n => (α_coaction s J hJ hinv hcomp hbij n).symm) (unitRestrict (A₀ := A₀) J e het)
    (fun n => Subtype.ext (by simp [hes])) (fun x => ?_) n
  induction x using TensorProduct.inductionOn with
  | tmul β j =>
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
    rw [Module.Descent.counit_tmul, mk_smul_of_tower, α_tmul]
    ext
    rw [unitRestrict_apply, s₀_mk, mk_smul_extJ, Submodule.coe_smul_of_tower, tJ_apply,
      smul_eq_mul, map_mul, hes, het, Submodule.coe_smul_of_tower, smul_eq_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

variable {D : Type u} [CommRing D] [Algebra B D] (σ : C ≃+* D)
  (hσ : ∀ b, σ (s b) = algebraMap B D b)
  (m : C →+* C ⊗[B] D) (hms : ∀ b, m (s b) = s b ⊗ₜ 1)
  (hmt : ∀ b, m (algebraMap B C b) = 1 ⊗ₜ σ (algebraMap B C b))

include hσ hms hmt in
/-- **The cocycle axiom.** Applying the coaction to the second factor of the coaction of `n`
agrees with inserting `1` in the middle factor. -/
lemma coassoc (n : J) :
    TensorProduct.AlgebraTensorModule.lTensor (B ⧸ J) (B ⧸ J)
        ((coaction s J hJ hinv hcomp hbij).restrictScalars A₀)
        (coaction s J hJ hinv hcomp hbij n) =
      TensorProduct.AlgebraTensorModule.lTensor (B ⧸ J) (B ⧸ J)
        (TensorProduct.mk A₀ (B ⧸ J) J 1) (coaction s J hJ hinv hcomp hbij n) := by
  obtain ⟨ι, hι, hιf⟩ := exists_injective_triple s J σ hσ hJ hinv hcomp (s₀ s J hinv) hcomp hbij
  let L := LinearEquiv.lTensor (B ⧸ J) (αE s J hinv hcomp hbij)
  have hL : ∀ y : B ⧸ J, ∀ x : (B ⧸ J) ⊗[A₀] J,
      L (y ⊗ₜ x) = y ⊗ₜ α s J hinv hcomp x := fun _ _ => rfl
  have hF : ∀ x : (B ⧸ J) ⊗[A₀] J,
      ι (L (TensorProduct.AlgebraTensorModule.lTensor (B ⧸ J) (B ⧸ J)
        ((coaction s J hJ hinv hcomp hbij).restrictScalars A₀) x)) =
        ((α s J hinv hcomp x : extJ C J) : C) ⊗ₜ[B] (1 : D) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul y j =>
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.restrictScalars_apply, hL,
        α_coaction, hιf _ _ (s b) (s₀_mk s J hinv b).symm, α_tmul, s₀_mk, mk_smul_extJ,
        Submodule.coe_smul_of_tower, tJ_apply, sJ_apply, hσ, smul_eq_mul,
        Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy, Submodule.coe_add, TensorProduct.add_tmul]
  have hG : ∀ x : (B ⧸ J) ⊗[A₀] J,
      ι (L (TensorProduct.AlgebraTensorModule.lTensor (B ⧸ J) (B ⧸ J)
        (TensorProduct.mk A₀ (B ⧸ J) J 1) x)) = m ((α s J hinv hcomp x : extJ C J) : C) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul y j =>
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul, TensorProduct.mk_apply, hL,
        α_tmul, hιf _ _ (s b) (s₀_mk s J hinv b).symm, α_tmul, s₀_mk, mk_smul_extJ,
        Submodule.coe_smul_of_tower, tJ_apply, smul_eq_mul, map_mul, hms, hmt,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [map_one, one_smul, tJ_apply]
    | add x y hx hy => simp only [map_add, hx, hy, Submodule.coe_add]
  apply L.injective
  apply hι
  rw [hF, hG, α_coaction, sJ_apply, hms]

/-- The descent datum on `J` relative to `A₀ → B₀`. -/
noncomputable def datum (e : C →+* B) (hes : ∀ b, e (s b) = b)
    (het : ∀ b, e (algebraMap B C b) = b) : Module.Descent.Datum A₀ (B ⧸ J) J where
  coaction := coaction s J hJ hinv hcomp hbij
  counit_coaction := counit_coaction s J hJ hinv hcomp hbij e hes het
  coassoc := coassoc s J hJ hinv hcomp hbij σ hσ m hms hmt

/-- An element `n ∈ J` lies in the descended module `J₀` if and only if `s n = t n`. -/
lemma mem_descended_iff (e : C →+* B) (hes : ∀ b, e (s b) = b)
    (het : ∀ b, e (algebraMap B C b) = b) (n : J) :
    n ∈ (datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).descended ↔
      s n = algebraMap B C n := by
  rw [Module.Descent.Datum.mem_descended_iff]
  constructor
  · intro h
    have h' := congrArg (fun x => ((α s J hinv hcomp x : extJ C J) : C)) h
    change ((α s J hinv hcomp (coaction s J hJ hinv hcomp hbij n) : extJ C J) : C) = _ at h'
    rw [α_coaction, sJ_apply, α_tmul, map_one, one_smul, tJ_apply] at h'
    exact h'
  · intro h
    apply (αE s J hinv hcomp hbij).injective
    change α s J hinv hcomp (coaction s J hJ hinv hcomp hbij n) = α s J hinv hcomp (1 ⊗ₜ n)
    rw [α_coaction, α_tmul, map_one, one_smul]
    ext
    rw [sJ_apply, tJ_apply, h]

include hJ hσ hms hmt hbij in
/-- **The vanishing of `H¹`.** An element of `B` whose two images in `C` agree modulo `J C` can
be corrected by an element of `J` so that they agree. -/
lemma exists_sub_mem_eqLocus [Module.FaithfullyFlat A₀ (B ⧸ J)] (e : C →+* B)
    (hes : ∀ b, e (s b) = b) (het : ∀ b, e (algebraMap B C b) = b) {b : B}
    (hb : s b - algebraMap B C b ∈ extJ C J) :
    ∃ j ∈ J, s (b - j) = algebraMap B C (b - j) := by
  set d := datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
  set J₀ := d.descended
  have hJ₀ : ∀ i : J₀, s (i : J) = algebraMap B C (i : J) := fun i =>
    (mem_descended_iff s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i).mp i.2
  let β := (d.isBaseChange).equiv
  have hβ : ∀ (y : B ⧸ J) (i : J₀), β (y ⊗ₜ i) = y • (i : J) := fun y i => by
    rw [IsBaseChange.equiv_tmul]
    rfl
  obtain ⟨ι, hι, hιf⟩ := exists_injective_triple s J σ hσ hJ hinv hcomp (s₀ s J hinv) hcomp hbij
  set x : extJ C J := ⟨s b - algebraMap B C b, hb⟩
  let L : (B ⧸ J) ⊗[A₀] ((B ⧸ J) ⊗[A₀] J₀) ≃ₗ[A₀] extJ C J :=
    (LinearEquiv.lTensor (B ⧸ J) (β.restrictScalars A₀)).trans (αE s J hinv hcomp hbij)
  have hL : ∀ (y₁ y₂ : B) (i : J₀),
      (L (Ideal.Quotient.mk J y₁ ⊗ₜ (Ideal.Quotient.mk J y₂ ⊗ₜ i)) : C) =
        s y₁ * algebraMap B C (y₂ * (i : B)) := fun y₁ y₂ i => by
    change ((α s J hinv hcomp (Ideal.Quotient.mk J y₁ ⊗ₜ β (Ideal.Quotient.mk J y₂ ⊗ₜ i)) :
      extJ C J) : C) = _
    rw [hβ, α_tmul, s₀_mk, mk_smul_extJ, Submodule.coe_smul_of_tower, tJ_apply,
      mk_smul_of_tower, smul_eq_mul]
    rfl
  set y := L.symm x
  let Φ : (B ⧸ J) ⊗[A₀] ((B ⧸ J) ⊗[A₀] ((B ⧸ J) ⊗[A₀] J₀)) →+ C ⊗[B] D :=
    ι.comp ((LinearEquiv.lTensor (B ⧸ J) L).toLinearMap.restrictScalars ℤ).toAddMonoidHom
  have hΦ : Function.Injective Φ := hι.comp (LinearEquiv.lTensor (B ⧸ J) L).injective
  let q : C →+ C ⊗[B] D :=
    (((Algebra.TensorProduct.includeRight : D →ₐ[B] C ⊗[B] D).toRingHom.comp
      (σ : C →+* D)).toAddMonoidHom)
  let p : C →+ C ⊗[B] D :=
    ((Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] D).toRingHom).toAddMonoidHom
  have hcoc : ∀ w, Φ (Module.Descent.amitsurDiff₁ A₀ (B ⧸ J) J₀ w) =
      (q - m.toAddMonoidHom + p) ((L w : extJ C J) : C) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, hw, hw', Submodule.coe_add]
    | tmul y₁ w =>
      induction w using TensorProduct.inductionOn with
      | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw', Submodule.coe_add]
      | tmul y₂ i =>
        obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
        obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
        rw [Module.Descent.amitsurDiff₁_tmul, map_add, map_sub, hL]
        simp only [Φ, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.lTensor_tmul]
        rw [← map_one (Ideal.Quotient.mk J),
          hιf _ _ 1 (by rw [s₀_mk, map_one, map_one, map_one]), hL,
          hιf _ _ (s b₁) (s₀_mk s J hinv b₁).symm, hL, hιf _ _ (s b₁) (s₀_mk s J hinv b₁).symm,
          hL]
        have h3 : s b₁ ⊗ₜ[B] σ (s b₂ * algebraMap B C (1 * ((i : J) : B))) =
            (s b₁ * algebraMap B C (b₂ * ((i : J) : B))) ⊗ₜ[B] (1 : D) := by
          rw [one_mul, ← hJ₀ i, ← map_mul, hσ, Algebra.algebraMap_eq_smul_one,
            TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm,
            map_mul]
        have hmw : m (s b₁ * algebraMap B C (b₂ * ((i : J) : B))) =
            s b₁ ⊗ₜ[B] σ (algebraMap B C (b₂ * ((i : J) : B))) := by
          rw [map_mul, hms, hmt, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [h3, map_one, one_mul]
        simp only [q, p, AddMonoidHom.add_apply, AddMonoidHom.sub_apply,
          RingHom.toAddMonoidHom_eq_coe,
          AddMonoidHom.coe_ofClass, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.includeLeft_apply, hmw]
  have hy : Module.Descent.amitsurDiff₁ A₀ (B ⧸ J) J₀ y = 0 := by
    apply hΦ
    rw [hcoc, LinearEquiv.apply_symm_apply, map_zero]
    have hmt' : m (algebraMap B C b) = 1 ⊗ₜ[B] σ (algebraMap B C b) := hmt b
    have hpt : (algebraMap B C b) ⊗ₜ[B] (1 : D) = (1 : C) ⊗ₜ[B] σ (s b) := by
      rw [hσ]
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul b
    simp only [q, p, x, AddMonoidHom.add_apply, AddMonoidHom.sub_apply,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, RingHom.coe_comp,
      Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeft_apply,
      map_sub, hms, hmt', hpt]
    abel
  obtain ⟨z, hz⟩ := Module.Descent.exists_amitsurDiff₀_eq A₀ (B ⧸ J) J₀ hy
  have hcob : ∀ z : (B ⧸ J) ⊗[A₀] J₀,
      ((L (Module.Descent.amitsurDiff₀ A₀ (B ⧸ J) J₀ z) : extJ C J) : C) =
        s ((β z : J) : B) - algebraMap B C ((β z : J) : B) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' =>
      simp only [map_add, Submodule.coe_add, hz, hz']
      ring
    | tmul y₁ i =>
      obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
      rw [Module.Descent.amitsurDiff₀_tmul, map_sub, Submodule.coe_sub,
        ← map_one (Ideal.Quotient.mk J), hL, hL, hβ, mk_smul_of_tower, Submodule.coe_smul_of_tower,
        smul_eq_mul]
      simp only [one_mul, map_one, map_mul, hJ₀ i]
  refine ⟨((β z : J) : B), (β z).2, ?_⟩
  have h1 : L (Module.Descent.amitsurDiff₀ A₀ (B ⧸ J) J₀ z) = x := by
    rw [hz, LinearEquiv.apply_symm_apply]
  have h2 := hcob z
  rw [h1] at h2
  change s b - algebraMap B C b = _ at h2
  rw [map_sub, map_sub]
  linear_combination h2

end Descent

end Module.Descent.SquareZero

end
