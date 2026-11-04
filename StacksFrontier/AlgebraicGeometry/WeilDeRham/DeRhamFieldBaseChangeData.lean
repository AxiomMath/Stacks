module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamBaseChangeBijective
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeData
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilPullbackAxiom

/-!
# The comparison data of Lemma 0FVT for de Rham cohomology

Section 0FWC of the Stacks project reduces the axioms for de Rham cohomology over a field `k` to an
extension `K` of `k` through Lemma 0FVT, whose hypothesis (3)
(`Stacks.WeilDeRham.FieldBaseChangeData`) asks for an isomorphism `F(1) ⊗_F F' ≅ F'(1)` and
functorial isomorphisms of graded algebras `H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})` compatible with the
first Chern classes. For de Rham cohomology, `F = k`, `F' = K`, `F(1) = k`, `F'(1) = K`, and the
isomorphism is the `K`-linear extension of the base change map
`pr^* : H^*_{dR}(X/k) ⟶ H^*_{dR}(X_K/K)` of `Stacks.DeRhamWeil.baseChangeRingHom`
(Lemma 0FM0 over a field: `Stacks.WeilDeRham.bijective_deRhamBaseChangeLinear`), which is a map
of graded rings, natural in `X` (`Stacks.DeRhamWeil.baseChangeRingHom_pullback`) and compatible
with `c₁^{dR}` (Lemma 0FMD, `Stacks.DeRhamWeil.baseChangePiece_firstChernClassPiece`).

## Main definitions

* `Stacks.WeilDeRham.deRhamCohBaseChangeLinear`: `K ⊗_k H^*_{dR}(X/k) ⟶ H^*_{dR}(X_K/K)`.
* `Stacks.WeilDeRham.deRhamCohBaseChangeAlgEquiv`: the same map, an isomorphism of
  `K`-algebras.
* `Stacks.WeilDeRham.deRhamFieldBaseChangeData`: **the comparison data of Lemma 0FVT for de Rham
  cohomology along `k ⟶ K`.**

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open scoped TensorProduct DirectSum

universe u

namespace Stacks.WeilDeRham

attribute [local instance] RestrictScalars.moduleOrig

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]

section Comparison

variable (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- The base change ring map `H^*_{dR}(X/k) ⟶ H^*_{dR}(X_K/K)`. -/
abbrev deRhamCohBaseChange :
    DeRhamWeil.cohomology X →+* DeRhamWeil.cohomology ((fieldBaseChange k K).obj X) :=
  DeRhamWeil.baseChangeRingHom (fieldBaseChangeProj X) (fieldBaseChangeProj_comp_hom X)

/-- **The base change map `H^*_{dR}(X/k) ⟶ H^*_{dR}(X_K/K)` as a `k`-linear map**, into
`H^*_{dR}(X_K/K)` with scalars restricted to `k`. -/
def deRhamCohBaseChangeRestrict :
    DeRhamWeil.cohomology X →ₗ[k]
      RestrictScalars k K (DeRhamWeil.cohomology ((fieldBaseChange k K).obj X)) where
  toFun a := (RestrictScalars.addEquiv k K _).symm (deRhamCohBaseChange K X a)
  map_add' a b := by rw [map_add, map_add]
  map_smul' c a := by
    rw [Algebra.smul_def, map_mul, DeRhamWeil.baseChangeRingHom_algebraMap, RingHom.id_apply,
      RestrictScalars.smul_def, ← Algebra.smul_def]
    rfl

/-- **The comparison map `K ⊗_k H^*_{dR}(X/k) ⟶ H^*_{dR}(X_K/K)`**, `c ⊗ a ↦ c · pr^* a`. -/
def deRhamCohBaseChangeLinear :
    K ⊗[k] DeRhamWeil.cohomology X →ₗ[K] DeRhamWeil.cohomology ((fieldBaseChange k K).obj X) where
  toFun t := RestrictScalars.addEquiv k K _ ((deRhamCohBaseChangeRestrict K X).liftBaseChange K t)
  map_add' s t := by rw [map_add, map_add]
  map_smul' c t := by
    rw [map_smul]
    rfl

/-- The comparison map sends `c ⊗ a` to `c · pr^* a`. -/
theorem deRhamCohBaseChangeLinear_tmul (c : K) (a : DeRhamWeil.cohomology X) :
    deRhamCohBaseChangeLinear K X (c ⊗ₜ a) = c • deRhamCohBaseChange K X a :=
  rfl

/-- **The comparison map is bijective**: on `K ⊗_k H^n_{dR}(X/k)` it is the degree-`n`
comparison map `Stacks.WeilDeRham.deRhamBaseChangeLinear`, bijective by Lemma 0FM0 over a
field. -/
theorem bijective_deRhamCohBaseChangeLinear :
    Function.Bijective (deRhamCohBaseChangeLinear K X) := by
  let e₁ := (TensorProduct.directSumRight k k K (DeRhamWeil.piece X)).toAddEquiv
  let e₂ : (⨁ n : ℤ, K ⊗[k] DeRhamWeil.piece X n) ≃+
      DeRhamWeil.cohomology ((fieldBaseChange k K).obj X) :=
    DFinsupp.mapRange.addEquiv fun n =>
      (LinearEquiv.ofBijective (deRhamBaseChangeLinear K X n)
        (bijective_deRhamBaseChangeLinear K X n)).toAddEquiv
  have h : ⇑(deRhamCohBaseChangeLinear K X) = ⇑(e₁.trans e₂) := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
    | tmul c a =>
      induction a using DirectSum.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add a b ha hb => rw [TensorProduct.tmul_add, map_add, map_add, ha, hb]
      | of n x =>
        rw [deRhamCohBaseChangeLinear_tmul, DeRhamWeil.baseChangeRingHom_of, AddEquiv.trans_apply]
        change _ = e₂ ((TensorProduct.directSumRight k k K (DeRhamWeil.piece X))
          (c ⊗ₜ DirectSum.lof k ℤ (DeRhamWeil.piece X) n x))
        rw [TensorProduct.directSumRight_tmul_lof, DirectSum.lof_eq_of]
        have he : e₂ (DirectSum.of _ n (c ⊗ₜ x)) =
            DirectSum.of _ n (deRhamBaseChangeLinear K X n (c ⊗ₜ x)) :=
          DFinsupp.mapRange_single (hf := fun n => map_zero _)
        rw [he, deRhamBaseChangeLinear_tmul]
        exact ((DirectSum.lof K ℤ (DeRhamWeil.piece ((fieldBaseChange k K).obj X)) n).map_smul c
          _).symm
  rw [h]
  exact (e₁.trans e₂).bijective

/-- **The comparison map, an isomorphism of `K`-algebras** `K ⊗_k H^*_{dR}(X/k) ≅ H^*_{dR}(X_K/K)`:
the base change map is a ring map, so its `K`-linear extension is a map of `K`-algebras. -/
def deRhamCohBaseChangeAlgEquiv :
    K ⊗[k] DeRhamWeil.cohomology X ≃ₐ[K] DeRhamWeil.cohomology ((fieldBaseChange k K).obj X) :=
  AlgEquiv.ofBijective
    (Algebra.TensorProduct.algHomOfLinearMapTensorProduct (deRhamCohBaseChangeLinear K X)
      (fun c₁ c₂ a₁ a₂ => by
        rw [deRhamCohBaseChangeLinear_tmul, deRhamCohBaseChangeLinear_tmul,
          deRhamCohBaseChangeLinear_tmul, map_mul, smul_mul_smul_comm])
      (by rw [deRhamCohBaseChangeLinear_tmul, map_one, one_smul]))
    (bijective_deRhamCohBaseChangeLinear K X)

/-- The comparison isomorphism sends `1 ⊗ a` to the base change `pr^* a`. -/
theorem deRhamCohBaseChangeAlgEquiv_one_tmul (a : DeRhamWeil.cohomology X) :
    deRhamCohBaseChangeAlgEquiv K X (1 ⊗ₜ a) = deRhamCohBaseChange K X a :=
  one_smul K _

/-- The coordinate `H(1) = H ⊗ k ≅ H` of the de Rham data is `v ↦ v ⊗ 1`. -/
theorem untwist_symm_apply {F : Type u} [Field F] (V : Type u) [AddCommGroup V] [Module F V]
    (v : V) :
    (DeRhamWeil.untwist V 1).symm v =
      (v ⊗ₜ PiTensorProduct.tprod F (fun _ : Fin 1 => (1 : F)) : tateTwist F F V 1) := by
  apply (DeRhamWeil.untwist V 1).injective
  rw [LinearEquiv.apply_symm_apply, DeRhamWeil.untwist, tateTwistCoordinates_tmul]
  change v = tensorPowerCoordinates _ 1 _ • v
  simp [tensorPowerCoordinates]

/-- The comparison isomorphisms are natural: they intertwine `f^*` and `(f_K)^*`. -/
theorem deRhamCohBaseChangeAlgEquiv_pull {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (a : DeRhamWeil.cohomology Y) :
    deRhamCohBaseChangeAlgEquiv K X (1 ⊗ₜ DeRhamWeil.pullback f a) =
      DeRhamWeil.pullback ((fieldBaseChange k K).map f)
        (deRhamCohBaseChangeAlgEquiv K Y (1 ⊗ₜ a)) := by
  rw [deRhamCohBaseChangeAlgEquiv_one_tmul, deRhamCohBaseChangeAlgEquiv_one_tmul]
  exact DeRhamWeil.baseChangeRingHom_pullback _ _ f _ _ _ (fieldBaseChange_map_comp_proj f) a

/-- The comparison isomorphisms are graded. -/
theorem deRhamCohBaseChangeAlgEquiv_mem_grade (n : ℤ) (a : DeRhamWeil.cohomology X)
    (ha : a ∈ DeRhamWeil.grade X n) :
    deRhamCohBaseChangeAlgEquiv K X (1 ⊗ₜ a) ∈
      DeRhamWeil.grade ((fieldBaseChange k K).obj X) n := by
  rw [deRhamCohBaseChangeAlgEquiv_one_tmul]
  exact DeRhamWeil.baseChangeRingHom_mem_grade _ _ n a ha

/-- **The comparison isomorphisms carry `c₁^{dR}(ℒ)` to `c₁^{dR}(ℒ_K)`** (Lemma 0FMD), read in
`H^2(1)` through the comparison of the Tate lines `k ⊗_k K = K`. -/
theorem twistEquiv_deRhamCohBaseChangeAlgEquiv_firstChernClass
    (L : ((toScheme k).obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
      ((toScheme k).obj X).ringCatSheaf.2 L) :
    twistEquiv (DeRhamWeil.deRhamFirstChernClassData k) (DeRhamWeil.deRhamFirstChernClassData K)
        (TensorProduct.AlgebraTensorModule.rid k K K) (fun X => deRhamCohBaseChangeAlgEquiv K X)
        X 1 (1 ⊗ₜ DeRhamWeil.firstChernClass X (picardClassOf _ L hL)) =
      DeRhamWeil.firstChernClass ((fieldBaseChange k K).obj X)
        (picardClassOf _ ((Scheme.Modules.pullback (fieldBaseChangeProj (k' := K) X)).obj L)
          (isInvertible_pullback_obj _ L hL)) := by
  set p := DeRhamWeil.firstChernClassPiece X (picardClassOf _ L hL)
  set p' := DeRhamWeil.firstChernClassPiece ((fieldBaseChange k K).obj X)
    (picardClassOf _ ((Scheme.Modules.pullback (fieldBaseChangeProj (k' := K) X)).obj L)
      (isInvertible_pullback_obj _ L hL))
  have hA : deRhamCohBaseChangeAlgEquiv K X (1 ⊗ₜ DirectSum.of (DeRhamWeil.piece X) 2 p) =
      DirectSum.of (DeRhamWeil.piece ((fieldBaseChange k K).obj X)) 2 p' :=
    (deRhamCohBaseChangeAlgEquiv_one_tmul K X _).trans
      ((DeRhamWeil.baseChangeRingHom_of _ _ 2 _).trans (congrArg _
        ((DeRhamWeil.baseChangePiece_firstChernClassPiece _ _ _).trans (congrArg _
          (Stacks.Picard.pullbackClass_classOf _ L _)))))
  have hB : TensorProduct.AlgebraTensorModule.rid k K K ((1 : K) ⊗ₜ (1 : k)) = 1 := by
    simp
  have hT := twistEquiv_one_tmul (𝔇 := DeRhamWeil.deRhamFirstChernClassData k)
    (𝔇' := DeRhamWeil.deRhamFirstChernClassData K) (TensorProduct.AlgebraTensorModule.rid k K K)
    (fun X => deRhamCohBaseChangeAlgEquiv K X) X (DirectSum.of (DeRhamWeil.piece X) 2 p) (1 : k)
  simp only [DeRhamWeil.firstChernClass, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe]
  rw [untwist_symm_apply, untwist_symm_apply]
  refine hT.trans ?_
  congr 1
  all_goals first
    | exact hA
    | (congr 1; funext; exact hB)

end Comparison

variable (k) in
/-- **The comparison data of Lemma 0FVT for de Rham cohomology** along an extension `K` of `k`
(Section 0FWC): `k ⊗_k K = K` on the Tate lines, and on cohomology the `K`-linear extension
`K ⊗_k H^*_{dR}(X/k) ≅ H^*_{dR}(X_K/K)` of the base change map, which is natural, graded and
compatible with `c₁^{dR}`. -/
def deRhamFieldBaseChangeData :
    FieldBaseChangeData (DeRhamWeil.deRhamFirstChernClassData k)
      (DeRhamWeil.deRhamFirstChernClassData K) where
  tateEquiv := TensorProduct.AlgebraTensorModule.rid k K K
  cohEquiv X := deRhamCohBaseChangeAlgEquiv K X
  cohEquiv_pull f a := deRhamCohBaseChangeAlgEquiv_pull K f a
  cohEquiv_grade X n a ha := deRhamCohBaseChangeAlgEquiv_mem_grade K X n a ha
  c₁_compat X L hL := twistEquiv_deRhamCohBaseChangeAlgEquiv_firstChernClass K X L hL

end Stacks.WeilDeRham

end
