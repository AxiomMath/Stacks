module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise
public import StacksFrontier.LinearAlgebra.SymmetricPower.BaseChange

/-!
# Symmetric powers of a cartesian presheaf of modules are cartesian

Let `O` be a presheaf of commutative rings on a category `C` and `F` a presheaf of modules over
it.  For a morphism `f : X ⟶ Y` of `Cᵒᵖ`, `F` is *cartesian over `f`* when the base-change
comparison `O(Y) ⊗_{O(X)} F(X) ⟶ F(Y)` (`Stacks.PresheafOfModules.restrictionBaseChange`) is an
isomorphism.  This file proves that **the presheaf of sectionwise symmetric powers
`PresheafOfModules.symPowInt n F` is then cartesian over `f` in every integer degree `n`**: the
formation of `Symⁿ` commutes with base change (`SymmetricAlgebra.symmetricPowerBaseChange`), and
the comparison of `Symⁿ F` is `Symⁿ` of the comparison of `F` followed by that isomorphism.

It also records that being cartesian over `f` transfers along a morphism of presheaves of modules
which is bijective on the sections over the source and the target of `f`; this is the form in
which the cartesian property passes through a sheafification unit that is bijective only over
some objects of the site.

## Main results

* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_iff_of_bijective_app`.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_symPowInt`.

## Implementation notes

The comparison of `Symⁿ F` is identified with the composite on the whole symmetric algebra
rather than degreewise: both are, after the coercion to `Sym_{O(Y)}(F(Y))`, the scalar `a` times
a ring homomorphism `Sym_{O(X)}(F(X)) →+* Sym_{O(Y)}(F(Y))` applied to `x`, and two such ring
homomorphisms agree as soon as they agree on the base ring and on degree-one generators
(`SymPow.ringHom_ext`).

## References

* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v w a

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **Being cartesian over `f` transfers along a morphism of presheaves of modules which is
bijective on the sections over the source and the target of `f`.** -/
theorem isIso_restrictionBaseChange_iff_of_bijective_app
    {M N : PresheafOfModules.{max w a} (O ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (hX : Function.Bijective (g.app X)) (hY : Function.Bijective (g.app Y)) :
    IsIso (restrictionBaseChange M f) ↔ IsIso (restrictionBaseChange N f) := by
  have _ : IsIso (g.app X) := (ConcreteCategory.isIso_iff_bijective _).2 hX
  have _ : IsIso (g.app Y) := (ConcreteCategory.isIso_iff_bijective _).2 hY
  have h := restrictionBaseChange_naturality g f
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have : IsIso ((ModuleCat.extendScalars (O.map f).hom).map (g.app X) ≫
        restrictionBaseChange N f) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((ModuleCat.extendScalars (O.map f).hom).map (g.app X)) (restrictionBaseChange N f)
  · have : IsIso (restrictionBaseChange M f ≫ g.app Y) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right (restrictionBaseChange M f) (g.app Y)

end Stacks.PresheafOfModules

namespace SymPow

section BaseChangeComparison

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module A N]

/-- `Sym` of a left inverse after `Sym` of a linear map is the identity. -/
private theorem mapₛₗ_comp_eq_self {A P Q : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (a : P →ₗ[A] Q) (b : Q →ₗ[A] P) (h : ∀ m, b (a m) = m)
    (x : SymmetricAlgebra A P) :
    SymmetricAlgebra.mapₛₗ (RingHom.id A) b (SymmetricAlgebra.mapₛₗ (RingHom.id A) a x) = x := by
  rw [← SymmetricAlgebra.mapₛₗ_eq_comp (φ := RingHom.id A) (ψ := RingHom.id A)
    (χ := RingHom.id A) a b LinearMap.id (fun _ => rfl) (fun m => (h m).symm)]
  exact SymmetricAlgebra.mapₛₗ_eq_self _ (fun _ => rfl) (fun _ => rfl) _

/-- `Symⁿ` of an equivalence of modules is bijective. -/
theorem bijective_symMapₛₗ_of_linearEquiv (n : ℕ) {M' : Type*} [AddCommGroup M'] [Module A M']
    (e : M' ≃ₗ[A] N) :
    Function.Bijective (symMapₛₗ n (RingHom.id A) (e : M' →ₗ[A] N)) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨symMapₛₗ n (RingHom.id A) (e.symm : N →ₗ[A] M'), fun x => Subtype.ext ?_,
      fun y => Subtype.ext ?_⟩
  · exact mapₛₗ_comp_eq_self (e : M' →ₗ[A] N) (e.symm : N →ₗ[A] M') e.symm_apply_apply _
  · exact mapₛₗ_comp_eq_self (e.symm : N →ₗ[A] M') (e : M' →ₗ[A] N) e.apply_symm_apply _

/-- The ring homomorphism `x ↦ Sym(e)(β⁻¹(1 ⊗ x))` from `Sym_R(M)` to `Sym_A(N)`, for `β` the
base-change isomorphism of the symmetric algebra. -/
noncomputable def symBaseChangeRingHom (e : A ⊗[R] M →ₗ[A] N) :
    SymmetricAlgebra R M →+* SymmetricAlgebra A N :=
  ((SymmetricAlgebra.mapₛₗ (RingHom.id A) e).comp
    (SymmetricAlgebra.symmetricAlgebraBaseChange R A M).symm.toRingEquiv.toRingHom).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := A)
      (B := SymmetricAlgebra R M)).toRingHom

/-- When `e (1 ⊗ m) = u m`, the ring homomorphism through the base change is `Sym` of `u`. -/
theorem symBaseChangeRingHom_eq_mapₛₗ (e : A ⊗[R] M →ₗ[A] N) (u : M →ₛₗ[algebraMap R A] N)
    (he : ∀ m, e (1 ⊗ₜ m) = u m) :
    symBaseChangeRingHom e = SymmetricAlgebra.mapₛₗ (algebraMap R A) u := by
  refine SymmetricAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
  · rw [SymmetricAlgebra.mapₛₗ_algebraMap]
    show SymmetricAlgebra.mapₛₗ (RingHom.id A) e
        ((SymmetricAlgebra.symmetricAlgebraBaseChange R A M).symm
          ((1 : A) ⊗ₜ algebraMap R (SymmetricAlgebra R M) r)) = _
    have h : (1 : A) ⊗ₜ[R] algebraMap R (SymmetricAlgebra R M) r =
        algebraMap A (A ⊗[R] SymmetricAlgebra R M) (algebraMap R A r) := by
      rw [Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_eq_smul_one (A := SymmetricAlgebra R M) r,
        Algebra.algebraMap_eq_smul_one (A := A) r,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rfl
    rw [h, AlgEquiv.commutes, SymmetricAlgebra.mapₛₗ_algebraMap]
    rfl
  · show SymmetricAlgebra.mapₛₗ (RingHom.id A) e
        ((SymmetricAlgebra.symmetricAlgebraBaseChange R A M).symm
          ((1 : A) ⊗ₜ SymmetricAlgebra.ι R M m)) = _
    rw [SymmetricAlgebra.symmetricAlgebraBaseChange_symm_tmul_ι, SymmetricAlgebra.mapₛₗ_ι,
      SymmetricAlgebra.mapₛₗ_ι, he]

/-- **The base-change comparison of the `n`-th symmetric power**, `A ⊗_R Symⁿ_R(M) ⟶ Symⁿ_A(N)`,
built from a comparison `e : A ⊗_R M ⟶ N`: the base-change isomorphism of symmetric powers
followed by `Symⁿ(e)`. -/
noncomputable def symPowBaseChangeHom (n : ℕ) (e : A ⊗[R] M →ₗ[A] N) :
    A ⊗[R] symmetricPower n R M →ₗ[A] symmetricPower n A N :=
  (symMapₛₗ n (RingHom.id A) e).comp
    (SymmetricAlgebra.symmetricPowerBaseChange R A M n).toLinearMap

/-- The comparison of the `n`-th symmetric power on a pure tensor, read in `Sym_A(N)`. -/
theorem coe_symPowBaseChangeHom_tmul (n : ℕ) (e : A ⊗[R] M →ₗ[A] N)
    (u : M →ₛₗ[algebraMap R A] N) (he : ∀ m, e (1 ⊗ₜ m) = u m) (a : A)
    (x : symmetricPower n R M) :
    (symPowBaseChangeHom n e (a ⊗ₜ x) : SymmetricAlgebra A N) =
      a • SymmetricAlgebra.mapₛₗ (algebraMap R A) u (x : SymmetricAlgebra R M) := by
  have h1 : (symPowBaseChangeHom n e (a ⊗ₜ x) : SymmetricAlgebra A N) =
      SymmetricAlgebra.mapₛₗ (RingHom.id A) e
        ((SymmetricAlgebra.symmetricAlgebraBaseChange R A M).symm
          (a ⊗ₜ (x : SymmetricAlgebra R M))) := rfl
  rw [h1, TensorProduct.tmul_eq_smul_one_tmul, map_smul, Algebra.smul_def, map_mul,
    SymmetricAlgebra.mapₛₗ_algebraMap, RingHom.id_apply, ← Algebra.smul_def]
  exact congrArg (a • ·) (RingHom.congr_fun (symBaseChangeRingHom_eq_mapₛₗ e u he) _)

/-- The comparison of the `n`-th symmetric power is bijective when `e` is. -/
theorem bijective_symPowBaseChangeHom (n : ℕ) (e : A ⊗[R] M →ₗ[A] N)
    (he : Function.Bijective e) : Function.Bijective (symPowBaseChangeHom n e) :=
  (bijective_symMapₛₗ_of_linearEquiv n (LinearEquiv.ofBijective e he)).comp
    (SymmetricAlgebra.symmetricPowerBaseChange R A M n).bijective

end BaseChangeComparison

end SymPow

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The sections over `Z` of the presheaf of `k`-th symmetric powers of `F` are the `k`-th
symmetric power of `F(Z)`. -/
private noncomputable def symPowIntObjEquiv (k : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ CommRingCat RingCat)) (Z : Cᵒᵖ) :
    ((PresheafOfModules.symPowInt (Int.ofNat k) F).obj Z) ≃ₗ[O.obj Z]
      SymPow.symmetricPower k (O.obj Z) (F.obj Z) where
  toFun x := ⟨PresheafOfModules.symPowIntVal x, PresheafOfModules.symPowIntVal_mem _ _ x⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The comparison of the presheaf of `k`-th symmetric powers of `F` is bijective when `F` is
cartesian over `f`. -/
private theorem bijective_restrictionBaseChange_symPowInt_ofNat (k : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (restrictionBaseChange F f)] :
    Function.Bijective (restrictionBaseChange (PresheafOfModules.symPowInt (Int.ofNat k) F) f) := by
  let : Algebra (O.obj X) (O.obj Y) := (O.map f).hom.toAlgebra
  let e : (O.obj Y) ⊗[O.obj X] (F.obj X) →ₗ[O.obj Y] F.obj Y :=
    { toFun := fun z => restrictionBaseChange F f z
      map_add' := fun z z' => map_add (restrictionBaseChange F f).hom z z'
      map_smul' := fun c z => (restrictionBaseChange F f).hom.map_smul c z }
  have he : Function.Bijective e :=
    (ConcreteCategory.isIso_iff_bijective (restrictionBaseChange F f)).1 inferInstance
  let Φ : (O.obj Y) ⊗[O.obj X] ((PresheafOfModules.symPowInt (Int.ofNat k) F).obj X)
      →ₗ[O.obj Y] ((PresheafOfModules.symPowInt (Int.ofNat k) F).obj Y) :=
    { toFun := fun z => restrictionBaseChange (PresheafOfModules.symPowInt (Int.ofNat k) F) f z
      map_add' := fun z z' =>
        map_add (restrictionBaseChange (PresheafOfModules.symPowInt (Int.ofNat k) F) f).hom z z'
      map_smul' := fun c z =>
        (restrictionBaseChange (PresheafOfModules.symPowInt (Int.ofNat k) F) f).hom.map_smul
          c z }
  let ιX := symPowIntObjEquiv k F X
  let ιY := symPowIntObjEquiv k F Y
  let Ψ := (ιY.symm.toLinearMap.comp (SymPow.symPowBaseChangeHom k e)).comp
    (LinearEquiv.baseChange (O.obj X) (O.obj Y) _ _ ιX).toLinearMap
  have hΦ : Φ = Ψ := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
    | tmul c x =>
      refine PresheafOfModules.symPowIntVal_injective _ _ ?_
      have h1 : PresheafOfModules.symPowIntVal (Ψ (c ⊗ₜ x)) =
          ((SymPow.symPowBaseChangeHom k e (c ⊗ₜ ιX x)) : SymmetricAlgebra (O.obj Y) (F.obj Y)) :=
        rfl
      rw [h1, SymPow.coe_symPowBaseChangeHom_tmul k e (F.restrictₛₗ f)
        (fun m => restrictionBaseChange_one_tmul F f m) c (ιX x)]
      exact congrArg PresheafOfModules.symPowIntVal (restrictionBaseChange_tmul
        (PresheafOfModules.symPowInt (Int.ofNat k) F) f c x)
  show Function.Bijective Φ
  rw [hΦ]
  exact (ιY.symm.bijective.comp (SymPow.bijective_symPowBaseChangeHom k e he)).comp
    (LinearEquiv.baseChange (O.obj X) (O.obj Y) _ _ ιX).bijective

/-- The comparison of the presheaf of symmetric powers of `F` in a negative degree is bijective,
both of its sides being zero. -/
private theorem bijective_restrictionBaseChange_symPowInt_negSucc (k : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Function.Bijective
      (restrictionBaseChange (PresheafOfModules.symPowInt (Int.negSucc k) F) f) := by
  have hs : ∀ (Z : Cᵒᵖ) (x y : (PresheafOfModules.symPowInt (Int.negSucc k) F).obj Z),
      x = y := fun Z x y =>
    (SymPow.eq_zero_of_neg_of_mem_symmetricPowerInt _ _ (Int.negSucc_lt_zero k) x).trans
      (SymPow.eq_zero_of_neg_of_mem_symmetricPowerInt _ _ (Int.negSucc_lt_zero k) y).symm
  have hz : ∀ z : (ModuleCat.extendScalars (O.map f).hom).obj
      ((PresheafOfModules.symPowInt (Int.negSucc k) F).obj X), z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add a b ha hb => rw [ha, hb]; exact add_zero _
    | tmul c x => rw [hs X x 0]; exact TensorProduct.tmul_zero _ _
  exact ⟨fun z z' _ => (hz z).trans (hz z').symm, fun y => ⟨0, hs Y _ _⟩⟩

/-- **The presheaf of sectionwise symmetric powers of a presheaf of modules cartesian over `f` is
cartesian over `f`**, in every integer degree. -/
theorem isIso_restrictionBaseChange_symPowInt (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (restrictionBaseChange F f)] :
    IsIso (restrictionBaseChange (PresheafOfModules.symPowInt n F) f) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  obtain k | k := n
  · exact bijective_restrictionBaseChange_symPowInt_ofNat k F f
  · exact bijective_restrictionBaseChange_symPowInt_negSucc k F f

end Stacks.PresheafOfModules

end
