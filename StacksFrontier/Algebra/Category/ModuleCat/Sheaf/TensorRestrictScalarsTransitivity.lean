module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness

/-!
# `M ⊗_{A₁} ρ_*N ≅ ρ_*((M ⊗_{A₁} A₂) ⊗_{A₂} N)` for sheaves of modules on a site

Let `θ : A₁ ⟶ A₂` be a morphism of sheaves of commutative rings on a site `(C, J)`, let `M` be a
sheaf of `A₁`-modules and let `N` be a sheaf of `A₂`-modules.  Restriction of scalars along `θ`
reads `N` as a sheaf of `A₁`-modules, and this file proves

`M ⊗_{A₁} ρ_*N ≅ ρ_*((M ⊗_{A₁} A₂) ⊗_{A₂} N)`,

the transitivity of the tensor product across a change of rings, **with no hypothesis on `θ`**.
Here `M ⊗_{A₁} A₂` is the extension of scalars of [Stacks, Tag 03CZ], in the concrete sheafified
sectionwise form `Stacks.Sheaves.RingedToposModules.extendScalars`.

## Main definitions

* `Stacks.SheafOfModules.TensorTransitivity.presheafTransitivityIso`: the statement for
  **presheaves** of modules, where the extension of scalars is the sectionwise tensor product
  `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings`.
* `Stacks.SheafOfModules.TensorTransitivity.sheafifyRestrictScalarsIso`: **restriction of scalars
  commutes with the sheafification of presheaves of modules.**
* `Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsTransitivityIso`: the statement
  for **sheaves** of modules.

## Main results

* `Stacks.SheafOfModules.TensorTransitivity.isIso_of_isIso_app`: a morphism of presheaves of
  modules whose components are isomorphisms is an isomorphism.
* `Stacks.SheafOfModules.TensorTransitivity.presheafComparison_app_tmul`: the presheaf comparison
  is the one carrying `n ⊗_{A₁} m` to `n ⊗_{A₂} (1 ⊗_{A₁} m)`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), the extension of
  scalars.
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU), the change-of-rings
  adjunction for presheaves of modules.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings (ringPresheaf changeOfRings restrictScalars cofObj
  cofMap_tmul)

universe u

namespace Stacks.SheafOfModules.TensorTransitivity

/-! ### A morphism of presheaves of modules with isomorphic components is an isomorphism -/

section Reflect

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M N : PresheafOfModules.{u} R} (φ : M ⟶ N)

/-- **A morphism of presheaves of modules whose components are isomorphisms is an
isomorphism.** -/
theorem isIso_of_isIso_app (h : ∀ X, IsIso (φ.app X)) : IsIso φ := by
  refine ⟨⟨{ app := fun X ↦ inv (φ.app X), naturality := fun {X Y} f ↦ ?_ }, ?_, ?_⟩⟩
  · rw [Functor.map_inv, IsIso.eq_inv_comp, ← Category.assoc, ← φ.naturality f, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  · exact PresheafOfModules.hom_ext fun X ↦ IsIso.hom_inv_id (φ.app X)
  · exact PresheafOfModules.hom_ext fun X ↦ IsIso.inv_hom_id (φ.app X)

end Reflect

/-! ### The comparison on sections

For a ring homomorphism `R → S`, an `S`-module `N` and an `R`-module `M`, the map
`N ⊗_R M ⟶ N ⊗_S (S ⊗_R M)`, `n ⊗ m ↦ n ⊗ (1 ⊗ m)`, is a bijection: it is the inverse of
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/

section Algebraic

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (N : Type u) [AddCommGroup N] [Module S N]
  (M : Type u) [AddCommGroup M] [Module R M]

/-- **The biadditive map `(n, m) ↦ n ⊗_S (1 ⊗_R m)`** into `N ⊗_S (S ⊗_R M)`. -/
def unitTmulOne : N →+ M →+ TensorProduct S N (TensorProduct R S M) :=
  AddMonoidHom.mk'
    (fun n ↦ AddMonoidHom.mk' (fun m ↦ n ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m))
      (fun m m' ↦ by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]))
    (fun n n' ↦ AddMonoidHom.ext fun m ↦ TensorProduct.add_tmul n n' _)

/-- The value of `unitTmulOne` on a pair of sections. -/
theorem unitTmulOne_apply (n : N) (m : M) :
    unitTmulOne R S N M n m = n ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m) := rfl

/-- `unitTmulOne` is `S`-linear in its first variable. -/
theorem unitTmulOne_smul_left (s : S) (n : N) (m : M) :
    unitTmulOne R S N M (s • n) m = s • unitTmulOne R S N M n m :=
  (TensorProduct.smul_tmul' s n _).symm

/-- `unitTmulOne` is `R`-linear in its second variable, the `R`-action on the target being the
restriction of the `S`-action along the structure map. -/
theorem unitTmulOne_smul_right (r : R) (n : N) (m : M) :
    unitTmulOne R S N M n (r • m) = (algebraMap R S r) • unitTmulOne R S N M n m := by
  change n ⊗ₜ[S] ((1 : S) ⊗ₜ[R] (r • m)) = (algebraMap R S r) • (n ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m))
  rw [← TensorProduct.tmul_smul]
  refine congrArg (fun z ↦ n ⊗ₜ[S] z) ?_
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
    TensorProduct.smul_tmul' (algebraMap R S r) (1 : S) m, smul_eq_mul, mul_one]

variable [Module R N] [IsScalarTower R S N]

/-- **Cancellation of a base change inside a tensor product**,
`N ⊗_S (S ⊗_R M) ≅ N ⊗_R M`: Mathlib's
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
def cancelBaseChangeEquiv :
    TensorProduct S N (TensorProduct R S M) ≃ₗ[S] TensorProduct R N M :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N M

/-- The inverse of the cancellation carries `n ⊗_R m` to `n ⊗_S (1 ⊗_R m)`. -/
theorem cancelBaseChangeEquiv_symm_tmul (n : N) (m : M) :
    (cancelBaseChangeEquiv R S N M).symm (n ⊗ₜ[R] m) = unitTmulOne R S N M n m := by
  simp [cancelBaseChangeEquiv, unitTmulOne_apply]

/-- The additive map underlying the inverse of the cancellation. -/
def cancelSymmAdd : TensorProduct R N M →+ TensorProduct S N (TensorProduct R S M) :=
  (cancelBaseChangeEquiv R S N M).symm.toLinearMap.toAddMonoidHom

/-- The inverse of the cancellation is bijective. -/
theorem bijective_cancelSymmAdd : Function.Bijective (cancelSymmAdd R S N M) :=
  (cancelBaseChangeEquiv R S N M).symm.bijective

/-- The value of `cancelSymmAdd` on a pure tensor. -/
theorem cancelSymmAdd_tmul (n : N) (m : M) :
    cancelSymmAdd R S N M (n ⊗ₜ[R] m) = unitTmulOne R S N M n m :=
  cancelBaseChangeEquiv_symm_tmul R S N M n m

/-- An additive map agreeing with `unitTmulOne` on pure tensors **is** `cancelSymmAdd`. -/
theorem eq_cancelSymmAdd (g : TensorProduct R N M →+ TensorProduct S N (TensorProduct R S M))
    (hg : ∀ (n : N) (m : M), g (n ⊗ₜ[R] m) = unitTmulOne R S N M n m) :
    ∀ t, g t = cancelSymmAdd R S N M t := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul n m => rw [hg, cancelSymmAdd_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **An additive map carrying `n ⊗_R m` to `n ⊗_S (1 ⊗_R m)` is bijective.** -/
theorem bijective_of_tmul (g : TensorProduct R N M →+ TensorProduct S N (TensorProduct R S M))
    (hg : ∀ (n : N) (m : M), g (n ⊗ₜ[R] m) = unitTmulOne R S N M n m) :
    Function.Bijective g := by
  rw [AddMonoidHom.ext (eq_cancelSymmAdd R S N M g hg)]
  exact bijective_cancelSymmAdd R S N M

end Algebraic

/-! ### The comparison for presheaves of modules -/

section Presheaf

variable {C : Type u} [SmallCategory C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (θ : O₁ ⟶ O₂)
  (N : PresheafOfModules.{u} (ringPresheaf O₂)) (M : PresheafOfModules.{u} (ringPresheaf O₁))

/-- The biadditive map `(n, m) ↦ n ⊗ (1 ⊗ m)` on sections over `X`. -/
def unitTmulOneApp (X : Cᵒᵖ) :
    (N.obj X : Type u) →+ (M.obj X : Type u) →+
      ((Stacks.tensorObj N ((changeOfRings θ).obj M)).obj X : Type u) :=
  letI := (θ.app X).hom.toAlgebra
  unitTmulOne (O₁.obj X) (O₂.obj X) (N.obj X) (M.obj X)

/-- The biadditive map `(n, m) ↦ n ⊗ (1 ⊗ m)` commutes with the restriction maps. -/
theorem unitTmulOneApp_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : N.obj X) (m : M.obj X) :
    (Stacks.tensorObj N ((changeOfRings θ).obj M)).map f (unitTmulOneApp θ N M X n m) =
      unitTmulOneApp θ N M Y (N.map f n) (M.map f m) := by
  let _ := (θ.app X).hom.toAlgebra
  let _ := (θ.app Y).hom.toAlgebra
  refine (Stacks.tensorObj_map_tmul N ((changeOfRings θ).obj M) f n
    (show (((changeOfRings θ).obj M).obj X : Type u) from
      (1 : O₂.obj X) ⊗ₜ[O₁.obj X] m)).trans ?_
  refine congrArg (fun z : (((changeOfRings θ).obj M).obj Y : Type u) ↦
    (N.map f n) ⊗ₜ[(ringPresheaf O₂).obj Y] z) ?_
  exact (cofMap_tmul θ M f (1 : O₂.obj X) m).trans (by rw [map_one]; rfl)

/-- **The bilinear map `(n, m) ↦ n ⊗ (1 ⊗ m)`** of presheaves of `O₁`-modules, out of
`N|_{O₁}` and `M` into `(N ⊗_{O₂} (O₂ ⊗_{O₁} M))|_{O₁}`. -/
def unitBilinear :
    Stacks.BilinearMap ((restrictScalars θ).obj N) M
      ((restrictScalars θ).obj (Stacks.tensorObj N ((changeOfRings θ).obj M))) where
  app X := unitTmulOneApp θ N M X
  map_smul_left X r n m := by
    let _ := (θ.app X).hom.toAlgebra
    exact unitTmulOne_smul_left (O₁.obj X) (O₂.obj X) (N.obj X) (M.obj X) ((θ.app X).hom r) n m
  map_smul_right X r n m := by
    let _ := (θ.app X).hom.toAlgebra
    exact unitTmulOne_smul_right (O₁.obj X) (O₂.obj X) (N.obj X) (M.obj X) r n m
  naturality f n m := unitTmulOneApp_naturality θ N M f n m

/-- **The transitivity comparison for presheaves of modules**
`N|_{O₁} ⊗_{O₁} M ⟶ (N ⊗_{O₂} (O₂ ⊗_{O₁} M))|_{O₁}`, the transpose of `unitBilinear` along the
universal property of the objectwise tensor product. -/
def presheafComparison :
    Stacks.tensorObj ((restrictScalars θ).obj N) M ⟶
      (restrictScalars θ).obj (Stacks.tensorObj N ((changeOfRings θ).obj M)) :=
  Stacks.tensorHomEquiv.symm (unitBilinear θ N M)

/-- **The comparison carries `n ⊗_{O₁} m` to `n ⊗_{O₂} (1 ⊗_{O₁} m)`.** -/
theorem presheafComparison_app_tmul (X : Cᵒᵖ) (n : N.obj X) (m : M.obj X) :
    (presheafComparison θ N M).app X (n ⊗ₜ[(ringPresheaf O₁).obj X] m) =
      unitTmulOneApp θ N M X n m :=
  Stacks.BilinearMap.toTensorHom_app_tmul (unitBilinear θ N M) X n m

/-- **The comparison is bijective on sections over every object.** -/
theorem bijective_presheafComparison_app (X : Cᵒᵖ) :
    Function.Bijective ((presheafComparison θ N M).app X) := by
  let _ := (θ.app X).hom.toAlgebra
  let _ : Module (O₁.obj X) (N.obj X) :=
    ((ModuleCat.restrictScalars (θ.app X).hom).obj (N.obj X)).isModule
  have hT : IsScalarTower (O₁.obj X) (O₂.obj X) (N.obj X) :=
    ⟨fun r s n ↦ mul_smul ((θ.app X).hom r) s n⟩
  exact @bijective_of_tmul (O₁.obj X) (O₂.obj X) _ _ _ (N.obj X) _ _ (M.obj X) _ _ _ hT
    ((presheafComparison θ N M).app X).hom.toAddMonoidHom
    (presheafComparison_app_tmul θ N M X)

/-- The comparison `N|_{O₁} ⊗_{O₁} M ⟶ (N ⊗_{O₂} (O₂ ⊗_{O₁} M))|_{O₁}` of presheaves of modules
is an isomorphism. -/
instance isIso_presheafComparison : IsIso (presheafComparison θ N M) :=
  isIso_of_isIso_app _ fun X ↦
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_presheafComparison_app θ N M X)

/-- **`N|_{O₁} ⊗_{O₁} M ≅ (N ⊗_{O₂} (O₂ ⊗_{O₁} M))|_{O₁}` for presheaves of modules**, with no
hypothesis on `θ`. -/
def presheafTransitivityIso :
    Stacks.tensorObj ((restrictScalars θ).obj N) M ≅
      (restrictScalars θ).obj (Stacks.tensorObj N ((changeOfRings θ).obj M)) :=
  asIso (presheafComparison θ N M)

end Presheaf

/-! ### Restriction of scalars commutes with sheafification -/

section Sheafification

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R₁ R₂ : Sheaf J RingCat.{u}} (ρ : R₁ ⟶ R₂)
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The comparison `(ρ_*P)^a ⟶ ρ_*(P^a)` between the sheafification of a restriction of scalars
and the restriction of scalars of the sheafification: the transpose of the sheafification unit
along the sheafification adjunction for `R₁`-modules. -/
def sheafifyRestrictComparison (P : PresheafOfModules.{u} R₂.obj) :
    (_root_.PresheafOfModules.sheafification (R := R₁) (𝟙 R₁.obj)).obj
        ((_root_.PresheafOfModules.restrictScalars ρ.hom).obj P) ⟶
      (SheafOfModules.restrictScalars ρ).obj
        ((_root_.PresheafOfModules.sheafification (R := R₂) (𝟙 R₂.obj)).obj P) :=
  (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R₁.obj)).symm
    ((_root_.PresheafOfModules.restrictScalars ρ.hom).map
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R₂.obj)).unit.app P))

/-- **On underlying sheaves of abelian groups the comparison is the identity.** -/
theorem toSheaf_map_sheafifyRestrictComparison (P : PresheafOfModules.{u} R₂.obj) :
    (SheafOfModules.toSheaf R₁).map (sheafifyRestrictComparison ρ P) = 𝟙 _ :=
  (_root_.PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm (𝟙 R₁.obj) _).trans
    ((Equiv.symm_apply_eq _).2
      ((_root_.PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 R₂.obj) P).trans
        (Adjunction.homEquiv_id (CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{u})
          _).symm))

/-- The comparison `(ρ_*P)^a ⟶ ρ_*(P^a)` of sheaves of `R₁`-modules is an isomorphism. -/
instance isIso_sheafifyRestrictComparison (P : PresheafOfModules.{u} R₂.obj) :
    IsIso (sheafifyRestrictComparison ρ P) :=
  haveI : IsIso ((SheafOfModules.toSheaf R₁).map (sheafifyRestrictComparison ρ P)) := by
    rw [toSheaf_map_sheafifyRestrictComparison]
    exact ⟨⟨𝟙 _, Category.id_comp _, Category.comp_id _⟩⟩
  isIso_of_reflects_iso _ (SheafOfModules.toSheaf R₁)

/-- **Restriction of scalars commutes with the sheafification of presheaves of modules.** -/
def sheafifyRestrictScalarsIso (P : PresheafOfModules.{u} R₂.obj) :
    (_root_.PresheafOfModules.sheafification (R := R₁) (𝟙 R₁.obj)).obj
        ((_root_.PresheafOfModules.restrictScalars ρ.hom).obj P) ≅
      (SheafOfModules.restrictScalars ρ).obj
        ((_root_.PresheafOfModules.sheafification (R := R₂) (𝟙 R₂.obj)).obj P) :=
  asIso (sheafifyRestrictComparison ρ P)

end Sheafification

/-! ### The transitivity for sheaves of modules -/

section Sheaf

open Stacks.Sheaves.RingedToposModules (commRingSheaf commRingSheafMap extendScalars)

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The sheafification unit `P ⟶ P^a` of a presheaf of `A₂`-modules is locally surjective on the
underlying presheaves of abelian groups. -/
instance isLocallySurjective_unitApp (P : PresheafOfModules.{u} (ringPresheaf A₂)) :
    Presheaf.IsLocallySurjective J
      ((_root_.PresheafOfModules.toPresheaf (ringPresheaf A₂)).map
        ((_root_.PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app P)) := by
  rw [_root_.PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact (J.W_toSheafify P.presheaf).isLocallySurjective

/-- The sheafification unit `P ⟶ P^a` of a presheaf of `A₂`-modules is locally injective on the
underlying presheaves of abelian groups. -/
instance isLocallyInjective_unitApp (P : PresheafOfModules.{u} (ringPresheaf A₂)) :
    Presheaf.IsLocallyInjective J
      ((_root_.PresheafOfModules.toPresheaf (ringPresheaf A₂)).map
        ((_root_.PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app P)) := by
  rw [_root_.PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact (J.W_toSheafify P.presheaf).isLocallyInjective

/-- **The sheafification in the second tensor factor may be deferred**: replacing the sectionwise
extension of scalars by its sheafification does not change the sheafified tensor product. -/
def deferredSheafificationIso (M : SheafOfModules.{u} (commRingSheaf J A₁ h₁))
    (N : SheafOfModules.{u} (commRingSheaf J A₂ h₂)) :
    (_root_.PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj
        (Stacks.tensorObj N.val ((changeOfRings θ).obj M.val)) ≅
      (_root_.PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj
        (Stacks.tensorObj N.val
          ((_root_.PresheafOfModules.restrictScalars (𝟙 (commRingSheaf J A₂ h₂).obj)).obj
            ((SheafOfModules.forget _).obj ((extendScalars J θ h₁ h₂).obj M)))) := by
  have hiso := Stacks.isIso_sheafification_map_tensorMapRight
    (R := commRingSheaf J A₂ h₂) (𝟙 (commRingSheaf J A₂ h₂).obj) (M := N.val)
    ((_root_.PresheafOfModules.sheafificationAdjunction
        (R := commRingSheaf J A₂ h₂) (𝟙 (commRingSheaf J A₂ h₂).obj)).unit.app
      ((changeOfRings θ).obj M.val))
  exact @asIso _ _ _ _ _ hiso

/-- **`M ⊗_{A₁} ρ_*N ≅ ρ_*((M ⊗_{A₁} A₂) ⊗_{A₂} N)` for sheaves of modules on a site**, with no
hypothesis on `θ`. -/
def tensorRestrictScalarsTransitivityIso (M : SheafOfModules.{u} (commRingSheaf J A₁ h₁))
    (N : SheafOfModules.{u} (commRingSheaf J A₂ h₂)) :
    (_root_.PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).obj
        (Stacks.tensorObj
          ((_root_.PresheafOfModules.restrictScalars
            (commRingSheafMap J θ h₁ h₂).hom).obj N.val) M.val) ≅
      (SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj
        ((_root_.PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj
          (Stacks.tensorObj N.val
            ((_root_.PresheafOfModules.restrictScalars (𝟙 (commRingSheaf J A₂ h₂).obj)).obj
              ((SheafOfModules.forget _).obj ((extendScalars J θ h₁ h₂).obj M))))) :=
  (_root_.PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).mapIso
      (presheafTransitivityIso θ N.val M.val) ≪≫
    sheafifyRestrictScalarsIso (commRingSheafMap J θ h₁ h₂)
      (Stacks.tensorObj N.val ((changeOfRings θ).obj M.val)) ≪≫
    (SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).mapIso
      (deferredSheafificationIso J θ h₁ h₂ M N)

end Sheaf

end Stacks.SheafOfModules.TensorTransitivity

end
