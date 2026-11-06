module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Homotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RingPresheaf

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This formalizes Stacks 18.9.2 (Tag 03CU): the change-of-rings (extension of
scalars / tensor product) functor for presheaves of modules over a presheaf of
rings on a category `C` is left adjoint to restriction of scalars.

Throughout we fix a category `C`. A *presheaf of rings* is a functor
`Cᵒᵖ ⥤ RingCat`; following the Stacks Modules-on-Sites convention we work with
*commutative* rings, i.e. presheaves of rings are modelled as functors
`Cᵒᵖ ⥤ CommRingCat`, with underlying presheaf of rings obtained by composing
with the forgetful functor `CommRingCat ⥤ RingCat`.

A *presheaf of `O`-modules* (Definition 2) is Mathlib's `PresheafOfModules`:
an `O(X)`-module for each object `X`, together with semilinear restriction maps
satisfying functoriality.

Given a morphism of presheaves of rings `θ : O₁ ⟶ O₂`:

* (Definition 3, restriction of scalars) `restrictScalars θ : PMod(O₂) ⥤ PMod(O₁)`
  regards an `O₂`-module presheaf `F` as an `O₁`-module presheaf via `θ`.  This is
  Mathlib's `PresheafOfModules.restrictScalars`.

* (Definition 4, change of rings / tensor product) `changeOfRings θ : PMod(O₁) ⥤ PMod(O₂)`
  sends `G` to the presheaf `X ↦ O₂(X) ⊗_{O₁(X)} G(X)`, with restriction maps
  `a ⊗ x ↦ O₂(f)(a) ⊗ G(f)(x)` induced by the restriction maps of `O₂` and `G`.

* (Main Statement, Tag 03CU) the change of rings functor is left adjoint to the
  restriction functor: `changeOfRings θ ⊣ restrictScalars θ`.  Equivalently there
  is a bijection, natural in `F` and `G`,
  `Hom_{O₁}(G, F_{O₁}) ≅ Hom_{O₂}(O₂ ⊗_{p,O₁} G, F)`.

## Notes

- This is the presheaf-level analogue of the pointwise ring-theoretic adjunction
  between extension and restriction of scalars (`ModuleCat.extendRestrictScalarsAdj`),
  applied at each object `X` of `C` together with naturality in `X`.
- The forward direction sends `φ : G ⟶ F_{O₁}` to the map with component at `U`
  given by `a ⊗ x ↦ a • φ_U(x)`; the inverse sends `ψ` to `x ↦ ψ_U(1 ⊗ x)`.
- We work with commutative rings (the Stacks Modules-on-Sites convention).  The
  presheaves carry no sheaf/topology condition: `C` is merely a category.
-/

open CategoryTheory TensorProduct

namespace Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type*} [Category C]

/-! The underlying presheaf of rings `O ⋙ forget₂ CommRingCat RingCat` of a presheaf of
commutative rings is defined once, as `Stacks.PresheafOfRings.ringPresheaf`; it is made
available here under the name `Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf` that this
file and its descendants use. -/

export Stacks.PresheafOfRings (ringPresheaf)

/-- A *presheaf of `O`-modules* (Definition 2), where `O : Cᵒᵖ ⥤ CommRingCat` is a
presheaf of commutative rings.  This is Mathlib's `PresheafOfModules` over the
underlying presheaf of rings. -/
abbrev PMod (O : Cᵒᵖ ⥤ CommRingCat) : Type _ := PresheafOfModules (ringPresheaf O)

variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat}

/-- Definition 3 (Restriction of scalars).  Given `θ : O₁ ⟶ O₂`, the restriction
functor `(-)_{O₁} : PMod(O₂) ⥤ PMod(O₁)` regards each `O₂(X)`-module `F(X)` as an
`O₁(X)`-module along `θ_X`.  This is Mathlib's `PresheafOfModules.restrictScalars`. -/
noncomputable def restrictScalars (θ : O₁ ⟶ O₂) : PMod O₂ ⥤ PMod O₁ :=
  PresheafOfModules.restrictScalars (Functor.whiskerRight θ (forget₂ CommRingCat RingCat))


noncomputable def tmulMap (R₁ R₂ R₁' R₂' : Type*)
    [CommRing R₁] [CommRing R₂] [CommRing R₁'] [CommRing R₂']
    [Algebra R₁ R₂] [Algebra R₁' R₂']
    (p : R₁ →+* R₁') (q : R₂ →+* R₂')
    (hsq : q.comp (algebraMap R₁ R₂) = (algebraMap R₁' R₂').comp p)
    (M : Type*) [AddCommGroup M] [Module R₁ M]
    (M' : Type*) [AddCommGroup M'] [Module R₁' M']
    (φ : M →+ M') (hφ : ∀ (r : R₁) (x : M), φ (r • x) = p r • φ x) :
    (TensorProduct R₁ R₂ M) →+ (TensorProduct R₁' R₂' M') := by
  refine TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun x => (q a) ⊗ₜ[R₁'] (φ x)) ?_) ?_) ?_
  · intro x y; simp [TensorProduct.tmul_add]
  · intro a b; ext x; simp [map_add, TensorProduct.add_tmul]
  · intro r a x
    simp only [AddMonoidHom.mk'_apply]
    rw [hφ]
    have hra : (r • a) = (algebraMap R₁ R₂) r * a := Algebra.smul_def r a
    rw [hra, map_mul]
    rw [show q ((algebraMap R₁ R₂) r) = (algebraMap R₁' R₂') (p r) from by
      rw [← RingHom.comp_apply, hsq]; rfl]
    rw [show ((algebraMap R₁' R₂') (p r) * q a) = (p r) • (q a) from
      (Algebra.smul_def (p r) (q a)).symm]
    rw [TensorProduct.smul_tmul]

@[simp] theorem tmulMap_tmul (R₁ R₂ R₁' R₂' : Type*)
    [CommRing R₁] [CommRing R₂] [CommRing R₁'] [CommRing R₂']
    [Algebra R₁ R₂] [Algebra R₁' R₂']
    (p : R₁ →+* R₁') (q : R₂ →+* R₂')
    (hsq : q.comp (algebraMap R₁ R₂) = (algebraMap R₁' R₂').comp p)
    (M : Type*) [AddCommGroup M] [Module R₁ M]
    (M' : Type*) [AddCommGroup M'] [Module R₁' M']
    (φ : M →+ M') (hφ : ∀ (r : R₁) (x : M), φ (r • x) = p r • φ x)
    (a : R₂) (x : M) :
    tmulMap R₁ R₂ R₁' R₂' p q hsq M M' φ hφ (a ⊗ₜ[R₁] x) = (q a) ⊗ₜ[R₁'] (φ x) := by
  simp only [tmulMap, TensorProduct.liftAddHom_tmul, AddMonoidHom.mk'_apply]

theorem tmulMap_smul (R₁ R₂ R₁' R₂' : Type*)
    [CommRing R₁] [CommRing R₂] [CommRing R₁'] [CommRing R₂']
    [Algebra R₁ R₂] [Algebra R₁' R₂']
    (p : R₁ →+* R₁') (q : R₂ →+* R₂')
    (hsq : q.comp (algebraMap R₁ R₂) = (algebraMap R₁' R₂').comp p)
    (M : Type*) [AddCommGroup M] [Module R₁ M]
    (M' : Type*) [AddCommGroup M'] [Module R₁' M']
    (φ : M →+ M') (hφ : ∀ (r : R₁) (x : M), φ (r • x) = p r • φ x)
    (s : R₂) (t : TensorProduct R₁ R₂ M) :
    tmulMap R₁ R₂ R₁' R₂' p q hsq M M' φ hφ (s • t) =
      q s • tmulMap R₁ R₂ R₁' R₂' p q hsq M M' φ hφ t := by
  induction t with
  | add a b ha hb => simp [ha, hb, smul_add]
  | tmul a x =>
    simp only [smul_tmul', smul_eq_mul]
    rw [tmulMap_tmul, tmulMap_tmul, map_mul, TensorProduct.smul_tmul', smul_eq_mul]

noncomputable def cofObj (θ : O₁ ⟶ O₂) (G : PMod O₁) (X : Cᵒᵖ) : ModuleCat ((ringPresheaf O₂).obj
    X) :=
  letI := (θ.app X).hom.toAlgebra
  ModuleCat.of (O₂.obj X) (TensorProduct (O₁.obj X) (O₂.obj X) (G.obj X))

theorem nat_sq (θ : O₁ ⟶ O₂) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    letI := (θ.app X).hom.toAlgebra
    letI := (θ.app Y).hom.toAlgebra
    ((O₂.map f).hom).comp (algebraMap (O₁.obj X) (O₂.obj X)) =
      (algebraMap (O₁.obj Y) (O₂.obj Y)).comp ((O₁.map f).hom) := by
  change ((O₂.map f).hom).comp ((θ.app X).hom) = ((θ.app Y).hom).comp ((O₁.map f).hom)
  have := θ.naturality f
  ext z
  have h2 := congrArg (fun (m : O₁.obj X ⟶ O₂.obj Y) => m.hom z) this
  simp only [CommRingCat.comp_apply] at h2
  exact h2.symm

/-- The `O(Y)`-module structure on a restriction of scalars along `O(f)`; instance search no
longer sees through `O ⋙ forget₂ CommRingCat RingCat` to find it. -/
local instance moduleRestrictScalarsObj (O : Cᵒᵖ ⥤ CommRingCat) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (M : ModuleCat ((ringPresheaf O).obj Y)) :
    Module (O.obj Y) ((ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).obj M) :=
  inferInstanceAs (Module ((ringPresheaf O).obj Y) M)

theorem G_semilin (G : PMod O₁) {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : O₁.obj X) (x : G.obj X) :
    (G.map f).hom (r • x) = (O₁.map f).hom r • (G.map f).hom x :=
  (G.map f).hom.map_smul r x

noncomputable def cofMap (θ : O₁ ⟶ O₂) (G : PMod O₁) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    cofObj θ G X ⟶ (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).obj (cofObj θ G
        Y) := by
  letI := (θ.app X).hom.toAlgebra
  letI := (θ.app Y).hom.toAlgebra
  refine ModuleCat.ofHom (R := O₂.obj X) (X := cofObj θ G X)
    (Y := (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).obj (cofObj θ G Y))
    { toFun := tmulMap (O₁.obj X) (O₂.obj X) (O₁.obj Y) (O₂.obj Y)
        (O₁.map f).hom (O₂.map f).hom (nat_sq θ f)
        (G.obj X) (G.obj Y) (G.map f).hom.toAddMonoidHom (G_semilin G f)
      map_add' := map_add _
      map_smul' := ?_ }
  intro s t
  exact tmulMap_smul (O₁.obj X) (O₂.obj X) (O₁.obj Y) (O₂.obj Y)
    (O₁.map f).hom (O₂.map f).hom (nat_sq θ f)
    (G.obj X) (G.obj Y) (G.map f).hom.toAddMonoidHom (G_semilin G f) s t

theorem cofMap_tmul (θ : O₁ ⟶ O₂) (G : PMod O₁) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : O₂.obj X) (x : G.obj X) :
    letI := (θ.app X).hom.toAlgebra
    letI := (θ.app Y).hom.toAlgebra
    (cofMap θ G f).hom (a ⊗ₜ[O₁.obj X] x) = ((O₂.map f).hom a) ⊗ₜ[O₁.obj Y] ((G.map f).hom x) := by
  let := (θ.app X).hom.toAlgebra
  let := (θ.app Y).hom.toAlgebra
  change (tmulMap (O₁.obj X) (O₂.obj X) (O₁.obj Y) (O₂.obj Y)
        (O₁.map f).hom (O₂.map f).hom (nat_sq θ f)
        (G.obj X) (G.obj Y) (G.map f).hom.toAddMonoidHom (G_semilin G f)) (a ⊗ₜ[O₁.obj X] x) = _
  rw [tmulMap_tmul]
  rfl

/-- Two morphisms out of `cofObj θ G X` agree if they agree on pure tensors. -/
private theorem cofObj_hom_ext (θ : O₁ ⟶ O₂) (G : PMod O₁) (X : Cᵒᵖ)
    {M : ModuleCat (O₂.obj X)} (f g : cofObj θ G X ⟶ M)
    (h : letI := (θ.app X).hom.toAlgebra
      ∀ (a : O₂.obj X) (x : G.obj X), f.hom (a ⊗ₜ[O₁.obj X] x) = g.hom (a ⊗ₜ[O₁.obj X] x)) :
    f = g := by
  let := (θ.app X).hom.toAlgebra
  refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a x => exact h a x

theorem cof_map_id (θ : O₁ ⟶ O₂) (G : PMod O₁) (X : Cᵒᵖ) :
    cofMap θ G (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((ringPresheaf O₂).map (𝟙 X)).hom (by simp)).inv.app
        (cofObj θ G X) := by
  let := (θ.app X).hom.toAlgebra
  refine cofObj_hom_ext θ _ _ _ _ fun a x => ?_
  rw [cofMap_tmul]
  rw [ModuleCat.restrictScalarsId'_inv_app]
  have hG : (G.map (𝟙 X)).hom x = x := by
    rw [G.map_id]; rw [ModuleCat.restrictScalarsId'_inv_app]; rfl
  have hO : ((O₂.map (𝟙 X)).hom) a = a := by simp
  rw [hG, hO]
  rfl

theorem G_map_comp_apply (G : PMod O₁) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : G.obj X) :
    (G.map (f ≫ g)).hom x = (G.map g).hom ((G.map f).hom x) := by
  rw [G.map_comp]
  simp [ModuleCat.restrictScalarsComp'_inv_app]

theorem cof_map_comp (θ : O₁ ⟶ O₂) (G : PMod O₁) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cofMap θ G (f ≫ g) =
      cofMap θ G f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map (cofMap θ G g) ≫
          (ModuleCat.restrictScalarsComp' ((ringPresheaf O₂).map f).hom
              ((ringPresheaf O₂).map g).hom ((ringPresheaf O₂).map (f ≫ g)).hom
              (by rw [(ringPresheaf O₂).map_comp]; rfl)).inv.app (cofObj θ G Z) := by
  let := (θ.app X).hom.toAlgebra
  let := (θ.app Y).hom.toAlgebra
  let := (θ.app Z).hom.toAlgebra
  refine cofObj_hom_ext θ _ _ _ _ fun a x => ?_
  rw [cofMap_tmul]
  simp only [ModuleCat.hom_comp, Function.comp_apply, LinearMap.coe_comp]
  rw [ModuleCat.restrictScalarsComp'_inv_app]
  change _ = (ModuleCat.restrictScalarsComp'App _ _ _ _ _).inv.hom
    (((ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map (cofMap θ G g)).hom
      ((cofMap θ G f).hom (a ⊗ₜ[O₁.obj X] x)))
  rw [cofMap_tmul]
  rw [ModuleCat.restrictScalarsComp'App_inv_apply]
  change _ = (cofMap θ G g).hom (((O₂.map f).hom a) ⊗ₜ[O₁.obj Y] ((G.map f).hom x))
  rw [cofMap_tmul]
  rw [← CategoryTheory.comp_apply, ← (O₂.map_comp f g)]
  rw [G_map_comp_apply]

/-- Definition 4: the presheaf `O₂ ⊗_{p,O₁} G` of `O₂`-modules, with objectwise
value `O₂(X) ⊗_{O₁(X)} G(X)` and restriction maps `a ⊗ x ↦ O₂(f)(a) ⊗ G(f)(x)`. -/
noncomputable def changeOfRingsObj (θ : O₁ ⟶ O₂) (G : PMod O₁) : PMod O₂ where
  obj X := cofObj θ G X
  map f := cofMap θ G f
  map_id X := cof_map_id θ G X
  map_comp f g := cof_map_comp θ G f g

/-- The component at `X` of the morphism `changeOfRingsObj θ G ⟶ changeOfRingsObj θ H`
induced by `φ : G ⟶ H`, namely `id ⊗ φ_X : O₂(X) ⊗ G(X) → O₂(X) ⊗ H(X)`. -/
noncomputable def cofHomApp (θ : O₁ ⟶ O₂) {G H : PMod O₁} (φ : G ⟶ H) (X : Cᵒᵖ) :
    cofObj θ G X ⟶ cofObj θ H X := by
  letI := (θ.app X).hom.toAlgebra
  refine ModuleCat.ofHom (R := O₂.obj X) (X := cofObj θ G X) (Y := cofObj θ H X)
    (LinearMap.baseChange (O₂.obj X) ?_)
  exact (φ.app X).hom

theorem cofHomApp_tmul (θ : O₁ ⟶ O₂) {G H : PMod O₁} (φ : G ⟶ H) (X : Cᵒᵖ)
    (a : O₂.obj X) (x : G.obj X) :
    letI := (θ.app X).hom.toAlgebra
    (cofHomApp θ φ X).hom (a ⊗ₜ[O₁.obj X] x) = a ⊗ₜ[O₁.obj X] ((φ.app X).hom x) := by
  let := (θ.app X).hom.toAlgebra
  rw [cofHomApp, ModuleCat.hom_ofHom]
  rfl

theorem phi_naturality (G H : PMod O₁) (φ : G ⟶ H) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : G.obj X) :
    (φ.app Y).hom ((G.map f).hom x) = (H.map f).hom ((φ.app X).hom x) := by
  have := φ.naturality f
  have h2 := congrArg (fun (m : G.obj X ⟶ (ModuleCat.restrictScalars ((ringPresheaf O₁).map
      f).hom).obj (H.obj Y)) => m.hom x) this
  simpa using h2

/-- The morphism `changeOfRingsObj θ G ⟶ changeOfRingsObj θ H` induced by `φ : G ⟶ H`. -/
noncomputable def cofHom (θ : O₁ ⟶ O₂) {G H : PMod O₁} (φ : G ⟶ H) :
    changeOfRingsObj θ G ⟶ changeOfRingsObj θ H :=
  PresheafOfModules.Hom.mk (fun X => cofHomApp θ φ X) (by
    intro X Y f
    let := (θ.app X).hom.toAlgebra
    let := (θ.app Y).hom.toAlgebra
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext (fun t => ?_)
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a x =>
      simp only [ModuleCat.hom_comp, Function.comp_apply, LinearMap.coe_comp]
      change (cofHomApp θ φ Y).hom ((cofMap θ G f).hom (a ⊗ₜ[O₁.obj X] x)) =
        (cofMap θ H f).hom ((cofHomApp θ φ X).hom (a ⊗ₜ[O₁.obj X] x))
      rw [cofMap_tmul, cofHomApp_tmul, cofHomApp_tmul, cofMap_tmul]
      rw [phi_naturality G H φ f x])

theorem cofHom_app_tmul (θ : O₁ ⟶ O₂) {G H : PMod O₁} (φ : G ⟶ H) (X : Cᵒᵖ)
    (a : O₂.obj X) (x : G.obj X) :
    letI := (θ.app X).hom.toAlgebra
    ((cofHom θ φ).app X).hom (a ⊗ₜ[O₁.obj X] x) = a ⊗ₜ[O₁.obj X] ((φ.app X).hom x) := by
  let := (θ.app X).hom.toAlgebra
  change (cofHomApp θ φ X).hom (a ⊗ₜ[O₁.obj X] x) = _
  rw [cofHomApp_tmul]

theorem cofHom_id (θ : O₁ ⟶ O₂) (G : PMod O₁) : cofHom θ (𝟙 G) = 𝟙 (changeOfRingsObj θ G) := by
  refine PresheafOfModules.hom_ext fun X => ?_
  refine cofObj_hom_ext θ _ _ _ _ fun a x => ?_
  exact cofHom_app_tmul θ (𝟙 G) X a x

theorem cofHom_comp (θ : O₁ ⟶ O₂) {G H K : PMod O₁} (φ : G ⟶ H) (ψ : H ⟶ K) :
    cofHom θ (φ ≫ ψ) = cofHom θ φ ≫ cofHom θ ψ := by
  refine PresheafOfModules.hom_ext fun X => ?_
  refine cofObj_hom_ext θ _ _ _ _ fun a x => ?_
  exact (cofHom_app_tmul θ (φ ≫ ψ) X a x).trans
    ((congrArg _ (cofHom_app_tmul θ φ X a x)).trans (cofHom_app_tmul θ ψ X a _)).symm

/-- **Definition 4 (change of rings functor).** The functor
`O₂ ⊗_{p,O₁} (-) : PMod(O₁) ⥤ PMod(O₂)` sending `G` to the tensor product presheaf
`changeOfRingsObj θ G` and a morphism `φ` to `cofHom θ φ`. -/
noncomputable def changeOfRings (θ : O₁ ⟶ O₂) : PMod O₁ ⥤ PMod O₂ where
  obj G := changeOfRingsObj θ G
  map φ := cofHom θ φ
  map_id G := cofHom_id θ G
  map_comp φ ψ := cofHom_comp θ φ ψ

/-!
## Proof sketch of Stacks 18.9.2 (Tag 03CU)

We assemble the *objectwise* extension/restriction-of-scalars adjunction
`ModuleCat.extendRestrictScalarsAdj (θ.app X).hom` (with algebra structure
`(θ.app X).hom.toAlgebra`, matching `cofObj`) into a presheaf-level adjunction.

The hom-set bijection, for `G : PMod O₁`, `F : PMod O₂`, is
`(changeOfRings θ).obj G ⟶ F  ≃  G ⟶ (restrictScalars θ).obj F`, with:

* **forward** `ψ ↦ φ`, where `φ_X(x) = ψ_X(1 ⊗ x)`  (the *unit* direction);
* **inverse** `φ ↦ ψ`, where `ψ_X(a ⊗ x) = a • φ_X(x)`  (the *counit* direction).

Each component is exactly the objectwise `extendRestrictScalarsAdj` bijection, so
the only genuine content is (i) the two maps are well-defined *presheaf*
morphisms (naturality in `X`), (ii) the two maps are mutually inverse (immediate
objectwise), and (iii) the bijection is natural in `G` and `F`.  Each of these is
established by a named sub-lemma below.
-/

/-- **Sub-lemma (counit / inverse map), objectwise component.**

The `O₂(X)`-linear map `cofObj θ G X ⟶ F.obj X` sending `a ⊗ x ↦ a • φ_X(x)`,
where `φ : G ⟶ (restrictScalars θ).obj F`.  This is the objectwise
`HomEquiv.fromExtendScalars (θ.app X).hom` applied to `φ.app X`.

ARGUMENT / STRATEGY: build the underlying additive/linear map by
`TensorProduct.lift` (or `LinearMap.liftBaseChange`/`TensorProduct.liftAddHom`)
of the bilinear map `(a, x) ↦ a • (φ.app X).hom x`, where the `O₂(X)`-action on
`F.obj X` is the genuine module structure and `(φ.app X).hom x : F.obj X` lives in
the restricted-scalars module (same carrier).  `O₂(X)`-linearity in `a` is the
left-factor action; `O₁(X)`-balancedness uses that `φ.app X` is `O₁(X)`-linear,
i.e. `(φ.app X).hom (r • x) = θ_X(r) • (φ.app X).hom x` (`map_smul` of `φ.app X`
combined with the `restrictScalars` action `r • y = θ_X(r) • y`).
The construction is structurally identical to the existing `tmulMap` /
`cofHomApp` builders in this file. -/
noncomputable def counitApp (θ : O₁ ⟶ O₂) {G : PMod O₁} {F : PMod O₂}
    (φ : G ⟶ (restrictScalars θ).obj F) (X : Cᵒᵖ) :
    cofObj θ G X ⟶ F.obj X := by
  letI := (θ.app X).hom.toAlgebra
  -- carrier-coercion of `φ_X x : restrictScalars module` back to `F.obj X`
  let g : G.obj X → F.obj X := fun x => (φ.app X).hom x
  -- the underlying additive map `a ⊗ x ↦ a • g x`
  let A : TensorProduct (O₁.obj X) (O₂.obj X) (G.obj X) →+ F.obj X :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk'
        (fun a => AddMonoidHom.mk' (fun x => a • g x)
          (fun x y => by simp only [g, map_add, smul_add]))
        (fun a b => by ext x; simp only [g, AddMonoidHom.mk'_apply, add_smul,
            AddMonoidHom.add_apply]))
      (fun r a x => by
        simp only [g, AddMonoidHom.mk'_apply]
        change (r • a) • (show F.obj X from (φ.app X).hom x)
            = a • (show F.obj X from (φ.app X).hom (r • x))
        have hmap : (show F.obj X from (φ.app X).hom (r • x))
            = (algebraMap (O₁.obj X) (O₂.obj X)) r • (show F.obj X from (φ.app X).hom x) := by
          rw [(φ.app X).hom.map_smul r x]; rfl
        rw [hmap, Algebra.smul_def, mul_smul, smul_smul, smul_smul, mul_comm])
  have hAsmul : ∀ (s : O₂.obj X) (t : TensorProduct (O₁.obj X) (O₂.obj X) (G.obj X)),
      A (s • t) = s • A t := by
    intro s t
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => simp only [smul_add, map_add, ha, hb]
    | tmul a x =>
      simp only [A, smul_tmul', smul_eq_mul, TensorProduct.liftAddHom_tmul,
        AddMonoidHom.mk'_apply, smul_smul]
  exact ModuleCat.ofHom (R := O₂.obj X) (X := cofObj θ G X) (Y := F.obj X)
    { toFun := A
      map_add' := map_add A
      map_smul' := hAsmul }

/-- `counitApp` on pure tensors: `a ⊗ x ↦ a • φ_X(x)`. -/
theorem counitApp_tmul (θ : O₁ ⟶ O₂) {G : PMod O₁} {F : PMod O₂}
    (φ : G ⟶ (restrictScalars θ).obj F) (X : Cᵒᵖ)
    (a : O₂.obj X) (x : G.obj X) :
    letI := (θ.app X).hom.toAlgebra
    -- the element `(φ.app X).hom x` lives in the `O₁`-restricted module, whose carrier is
    -- `F.obj X`; we view it back in `F.obj X` to apply the genuine `O₂(X)`-action by `a`.
    (counitApp θ φ X).hom (a ⊗ₜ[O₁.obj X] x) = a • (show F.obj X from (φ.app X).hom x) := by
  let := (θ.app X).hom.toAlgebra
  rw [counitApp, ModuleCat.hom_ofHom]
  rfl

/-- **Sub-lemma (inverse map is a presheaf morphism).**

The components `counitApp θ φ X` assemble into a morphism of presheaves of
`O₂`-modules `(changeOfRings θ).obj G ⟶ F`.

ARGUMENT / STRATEGY: naturality in `X`.  For `f : X ⟶ Y` we must check the square
`cofMap θ G f` followed by `counitApp θ φ Y` equals `counitApp θ φ X` followed by
`F.map f` (modulo the semilinear `restrictScalars` wrapper).  Reduce to pure
tensors `a ⊗ x` via `TensorProduct.induction_on` (cf. `cofHom`'s naturality
proof).  On `a ⊗ x`:
* LHS = `counitApp θ φ Y (cofMap θ G f (a⊗x))`
      = `counitApp θ φ Y (O₂(f)(a) ⊗ G(f)(x))`        [`cofMap_tmul`]
      = `O₂(f)(a) • φ_Y(G(f)(x))`                       [`counitApp_tmul`]
      = `O₂(f)(a) • F(f)(φ_X(x))`                       [`phi_naturality`, i.e. `φ.naturality f`]
* RHS = `F.map f (counitApp θ φ X (a⊗x))`
      = `F.map f (a • φ_X(x))`                          [`counitApp_tmul`]
      = `O₂(f)(a) • F.map f (φ_X(x))`                   [`F.map f` is `O₂`-semilinear].
These agree.  Use the existing `phi_naturality` (adapted to `φ : G ⟶ restrictScalars F`)
and the semilinearity `(F.map f).hom (s • y) = O₂(f)(s) • (F.map f).hom y`. -/
noncomputable def counitHom (θ : O₁ ⟶ O₂) {G : PMod O₁} {F : PMod O₂}
    (φ : G ⟶ (restrictScalars θ).obj F) :
    (changeOfRings θ).obj G ⟶ F :=
  PresheafOfModules.Hom.mk (fun X => counitApp θ φ X) (by
    -- naturality square; reduce to pure tensors and use `cofMap_tmul`, `counitApp_tmul`,
    -- naturality of `φ`, and semilinearity of `F.map f`.
    intro X Y f
    let := (θ.app X).hom.toAlgebra
    let := (θ.app Y).hom.toAlgebra
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext (fun t => ?_)
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a x =>
      simp only [ModuleCat.hom_comp, Function.comp_apply, LinearMap.coe_comp]
      change (counitApp θ φ Y).hom ((cofMap θ G f).hom (a ⊗ₜ[O₁.obj X] x)) =
        (F.map f).hom ((counitApp θ φ X).hom (a ⊗ₜ[O₁.obj X] x))
      rw [cofMap_tmul, counitApp_tmul, counitApp_tmul]
      rw [phi_naturality G ((restrictScalars θ).obj F) φ f x]
      rw [(F.map f).hom.map_smul a ((φ.app X).hom x)]
      rfl)

/-- **Sub-lemma (unit / forward map), objectwise component.**

The `O₁(X)`-linear map `G.obj X ⟶ ((restrictScalars θ).obj F).obj X` sending
`x ↦ ψ_X(1 ⊗ x)`, where `ψ : (changeOfRings θ).obj G ⟶ F`.  This is the objectwise
`HomEquiv.toRestrictScalars (θ.app X).hom` applied to `ψ.app X`.

ARGUMENT / STRATEGY: `((restrictScalars θ).obj F).obj X` has the same carrier as
`F.obj X` with `O₁(X)`-action via `θ_X`.  Define the map as `(ψ.app X).hom` post-
composed with the `O₁(X)`-linear map `x ↦ (1 : O₂(X)) ⊗ₜ x : cofObj θ G X` (the
unit of the objectwise adjunction).  `O₁(X)`-linearity: `1 ⊗ (r • x) = θ_X(r) • (1 ⊗ x)`
in `cofObj`, and `ψ.app X` is `O₂(X)`-linear, so `ψ_X(θ_X(r) • (1⊗x)) = θ_X(r) • ψ_X(1⊗x)`,
which is exactly the `restrictScalars` `O₁(X)`-action `r • ψ_X(1⊗x)`. -/
noncomputable def unitApp (θ : O₁ ⟶ O₂) {G : PMod O₁} {F : PMod O₂}
    (ψ : (changeOfRings θ).obj G ⟶ F) (X : Cᵒᵖ) :
    G.obj X ⟶ ((restrictScalars θ).obj F).obj X := by
  letI := (θ.app X).hom.toAlgebra
  refine ModuleCat.ofHom (R := O₁.obj X) (X := G.obj X)
    (Y := ((restrictScalars θ).obj F).obj X)
    { toFun := fun x => (ψ.app X).hom ((1 : O₂.obj X) ⊗ₜ[O₁.obj X] x)
      map_add' := fun x y => by
        simp only [TensorProduct.tmul_add, map_add]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        change (ψ.app X).hom ((1 : O₂.obj X) ⊗ₜ[O₁.obj X] (r • x))
            = (algebraMap (O₁.obj X) (O₂.obj X) r) • (ψ.app X).hom ((1 : O₂.obj X) ⊗ₜ[O₁.obj X] x)
        rw [show (1 : O₂.obj X) ⊗ₜ[O₁.obj X] (r • x)
              = (algebraMap (O₁.obj X) (O₂.obj X) r) • ((1 : O₂.obj X) ⊗ₜ[O₁.obj X] x) from by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
              Algebra.smul_def, mul_one]]
        rw [map_smul] }

/-- `unitApp` formula: `x ↦ ψ_X(1 ⊗ x)`. -/
theorem unitApp_apply (θ : O₁ ⟶ O₂) {G : PMod O₁} {F : PMod O₂}
    (ψ : (changeOfRings θ).obj G ⟶ F) (X : Cᵒᵖ) (x : G.obj X) :
    letI := (θ.app X).hom.toAlgebra
    (unitApp θ ψ X).hom x = (ψ.app X).hom ((1 : O₂.obj X) ⊗ₜ[O₁.obj X] x) := by
  let := (θ.app X).hom.toAlgebra
  rw [unitApp, ModuleCat.hom_ofHom]
  rfl

/-- **Sub-lemma (forward map is a presheaf morphism).**

The components `unitApp θ ψ X` assemble into a morphism of presheaves of
`O₁`-modules `G ⟶ (restrictScalars θ).obj F`.

ARGUMENT / STRATEGY: naturality in `X`.  For `f : X ⟶ Y`, on `x : G.obj X`:
* `unitApp θ ψ Y (G.map f x) = ψ_Y(1 ⊗ G(f)(x))`                  [`unitApp_apply`]
      `= ψ_Y(cofMap θ G f (1 ⊗ x))`                               [`cofMap_tmul` with `O₂(f)(1)=1`]
      `= F.map f (ψ_X(1 ⊗ x))`                                    [naturality of `ψ`]
      `= F.map f (unitApp θ ψ X x)`.                              [`unitApp_apply`]
The key step `O₂(f)(1) = 1` is `map_one`; naturality of `ψ` is `ψ.naturality f`
read on the element `1 ⊗ x` (cf. `phi_naturality`).  Then this is exactly the
`restrictScalars` naturality square for `unitApp`. -/
noncomputable def unitHom (θ : O₁ ⟶ O₂) {G : PMod O₁} {F : PMod O₂}
    (ψ : (changeOfRings θ).obj G ⟶ F) :
    G ⟶ (restrictScalars θ).obj F :=
  PresheafOfModules.Hom.mk (fun X => unitApp θ ψ X) (by
    -- naturality square; reduce on elements `x`, use `unitApp_apply`, `cofMap_tmul`
    -- (`map_one`), and naturality of `ψ`.
    intro X Y f
    let := (θ.app X).hom.toAlgebra
    let := (θ.app Y).hom.toAlgebra
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext (fun x => ?_)
    simp only [ModuleCat.hom_comp, Function.comp_apply, LinearMap.coe_comp]
    change (unitApp θ ψ Y).hom ((G.map f).hom x) =
      (F.map f).hom ((unitApp θ ψ X).hom x)
    rw [unitApp_apply, unitApp_apply]
    have hcof : (cofMap θ G f).hom ((1 : O₂.obj X) ⊗ₜ[O₁.obj X] x)
        = (1 : O₂.obj Y) ⊗ₜ[O₁.obj Y] ((G.map f).hom x) := by
      rw [cofMap_tmul, map_one]
    have hψ := phi_naturality ((changeOfRings θ).obj G) F ψ f ((1 : O₂.obj X) ⊗ₜ[O₁.obj X] x)
    rw [← hcof]
    exact hψ)

/-- **The canonical bijection of Tag 03CU.**

For `θ : O₁ ⟶ O₂` a morphism of presheaves of commutative rings, `G` a presheaf of
`O₁`-modules and `F` a presheaf of `O₂`-modules, the bijection
`Hom_{O₂}(O₂ ⊗_{p,O₁} G, F) ≃ Hom_{O₁}(G, F_{O₁})`.

It sends `ψ` to `x ↦ ψ_X(1 ⊗ x)` and its inverse sends `φ` to `a ⊗ x ↦ a • φ_X(x)`;
objectwise these are the two directions of the ring-theoretic extension/restriction of
scalars bijection `ModuleCat.extendRestrictScalarsAdj`. -/
@[stacks 03CU "the canonical bijection of Hom-sets"]
noncomputable def homEquivCore (θ : O₁ ⟶ O₂) (G : PMod O₁) (F : PMod O₂) :
    ((changeOfRings θ).obj G ⟶ F) ≃ (G ⟶ (restrictScalars θ).obj F) where
  toFun ψ := unitHom θ ψ
  invFun φ := counitHom θ φ
  left_inv ψ := by
    -- counitHom (unitHom ψ) = ψ : PresheafOfModules.hom_ext + TensorProduct induction.
    refine PresheafOfModules.hom_ext ?_
    intro X
    let := (θ.app X).hom.toAlgebra
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext (fun t => ?_)
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a x =>
      change (counitApp θ (unitHom θ ψ) X).hom (a ⊗ₜ[O₁.obj X] x) = (ψ.app X).hom (a ⊗ₜ[O₁.obj X] x)
      rw [counitApp_tmul]
      change a • (show F.obj X from ((unitHom θ ψ).app X).hom x) = (ψ.app X).hom (a ⊗ₜ[O₁.obj X] x)
      rw [show ((unitHom θ ψ).app X).hom x = (unitApp θ ψ X).hom x from rfl, unitApp_apply]
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  right_inv φ := by
    -- unitHom (counitHom φ) = φ : PresheafOfModules.hom_ext, `one_smul`.
    refine PresheafOfModules.hom_ext ?_
    intro X
    let := (θ.app X).hom.toAlgebra
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext (fun x => ?_)
    change (unitApp θ (counitHom θ φ) X).hom x = (φ.app X).hom x
    rw [unitApp_apply]
    change (show F.obj X from ((counitHom θ φ).app X).hom ((1 : O₂.obj X) ⊗ₜ[O₁.obj X] x)) = _
    rw [show ((counitHom θ φ).app X).hom ((1 : O₂.obj X) ⊗ₜ[O₁.obj X] x)
          = (counitApp θ φ X).hom ((1 : O₂.obj X) ⊗ₜ[O₁.obj X] x) from rfl, counitApp_tmul,
        one_smul]

/-- **Main statement of Tag 03CU.**

The change-of-rings functor is left adjoint to restriction of scalars,
`changeOfRings θ ⊣ restrictScalars θ`.  It is obtained from the bijection
`homEquivCore`, which it exhibits as natural in both variables.

The unit is `unitHom θ (𝟙 _)`, so it is `x ↦ 1 ⊗ x` on sections; see
`changeOfRingsAdjunction_unit_app_apply`. -/
@[stacks 03CU "the adjunction: restriction and change of rings are adjoint"]
noncomputable def changeOfRingsAdjunction (θ : O₁ ⟶ O₂) :
    changeOfRings θ ⊣ restrictScalars θ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G F => homEquivCore θ G F
      homEquiv_naturality_left_symm := by
        -- naturality in G; reduce via hom_ext + tensor induction to `counitApp_tmul`,
        -- `cofHom_app_tmul`, `comp_app`.
        intro G' G F h g
        change counitHom θ (h ≫ g) = cofHom θ h ≫ counitHom θ g
        refine PresheafOfModules.hom_ext ?_
        intro X
        let := (θ.app X).hom.toAlgebra
        refine ModuleCat.hom_ext ?_
        refine LinearMap.ext (fun t => ?_)
        induction t using TensorProduct.inductionOn with
        | add a b ha hb => simp only [map_add, ha, hb]
        | tmul a x =>
          change (counitApp θ (h ≫ g) X).hom (a ⊗ₜ[O₁.obj X] x) = _
          rw [counitApp_tmul]
          rw [show ((h ≫ g).app X) = h.app X ≫ g.app X from
            PresheafOfModules.comp_app _ _ _]
          rw [show (cofHom θ h ≫ counitHom θ g).app X
              = (cofHom θ h).app X ≫ (counitHom θ g).app X from
            PresheafOfModules.comp_app _ _ _]
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
          change _ = (counitApp θ g X).hom ((cofHomApp θ h X).hom (a ⊗ₜ[O₁.obj X] x))
          rw [cofHomApp_tmul, counitApp_tmul]
      homEquiv_naturality_right := by
        -- naturality in F; reduce via hom_ext to `unitApp_apply`, `comp_app`.
        intro X Y Y' f g
        change unitHom θ (f ≫ g) = unitHom θ f ≫ (restrictScalars θ).map g
        refine PresheafOfModules.hom_ext ?_
        intro W
        let := (θ.app W).hom.toAlgebra
        refine ModuleCat.hom_ext ?_
        refine LinearMap.ext (fun x => ?_)
        change (unitApp θ (f ≫ g) W).hom x = _
        rw [unitApp_apply]
        rw [show ((f ≫ g).app W) = f.app W ≫ g.app W from
          PresheafOfModules.comp_app _ _ _]
        rw [show (unitHom θ f ≫ (restrictScalars θ).map g).app W
            = (unitHom θ f).app W ≫ ((restrictScalars θ).map g).app W from
          PresheafOfModules.comp_app _ _ _]
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        rw [show ((unitHom θ f).app W).hom x = (unitApp θ f W).hom x from rfl,
          unitApp_apply]
        rfl }

/-- The unit of `changeOfRingsAdjunction θ` at `G` is `unitHom θ (𝟙 _)`. -/
theorem changeOfRingsAdjunction_unit_app (θ : O₁ ⟶ O₂) (G : PMod O₁) :
    (changeOfRingsAdjunction θ).unit.app G = unitHom θ (𝟙 ((changeOfRings θ).obj G)) :=
  rfl

/-- The component at `X` of the unit of `changeOfRingsAdjunction θ` at `G` is `unitApp`
applied to the identity. -/
theorem changeOfRingsAdjunction_unit_app_app (θ : O₁ ⟶ O₂) (G : PMod O₁) (X : Cᵒᵖ) :
    ((changeOfRingsAdjunction θ).unit.app G).app X
      = unitApp θ (𝟙 ((changeOfRings θ).obj G)) X :=
  rfl

/-- **The unit of the change-of-rings adjunction on sections: `x ↦ 1 ⊗ x`.**

For `G` a presheaf of `O₁`-modules, `X` an object and `x : G(X)`, the component at `X` of
`(changeOfRingsAdjunction θ).unit.app G` sends `x` to `1 ⊗ x` in
`O₂(X) ⊗_{O₁(X)} G(X)`. -/
@[simp]
theorem changeOfRingsAdjunction_unit_app_apply (θ : O₁ ⟶ O₂) (G : PMod O₁) (X : Cᵒᵖ)
    (x : G.obj X) :
    letI := (θ.app X).hom.toAlgebra
    (((changeOfRingsAdjunction θ).unit.app G).app X).hom x
      = (1 : O₂.obj X) ⊗ₜ[O₁.obj X] x := by
  let := (θ.app X).hom.toAlgebra
  exact unitApp_apply θ (𝟙 ((changeOfRings θ).obj G)) X x

end Stacks.PresheafOfModules.ChangeOfRings
