module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings

/-!
# The mixed tensor product of presheaves of modules

Let `θ : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a category `C`, let `H`
be a presheaf of `O₂`-modules and let `G` be a presheaf of `O₁`-modules.  Reading `H` as a
presheaf of `O₁`-modules along `θ`, the sections `H(X) ⊗_{O₁(X)} G(X)` of the tensor product
over the *smaller* ring are again `O₂(X)`-modules, the action coming from `H(X)`, and they
assemble into a presheaf of `O₂`-modules

`H ⊗_{O₁} G`.

This is the presheaf-of-modules analogue of `TensorProduct.AlgebraTensorModule`, and it is the
object the `O₂`-linear cancellation of a base change compares with `H ⊗_{O₂} (O₂ ⊗_{O₁} G)`.
The cancellation is sectionwise `TensorProduct.AlgebraTensorModule.cancelBaseChange`, which is
`O₂(X)`-linear; what is new here is a presheaf of `O₂`-modules for it to be an isomorphism *of*.

## Main definitions

* `Stacks.MixedTensor.mixedTmulMap`: the sectionwise comparison map
  `H ⊗_{R₁} G →+ H' ⊗_{R₁'} G'` attached to a square of rings and a pair of semilinear maps.
* `Stacks.MixedTensor.mixedTensorObj`: the presheaf of `O₂`-modules `H ⊗_{O₁} G`.
* `Stacks.MixedTensor.mixedTensorRight`: the endofunctor `H ↦ H ⊗_{O₁} G` of presheaves of
  `O₂`-modules, and `mixedTensorNatTrans` its functoriality in `G`.

## Main results

* `Stacks.MixedTensor.mixedBaseChange`: **the `O₂`-linear cancellation of a base change**
  `H ⊗_{O₂} (O₂ ⊗_{O₁} G) ≅ H ⊗_{O₁} G`, as presheaves of `O₂`-modules, and
  `mixedBaseChangeNatIso` the same as an isomorphism of endofunctors.
* `Stacks.MixedTensor.mixedObj_hom_ext`: two morphisms out of `H ⊗_{O₁} G` agreeing on the pure
  tensors agree.

## Implementation notes

`Stacks.FlatChangeOfRings.baseChange` is the same cancellation after restriction of scalars
along `θ`: its sectionwise input is the `O₂(X)`-linear equivalence
`Stacks.FlatChangeOfRings.tensorBaseChange`, but its target `H|_{O₁} ⊗_{O₁} G` is a presheaf of
`O₁`-modules, so the statement restricts that equivalence along `θ_X`.  Nothing of the linearity
is lost sectionwise; it is lost in the packaging, and the presheaf below is the packaging that
keeps it.

The `O₂(X)`-module structure on `H(X) ⊗_{O₁(X)} G(X)` is `TensorProduct.leftModule`, which asks
for `SMulCommClass (O₁(X)) (O₂(X)) (H(X))`; both actions on `H(X)` are through the commutative
ring `O₂(X)`, so that holds, and it is supplied alongside the scalar tower in each `letI` block.
The blocks are repeated verbatim rather than factored out because the instances depend on the
object `X` of the site, so they cannot be local instances; the two data-valued ones must be
written identically everywhere, while `IsScalarTower` and `SMulCommClass` are `Prop`s and so
carry no such obligation.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe v u w

namespace Stacks.MixedTensor

open Stacks Stacks.PresheafOfModules.ChangeOfRings

/-! ### The sectionwise mixed tensor product -/

section Algebraic

variable (R₁ R₂ R₁' R₂' : Type*) [CommRing R₁] [CommRing R₂] [CommRing R₁'] [CommRing R₂']
  [Algebra R₁ R₂] [Algebra R₁' R₂']
  (p : R₁ →+* R₁') (q : R₂ →+* R₂')
  (hsq : q.comp (algebraMap R₁ R₂) = (algebraMap R₁' R₂').comp p)
  (H : Type*) [AddCommGroup H] [Module R₁ H] [Module R₂ H] [IsScalarTower R₁ R₂ H]
    [SMulCommClass R₁ R₂ H]
  (H' : Type*) [AddCommGroup H'] [Module R₁' H'] [Module R₂' H'] [IsScalarTower R₁' R₂' H']
    [SMulCommClass R₁' R₂' H']
  (G : Type*) [AddCommGroup G] [Module R₁ G]
  (G' : Type*) [AddCommGroup G'] [Module R₁' G']
  (ψ : H →+ H') (hψ : ∀ (s : R₂) (x : H), ψ (s • x) = q s • ψ x)
  (φ : G →+ G') (hφ : ∀ (r : R₁) (x : G), φ (r • x) = p r • φ x)

omit [SMulCommClass R₁ R₂ H] [SMulCommClass R₁' R₂' H'] in
include hsq hψ in
/-- A map semilinear over `q : R₂ →+* R₂'` is semilinear over `p : R₁ →+* R₁'` as well, the two
scalar towers being compatible. -/
theorem map_smul_base (r : R₁) (x : H) : ψ (r • x) = p r • ψ x := by
  rw [← IsScalarTower.algebraMap_smul R₂ r x, hψ,
    show q (algebraMap R₁ R₂ r) = algebraMap R₁' R₂' (p r) from RingHom.congr_fun hsq r,
    IsScalarTower.algebraMap_smul]

include hsq hψ hφ in
/-- **The sectionwise comparison map of mixed tensor products.**  A square of rings and a pair
of maps semilinear over its two sides induce `H ⊗_{R₁} G →+ H' ⊗_{R₁'} G'`. -/
noncomputable def mixedTmulMap : (H ⊗[R₁] G) →+ (H' ⊗[R₁'] G') := by
  refine TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun a ↦ AddMonoidHom.mk' (fun x ↦ (ψ a) ⊗ₜ[R₁'] (φ x)) ?_) ?_) ?_
  · intro x y
    simp [TensorProduct.tmul_add]
  · intro a b
    ext x
    simp [TensorProduct.add_tmul]
  · intro r a x
    simp only [AddMonoidHom.mk'_apply]
    rw [map_smul_base R₁ R₂ R₁' R₂' p q hsq H H' ψ hψ, hφ, TensorProduct.smul_tmul]

omit [SMulCommClass R₁ R₂ H] [SMulCommClass R₁' R₂' H'] in
/-- `mixedTmulMap` sends a pure tensor `a ⊗ₜ x` to `ψ a ⊗ₜ φ x`. -/
@[simp]
theorem mixedTmulMap_tmul (a : H) (x : G) :
    mixedTmulMap R₁ R₂ R₁' R₂' p q hsq H H' G G' ψ hψ φ hφ (a ⊗ₜ[R₁] x) =
      ψ a ⊗ₜ[R₁'] φ x := by
  simp only [mixedTmulMap, TensorProduct.liftAddHom_tmul, AddMonoidHom.mk'_apply]

/-- `mixedTmulMap` is semilinear over `q : R₂ →+* R₂'`. -/
theorem mixedTmulMap_smul (s : R₂) (t : H ⊗[R₁] G) :
    mixedTmulMap R₁ R₂ R₁' R₂' p q hsq H H' G G' ψ hψ φ hφ (s • t) =
      q s • mixedTmulMap R₁ R₂ R₁' R₂' p q hsq H H' G G' ψ hψ φ hφ t := by
  induction t with
  | add a b ha hb => simp [ha, hb, smul_add]
  | tmul a x =>
    rw [TensorProduct.smul_tmul', mixedTmulMap_tmul, mixedTmulMap_tmul, hψ,
      TensorProduct.smul_tmul']

end Algebraic

/-! ### The presheaf of modules -/

section Presheaf

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)

/-- The restriction of a section of a presheaf of modules, read in the sections at the
target.  Spelling the restriction maps through this keeps every statement below type-correct
without unfolding `ModuleCat.restrictScalars`. -/
noncomputable def restrictSect {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (M : PresheafOfModules.{w} (ringPresheaf O)) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    M.obj Y :=
  (M.map f).hom x

/-- Restricting along an identity changes nothing. -/
theorem restrictSect_id {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (M : PresheafOfModules.{w} (ringPresheaf O)) {X : Cᵒᵖ} (x : M.obj X) :
    restrictSect M (𝟙 X) x = x := by
  change (M.map (𝟙 X)).hom x = x
  rw [M.map_id, ModuleCat.restrictScalarsId'_inv_app]
  rfl

/-- Restricting along a composite restricts twice. -/
theorem restrictSect_comp {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (M : PresheafOfModules.{w} (ringPresheaf O)) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : M.obj X) :
    restrictSect M (f ≫ g) x = restrictSect M g (restrictSect M f x) :=
  M.map_comp_apply f g x

/-- Restriction is semilinear. -/
theorem restrictSect_smul {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (M : PresheafOfModules.{w} (ringPresheaf O)) {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : O.obj X)
    (x : M.obj X) :
    restrictSect M f (r • x) = (O.map f).hom r • restrictSect M f x :=
  (M.map f).hom.map_smul r x

/-- Restriction commutes with a morphism of presheaves of modules. -/
theorem restrictSect_naturality {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {M N : PresheafOfModules.{w} (ringPresheaf O)} (φ : M ⟶ N) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : M.obj X) :
    (φ.app Y).hom (restrictSect M f x) = restrictSect N f ((φ.app X).hom x) :=
  PresheafOfModules.naturality_apply φ f x

variable (H : PresheafOfModules.{w} (ringPresheaf O₂))
  (G : PresheafOfModules.{w} (ringPresheaf O₁))

/-- **The sections of the mixed tensor product**: `H(X) ⊗_{O₁(X)} G(X)`, an `O₂(X)`-module
through the first factor. -/
noncomputable def mixedObj (X : Cᵒᵖ) : ModuleCat ((ringPresheaf O₂).obj X) :=
  letI : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (G.obj X) := (G.obj X).isModule
  letI : Module (O₂.obj X) (H.obj X) := (H.obj X).isModule
  letI : Module (O₁.obj X) (H.obj X) := Module.compHom _ (θ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : SMulCommClass (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.to_smulCommClass
  ModuleCat.of (O₂.obj X) (H.obj X ⊗[O₁.obj X] G.obj X)

/-- **The pure tensor `a ⊗ x` of the mixed tensor product.**  Every statement about the mixed
tensor product is phrased through this, so that the `O₁(X)`-module structure on `H(X)` — which
is not an instance, being read off `θ` — occurs in one place only. -/
noncomputable def mixedPure (X : Cᵒᵖ) (a : H.obj X) (x : G.obj X) : mixedObj θ H G X :=
  letI : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (G.obj X) := (G.obj X).isModule
  letI : Module (O₂.obj X) (H.obj X) := (H.obj X).isModule
  letI : Module (O₁.obj X) (H.obj X) := Module.compHom _ (θ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : SMulCommClass (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.to_smulCommClass
  a ⊗ₜ[O₁.obj X] x

/-- The restriction map of the mixed tensor product: restrict each factor. -/
noncomputable def mixedMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    mixedObj θ H G X ⟶
      (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).obj (mixedObj θ H G Y) := by
  letI : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (G.obj X) := (G.obj X).isModule
  letI : Module (O₂.obj X) (H.obj X) := (H.obj X).isModule
  letI : Module (O₁.obj X) (H.obj X) := Module.compHom _ (θ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : SMulCommClass (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.to_smulCommClass
  letI : Algebra (O₁.obj Y) (O₂.obj Y) := (θ.app Y).hom.toAlgebra
  letI : Module (O₁.obj Y) (G.obj Y) := (G.obj Y).isModule
  letI : Module (O₂.obj Y) (H.obj Y) := (H.obj Y).isModule
  letI : Module (O₁.obj Y) (H.obj Y) := Module.compHom _ (θ.app Y).hom
  letI : IsScalarTower (O₁.obj Y) (O₂.obj Y) (H.obj Y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : SMulCommClass (O₁.obj Y) (O₂.obj Y) (H.obj Y) :=
    IsScalarTower.to_smulCommClass
  exact ModuleCat.ofHom (R := O₂.obj X) (X := mixedObj θ H G X)
    (Y := (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).obj (mixedObj θ H G Y))
    { toFun := mixedTmulMap (O₁.obj X) (O₂.obj X) (O₁.obj Y) (O₂.obj Y)
        (O₁.map f).hom (O₂.map f).hom (nat_sq θ f) (H.obj X) (H.obj Y) (G.obj X) (G.obj Y)
        (H.map f).hom.toAddMonoidHom (fun s y ↦ restrictSect_smul H f s y)
        (G.map f).hom.toAddMonoidHom (fun r y ↦ restrictSect_smul G f r y)
      map_add' := map_add _
      map_smul' := fun s t ↦ mixedTmulMap_smul (O₁.obj X) (O₂.obj X) (O₁.obj Y) (O₂.obj Y)
        (O₁.map f).hom (O₂.map f).hom (nat_sq θ f) (H.obj X) (H.obj Y) (G.obj X) (G.obj Y)
        (H.map f).hom.toAddMonoidHom (fun s y ↦ restrictSect_smul H f s y)
        (G.map f).hom.toAddMonoidHom (fun r y ↦ restrictSect_smul G f r y) s t }

/-- The restriction map of the mixed tensor product on a pure tensor. -/
theorem mixedMap_mixedPure {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : H.obj X) (x : G.obj X) :
    (mixedMap θ H G f).hom (mixedPure θ H G X a x) =
      mixedPure θ H G Y (restrictSect H f a) (restrictSect G f x) := by
  let : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  let : Module (O₁.obj X) (G.obj X) := (G.obj X).isModule
  let : Module (O₂.obj X) (H.obj X) := (H.obj X).isModule
  let : Module (O₁.obj X) (H.obj X) := Module.compHom _ (θ.app X).hom
  let : IsScalarTower (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : SMulCommClass (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.to_smulCommClass
  let : Algebra (O₁.obj Y) (O₂.obj Y) := (θ.app Y).hom.toAlgebra
  let : Module (O₁.obj Y) (G.obj Y) := (G.obj Y).isModule
  let : Module (O₂.obj Y) (H.obj Y) := (H.obj Y).isModule
  let : Module (O₁.obj Y) (H.obj Y) := Module.compHom _ (θ.app Y).hom
  let : IsScalarTower (O₁.obj Y) (O₂.obj Y) (H.obj Y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : SMulCommClass (O₁.obj Y) (O₂.obj Y) (H.obj Y) :=
    IsScalarTower.to_smulCommClass
  exact mixedTmulMap_tmul (O₁.obj X) (O₂.obj X) (O₁.obj Y) (O₂.obj Y)
    (O₁.map f).hom (O₂.map f).hom (nat_sq θ f) (H.obj X) (H.obj Y) (G.obj X) (G.obj Y)
    (H.map f).hom.toAddMonoidHom (fun s y ↦ restrictSect_smul H f s y)
    (G.map f).hom.toAddMonoidHom (fun r y ↦ restrictSect_smul G f r y) a x

/-- **Two morphisms out of the mixed tensor product agreeing on the pure tensors agree.** -/
theorem mixedObj_hom_ext {X : Cᵒᵖ} {P : ModuleCat ((ringPresheaf O₂).obj X)}
    (u v : mixedObj θ H G X ⟶ P)
    (hpure : ∀ (a : H.obj X) (x : G.obj X),
      u.hom (mixedPure θ H G X a x) = v.hom (mixedPure θ H G X a x)) :
    u = v := by
  let : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  let : Module (O₁.obj X) (G.obj X) := (G.obj X).isModule
  let : Module (O₂.obj X) (H.obj X) := (H.obj X).isModule
  let : Module (O₁.obj X) (H.obj X) := Module.compHom _ (θ.app X).hom
  let : IsScalarTower (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : SMulCommClass (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.to_smulCommClass
  let L : (H.obj X ⊗[O₁.obj X] G.obj X) →+ P := u.hom.toAddMonoidHom
  let R : (H.obj X ⊗[O₁.obj X] G.obj X) →+ P := v.hom.toAddMonoidHom
  have key : ∀ t : H.obj X ⊗[O₁.obj X] G.obj X, L t = R t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add c d hc hd => rw [map_add, map_add, hc, hd]
    | tmul a x => exact hpure a x
  exact ModuleCat.hom_ext (LinearMap.ext key)

/-- The restriction map of `H ⊗_{O₁} G` along an identity is the identity. -/
theorem mixed_map_id (X : Cᵒᵖ) :
    mixedMap θ H G (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((ringPresheaf O₂).map (𝟙 X)).hom (by simp)).inv.app
        (mixedObj θ H G X) := by
  refine mixedObj_hom_ext θ H G _ _ fun a x ↦ ?_
  rw [mixedMap_mixedPure, ModuleCat.restrictScalarsId'_inv_app, restrictSect_id,
    restrictSect_id]
  rfl

/-- The restriction maps of `H ⊗_{O₁} G` are compatible with composition. -/
theorem mixed_map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mixedMap θ H G (f ≫ g) =
      mixedMap θ H G f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map (mixedMap θ H G g) ≫
          (ModuleCat.restrictScalarsComp' ((ringPresheaf O₂).map f).hom
              ((ringPresheaf O₂).map g).hom ((ringPresheaf O₂).map (f ≫ g)).hom
              (by rw [(ringPresheaf O₂).map_comp]; rfl)).inv.app (mixedObj θ H G Z) := by
  refine mixedObj_hom_ext θ H G _ _ fun a x ↦ ?_
  rw [mixedMap_mixedPure]
  change _ = (mixedMap θ H G g).hom ((mixedMap θ H G f).hom (mixedPure θ H G X a x))
  rw [mixedMap_mixedPure, mixedMap_mixedPure, restrictSect_comp H f g a,
    restrictSect_comp G f g x]

/-- **The mixed tensor product `H ⊗_{O₁} G` as a presheaf of `O₂`-modules.** -/
noncomputable def mixedTensorObj : PresheafOfModules.{w} (ringPresheaf O₂) where
  obj X := mixedObj θ H G X
  map f := mixedMap θ H G f
  map_id X := mixed_map_id θ H G X
  map_comp f g := mixed_map_comp θ H G f g

end Presheaf

/-! ### Functoriality in the presheaf of `O₂`-modules -/

section Functoriality

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)
  (G : PresheafOfModules.{w} (ringPresheaf O₁))

/-- The component at `X` of the morphism of mixed tensor products induced by a morphism of
presheaves of `O₂`-modules. -/
noncomputable def mixedHomApp {H H' : PresheafOfModules.{w} (ringPresheaf O₂)} (φ : H ⟶ H')
    (X : Cᵒᵖ) : mixedObj θ H G X ⟶ mixedObj θ H' G X := by
  letI : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (G.obj X) := (G.obj X).isModule
  letI : Module (O₂.obj X) (H.obj X) := (H.obj X).isModule
  letI : Module (O₁.obj X) (H.obj X) := Module.compHom _ (θ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : SMulCommClass (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.to_smulCommClass
  letI : Module (O₂.obj X) (H'.obj X) := (H'.obj X).isModule
  letI : Module (O₁.obj X) (H'.obj X) := Module.compHom _ (θ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (H'.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : SMulCommClass (O₁.obj X) (O₂.obj X) (H'.obj X) :=
    IsScalarTower.to_smulCommClass
  exact ModuleCat.ofHom (R := O₂.obj X) (X := mixedObj θ H G X) (Y := mixedObj θ H' G X)
    { toFun := mixedTmulMap (O₁.obj X) (O₂.obj X) (O₁.obj X) (O₂.obj X)
        (RingHom.id (O₁.obj X)) (RingHom.id (O₂.obj X)) (by ext r; rfl)
        (H.obj X) (H'.obj X) (G.obj X) (G.obj X)
        (φ.app X).hom.toAddMonoidHom (fun s y ↦ (φ.app X).hom.map_smul s y)
        (AddMonoidHom.id (G.obj X)) (fun r y ↦ rfl)
      map_add' := map_add _
      map_smul' := fun s t ↦ mixedTmulMap_smul (O₁.obj X) (O₂.obj X) (O₁.obj X) (O₂.obj X)
        (RingHom.id (O₁.obj X)) (RingHom.id (O₂.obj X)) (by ext r; rfl)
        (H.obj X) (H'.obj X) (G.obj X) (G.obj X)
        (φ.app X).hom.toAddMonoidHom (fun s y ↦ (φ.app X).hom.map_smul s y)
        (AddMonoidHom.id (G.obj X)) (fun r y ↦ rfl) s t }

/-- `mixedHomApp θ G φ X` sends the pure tensor `a ⊗ₜ x` to `φ_X a ⊗ₜ x`. -/
theorem mixedHomApp_mixedPure {H H' : PresheafOfModules.{w} (ringPresheaf O₂)} (φ : H ⟶ H')
    (X : Cᵒᵖ) (a : H.obj X) (x : G.obj X) :
    (mixedHomApp θ G φ X).hom (mixedPure θ H G X a x) =
      mixedPure θ H' G X ((φ.app X).hom a) x := by
  let : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  let : Module (O₁.obj X) (G.obj X) := (G.obj X).isModule
  let : Module (O₂.obj X) (H.obj X) := (H.obj X).isModule
  let : Module (O₁.obj X) (H.obj X) := Module.compHom _ (θ.app X).hom
  let : IsScalarTower (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : SMulCommClass (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.to_smulCommClass
  let : Module (O₂.obj X) (H'.obj X) := (H'.obj X).isModule
  let : Module (O₁.obj X) (H'.obj X) := Module.compHom _ (θ.app X).hom
  let : IsScalarTower (O₁.obj X) (O₂.obj X) (H'.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : SMulCommClass (O₁.obj X) (O₂.obj X) (H'.obj X) :=
    IsScalarTower.to_smulCommClass
  exact mixedTmulMap_tmul (O₁.obj X) (O₂.obj X) (O₁.obj X) (O₂.obj X)
    (RingHom.id (O₁.obj X)) (RingHom.id (O₂.obj X)) (by ext r; rfl)
    (H.obj X) (H'.obj X) (G.obj X) (G.obj X)
    (φ.app X).hom.toAddMonoidHom (fun s y ↦ (φ.app X).hom.map_smul s y)
    (AddMonoidHom.id (G.obj X)) (fun r y ↦ rfl) a x

/-- The morphism of mixed tensor products induced by a morphism of presheaves of
`O₂`-modules. -/
noncomputable def mixedHom {H H' : PresheafOfModules.{w} (ringPresheaf O₂)} (φ : H ⟶ H') :
    mixedTensorObj θ H G ⟶ mixedTensorObj θ H' G :=
  PresheafOfModules.Hom.mk (fun X ↦ mixedHomApp θ G φ X) (by
    intro X Y f
    refine mixedObj_hom_ext θ H G _ _ fun a x ↦ ?_
    change (mixedHomApp θ G φ Y).hom ((mixedMap θ H G f).hom (mixedPure θ H G X a x)) =
      (mixedMap θ H' G f).hom ((mixedHomApp θ G φ X).hom (mixedPure θ H G X a x))
    rw [mixedMap_mixedPure, mixedHomApp_mixedPure, mixedHomApp_mixedPure, mixedMap_mixedPure,
      restrictSect_naturality φ f a])

/-- The morphism of mixed tensor products induced by the identity is the identity. -/
theorem mixedHom_id (H : PresheafOfModules.{w} (ringPresheaf O₂)) :
    mixedHom θ G (𝟙 H) = 𝟙 (mixedTensorObj θ H G) := by
  refine PresheafOfModules.hom_ext fun X ↦ ?_
  change mixedHomApp θ G (𝟙 H) X = 𝟙 (mixedObj θ H G X)
  refine mixedObj_hom_ext θ H G _ _ fun a x ↦ ?_
  rw [mixedHomApp_mixedPure]
  rfl

/-- The morphism of mixed tensor products induced by a composite is the composite. -/
theorem mixedHom_comp {H H' H'' : PresheafOfModules.{w} (ringPresheaf O₂)} (φ : H ⟶ H')
    (φ' : H' ⟶ H'') :
    mixedHom θ G φ ≫ mixedHom θ G φ' = mixedHom θ G (φ ≫ φ') := by
  refine PresheafOfModules.hom_ext fun X ↦ ?_
  change mixedHomApp θ G φ X ≫ mixedHomApp θ G φ' X = mixedHomApp θ G (φ ≫ φ') X
  refine mixedObj_hom_ext θ H G _ _ fun a x ↦ ?_
  change (mixedHomApp θ G φ' X).hom ((mixedHomApp θ G φ X).hom (mixedPure θ H G X a x)) = _
  rw [mixedHomApp_mixedPure, mixedHomApp_mixedPure, mixedHomApp_mixedPure]
  rfl

/-- **Tensoring presheaves of `O₂`-modules on the right by a presheaf of `O₁`-modules.** -/
noncomputable def mixedTensorRight :
    PresheafOfModules.{w} (ringPresheaf O₂) ⥤ PresheafOfModules.{w} (ringPresheaf O₂) where
  obj H := mixedTensorObj θ H G
  map φ := mixedHom θ G φ
  map_id H := mixedHom_id θ G H
  map_comp φ φ' := (mixedHom_comp θ G φ φ').symm

end Functoriality

/-! ### The `O₂`-linear cancellation of a base change -/

section BaseChange

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)
  (G : PresheafOfModules.{w} (ringPresheaf O₁))

/-- The component at `X` of the `O₂`-linear cancellation of a base change: sectionwise it is
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
noncomputable def mixedBaseChangeApp (H : PresheafOfModules.{w} (ringPresheaf O₂)) (X : Cᵒᵖ) :
    (tensorObj H ((changeOfRings θ).obj G)).obj X ≅ mixedObj θ H G X := by
  letI : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (G.obj X) := (G.obj X).isModule
  letI : Module (O₂.obj X) (H.obj X) := (H.obj X).isModule
  letI : Module (O₁.obj X) (H.obj X) := Module.compHom _ (θ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : SMulCommClass (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.to_smulCommClass
  exact LinearEquiv.toModuleIso
    (Stacks.FlatChangeOfRings.tensorBaseChange (R := O₁.obj X) (S := O₂.obj X)
      (G := G.obj X) (H := H.obj X))

/-- **The `O₂`-linear cancellation of a base change**:
`H ⊗_{O₂} (O₂ ⊗_{O₁} G) ≅ H ⊗_{O₁} G` as presheaves of `O₂`-modules. -/
noncomputable def mixedBaseChange (H : PresheafOfModules.{w} (ringPresheaf O₂)) :
    tensorObj H ((changeOfRings θ).obj G) ≅ mixedTensorObj θ H G := by
  refine PresheafOfModules.isoMk (mixedBaseChangeApp θ G H) fun X Y g ↦ ?_
  let : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  let : Module (O₁.obj X) (G.obj X) := (G.obj X).isModule
  let : Module (O₂.obj X) (H.obj X) := (H.obj X).isModule
  let : Module (O₁.obj X) (H.obj X) := Module.compHom _ (θ.app X).hom
  let : IsScalarTower (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : SMulCommClass (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.to_smulCommClass
  let : Algebra (O₁.obj Y) (O₂.obj Y) := (θ.app Y).hom.toAlgebra
  let : Module (O₁.obj Y) (G.obj Y) := (G.obj Y).isModule
  let : Module (O₂.obj Y) (H.obj Y) := (H.obj Y).isModule
  let : Module (O₁.obj Y) (H.obj Y) := Module.compHom _ (θ.app Y).hom
  let : IsScalarTower (O₁.obj Y) (O₂.obj Y) (H.obj Y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : SMulCommClass (O₁.obj Y) (O₂.obj Y) (H.obj Y) :=
    IsScalarTower.to_smulCommClass
  let L : (H.obj X ⊗[O₂.obj X] (O₂.obj X ⊗[O₁.obj X] G.obj X)) →+
      (H.obj Y ⊗[O₁.obj Y] G.obj Y) :=
    (mixedBaseChangeApp θ G H Y).hom.hom.toAddMonoidHom.comp
      ((tensorObj H ((changeOfRings θ).obj G)).map g).hom.toAddMonoidHom
  let R : (H.obj X ⊗[O₂.obj X] (O₂.obj X ⊗[O₁.obj X] G.obj X)) →+
      (H.obj Y ⊗[O₁.obj Y] G.obj Y) :=
    (mixedMap θ H G g).hom.toAddMonoidHom.comp
      (mixedBaseChangeApp θ G H X).hom.hom.toAddMonoidHom
  refine ModuleCat.hom_ext (LinearMap.ext ?_)
  refine Stacks.FlatChangeOfRings.tensorBaseChange_hom_ext L R ?_
  intro a s x
  change Stacks.FlatChangeOfRings.tensorBaseChange
      (restrictSect H g a ⊗ₜ[O₂.obj Y]
        (((O₂.map g).hom s) ⊗ₜ[O₁.obj Y] restrictSect G g x)) =
    (mixedMap θ H G g).hom (mixedPure θ H G X (s • a) x)
  rw [Stacks.FlatChangeOfRings.tensorBaseChange_tmul, mixedMap_mixedPure,
    restrictSect_smul H g s a]
  rfl

/-- The `O₂`-linear cancellation of a base change is natural in the presheaf of
`O₂`-modules. -/
theorem mixedBaseChange_naturality {H H' : PresheafOfModules.{w} (ringPresheaf O₂)}
    (φ : H ⟶ H') :
    (tensorRight ((changeOfRings θ).obj G)).map φ ≫ (mixedBaseChange θ G H').hom =
      (mixedBaseChange θ G H).hom ≫ (mixedTensorRight θ G).map φ := by
  refine PresheafOfModules.hom_ext fun X ↦ ?_
  let : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  let : Module (O₁.obj X) (G.obj X) := (G.obj X).isModule
  let : Module (O₂.obj X) (H.obj X) := (H.obj X).isModule
  let : Module (O₁.obj X) (H.obj X) := Module.compHom _ (θ.app X).hom
  let : IsScalarTower (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : SMulCommClass (O₁.obj X) (O₂.obj X) (H.obj X) :=
    IsScalarTower.to_smulCommClass
  let : Module (O₂.obj X) (H'.obj X) := (H'.obj X).isModule
  let : Module (O₁.obj X) (H'.obj X) := Module.compHom _ (θ.app X).hom
  let : IsScalarTower (O₁.obj X) (O₂.obj X) (H'.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : SMulCommClass (O₁.obj X) (O₂.obj X) (H'.obj X) :=
    IsScalarTower.to_smulCommClass
  let L : (H.obj X ⊗[O₂.obj X] (O₂.obj X ⊗[O₁.obj X] G.obj X)) →+
      (H'.obj X ⊗[O₁.obj X] G.obj X) :=
    (((tensorRight ((changeOfRings θ).obj G)).map φ ≫
      (mixedBaseChange θ G H').hom).app X).hom.toAddMonoidHom
  let R : (H.obj X ⊗[O₂.obj X] (O₂.obj X ⊗[O₁.obj X] G.obj X)) →+
      (H'.obj X ⊗[O₁.obj X] G.obj X) :=
    (((mixedBaseChange θ G H).hom ≫ (mixedTensorRight θ G).map φ).app X).hom.toAddMonoidHom
  refine ModuleCat.hom_ext (LinearMap.ext ?_)
  refine Stacks.FlatChangeOfRings.tensorBaseChange_hom_ext L R ?_
  intro a s x
  change Stacks.FlatChangeOfRings.tensorBaseChange
      ((φ.app X).hom a ⊗ₜ[O₂.obj X] (s ⊗ₜ[O₁.obj X] x)) =
    (mixedHomApp θ G φ X).hom (mixedPure θ H G X (s • a) x)
  rw [Stacks.FlatChangeOfRings.tensorBaseChange_tmul, mixedHomApp_mixedPure,
    (φ.app X).hom.map_smul s a]
  rfl

/-- **The `O₂`-linear cancellation of a base change, as an isomorphism of endofunctors** of
presheaves of `O₂`-modules. -/
noncomputable def mixedBaseChangeNatIso :
    tensorRight ((changeOfRings θ).obj G) ≅ mixedTensorRight θ G :=
  NatIso.ofComponents (fun H ↦ mixedBaseChange θ G H) (mixedBaseChange_naturality θ G)

end BaseChange

end Stacks.MixedTensor

end
