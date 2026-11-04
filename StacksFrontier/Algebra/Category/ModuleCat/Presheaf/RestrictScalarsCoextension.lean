module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Restriction of scalars and coextension of scalars for presheaves of modules

Let `C` be a category and let `φ : O ⟶ O'` be a morphism of presheaves of (not necessarily
commutative) rings on `C`. Restriction of scalars along `φ` sends a presheaf of
`O'`-modules `G` to the presheaf of `O`-modules `G_O` on which `O(U)` acts through
`φ_U : O(U) ⟶ O'(U)`; it is Mathlib's `PresheafOfModules.restrictScalars φ`.

This file constructs the right adjoint, coextension of scalars. For a presheaf of
`O`-modules `F` the internal hom `SheafHom_O(O', F)` is the presheaf whose sections over `U`
are the `O|_U`-linear maps `O'|_U ⟶ F|_U` on the localization `C/U = Over U`, with
restriction maps induced by `Over.map`, and with the `O'(U)`-action given by precomposition
with right multiplication: `(a' • ψ)(b') = ψ(b' * a')`. This uses the `(O, O')`-bimodule
structure of `O'`, exactly as in the ring-theoretic case
(`ModuleCat.restrictCoextendScalarsAdj`).

## Main definitions

* `coextObj φ F`: the internal hom `SheafHom_O(O', F)`, a presheaf of `O'`-modules.
* `coextendScalars φ`: the coextension-of-scalars functor
  `PresheafOfModules O ⥤ PresheafOfModules O'`.
* `homEquivForward`, `homEquivInverse`, `homEquiv`: the Hom-bijection
  `Hom_O(G_O, F) ≃ Hom_{O'}(G, SheafHom_O(O', F))`, with the explicit formulas
  `α ↦ (g ↦ (a' ↦ α(a' • g)))` and `β ↦ (g ↦ β(g)(1))`.

## Main results

* `restrictScalars_coextendScalars_adjunction`: restriction of scalars along `φ` is left
  adjoint to coextension of scalars ([Stacks, Tag 0932], for presheaves).

## Implementation notes

Sections of the internal hom are morphisms in `PresheafOfModules ((Over.forget U).op ⋙ O)`,
an abelian group because that category is preadditive. The restriction map along
`g : V ⟶ U` is the pullback along `Over.map g` conjugated by the coherence isomorphism
`overRestrictIso`, which identifies the two ways of restricting a module from `C` to `C/V`.
Forgetting the module structures identifies a section with a section of Mathlib's
`CategoryTheory.presheafHom`, which gives the coherence-free formula
`coextRestrFun_app_apply` for the value of a restricted section.

"Module" means left module throughout, matching the Mathlib dependency.

## References

* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
* [Stacks Project, Tag 08YP](https://stacks.math.columbia.edu/tag/08YP) (the ring case)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.PresheafOfModules.CoextendScalars

universe u

variable {C : Type u} [Category.{u} C] {O O' : Cᵒᵖ ⥤ RingCat.{u}}

/-! ## Restriction of scalars -/

/-- Restriction of scalars along `φ : O ⟶ O'`: an `O'`-module `G` viewed as an `O`-module
`G_O`, with `O(U)` acting through `φ_U` (`PresheafOfModules.restrictScalars`). -/
noncomputable abbrev restrictionOfScalars (φ : O ⟶ O') :
    PresheafOfModules.{u} O' ⥤ PresheafOfModules.{u} O :=
  PresheafOfModules.restrictScalars.{u} φ

/-! ## The section groups of the internal hom -/

/-- `O'`, viewed as a presheaf of `O`-modules via `φ : O ⟶ O'` (the `(O, O')`-bimodule
`O'`, with left `O`-action through `φ`). -/
noncomputable abbrev O'asOModule (φ : O ⟶ O') : PresheafOfModules.{u} O :=
  (PresheafOfModules.restrictScalars φ).obj (PresheafOfModules.unit O')

/-- Restriction of a presheaf of `O`-modules to the localized category `C/U = Over U`,
i.e. its pullback along `Over.forget U : Over U ⥤ C`. This is `F|_U`. -/
noncomputable abbrev restrictToOver (U : C) (F : PresheafOfModules.{u} O) :
    PresheafOfModules ((Over.forget U).op ⋙ O) :=
  (PresheafOfModules.pushforward₀ (Over.forget U) O).obj F

/-- The section group of the internal hom at `X : Cᵒᵖ`:
`SheafHom_O(O', F)(X) = Hom_{O|_X}(O'|_X, F|_X)`, the morphisms of presheaves of
`(O|_X)`-modules from the restriction of `O'` (as an `O`-module) to the restriction of `F`.
As a morphism group in a preadditive category it is an abelian group. -/
noncomputable abbrev coextSec (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ) : Type _ :=
  restrictToOver X.unop (O'asOModule φ) ⟶ restrictToOver X.unop F

/-! ### The right-multiplication endomorphism (giving the `O'`-action). -/

/-- The component, at `V : (Over U)ᵒᵖ`, of the right-multiplication endomorphism of `O'|_U`:
right multiplication on `O'(V.left)` by the restriction of `a' ∈ O'(U)`. -/
noncomputable def rightMulComp (φ : O ⟶ O') (U : C) (a' : (O'.obj (Opposite.op U) : Type _))
    (V : (Over U)ᵒᵖ) :
    (restrictToOver U (O'asOModule φ)).presheaf.obj V ⟶
      (restrictToOver U (O'asOModule φ)).presheaf.obj V :=
  AddCommGrpCat.ofHom
    (show (O'.obj (Opposite.op V.unop.left) : Type _) →+
        (O'.obj (Opposite.op V.unop.left) : Type _)
      from AddMonoidHom.mulRight ((O'.map (V.unop.hom.op)) a'))

/-- `rightMulComp φ U a' V` is right multiplication by the restriction of `a'` to `V.left`. -/
theorem rightMulComp_apply (φ : O ⟶ O') (U : C) (a' : (O'.obj (Opposite.op U) : Type _))
    (V : (Over U)ᵒᵖ) (b : (O'.obj (Opposite.op V.unop.left) : Type _)) :
    (rightMulComp φ U a' V) b = b * (O'.map V.unop.hom.op) a' :=
  rfl

/-- Naturality of the right-multiplication components, on sections. -/
theorem rightMulComp_naturality_apply (φ : O ⟶ O') (U : C)
    (a' : (O'.obj (Opposite.op U) : Type _)) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y)
    (b : (O'.obj (Opposite.op X.unop.left) : Type _)) :
    (rightMulComp φ U a' Y) ((O'.map f.unop.left.op) b)
      = (O'.map f.unop.left.op) ((rightMulComp φ U a' X) b) := by
  rw [rightMulComp_apply, rightMulComp_apply, map_mul]
  congr 1
  have hslice : (Opposite.unop X).hom.op ≫ f.unop.left.op = (Opposite.unop Y).hom.op := by
    rw [← op_comp]; congr 1; exact (Over.w f.unop)
  rw [← hslice, O'.map_comp]
  rfl

/-- Naturality of the right-multiplication components. -/
theorem rightMulComp_naturality (φ : O ⟶ O') (U : C)
    (a' : (O'.obj (Opposite.op U) : Type _)) :
    ∀ ⦃X Y : (Over U)ᵒᵖ⦄ (f : X ⟶ Y),
      (restrictToOver U (O'asOModule φ)).presheaf.map f ≫ rightMulComp φ U a' Y =
        rightMulComp φ U a' X ≫ (restrictToOver U (O'asOModule φ)).presheaf.map f := by
  intro X Y f
  ext b
  exact rightMulComp_naturality_apply φ U a' f b

/-- The right-multiplication endomorphism, as a morphism of presheaves of abelian groups. -/
noncomputable def rightMulPresheaf (φ : O ⟶ O') (U : C)
    (a' : (O'.obj (Opposite.op U) : Type _)) :
    (restrictToOver U (O'asOModule φ)).presheaf ⟶
      (restrictToOver U (O'asOModule φ)).presheaf where
  app V := rightMulComp φ U a' V
  naturality _ _ f := rightMulComp_naturality φ U a' f

/-- The right-multiplication components are `O|_U`-linear. -/
theorem rightMulComp_smul (φ : O ⟶ O') (U : C) (a' : (O'.obj (Opposite.op U) : Type _))
    (V : (Over U)ᵒᵖ) (r : (((Over.forget U).op ⋙ O).obj V : Type _))
    (m : ((restrictToOver U (O'asOModule φ)).obj V : Type _)) :
    (rightMulComp φ U a' V) (r • m) = r • (rightMulComp φ U a' V) m :=
  mul_assoc (G := O'.obj (Opposite.op (Opposite.unop V).left)) _ _ _

/-- The right-multiplication endomorphism `b' ↦ b' * a'` of `O'|_U` as a morphism of
presheaves of `O|_U`-modules. -/
noncomputable def rightMulEndo (φ : O ⟶ O') (U : C)
    (a' : (O'.obj (Opposite.op U) : Type _)) :
    restrictToOver U (O'asOModule φ) ⟶ restrictToOver U (O'asOModule φ) :=
  PresheafOfModules.homMk (rightMulPresheaf φ U a') (rightMulComp_smul φ U a')

/-- Right multiplication by `1` is the identity. -/
theorem rightMulComp_one (φ : O ⟶ O') (U : C) (V : (Over U)ᵒᵖ)
    (b : (O'.obj (Opposite.op V.unop.left) : Type _)) :
    (rightMulComp φ U (1 : (O'.obj (Opposite.op U) : Type _)) V) b = b := by
  rw [rightMulComp_apply, map_one, mul_one]

/-- Right multiplication by a product is the composite of the right multiplications, in the
opposite order. -/
theorem rightMulComp_mul (φ : O ⟶ O') (U : C) (a b : (O'.obj (Opposite.op U) : Type _))
    (V : (Over U)ᵒᵖ) (z : (O'.obj (Opposite.op V.unop.left) : Type _)) :
    (rightMulComp φ U (a * b) V) z
      = (rightMulComp φ U b V) ((rightMulComp φ U a V) z) := by
  simp only [rightMulComp_apply, map_mul]
  exact (mul_assoc (G := (O'.obj (Opposite.op V.unop.left) : Type _)) _ _ _).symm

/-- Right multiplication is additive in the multiplier. -/
theorem rightMulComp_add (φ : O ⟶ O') (U : C) (a b : (O'.obj (Opposite.op U) : Type _))
    (V : (Over U)ᵒᵖ) (z : (O'.obj (Opposite.op V.unop.left) : Type _)) :
    (rightMulComp φ U (a + b) V) z
      = (rightMulComp φ U a V) z + (rightMulComp φ U b V) z := by
  simp only [rightMulComp_apply, map_add, mul_add]
  rfl

/-- Right multiplication by `0` is zero. -/
theorem rightMulComp_zero (φ : O ⟶ O') (U : C) (V : (Over U)ᵒᵖ)
    (z : (O'.obj (Opposite.op V.unop.left) : Type _)) :
    (rightMulComp φ U (0 : (O'.obj (Opposite.op U) : Type _)) V) z = 0 := by
  simp only [rightMulComp_apply, map_zero, mul_zero]
  rfl

/-! ### The `O'(X)`-module structure on the section group. -/

/-- The `O'(X)`-action on a section `ψ`: `a' • ψ` is `ψ` precomposed with right
multiplication by `a'`, i.e. `b' ↦ ψ(b' * a')`. -/
noncomputable instance coextSMul (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ) :
    SMul (O'.obj X) (coextSec φ F X) where
  smul a' ψ := rightMulEndo φ X.unop a' ≫ ψ

/-- The unit of `O'(X)` acts trivially on the section group. -/
theorem coext_one (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ)
    (ψ : coextSec φ F X) : (1 : O'.obj X) • ψ = ψ := by
  show rightMulEndo φ X.unop 1 ≫ ψ = ψ
  rw [show rightMulEndo φ X.unop (1 : O'.obj X) = 𝟙 _ from ?_, Category.id_comp]
  ext V b
  exact rightMulComp_one φ X.unop V b

/-- Scaling by a product is scaling by each factor in turn. -/
theorem coext_mul (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ)
    (a b : O'.obj X) (ψ : coextSec φ F X) : (a * b) • ψ = a • b • ψ := by
  show rightMulEndo φ X.unop (a * b) ≫ ψ = rightMulEndo φ X.unop a ≫ rightMulEndo φ X.unop b ≫ ψ
  rw [show rightMulEndo φ X.unop (a * b) = rightMulEndo φ X.unop a ≫ rightMulEndo φ X.unop b from
      ?_,
    Category.assoc]
  ext V z
  exact rightMulComp_mul φ X.unop a b V z

/-- Scaling the zero section gives zero. -/
theorem coext_smul_zero (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ)
    (a : O'.obj X) : a • (0 : coextSec φ F X) = 0 := by
  show rightMulEndo φ X.unop a ≫ 0 = 0
  exact Limits.comp_zero

/-- The action of `O'(X)` on the section group distributes over addition of sections. -/
theorem coext_smul_add (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ)
    (a : O'.obj X) (x y : coextSec φ F X) : a • (x + y) = a • x + a • y := by
  show rightMulEndo φ X.unop a ≫ (x + y) =
    rightMulEndo φ X.unop a ≫ x + rightMulEndo φ X.unop a ≫ y
  rw [Preadditive.comp_add]

/-- The action of `O'(X)` on the section group distributes over addition of scalars. -/
theorem coext_add_smul (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ)
    (a b : O'.obj X) (x : coextSec φ F X) : (a + b) • x = a • x + b • x := by
  show rightMulEndo φ X.unop (a + b) ≫ x =
    rightMulEndo φ X.unop a ≫ x + rightMulEndo φ X.unop b ≫ x
  rw [show rightMulEndo φ X.unop (a + b) = rightMulEndo φ X.unop a + rightMulEndo φ X.unop b from
      ?_,
    Preadditive.add_comp]
  ext V z
  exact rightMulComp_add φ X.unop a b V z

/-- The zero of `O'(X)` acts as zero on the section group. -/
theorem coext_zero_smul (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ)
    (x : coextSec φ F X) : (0 : O'.obj X) • x = 0 := by
  show rightMulEndo φ X.unop 0 ≫ x = 0
  rw [show rightMulEndo φ X.unop (0 : O'.obj X) = 0 from ?_, Limits.zero_comp]
  ext V z
  exact rightMulComp_zero φ X.unop V z

/-- The `O'(X)`-module structure on `SheafHom_O(O', F)(X)`, with the right-multiplication
action. -/
noncomputable instance coextModule (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ) :
    Module (O'.obj X) (coextSec φ F X) where
  one_smul := coext_one φ F X
  mul_smul := coext_mul φ F X
  smul_zero := coext_smul_zero φ F X
  smul_add := coext_smul_add φ F X
  add_smul := coext_add_smul φ F X
  zero_smul := coext_zero_smul φ F X

/-- The value `SheafHom_O(O', F)(X) = Hom_{O|_X}(O'|_X, F|_X)`, as an `O'(X)`-module. -/
noncomputable def coextObjModule (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ) :
    ModuleCat (O'.obj X) :=
  ModuleCat.of (O'.obj X) (coextSec φ F X)

/-! ### Restriction maps of the internal hom. -/

/-- The base-ring coherence isomorphism for the pullback along `Over.map g`. -/
noncomputable def baseRingIso (V U : C) (g : V ⟶ U) :
    (Over.map g).op ⋙ ((Over.forget U).op ⋙ O) ≅ (Over.forget V).op ⋙ O :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (NatIso.op (Over.mapForget g)) O

private theorem baseRingIso_inv_eq_id (V U : C) (g : V ⟶ U) :
    (baseRingIso (O := O) V U g).inv = 𝟙 ((Over.forget V).op ⋙ O) := by
  ext X; simp [baseRingIso, Over.mapForget]

/-- The restriction functor on presheaves of modules over slices, along `g : V ⟶ U`. -/
noncomputable def overRestrictFunctor (V U : C) (g : V ⟶ U) :
    PresheafOfModules ((Over.forget U).op ⋙ O) ⥤ PresheafOfModules ((Over.forget V).op ⋙ O) :=
  PresheafOfModules.pushforward (F := Over.map g) (baseRingIso V U g).inv

/-- Restricting `F|_U` to `C/V` via `Over.map g` recovers `F|_V`. -/
theorem overRestrict_objEq (V U : C) (g : V ⟶ U) (F : PresheafOfModules.{u} O) :
    (overRestrictFunctor V U g).obj (restrictToOver U F) = restrictToOver V F := by
  unfold overRestrictFunctor
  rw [PresheafOfModules.pushforward]
  simp only [Functor.comp_obj]
  rw [baseRingIso_inv_eq_id]
  rfl

/-- Coherence isomorphism: restricting `F|_U` to `C/V` via `Over.map g` recovers `F|_V`. -/
noncomputable def overRestrictIso (V U : C) (g : V ⟶ U) (F : PresheafOfModules.{u} O) :
    (overRestrictFunctor V U g).obj (restrictToOver U F) ≅ restrictToOver V F :=
  eqToIso (overRestrict_objEq V U g F)

/-- The underlying function of the restriction map of `SheafHom_O(O', F)` along `f : X ⟶ Y`
in `Cᵒᵖ`: restrict a section over `C/X.unop` to a section over `C/Y.unop`. -/
noncomputable def coextRestrFun (φ : O ⟶ O') (F : PresheafOfModules.{u} O)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    coextSec φ F X → coextSec φ F Y :=
  fun ψ =>
    (overRestrictIso Y.unop X.unop f.unop (O'asOModule φ)).inv ≫
      (overRestrictFunctor Y.unop X.unop f.unop).map ψ ≫
        (overRestrictIso Y.unop X.unop f.unop F).hom

/-- The restriction map of `SheafHom_O(O', F)` is additive. -/
theorem coextRestrFun_add (φ : O ⟶ O') (F : PresheafOfModules.{u} O) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x y : coextSec φ F X) :
    coextRestrFun φ F f (x + y) = coextRestrFun φ F f x + coextRestrFun φ F f y := by
  simp only [coextRestrFun]
  have h : (overRestrictFunctor Y.unop X.unop f.unop).map (x + y) =
      (overRestrictFunctor Y.unop X.unop f.unop).map x +
        (overRestrictFunctor Y.unop X.unop f.unop).map y := by
    ext V z
    rfl
  rw [h, Preadditive.add_comp, Preadditive.comp_add]

private theorem pom_hom_heq {D : Type u} [Category.{u} D] {R : Dᵒᵖ ⥤ RingCat}
    {M₁ M₂ N₁ N₂ : PresheafOfModules R} (e₁ : M₁ = N₁) (e₂ : M₂ = N₂)
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    (h : ∀ V, HEq (f.app V) (g.app V)) : HEq f g := by
  subst e₁ e₂
  exact heq_of_eq (PresheafOfModules.Hom.ext (funext fun V => eq_of_heq (h V)))

/-- Heterogeneous congruence for function application, allowing the codomains to differ by an
equality `β₁ = β₂`. -/
theorem hfun_congr_heq {α₁ α₂ β₁ β₂ : Type u} (hβ : β₁ = β₂) {f : α₁ → β₁}
    {g : α₂ → β₂} {a : α₁} {b : α₂} (hf : HEq f g) (ha : HEq a b) : HEq (f a) (g b) := by
  subst hβ
  obtain rfl : α₁ = α₂ := type_eq_of_heq ha
  cases hf; cases ha; rfl

/-- Two morphisms of modules between equal source and target modules are heterogeneously
equal as soon as their underlying functions agree pointwise up to transport. -/
theorem mc_hom_heq {R : Type u} [Ring R] {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (e₁ : M₁ = N₁) (e₂ : M₂ = N₂) (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    (h : ∀ z, HEq ((ModuleCat.Hom.hom f) z) ((ModuleCat.Hom.hom g) (e₁ ▸ z))) : HEq f g := by
  subst e₁ e₂
  exact heq_of_eq (ModuleCat.hom_ext (LinearMap.ext fun z => eq_of_heq (h z)))

/-- Morphisms of presheaves of modules between equal source and target are heterogeneously equal
as soon as their underlying functions are heterogeneously equal sectionwise. -/
private theorem pom_hom_heq_of_fun_heq {D : Type u} [Category.{u} D] {R : Dᵒᵖ ⥤ RingCat.{u}}
    {M₁ M₂ N₁ N₂ : PresheafOfModules.{u} R} (e₁ : M₁ = N₁) (e₂ : M₂ = N₂)
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    (h : ∀ V, HEq ⇑(ModuleCat.Hom.hom (f.app V)) ⇑(ModuleCat.Hom.hom (g.app V))) : HEq f g :=
  pom_hom_heq e₁ e₂ f g fun V =>
    mc_hom_heq (congrArg (fun M => M.obj V) e₁) (congrArg (fun M => M.obj V) e₂) _ _ fun z =>
      hfun_congr_heq (congrArg (fun (M : ModuleCat (R.obj _)) => (M : Type u))
        (congrArg (fun M => M.obj V) e₂)) (h V) (eqRec_heq _ z).symm

/-- The structure map of `(Over.map g).op.obj V`, as a morphism in `Cᵒᵖ`. -/
private theorem over_map_hom_op {X Y : Cᵒᵖ} (f : X ⟶ Y) (V : (Over Y.unop)ᵒᵖ) :
    ((Over.map f.unop).op.obj V).unop.hom.op = f ≫ V.unop.hom.op := by
  show (V.unop.hom ≫ f.unop).op = f ≫ V.unop.hom.op
  rw [op_comp]
  rfl

/-- Restricting a morphism `f` of sections over `C/U` along `g : V ⟶ U` and conjugating by the
coherence isomorphisms gives `h` as soon as the underlying functions agree up to `HEq`. -/
private theorem overRestrict_conj_eq {V U : C} (g : V ⟶ U) {M N : PresheafOfModules.{u} O}
    (f : restrictToOver U M ⟶ restrictToOver U N) (h : restrictToOver V M ⟶ restrictToOver V N)
    (H : ∀ W : (Over V)ᵒᵖ, HEq ⇑(ModuleCat.Hom.hom (f.app ((Over.map g).op.obj W)))
      ⇑(ModuleCat.Hom.hom (h.app W))) :
    (overRestrictIso V U g M).inv ≫ (overRestrictFunctor V U g).map f ≫
      (overRestrictIso V U g N).hom = h := by
  simp only [overRestrictIso, eqToIso.inv, eqToIso.hom]
  rw [eqToHom_comp_iff, comp_eqToHom_iff, Category.assoc, conj_eqToHom_iff_heq]
  · refine pom_hom_heq_of_fun_heq (overRestrict_objEq V U g M) (overRestrict_objEq V U g N)
      _ _ fun W => ?_
    unfold overRestrictFunctor
    simp only [PresheafOfModules.pushforward]
    rw [baseRingIso_inv_eq_id]
    simp only [Functor.comp_obj, Functor.comp_map, PresheafOfModules.restrictScalars_map_app]
    exact (HEq.refl _).trans (H W)
  · exact overRestrict_objEq V U g N

/-- The restriction map of `SheafHom_O(O', F)` along `f` is semilinear along `O'.map f`. -/
theorem coextRestrFun_smul (φ : O ⟶ O') (F : PresheafOfModules.{u} O) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (O'.obj X : Type _)) (x : coextSec φ F X) :
    coextRestrFun φ F f (m • x) = (RingCat.Hom.hom (O'.map f)) m • coextRestrFun φ F f x := by
  simp only [coextRestrFun]
  show (overRestrictIso Y.unop X.unop f.unop (O'asOModule φ)).inv ≫
      (overRestrictFunctor Y.unop X.unop f.unop).map (rightMulEndo φ X.unop m ≫ x) ≫
        (overRestrictIso Y.unop X.unop f.unop F).hom =
    rightMulEndo φ Y.unop ((RingCat.Hom.hom (O'.map f)) m) ≫
      ((overRestrictIso Y.unop X.unop f.unop (O'asOModule φ)).inv ≫
        (overRestrictFunctor Y.unop X.unop f.unop).map x ≫
          (overRestrictIso Y.unop X.unop f.unop F).hom)
  rw [Functor.map_comp]
  have key := overRestrict_conj_eq (M := O'asOModule φ) f.unop (rightMulEndo φ X.unop m)
      (rightMulEndo φ Y.unop ((RingCat.Hom.hom (O'.map f)) m)) fun V => by
    have hmul : (ConcreteCategory.hom (O'.map (Opposite.unop ((Over.map f.unop).op.obj
        V)).hom.op)) m
        = (ConcreteCategory.hom (O'.map (Opposite.unop V).hom.op))
          ((RingCat.Hom.hom (O'.map f)) m) := by
      rw [over_map_hom_op, O'.map_comp]
      rfl
    apply heq_of_eq
    simp only [rightMulEndo, PresheafOfModules.homMk_app, rightMulPresheaf, rightMulComp,
      AddCommGrpCat.ofHom, ModuleCat.hom_ofHom]
    exact congrArg (fun (a : (O'.obj (Opposite.op (Opposite.unop V).left) : Type _)) =>
      ⇑(AddMonoidHom.mulRight a)) hmul
  rw [← key]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The restriction map of `SheafHom_O(O', F)` along `f`, as a semilinear map (semilinear
along `O'.map f`). -/
noncomputable def coextRestrSemilinear (φ : O ⟶ O') (F : PresheafOfModules.{u} O)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (coextObjModule φ F X) →ₛₗ[(RingCat.Hom.hom (O'.map f))] (coextObjModule φ F Y) where
  toFun := coextRestrFun φ F f
  map_add' := coextRestrFun_add φ F f
  map_smul' := coextRestrFun_smul φ F f

/-- The restriction map of `SheafHom_O(O', F)` along `f`, as a morphism into the
restriction-of-scalars of the target module. -/
noncomputable def coextMap (φ : O ⟶ O') (F : PresheafOfModules.{u} O) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    coextObjModule φ F X ⟶
      (ModuleCat.restrictScalars (RingCat.Hom.hom (O'.map f))).obj (coextObjModule φ F Y) :=
  ModuleCat.semilinearMapAddEquiv (RingCat.Hom.hom (O'.map f)) _ _ (coextRestrSemilinear φ F f)

/-- Restricting a section of `SheafHom_O(O', F)` along the identity leaves it unchanged. -/
theorem coextRestrFun_id (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ)
    (ψ : coextSec φ F X) : coextRestrFun φ F (𝟙 X) ψ = ψ := by
  exact overRestrict_conj_eq (𝟙 X).unop ψ ψ fun V =>
    congr_arg_heq (fun (W : (Over X.unop)ᵒᵖ) => ⇑(ModuleCat.Hom.hom (ψ.app W)))
      (congrArg Opposite.op (by cases V.unop; simp [Over.map, Comma.mapRight]))

/-- The restriction map of `SheafHom_O(O', F)` along an identity is the identity, up to the
`restrictScalars` coherence isomorphism for `O'.map (𝟙 X) = 𝟙`. -/
theorem coextMap_id (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ) :
    coextMap φ F (𝟙 X) =
      (ModuleCat.restrictScalarsId' (RingCat.Hom.hom (O'.map (𝟙 X)))
        (by rw [O'.map_id]; rfl)).inv.app (coextObjModule φ F X) := by
  ext ψ
  simp only [coextMap, coextRestrSemilinear, ModuleCat.semilinearMapAddEquiv]
  show coextRestrFun φ F (𝟙 X) ψ = ψ
  exact coextRestrFun_id φ F X ψ

/-- The restriction maps of `SheafHom_O(O', F)` are compatible with composition, up to the
`restrictScalars` coherence isomorphism for `O'.map (f ≫ g) = O'.map f ≫ O'.map g`. -/
theorem coextMap_comp (φ : O ⟶ O') (F : PresheafOfModules.{u} O) {X Y Z : Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    coextMap φ F (f ≫ g) =
      coextMap φ F f ≫
        (ModuleCat.restrictScalars (RingCat.Hom.hom (O'.map f))).map (coextMap φ F g) ≫
          (ModuleCat.restrictScalarsComp' (RingCat.Hom.hom (O'.map f)) (RingCat.Hom.hom (O'.map g))
            (RingCat.Hom.hom (O'.map (f ≫ g))) (by rw [O'.map_comp]; rfl)).inv.app
              (coextObjModule φ F Z) := by
  ext ψ
  simp only [coextMap, coextRestrSemilinear, ModuleCat.semilinearMapAddEquiv]
  show coextRestrFun φ F (f ≫ g) ψ = coextRestrFun φ F g (coextRestrFun φ F f ψ)
  simp only [coextRestrFun]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [overRestrictIso, eqToIso.inv, eqToIso.hom, eqToHom_map]
  rw [eqToHom_comp_iff, comp_eqToHom_iff]
  simp only [Category.assoc, eqToHom_trans]
  rw [← Category.assoc (eqToHom _) (eqToHom _), eqToHom_trans,
    ← Category.assoc (eqToHom _) (eqToHom _), eqToHom_trans]
  rw [conj_eqToHom_iff_heq]
  · have hobj : ∀ (M : PresheafOfModules.{u} O),
        (overRestrictFunctor Z.unop X.unop (f ≫ g).unop).obj (restrictToOver X.unop M) =
          (overRestrictFunctor Z.unop Y.unop g.unop).obj
            ((overRestrictFunctor Y.unop X.unop f.unop).obj (restrictToOver X.unop M)) := by
      intro M
      rw [overRestrict_objEq Y.unop X.unop f.unop M, overRestrict_objEq Z.unop Y.unop g.unop M,
        overRestrict_objEq Z.unop X.unop (f ≫ g).unop M]
    refine pom_hom_heq_of_fun_heq (hobj (O'asOModule φ)) (hobj F) _ _ (fun V => ?_)
    unfold overRestrictFunctor
    simp only [PresheafOfModules.pushforward]
    simp only [Functor.comp_obj, Functor.comp_map, PresheafOfModules.restrictScalars_map_app]
    refine HEq.trans (b := ⇑(ModuleCat.Hom.hom (ψ.app ((Over.map (f ≫ g).unop).op.obj V)))) ?_ ?_
    · rfl
    · refine congr_arg_heq (fun (W : (Over X.unop)ᵒᵖ) => ⇑(ModuleCat.Hom.hom (ψ.app W))) ?_
      refine congrArg Opposite.op (congrArg Over.mk ?_)
      show (Opposite.unop V).hom ≫ (f ≫ g).unop = ((Opposite.unop V).hom ≫ g.unop) ≫ f.unop
      rw [unop_comp, Category.assoc]
  · rw [overRestrict_objEq Y.unop X.unop f.unop F, overRestrict_objEq Z.unop Y.unop g.unop F,
      overRestrict_objEq Z.unop X.unop (f ≫ g).unop F]

/-! ### Restriction of sections, at the level of underlying abelian presheaves.

Forgetting the module structures identifies a section of `SheafHom_O(O', F)` over `X` with a
section of Mathlib's `CategoryTheory.presheafHom` of the underlying abelian presheaves, in a
way compatible with the restriction maps. This gives a formula for the value of a restricted
section which avoids the coherence isomorphisms. -/

/-- The underlying morphism of abelian presheaves on the slice category of a section of
`SheafHom_O(O', F)` over `X`, as a section of `CategoryTheory.presheafHom`. -/
noncomputable def coextSecPresheafHom (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ)
    (ψ : coextSec φ F X) : (presheafHom (O'asOModule φ).presheaf F.presheaf).obj X :=
  (PresheafOfModules.toPresheaf ((Over.forget X.unop).op ⋙ O)).map ψ

/-- Restricting a section of `SheafHom_O(O', F)` along `f` is, on underlying abelian
presheaves, the restriction map of `CategoryTheory.presheafHom`. -/
theorem coextSecPresheafHom_restr (φ : O ⟶ O') (F : PresheafOfModules.{u} O) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (ψ : coextSec φ F X) :
    (presheafHom (O'asOModule φ).presheaf F.presheaf).map f (coextSecPresheafHom φ F X ψ)
      = coextSecPresheafHom φ F Y (coextRestrFun φ F f ψ) := by
  have e₁ : (PresheafOfModules.toPresheaf ((Over.forget Y.unop).op ⋙ O)).map
      (overRestrictIso Y.unop X.unop f.unop (O'asOModule φ)).inv
      = 𝟙 ((PresheafOfModules.toPresheaf ((Over.forget Y.unop).op ⋙ O)).obj
          (restrictToOver Y.unop (O'asOModule φ))) := by
    rw [overRestrictIso, eqToIso.inv, eqToHom_map]
    rfl
  have e₂ : (PresheafOfModules.toPresheaf ((Over.forget Y.unop).op ⋙ O)).map
      (overRestrictIso Y.unop X.unop f.unop F).hom
      = 𝟙 ((PresheafOfModules.toPresheaf ((Over.forget Y.unop).op ⋙ O)).obj
          (restrictToOver Y.unop F)) := by
    rw [overRestrictIso, eqToIso.hom, eqToHom_map]
    rfl
  have hR : coextRestrFun φ F f ψ =
      (overRestrictIso Y.unop X.unop f.unop (O'asOModule φ)).inv ≫
        (overRestrictFunctor Y.unop X.unop f.unop).map ψ ≫
          (overRestrictIso Y.unop X.unop f.unop F).hom := rfl
  have key : (PresheafOfModules.toPresheaf ((Over.forget Y.unop).op ⋙ O)).map
        (coextRestrFun φ F f ψ)
      = (PresheafOfModules.toPresheaf ((Over.forget Y.unop).op ⋙ O)).map
          ((overRestrictFunctor Y.unop X.unop f.unop).map ψ) := by
    rw [hR, Functor.map_comp, Functor.map_comp, e₁, e₂]
    exact (Category.id_comp _).trans (Category.comp_id _)
  exact key.symm

/-- **The value of a restricted section.** If `p ≫ f.unop = q`, then the restriction along
`f` of a section `ψ` of `SheafHom_O(O', F)` over `X`, evaluated at the slice object `p`, is
`ψ` evaluated at the slice object `q`. -/
theorem coextRestrFun_app_apply (φ : O ⟶ O') (F : PresheafOfModules.{u} O) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (ψ : coextSec φ F X) {Z : C} (p : Z ⟶ Y.unop) (q : Z ⟶ X.unop)
    (w : p ≫ f.unop = q) (a' : (O'.obj (Opposite.op Z) : Type _)) :
    ((coextRestrFun φ F f ψ).app (Opposite.op (Over.mk p))) a'
      = (ψ.app (Opposite.op (Over.mk q))) a' := by
  have h2 := presheafHom_map_app (F := (O'asOModule φ).presheaf) (G := F.presheaf) p f.unop q w
    (coextSecPresheafHom φ F X ψ)
  rw [coextSecPresheafHom_restr φ F f.unop.op ψ] at h2
  exact congrArg (fun m => (ConcreteCategory.hom m) a') h2

/-! ## The internal-hom object and the coextension-of-scalars functor. -/

/-- The internal-hom object `SheafHom_O(O', F)`, a presheaf of `O'`-modules. Its value at `X`
is `coextObjModule φ F X = Hom_{O|_X}(O'|_X, F|_X)` (with the right-multiplication
`O'`-action), and its restriction maps are `coextMap`. -/
noncomputable def coextObj (φ : O ⟶ O') (F : PresheafOfModules.{u} O) : PresheafOfModules.{u} O' :=
  PresheafOfModules.mk (obj := coextObjModule φ F) (map := fun f => coextMap φ F f)
    (map_id := coextMap_id φ F) (map_comp := fun f g => coextMap_comp φ F f g)

/-! ### Action of the coextension functor on morphisms. -/

/-- The sectionwise action of the coextension functor on a morphism `η : F ⟶ G` of
`O`-modules: postcompose a section `ψ : O'|_X ⟶ F|_X` with the restriction `η|_X` of `η`. -/
noncomputable def coextFunMapFun (φ : O ⟶ O') {F G : PresheafOfModules.{u} O} (η : F ⟶ G)
    (X : Cᵒᵖ) : coextSec φ F X → coextSec φ G X :=
  fun ψ => ψ ≫ (PresheafOfModules.pushforward₀ (Over.forget X.unop) O).map η

/-- Postcomposition with `η` is additive. -/
theorem coextFunMapFun_add (φ : O ⟶ O') {F G : PresheafOfModules.{u} O} (η : F ⟶ G) (X : Cᵒᵖ)
    (x y : coextSec φ F X) :
    coextFunMapFun φ η X (x + y) = coextFunMapFun φ η X x + coextFunMapFun φ η X y := by
  simp only [coextFunMapFun, Preadditive.add_comp]

/-- Postcomposition with `η` is `O'(X)`-linear. -/
theorem coextFunMapFun_smul (φ : O ⟶ O') {F G : PresheafOfModules.{u} O} (η : F ⟶ G) (X : Cᵒᵖ)
    (a : (O'.obj X : Type _)) (x : coextSec φ F X) :
    coextFunMapFun φ η X (a • x) = a • coextFunMapFun φ η X x := by
  show (rightMulEndo φ X.unop a ≫ x) ≫ _ = rightMulEndo φ X.unop a ≫ (x ≫ _)
  rw [Category.assoc]

/-- The sectionwise action of the functor on `η`, as an `O'(X)`-linear map. -/
noncomputable def coextFunMapLinear (φ : O ⟶ O') {F G : PresheafOfModules.{u} O} (η : F ⟶ G)
    (X : Cᵒᵖ) : (coextObjModule φ F X) →ₗ[O'.obj X] (coextObjModule φ G X) where
  toFun := coextFunMapFun φ η X
  map_add' := coextFunMapFun_add φ η X
  map_smul' a x := coextFunMapFun_smul φ η X a x

/-- Postcomposition with `η` commutes with the restriction maps of the internal hom. -/
theorem coextFunMapFun_restr (φ : O ⟶ O') {F G : PresheafOfModules.{u} O} (η : F ⟶ G)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (ψ : coextSec φ F X) :
    coextFunMapFun φ η Y (coextRestrFun φ F f ψ)
      = coextRestrFun φ G f (coextFunMapFun φ η X ψ) := by
  simp only [coextFunMapFun, coextRestrFun, Functor.map_comp, Category.assoc]
  rw [← overRestrict_conj_eq f.unop ((PresheafOfModules.pushforward₀ (Over.forget X.unop) O).map η)
    ((PresheafOfModules.pushforward₀ (Over.forget Y.unop) O).map η)
    fun V => congr_arg_heq (fun (W : Cᵒᵖ) => ⇑(ModuleCat.Hom.hom (η.app W))) rfl,
    Iso.hom_inv_id_assoc]

/-- Naturality of the functorial action of `coextendScalars` with respect to the restriction
maps of the internal hom. -/
theorem coextFunMap_naturality (φ : O ⟶ O') {F G : PresheafOfModules.{u} O} (η : F ⟶ G)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (coextObj φ F).map f ≫
        (ModuleCat.restrictScalars (RingCat.Hom.hom (O'.map f))).map
          (ModuleCat.ofHom (coextFunMapLinear φ η Y)) =
      ModuleCat.ofHom (coextFunMapLinear φ η X) ≫ (coextObj φ G).map f := by
  ext ψ
  show coextFunMapFun φ η Y (coextRestrFun φ F f ψ)
    = coextRestrFun φ G f (coextFunMapFun φ η X ψ)
  exact coextFunMapFun_restr φ η f ψ

/-- The action of the coextension functor on a morphism `η : F ⟶ G`. -/
noncomputable def coextFunMap (φ : O ⟶ O') {F G : PresheafOfModules.{u} O} (η : F ⟶ G) :
    coextObj φ F ⟶ coextObj φ G :=
  PresheafOfModules.Hom.mk (fun X => ModuleCat.ofHom (coextFunMapLinear φ η X))
    (fun f => coextFunMap_naturality φ η f)

/-- `coextFunMap` preserves identities. -/
theorem coextFunMap_id (φ : O ⟶ O') (F : PresheafOfModules.{u} O) :
    coextFunMap φ (𝟙 F) = 𝟙 (coextObj φ F) := by
  rfl

/-- `coextFunMap` preserves composition. -/
theorem coextFunMap_comp (φ : O ⟶ O') {F G H : PresheafOfModules.{u} O} (η : F ⟶ G) (θ : G ⟶ H) :
    coextFunMap φ (η ≫ θ) = coextFunMap φ η ≫ coextFunMap φ θ := by
  rfl

/-- The coextension-of-scalars functor
`φ_*^coext : Mod(O) ⥤ Mod(O')`, `F ↦ SheafHom_O(O', F)`, the internal hom
`SheafHom_O(O', -)`. -/
noncomputable def coextendScalars (φ : O ⟶ O') :
    PresheafOfModules.{u} O ⥤ PresheafOfModules.{u} O' where
  obj F := coextObj φ F
  map η := coextFunMap φ η
  map_id F := coextFunMap_id φ F
  map_comp η θ := coextFunMap_comp φ η θ

/-! ## The Hom-bijection

The forward map sends `α : G_O ⟶ F` to the `O'`-linear map `g ↦ (a' ↦ α(a' • g))`; the
inverse sends `β : G ⟶ SheafHom_O(O', F)` to `g ↦ β(g)(1)`. -/

/-! ### The forward map `α ↦ (g ↦ (a' ↦ α(a' • g)))`. -/

/-- The additive-group component, at `V : (Over X.unop)ᵒᵖ`, of the section `α'_X(g)`:
sends `a' ∈ O'(V.left)` to `α(a' • g|_{V.left})` in `F(V.left)`. This is the explicit formula
`α'_U(g)(a') = α_U(a' • g)`. -/
noncomputable def fwdSecApp (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F)
    (X : Cᵒᵖ) (g : (G.obj X : Type _)) (V : (Over X.unop)ᵒᵖ) :
    (restrictToOver X.unop (O'asOModule φ)).presheaf.obj V ⟶
      (restrictToOver X.unop F).presheaf.obj V :=
  AddCommGrpCat.ofHom
    (show (O'.obj (Opposite.op V.unop.left) : Type _) →+ (F.obj (Opposite.op V.unop.left) : Type _)
      from
      { toFun := fun a' => α.app (Opposite.op V.unop.left) (a' • (G.map (V.unop.hom.op) g))
        map_zero' := by
          rw [zero_smul]
          exact map_zero _
        map_add' := fun x y => by
          rw [add_smul]
          exact map_add _ _ _ })

/-- The explicit formula `α'_X(g)(a') = α(a' • g)` for the forward map. -/
theorem fwdSecApp_apply (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F)
    (X : Cᵒᵖ) (g : (G.obj X : Type _)) (V : (Over X.unop)ᵒᵖ)
    (a' : (O'.obj (Opposite.op V.unop.left) : Type _)) :
    (fwdSecApp φ G F α X g V) a'
      = α.app (Opposite.op V.unop.left) (a' • (G.map (V.unop.hom.op) g)) :=
  rfl

/-- Naturality of the forward section `α'_X(g)`, sectionwise: restricting the argument along
`f` and applying the section at `B` is applying the section at `A` and restricting. -/
theorem fwdSecApp_naturality_apply (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F)
    (X : Cᵒᵖ) (g : (G.obj X : Type _)) {A B : (Over X.unop)ᵒᵖ} (f : A ⟶ B)
    (a' : (O'.obj (Opposite.op A.unop.left) : Type _)) :
    (fwdSecApp φ G F α X g B) ((O'.map f.unop.left.op) a')
      = (F.map f.unop.left.op) ((fwdSecApp φ G F α X g A) a') := by
  show (α.app (Opposite.op (Opposite.unop B).left)).hom
        (((O'.map f.unop.left.op).hom a') • (G.map (Opposite.unop B).hom.op) g)
      = (F.map f.unop.left.op).hom
        ((α.app (Opposite.op (Opposite.unop A).left)).hom
          (a' • (G.map (Opposite.unop A).hom.op) g))
  have key : (F.map f.unop.left.op).hom
        ((α.app (Opposite.op (Opposite.unop A).left)).hom
          (a' • (G.map (Opposite.unop A).hom.op) g))
      = (α.app (Opposite.op (Opposite.unop B).left)).hom
          ((G.map f.unop.left.op).hom (a' • (G.map (Opposite.unop A).hom.op) g)) :=
    (PresheafOfModules.naturality_apply α f.unop.left.op
      (a' • (G.map (Opposite.unop A).hom.op) g)).symm
  have hG : (G.map (Opposite.unop B).hom.op) g
      = (G.map f.unop.left.op).hom ((G.map (Opposite.unop A).hom.op) g) := by
    have hslice : (Opposite.unop A).hom.op ≫ f.unop.left.op = (Opposite.unop B).hom.op := by
      rw [← op_comp]; congr 1; exact (Over.w f.unop)
    rw [← PresheafOfModules.map_comp_apply, hslice]
  have hsm := PresheafOfModules.map_smul G f.unop.left.op a'
    ((G.map (Opposite.unop A).hom.op) g)
  exact (congrArg (ConcreteCategory.hom (α.app (Opposite.op (Opposite.unop B).left)))
    ((hsm.trans (congrArg
      (fun y : (G.obj (Opposite.op (Opposite.unop B).left) : Type _) =>
        ((O'.map f.unop.left.op) a') • y) hG.symm)).symm)).trans key.symm

/-- Naturality of the forward section `α'_X(g)` as a morphism of presheaves of abelian
groups on the slice category. -/
theorem fwdSec_naturality (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F)
    (X : Cᵒᵖ) (g : (G.obj X : Type _)) :
    ∀ ⦃A B : (Over X.unop)ᵒᵖ⦄ (f : A ⟶ B),
      (restrictToOver X.unop (O'asOModule φ)).presheaf.map f ≫ fwdSecApp φ G F α X g B =
        fwdSecApp φ G F α X g A ≫ (restrictToOver X.unop F).presheaf.map f := by
  intro A B f
  ext a'
  exact fwdSecApp_naturality_apply φ G F α X g f a'

/-- The underlying presheaf morphism of `α'_X(g)`. -/
noncomputable def fwdSecPresheaf (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F)
    (X : Cᵒᵖ) (g : (G.obj X : Type _)) :
    (restrictToOver X.unop (O'asOModule φ)).presheaf ⟶ (restrictToOver X.unop F).presheaf where
  app V := fwdSecApp φ G F α X g V
  naturality _ _ f := fwdSec_naturality φ G F α X g f

/-- The components of the forward section `α'_X(g)` are `O|_X`-linear. -/
theorem fwdSec_smul (φ : O ⟶ O') (G : PresheafOfModules.{u} O') (F : PresheafOfModules.{u} O)
    (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F) (X : Cᵒᵖ) (g : (G.obj X : Type _))
    (V : (Over X.unop)ᵒᵖ) (r : (((Over.forget X.unop).op ⋙ O).obj V : Type _))
    (m : ((restrictToOver X.unop (O'asOModule φ)).obj V : Type _)) :
    (fwdSecApp φ G F α X g V) (r • m) = r • (fwdSecApp φ G F α X g V) m := by
  show (α.app (Opposite.op V.unop.left)).hom
        ((show (O'.obj (Opposite.op V.unop.left) : Type _) from r • m) •
          (G.map V.unop.hom.op) g)
      = r • (α.app (Opposite.op V.unop.left)).hom
        ((show (O'.obj (Opposite.op V.unop.left) : Type _) from m) • (G.map V.unop.hom.op) g)
  rw [show (show (O'.obj (Opposite.op V.unop.left) : Type _) from r • m) •
          (G.map V.unop.hom.op) g
        = (RingCat.Hom.hom (φ.app (Opposite.op V.unop.left)) r) •
            ((show (O'.obj (Opposite.op V.unop.left) : Type _) from m) •
              (G.map V.unop.hom.op) g)
        from by rw [← mul_smul]; rfl]
  exact (α.app (Opposite.op V.unop.left)).hom.map_smul r _

/-- The section value `α'_X(g) : O'|_X ⟶ F|_X` of the forward map, as a morphism of
presheaves of `O|_X`-modules, given explicitly by `a' ↦ α(a' • g)`. -/
noncomputable def fwdSec (φ : O ⟶ O') (G : PresheafOfModules.{u} O') (F : PresheafOfModules.{u} O)
    (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F) (X : Cᵒᵖ) (g : (G.obj X : Type _)) :
    coextSec φ F X :=
  PresheafOfModules.homMk (fwdSecPresheaf φ G F α X g) (fwdSec_smul φ G F α X g)

/-- The forward section is additive in `g`, sectionwise. -/
theorem fwdSecApp_add (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F)
    (X : Cᵒᵖ) (g h : (G.obj X : Type _)) (V : (Over X.unop)ᵒᵖ)
    (a' : (O'.obj (Opposite.op V.unop.left) : Type _)) :
    (fwdSecApp φ G F α X (g + h) V) a'
      = (fwdSecApp φ G F α X g V) a' + (fwdSecApp φ G F α X h V) a' := by
  simp only [fwdSecApp_apply, map_add, smul_add]
  exact map_add _ _ _

/-- The forward map is additive. -/
theorem fwdLinear_add (φ : O ⟶ O') (G : PresheafOfModules.{u} O') (F : PresheafOfModules.{u} O)
    (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F) (X : Cᵒᵖ) (g h : (G.obj X : Type _)) :
    fwdSec φ G F α X (g + h) = fwdSec φ G F α X g + fwdSec φ G F α X h := by
  ext V a'
  exact fwdSecApp_add φ G F α X g h V a'

/-- The forward section is `O'`-semilinear in `g`: scaling `g` by `a` precomposes the section
with right multiplication by `a`. -/
theorem fwdSecApp_smul (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F)
    (X : Cᵒᵖ) (a : (O'.obj X : Type _)) (g : (G.obj X : Type _)) (V : (Over X.unop)ᵒᵖ)
    (a' : (O'.obj (Opposite.op V.unop.left) : Type _)) :
    (fwdSecApp φ G F α X (a • g) V) a'
      = (fwdSecApp φ G F α X g V) ((rightMulComp φ X.unop a V) a') := by
  simp only [fwdSecApp_apply, rightMulComp_apply, PresheafOfModules.map_smul]
  exact congrArg (ConcreteCategory.hom (α.app (Opposite.op V.unop.left)))
    (mul_smul a' ((O'.map V.unop.hom.op) a) ((G.map V.unop.hom.op) g)).symm

/-- The forward map is `O'`-linear. -/
theorem fwdLinear_smul (φ : O ⟶ O') (G : PresheafOfModules.{u} O') (F : PresheafOfModules.{u} O)
    (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F) (X : Cᵒᵖ) (a : (O'.obj X : Type _))
    (g : (G.obj X : Type _)) :
    fwdSec φ G F α X (a • g) = a • fwdSec φ G F α X g := by
  show fwdSec φ G F α X (a • g) = rightMulEndo φ X.unop a ≫ fwdSec φ G F α X g
  ext V a'
  exact fwdSecApp_smul φ G F α X a g V a'

/-- The forward map at section `X`, as an `O'(X)`-linear map `G(X) → SheafHom_O(O', F)(X)`. -/
noncomputable def fwdAppLinear (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F)
    (X : Cᵒᵖ) : (G.obj X) →ₗ[O'.obj X] (coextObjModule φ F X) where
  toFun g := fwdSec φ G F α X g
  map_add' := fwdLinear_add φ G F α X
  map_smul' a g := fwdLinear_smul φ G F α X a g

/-- The forward section is compatible with restricting the section variable along `f`:
`α'_X(g)` restricted to the slice over `Y.unop` is `α'_Y(g|_Y)`, sectionwise. -/
theorem fwdSecApp_restr (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : (G.obj X : Type _)) (V : (Over Y.unop)ᵒᵖ)
    (a' : (O'.obj (Opposite.op V.unop.left) : Type _)) :
    (fwdSecApp φ G F α X g ((Over.map f.unop).op.obj V)) a'
      = (fwdSecApp φ G F α Y ((G.map f) g) V) a' := by
  have hhom : (G.map ((Over.map f.unop).op.obj V).unop.hom.op) g
      = (G.map V.unop.hom.op) ((ConcreteCategory.hom (G.map f)) g) := by
    rw [over_map_hom_op, PresheafOfModules.map_comp_apply]
  exact congrArg (ConcreteCategory.hom (α.app (Opposite.op V.unop.left)))
    (congrArg (fun y : (G.obj (Opposite.op V.unop.left) : Type _) => a' • y) hhom)

/-- The forward map `g ↦ α'_X(g)` commutes with the restriction maps of `G` and of
`SheafHom_O(O', F)`. -/
theorem fwd_naturality (φ : O ⟶ O') (G : PresheafOfModules.{u} O') (F : PresheafOfModules.{u} O)
    (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    G.map f ≫ (ModuleCat.restrictScalars (RingCat.Hom.hom (O'.map f))).map
        (ModuleCat.ofHom (fwdAppLinear φ G F α Y)) =
      ModuleCat.ofHom (fwdAppLinear φ G F α X) ≫ (coextObj φ F).map f := by
  ext g
  show fwdSec φ G F α Y ((ConcreteCategory.hom (G.map f)) g)
      = coextRestrFun φ F f (fwdSec φ G F α X g)
  exact (overRestrict_conj_eq (M := O'asOModule φ) f.unop _ _ fun V =>
    heq_of_eq (funext fun a' => fwdSecApp_restr φ G F α f g V a')).symm

/-- **The forward map of the Hom-bijection.** Given an `O`-linear
`α : G_O ⟶ F`, this is the `O'`-linear `α' : G ⟶ SheafHom_O(O', F)` with the explicit formula
`α'_U(g)(a') = α_U(a' • g)`. -/
noncomputable def homEquivForward (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O)
    (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F) : G ⟶ coextObj φ F :=
  PresheafOfModules.Hom.mk (fun X => ModuleCat.ofHom (fwdAppLinear φ G F α X))
    (fun f => fwd_naturality φ G F α f)

/-! ### The inverse map `β ↦ (g ↦ β(g)(1))`. -/

/-- The section value `β'_X(g) = β_X(g)(1) ∈ F(X)` of the inverse map: evaluate the section
`β_X(g) : O'|_X ⟶ F|_X` at the terminal slice object `(𝟙 X)` on the unit `1 ∈ O'(X)`. This is
the explicit formula `β'_U(g) = β_U(g)(1)`. -/
noncomputable def invSecVal (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ)
    (ψ : coextSec φ F X) : (F.obj X : Type _) :=
  ψ.app (Opposite.op (Over.mk (𝟙 X.unop))) (1 : (O'.obj (Opposite.op X.unop) : Type _))

/-- Evaluating `a' • ψ` at the terminal slice object on the unit gives the value of `ψ` at
`a'`. -/
theorem invSecVal_smul (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ)
    (a' : (O'.obj X : Type _)) (ψ : coextSec φ F X) :
    invSecVal φ F X (a' • ψ) = (ψ.app (Opposite.op (Over.mk (𝟙 X.unop)))) a' := by
  show ((rightMulEndo φ X.unop a' ≫ ψ).app (Opposite.op (Over.mk (𝟙 X.unop))))
      (1 : (O'.obj (Opposite.op X.unop) : Type _))
    = (ψ.app (Opposite.op (Over.mk (𝟙 X.unop)))) a'
  rw [PresheafOfModules.comp_app]
  have hval : ((rightMulEndo φ X.unop a').app (Opposite.op (Over.mk (𝟙 X.unop))))
      (1 : (O'.obj (Opposite.op X.unop) : Type _)) = a' := by
    show (rightMulComp φ X.unop a' (Opposite.op (Over.mk (𝟙 X.unop))))
        (1 : (O'.obj (Opposite.op X.unop) : Type _)) = a'
    rw [rightMulComp_apply]
    show (1 : (O'.obj (Opposite.op X.unop) : Type _)) * (O'.map ((𝟙 X.unop).op)).hom a' = a'
    rw [op_id, O'.map_id, one_mul]
    rfl
  exact (ModuleCat.comp_apply _ _ _).trans
    (congrArg (ConcreteCategory.hom (ψ.app (Opposite.op (Over.mk (𝟙 X.unop))))) hval)

/-- The value at the terminal slice object of a section of the internal hom is `O`-linear
through `φ`: evaluating at `φ r` is scaling the value at the unit by `r`. -/
theorem invSecVal_smul_left (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (X : Cᵒᵖ)
    (r : (O.obj X : Type _)) (ψ : coextSec φ F X) :
    (ψ.app (Opposite.op (Over.mk (𝟙 X.unop)))) (RingCat.Hom.hom (φ.app X) r)
      = r • invSecVal φ F X ψ := by
  have hsm := (ψ.app (Opposite.op (Over.mk (𝟙 X.unop)))).hom.map_smul r
    (1 : (O'.obj (Opposite.op X.unop) : Type _))
  refine (congrArg (ConcreteCategory.hom (ψ.app (Opposite.op (Over.mk (𝟙 X.unop))))) ?_).trans hsm
  show RingCat.Hom.hom (φ.app X) r
      = (RingCat.Hom.hom (φ.app X) r) * (1 : (O'.obj (Opposite.op X.unop) : Type _))
  rw [mul_one]

/-- The inverse map sends `0` to `0`. -/
theorem invSec_zero (φ : O ⟶ O') (G : PresheafOfModules.{u} O') (F : PresheafOfModules.{u} O)
    (β : G ⟶ coextObj φ F) (X : Cᵒᵖ) :
    invSecVal φ F X ((β.app X) 0) = 0 := by
  simp only [invSecVal, map_zero]
  rfl

/-- The inverse map is additive. -/
theorem invSec_add (φ : O ⟶ O') (G : PresheafOfModules.{u} O') (F : PresheafOfModules.{u} O)
    (β : G ⟶ coextObj φ F) (X : Cᵒᵖ) (g h : (G.obj X : Type _)) :
    invSecVal φ F X ((β.app X) (g + h)) =
      invSecVal φ F X ((β.app X) g) + invSecVal φ F X ((β.app X) h) := by
  rw [map_add]
  rfl

/-- The underlying additive-group component, at `X`, of the inverse morphism `β'`. -/
noncomputable def invSecPresheafApp (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (β : G ⟶ coextObj φ F) (X : Cᵒᵖ) :
    G.presheaf.obj X ⟶ F.presheaf.obj X :=
  AddCommGrpCat.ofHom
    (show (G.obj X : Type _) →+ (F.obj X : Type _) from
      { toFun := fun g => invSecVal φ F X ((β.app X) g)
        map_zero' := invSec_zero φ G F β X
        map_add' := invSec_add φ G F β X })

/-- The components of the inverse map `β'` commute with the restriction maps of `G` and `F`. -/
theorem invSec_naturality (φ : O ⟶ O') (G : PresheafOfModules.{u} O') (F : PresheafOfModules.{u} O)
    (β : G ⟶ coextObj φ F) :
    ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y),
      G.presheaf.map f ≫ invSecPresheafApp φ G F β Y =
        invSecPresheafApp φ G F β X ≫ F.presheaf.map f := by
  intro X Y f
  ext g
  show invSecVal φ F Y ((β.app Y) ((ConcreteCategory.hom (G.map f)) g))
      = (ConcreteCategory.hom (F.map f)) (invSecVal φ F X ((β.app X) g))
  set ψ : coextSec φ F X := (β.app X) g with hψ
  have hii : (β.app Y) ((ConcreteCategory.hom (G.map f)) g)
      = coextRestrFun φ F f ψ := by
    have hel := DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (PresheafOfModules.Hom.naturality β f)) g
    simp only [ModuleCat.hom_comp] at hel
    exact hel
  rw [hii]
  refine (coextRestrFun_app_apply φ F f ψ (𝟙 Y.unop) f.unop (Category.id_comp f.unop)
    (1 : (O'.obj (Opposite.op Y.unop) : Type _))).trans ?_
  have hel := PresheafOfModules.naturality_apply ψ
    ((Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 X.unop)).op)
    (1 : (O'.obj (Opposite.op X.unop) : Type _))
  have hone : (ConcreteCategory.hom ((restrictToOver X.unop (O'asOModule φ)).map
        ((Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 X.unop)).op)))
        (1 : (O'.obj (Opposite.op X.unop) : Type _))
      = (1 : (O'.obj (Opposite.op Y.unop) : Type _)) :=
    map_one (RingCat.Hom.hom (O'.map f.unop.op))
  exact (congrArg (ConcreteCategory.hom (ψ.app (Opposite.op (Over.mk f.unop)))) hone).symm.trans hel

/-- The underlying presheaf morphism of the inverse map `β'`. -/
noncomputable def invSecPresheaf (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (β : G ⟶ coextObj φ F) :
    G.presheaf ⟶ F.presheaf where
  app X := invSecPresheafApp φ G F β X
  naturality _ _ f := invSec_naturality φ G F β f

/-- `O`-linearity (through `φ`) of the inverse morphism `β'`: it is `O(X)`-linear for the
restriction-of-scalars module structure on `G`. -/
theorem invSec_smul (φ : O ⟶ O') (G : PresheafOfModules.{u} O') (F : PresheafOfModules.{u} O)
    (β : G ⟶ coextObj φ F) (X : Cᵒᵖ) (r : (O.obj X : Type _)) (g : (G.obj X : Type _)) :
    (invSecPresheafApp φ G F β X) ((RingCat.Hom.hom (φ.app X) r) • g) =
      r • (invSecPresheafApp φ G F β X) g := by
  show invSecVal φ F X ((β.app X) ((RingCat.Hom.hom (φ.app X) r) • g))
      = r • invSecVal φ F X ((β.app X) g)
  have h1 : invSecVal φ F X ((β.app X) ((RingCat.Hom.hom (φ.app X) r) • g))
      = (((β.app X) g).app (Opposite.op (Over.mk (𝟙 X.unop))))
          (RingCat.Hom.hom (φ.app X) r) := by
    rw [(β.app X).hom.map_smul]
    exact invSecVal_smul φ F X (RingCat.Hom.hom (φ.app X) r) ((β.app X) g)
  rw [h1]
  exact invSecVal_smul_left φ F X r ((β.app X) g)

/-- **The inverse map of the Hom-bijection.** Given an `O'`-linear
`β : G ⟶ SheafHom_O(O', F)`, this is the `O`-linear `β' : G_O ⟶ F` with the explicit formula
`β'_U(g) = β_U(g)(1)`. -/
noncomputable def homEquivInverse (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O)
    (β : G ⟶ coextObj φ F) : (PresheafOfModules.restrictScalars φ).obj G ⟶ F :=
  PresheafOfModules.homMk (invSecPresheaf φ G F β) (invSec_smul φ G F β)

/-! ### Mutual inverseness and naturality of the bijection. -/

/-- The value of the forward section at the terminal slice object on the unit recovers `α`:
`α'_X(g)(1) = α_X(g)`. -/
theorem fwdSecApp_one (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F)
    (X : Cᵒᵖ) (g : (G.obj X : Type _)) :
    (fwdSecApp φ G F α X g (Opposite.op (Over.mk (𝟙 X.unop))))
        (1 : (O'.obj (Opposite.op X.unop) : Type _))
      = α.app X g := by
  have hid : (ConcreteCategory.hom (G.map (𝟙 X.unop).op)) g = g := by
    rw [show (𝟙 X.unop).op = 𝟙 X from rfl, G.map_id]
    rfl
  show (ConcreteCategory.hom (α.app (Opposite.op X.unop)))
      ((1 : (O'.obj (Opposite.op X.unop) : Type _)) •
        (show (G.obj (Opposite.op X.unop) : Type _) from
          (ConcreteCategory.hom (G.map (𝟙 X.unop).op)) g))
    = (ModuleCat.Hom.hom (α.app X)) g
  rw [one_smul, hid]

/-- `homEquivInverse` is a left inverse of `homEquivForward`. -/
theorem homEquiv_left_inv (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O)
    (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F) :
    homEquivInverse φ G F (homEquivForward φ G F α) = α := by
  ext X g
  show invSecVal φ F X ((homEquivForward φ G F α).app X g) = (ModuleCat.Hom.hom (α.app X)) g
  show (ConcreteCategory.hom
      (fwdSecApp φ G F α X g (Opposite.op (Over.mk (𝟙 X.unop)))))
        (1 : (O'.obj (Opposite.op X.unop) : Type _))
      = (ModuleCat.Hom.hom (α.app X)) g
  exact fwdSecApp_one φ G F α X g

/-- Sectionwise form of the second half of the Hom-bijection: the forward map applied to the
inverse map of `β` agrees with `β` on every section. -/
theorem fwdSec_invSec_app (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (β : G ⟶ coextObj φ F) (X : Cᵒᵖ) (g : (G.obj X : Type _))
    (V : (Over X.unop)ᵒᵖ) (a' : (O'.obj (Opposite.op V.unop.left) : Type _)) :
    ((fwdSec φ G F (homEquivInverse φ G F β) X g).app V) a' = (((β.app X) g).app V) a' := by
  obtain ⟨h, hh⟩ : ∃ h : (G.obj (Opposite.op V.unop.left) : Type _),
      (ConcreteCategory.hom (G.map V.unop.hom.op)) g = h := ⟨_, rfl⟩
  have h1 : ((fwdSec φ G F (homEquivInverse φ G F β) X g).app V) a'
      = (((β.app (Opposite.op V.unop.left)) h).app
          (Opposite.op (Over.mk (𝟙 V.unop.left)))) a' := by
    have eval : ((fwdSec φ G F (homEquivInverse φ G F β) X g).app V) a'
        = invSecVal φ F (Opposite.op V.unop.left)
            ((ModuleCat.Hom.hom (β.app (Opposite.op V.unop.left))) (a' • h)) := by
      rw [← hh]
      rfl
    rw [eval, (β.app (Opposite.op V.unop.left)).hom.map_smul]
    exact invSecVal_smul φ F (Opposite.op V.unop.left) a'
      ((β.app (Opposite.op V.unop.left)) h)
  rw [h1]
  have hii : (β.app (Opposite.op V.unop.left)) h
      = coextRestrFun φ F V.unop.hom.op ((β.app X) g) := by
    have natβ := PresheafOfModules.Hom.naturality β V.unop.hom.op
    have hel := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp natβ) g
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hel
    rw [← hh]
    exact hel
  rw [hii]
  exact coextRestrFun_app_apply φ F V.unop.hom.op ((β.app X) g) (𝟙 V.unop.left) V.unop.hom
    (Category.id_comp V.unop.hom) a'

/-- `homEquivInverse` is a right inverse of `homEquivForward`. -/
theorem homEquiv_right_inv (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) (β : G ⟶ coextObj φ F) :
    homEquivForward φ G F (homEquivInverse φ G F β) = β := by
  ext X g
  show fwdSec φ G F (homEquivInverse φ G F β) X g = β.app X g
  ext V a'
  exact fwdSec_invSec_app φ G F β X g V a'

/-- The bijection `Hom_O(G_O, F) ≃ Hom_{O'}(G, SheafHom_O(O', F))`, with forward map
`α ↦ (g ↦ a' ↦ α(a' • g))` and inverse `β ↦ (g ↦ β(g)(1))`. -/
noncomputable def homEquiv (φ : O ⟶ O') (G : PresheafOfModules.{u} O')
    (F : PresheafOfModules.{u} O) :
    ((PresheafOfModules.restrictScalars φ).obj G ⟶ F) ≃ (G ⟶ coextObj φ F) where
  toFun := homEquivForward φ G F
  invFun := homEquivInverse φ G F
  left_inv := homEquiv_left_inv φ G F
  right_inv := homEquiv_right_inv φ G F

/-- Naturality of the inverse map `homEquivInverse` in `G` (precomposition with
`γ : G' ⟶ G`). -/
theorem homEquiv_naturality_left_symm (φ : O ⟶ O') {G' G : PresheafOfModules.{u} O'}
    {F : PresheafOfModules.{u} O} (γ : G' ⟶ G) (β : G ⟶ coextObj φ F) :
    homEquivInverse φ G' F (γ ≫ β) =
      (PresheafOfModules.restrictScalars φ).map γ ≫ homEquivInverse φ G F β := by
  ext X g
  show invSecVal φ F X ((γ ≫ β).app X g)
      = invSecVal φ F X ((β.app X) ((γ.app X) g))
  rw [PresheafOfModules.comp_app]
  rfl

/-- Naturality of the Hom-bijection in `F` (postcomposition with `η : F ⟶ F'`). -/
theorem homEquiv_naturality_right (φ : O ⟶ O') {G : PresheafOfModules.{u} O'}
    {F F' : PresheafOfModules.{u} O} (α : (PresheafOfModules.restrictScalars φ).obj G ⟶ F)
    (η : F ⟶ F') :
    homEquivForward φ G F' (α ≫ η) =
      homEquivForward φ G F α ≫ (coextendScalars φ).map η := by
  ext X g
  show fwdSec φ G F' (α ≫ η) X g
      = fwdSec φ G F α X g ≫ (PresheafOfModules.pushforward₀ (Over.forget X.unop) O).map η
  ext V a'
  simp only [fwdSec, fwdSecPresheaf, fwdSecApp, PresheafOfModules.comp_app,
    PresheafOfModules.homMk_app, AddCommGrpCat.ofHom]
  rfl

/-! ### The adjunction `φ*_res ⊣ φ_*^coext`. -/

/-- The adjunction `φ*_res ⊣ φ_*^coext`: restriction of scalars along `φ` is left adjoint to the
coextension-of-scalars functor `φ_*^coext = coextendScalars φ`, with Hom-bijection `homEquiv`
(forward `α ↦ (g ↦ a' ↦ α(a' • g))`, inverse `β ↦ (g ↦ β(g)(1))`). This is the
presheaf-of-modules analogue of `ModuleCat.restrictCoextendScalarsAdj`. -/
@[stacks 0932 "the presheaf case: Hom_O(G, F) = Hom_O'(G, SheafHom_O(O', F)) for C a category \
and O ⟶ O' a map of presheaves of rings"]
noncomputable def restrictScalars_coextendScalars_adjunction (φ : O ⟶ O') :
    PresheafOfModules.restrictScalars.{u} φ ⊣ coextendScalars φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G F => homEquiv φ G F
      homEquiv_naturality_left_symm := fun γ β => homEquiv_naturality_left_symm φ γ β
      homEquiv_naturality_right := fun α η => homEquiv_naturality_right φ α η }

end Stacks.PresheafOfModules.CoextendScalars
