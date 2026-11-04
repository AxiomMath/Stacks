module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RingPresheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# The objectwise tensor product of presheaves of modules and sheafification

Let `O` be a presheaf of commutative rings on a category `C`. The *objectwise tensor product*
of two presheaves of `O`-modules `G` and `F` is the presheaf of modules
`U ↦ G(U) ⊗_{O(U)} F(U)`. Tensoring sheaves of modules is this construction followed by
sheafification, which is the functor whose exactness defines flatness of a sheaf of modules
(Stacks 03ER).

The main result is that **sheafification does not see a local bijection in either tensor
factor**: if `α : M ⟶ M'` is locally injective and locally surjective, then so are
`(tensorRight N).map α` and `tensorMapRight M α`. This is the technical heart of the
statement that the tensor product of sheaves of modules only depends on the sheafifications
of its arguments; it is what makes a presheaf-level computation of a tensor product legitimate
after sheafifying, and it is the form in which "tensoring commutes with sheafification" is
consumed by the exactness arguments of Stacks 03EX and 03ET.

The proof is not an element chase. Rather, by the universal property `tensorHomEquiv` below,
morphisms out of the objectwise tensor product are bilinear maps on sections, and
`Stacks.BilinearMap.compLeftEquiv` already says that restricting a bilinear
map into a *sheaf* along a locally bijective morphism is a bijection. Conjugating that
bijection through the sheafification adjunction shows that sheafification inverts the induced
morphism of tensor products, and `GrothendieckTopology.W_iff_isLocallyBijective` converts that
back into local bijectivity.

## Main definitions

* `Stacks.tensorObj` is the objectwise tensor product of two presheaves of
  modules, whose two module universes are independent of each other and of the ring universe.
* `Stacks.tensorRight` is the functor given by tensoring on the right by a
  fixed presheaf of modules, and `Stacks.tensorMapRight` is the morphism
  obtained by tensoring a morphism in the second variable.
* `Stacks.IsFlat` and `Stacks.SheafOfModules.IsFlat` define flatness of a
  presheaf, respectively sheaf, of modules as exactness of tensoring on the right with it.
* The native bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` supplies the endofunctor
  `G ↦ (G ⊗ F)^#` by fixing its right-hand argument.

## Main results

* `Stacks.tensorHomEquiv`: the universal property of `tensorObj`, namely
  that morphisms out of it are exactly the bilinear maps on sections.
* `Stacks.PresheafOfModules.isIso_sheafification_map_tensorRight_map` and
  `Stacks.PresheafOfModules.isIso_sheafification_map_tensorMapRight`: sheafification turns the
  morphism of tensor products induced by a locally bijective morphism into an isomorphism.
* `Stacks.PresheafOfModules.isLocallyInjective_tensorRight_map`,
  `isLocallySurjective_tensorRight_map`, `isLocallyInjective_tensorMapRight` and
  `isLocallySurjective_tensorMapRight`: the same statement in the form in which it is used,
  namely that tensoring preserves local bijectivity in each variable.
* `Stacks.SheafOfModules.sheafTensorRight_shortExact_of_flat_factor`: tensoring a short exact
  sequence of sheaves of modules by a *flat* sheaf of modules gives a short exact sequence.
  This is the formal consequence of flatness being defined as exactness of the tensor functor;
  it is **not** Stacks 03EX, whose hypothesis is flatness of the third term of the sequence
  rather than of the sheaf being tensored with.

## Implementation notes

The objectwise tensor product is built by hand rather than taken from Mathlib's monoidal
structure on presheaves of modules, because that structure forces the module universe to equal
the ring universe: `PresheafOfModules.Monoidal.tensorObj` in
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal` declares its factors as
`PresheafOfModules.{u} (R ⋙ forget₂ _ _)` for `R : Cᵒᵖ ⥤ CommRingCat.{u}`, one universe `u` for
both. The statements here keep them independent. The ring presheaf is one of commutative
rings, which is what the tensor product of two modules over it requires; the module universes
of the two factors are independent and the result lies in their maximum.

The comparison results are stated for a locally bijective morphism `α₀ : ringPresheaf O ⟶ R.obj`
from the ring presheaf to a sheaf of rings, which is the generality in which Mathlib's
`PresheafOfModules.sheafification` is defined; the case of interest takes `α₀` to be the
identity of the ring presheaf underlying a sheaf of commutative rings.

**No declaration forces a module universe here to equal the ring universe `w`.** Mathlib's
`PresheafOfModules.sheafification` keeps its module universe `v` independent of its ring
universe `u`, and `Stacks.BilinearMap` together with the
extension-along-a-local-bijection theorem it supplies
(`Stacks.BilinearMap.compLeftEquiv` and `compRightEquiv`) is stated at
three independent module universes. The only constraints are the ones typing forces:
`tensorObj M N` lies in `PresheafOfModules.{max z₁ z}` when `M` is at `z₁` and `N` at `z`, so a
morphism out of it has its target in that same universe, and sheafifying such a morphism needs
`J.WEqualsLocallyBijective AddCommGrpCat.{max z₁ z}` and
`HasWeakSheafify J AddCommGrpCat.{max z₁ z}`. Taking `z₁ = z = w` recovers the earlier
single-universe form of every statement in the `UniversalProperty` and `Comparison` sections.

`Stacks.isSheaf_forget_restrictScalars` and
`Stacks.W_toPresheaf_map_of_isIso` mention no tensor product, so they are
stated at their own free module universe `t` rather than at `max z₁ z`. This is not only more
general: a caller that supplies the morphism as `_` and lets its universe be inferred from a
hypothesis needs the universe to be a bare variable, because Lean's unifier assigns
`?t := w` but gets stuck on `max ?z₁ ?z =?= w`.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TensorProduct

universe v u w z z₁ t

namespace Stacks

variable {C : Type u} [Category.{v} C]

/-- A morphism such that precomposition with it is bijective on morphisms into every object
is an isomorphism. -/
lemma isIso_of_bijective_precomp {D : Type*} [Category D] {X Y : D} (u : X ⟶ Y)
    (h : ∀ Z : D, Function.Bijective (fun (ψ : Y ⟶ Z) ↦ u ≫ ψ)) : IsIso u := by
  obtain ⟨v, hv⟩ := (h X).2 (𝟙 X)
  refine ⟨v, hv, (h Y).1 ?_⟩
  change u ≫ v ≫ u = u ≫ 𝟙 Y
  rw [← Category.assoc, show u ≫ v = 𝟙 X from hv, Category.id_comp, Category.comp_id]


variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The restriction map on the objectwise tensor product of two presheaves of modules. -/
noncomputable def tensorMap
    (G : PresheafOfModules.{z₁} (ringPresheaf O))
    (F : PresheafOfModules.{z} (ringPresheaf O))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of ((ringPresheaf O).obj X) (G.obj X ⊗[(ringPresheaf O).obj X] F.obj X) ⟶
      (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).obj
        (ModuleCat.of ((ringPresheaf O).obj Y) (G.obj Y ⊗[(ringPresheaf O).obj Y] F.obj Y)) := by
  let T := (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).obj
    (ModuleCat.of ((ringPresheaf O).obj Y) (G.obj Y ⊗[(ringPresheaf O).obj Y] F.obj Y))
  letI : Module ((ringPresheaf O).obj X) T := T.isModule
  let l : (G.obj X ⊗[(ringPresheaf O).obj X] F.obj X) →ₗ[(ringPresheaf O).obj X] T :=
    { toFun := TensorProduct.map (G.restrictₛₗ f) (F.restrictₛₗ f)
      map_add' := map_add _
      map_smul' := by
        intro r x
        exact (TensorProduct.map (G.restrictₛₗ f) (F.restrictₛₗ f)).map_smulₛₗ r x }
  exact ConcreteCategory.ofHom l

/-- The restriction map of the objectwise tensor product on pure tensors. -/
@[simp]
lemma tensorMap_tmul
    (G : PresheafOfModules.{z₁} (ringPresheaf O))
    (F : PresheafOfModules.{z} (ringPresheaf O))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : G.obj X) (y : F.obj X) :
    tensorMap G F f (x ⊗ₜ[(ringPresheaf O).obj X] y) =
      G.map f x ⊗ₜ[(ringPresheaf O).obj Y] F.map f y := rfl

/-- The objectwise tensor product of two independently sized presheaves of modules. -/
noncomputable def tensorObj
    (G : PresheafOfModules.{z₁} (ringPresheaf O))
    (F : PresheafOfModules.{z} (ringPresheaf O)) :
    PresheafOfModules.{max z₁ z} (ringPresheaf O) where
  obj X := ModuleCat.of ((ringPresheaf O).obj X) (G.obj X ⊗[(ringPresheaf O).obj X] F.obj X)
  map f := ModuleCat.tensorRestrictMap ((ringPresheaf O).map f).hom
    (G.restrictₛₗ f) (F.restrictₛₗ f)
  map_id X := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    change tensorMap G F (𝟙 X) (x ⊗ₜ[(ringPresheaf O).obj X] y) = _
    rw [tensorMap_tmul]
    simp
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    change tensorMap G F (f ≫ g) (x ⊗ₜ[(ringPresheaf O).obj _] y) = _
    rw [tensorMap_tmul, G.map_comp_apply, F.map_comp_apply]
    change (G.map g (G.map f x) ⊗ₜ[(ringPresheaf O).obj _] F.map g (F.map f y)) =
      (G.map g (G.map f x) ⊗ₜ[(ringPresheaf O).obj _] F.map g (F.map f y))
    rfl

/-- The restriction maps of `tensorObj G F` act factorwise on pure tensors. -/
@[simp]
lemma tensorObj_map_tmul
    (G : PresheafOfModules.{z₁} (ringPresheaf O))
    (F : PresheafOfModules.{z} (ringPresheaf O))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : G.obj X) (y : F.obj X) :
    (tensorObj G F).map f (x ⊗ₜ[(ringPresheaf O).obj X] y) =
      G.map f x ⊗ₜ[(ringPresheaf O).obj Y] F.map f y := rfl

/-- Tensoring presheaves of modules on the right by `F`. -/
@[implicit_reducible]
noncomputable def tensorRight (F : PresheafOfModules.{z} (ringPresheaf O)) :
    PresheafOfModules.{z₁} (ringPresheaf O) ⥤
      PresheafOfModules.{max z₁ z} (ringPresheaf O) where
  obj G := tensorObj G F
  map {G H} φ :=
    { app := fun X ↦ ModuleCat.ofHom (TensorProduct.map (φ.app X).hom LinearMap.id)
      naturality := by
        intro X Y f
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext x y
        change ((tensorMap G F f ≫
          (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).map
            (ModuleCat.ofHom (TensorProduct.map (φ.app Y).hom LinearMap.id)))
              (x ⊗ₜ[(ringPresheaf O).obj X] y)) =
          ((ModuleCat.ofHom (TensorProduct.map (φ.app X).hom LinearMap.id) ≫
            tensorMap H F f) (x ⊗ₜ[(ringPresheaf O).obj X] y))
        change φ.app Y (G.map f x) ⊗ₜ[(ringPresheaf O).obj Y] F.map f y =
          H.map f (φ.app X x) ⊗ₜ[(ringPresheaf O).obj Y] F.map f y
        exact congrArg₂ (fun a b ↦ a ⊗ₜ[(ringPresheaf O).obj Y] b)
          (PresheafOfModules.naturality_apply φ f x) rfl }
  map_id G := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  map_comp φ ψ := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

/-- `(tensorRight F).map φ` applies `φ` to the first factor of a pure tensor. -/
@[simp]
lemma tensorRight_map_app_tmul
    (F : PresheafOfModules.{z} (ringPresheaf O))
    {G H : PresheafOfModules.{z₁} (ringPresheaf O)} (φ : G ⟶ H) (X : Cᵒᵖ)
    (x : G.obj X) (y : F.obj X) :
    ((tensorRight F).map φ).app X (show (tensorObj G F).obj X from
        x ⊗ₜ[(ringPresheaf O).obj X] y) =
      φ.app X x ⊗ₜ[(ringPresheaf O).obj X] y := rfl

/-- Tensoring on the left by `M`, applied to a morphism in the second variable. -/
noncomputable def tensorMapRight
    (M : PresheafOfModules.{z₁} (ringPresheaf O))
    {N N' : PresheafOfModules.{z} (ringPresheaf O)} (α : N ⟶ N') :
    tensorObj M N ⟶ tensorObj M N' where
  app X := ModuleCat.ofHom (TensorProduct.map LinearMap.id (α.app X).hom)
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    change ((tensorMap M N f ≫
      (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).map
        (ModuleCat.ofHom (TensorProduct.map LinearMap.id (α.app Y).hom)))
          (x ⊗ₜ[(ringPresheaf O).obj X] y)) =
      ((ModuleCat.ofHom (TensorProduct.map LinearMap.id (α.app X).hom) ≫
        tensorMap M N' f) (x ⊗ₜ[(ringPresheaf O).obj X] y))
    change M.map f x ⊗ₜ[(ringPresheaf O).obj Y] α.app Y (N.map f y) =
      M.map f x ⊗ₜ[(ringPresheaf O).obj Y] N'.map f (α.app X y)
    exact congrArg₂ (fun a b ↦ a ⊗ₜ[(ringPresheaf O).obj Y] b) rfl
      (PresheafOfModules.naturality_apply α f y)

/-- `tensorMapRight M α` applies `α` to the second factor of a pure tensor. -/
@[simp]
lemma tensorMapRight_app_tmul
    (M : PresheafOfModules.{z₁} (ringPresheaf O))
    {N N' : PresheafOfModules.{z} (ringPresheaf O)} (α : N ⟶ N') (X : Cᵒᵖ)
    (x : M.obj X) (y : N.obj X) :
    (tensorMapRight M α).app X (show (tensorObj M N).obj X from
        x ⊗ₜ[(ringPresheaf O).obj X] y) =
      x ⊗ₜ[(ringPresheaf O).obj X] α.app X y := rfl

section UniversalProperty

variable
  {M M' : PresheafOfModules.{z₁} (ringPresheaf O)}
  {N N' : PresheafOfModules.{z} (ringPresheaf O)}
  {P : PresheafOfModules.{max z₁ z} (ringPresheaf O)}

/-- The `(ringPresheaf O).obj X`-bilinear map on sections underlying a bilinear map of
presheaves of modules. -/
def BilinearMap.toLinearMap₂ (β : BilinearMap M N P) (X : Cᵒᵖ) :
    M.obj X →ₗ[(ringPresheaf O).obj X] N.obj X →ₗ[(ringPresheaf O).obj X] P.obj X where
  toFun x :=
    { toFun := fun y ↦ β.app X x y
      map_add' := fun y y' ↦ map_add (β.app X x) y y'
      map_smul' := fun r y ↦ β.map_smul_right X r x y }
  map_add' x x' := by ext y; exact β.map_add_left X x x' y
  map_smul' r x := by ext y; exact β.map_smul_left X r x y

/-- The morphism out of the objectwise tensor product determined by a bilinear map. -/
noncomputable def BilinearMap.toTensorHom (β : BilinearMap M N P) : tensorObj M N ⟶ P where
  app X := ModuleCat.ofHom (TensorProduct.lift (β.toLinearMap₂ X))
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    change ((tensorMap M N f ≫
      (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).map
        (ModuleCat.ofHom (TensorProduct.lift (β.toLinearMap₂ Y))))
          (x ⊗ₜ[(ringPresheaf O).obj X] y)) =
      ((ModuleCat.ofHom (TensorProduct.lift (β.toLinearMap₂ X)) ≫ P.map f)
        (x ⊗ₜ[(ringPresheaf O).obj X] y))
    change β.app Y (M.map f x) (N.map f y) = P.map f (β.app X x y)
    exact (β.naturality f x y).symm

/-- The morphism `β.toTensorHom` sends a pure tensor `x ⊗ₜ y` to `β.app X x y`. -/
@[simp]
lemma BilinearMap.toTensorHom_app_tmul (β : BilinearMap M N P) (X : Cᵒᵖ) (x : M.obj X)
    (y : N.obj X) :
    β.toTensorHom.app X (show (tensorObj M N).obj X from
      x ⊗ₜ[(ringPresheaf O).obj X] y) = β.app X x y := rfl

/-- The sectionwise bilinear map underlying a morphism out of the objectwise tensor product. -/
noncomputable def tensorHomCurry (φ : tensorObj M N ⟶ P) (X : Cᵒᵖ) :
    M.obj X →ₗ[(ringPresheaf O).obj X] N.obj X →ₗ[(ringPresheaf O).obj X] P.obj X :=
  TensorProduct.curry
    (show (M.obj X ⊗[(ringPresheaf O).obj X] N.obj X) →ₗ[(ringPresheaf O).obj X] P.obj X from
      ModuleCat.Hom.hom (φ.app X))

/-- `tensorHomCurry φ X x y` is `φ` applied to the pure tensor `x ⊗ₜ y`. -/
@[simp]
lemma tensorHomCurry_apply (φ : tensorObj M N ⟶ P) (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X) :
    tensorHomCurry φ X x y = φ.app X (x ⊗ₜ[(ringPresheaf O).obj X] y) := rfl

/-- The bilinear map determined by a morphism out of the objectwise tensor product. -/
noncomputable def BilinearMap.ofTensorHom (φ : tensorObj M N ⟶ P) : BilinearMap M N P where
  app X :=
    AddMonoidHom.mk'
      (fun x ↦ AddMonoidHom.mk' (fun y ↦ tensorHomCurry φ X x y)
        (fun y y' ↦ map_add (tensorHomCurry φ X x) y y'))
      (fun x x' ↦ by
        ext y
        exact LinearMap.congr_fun (map_add (tensorHomCurry φ X) x x') y)
  map_smul_left X r x y := LinearMap.congr_fun (map_smul (tensorHomCurry φ X) r x) y
  map_smul_right X r x y := map_smul (tensorHomCurry φ X x) r y
  naturality {X Y} f x y :=
    (PresheafOfModules.naturality_apply φ f
      (show (tensorObj M N).obj X from x ⊗ₜ[(ringPresheaf O).obj X] y)).symm

/-- The bilinear map `BilinearMap.ofTensorHom φ` is given on sections by `tensorHomCurry φ`. -/
@[simp]
lemma BilinearMap.ofTensorHom_app (φ : tensorObj M N ⟶ P) (X : Cᵒᵖ) (x : M.obj X)
    (y : N.obj X) :
    (BilinearMap.ofTensorHom φ).app X x y = tensorHomCurry φ X x y := rfl

/-- **Universal property of the objectwise tensor product of presheaves of modules.**
Morphisms out of `tensorObj M N` are the same thing as bilinear maps on sections. -/
@[simps]
noncomputable def tensorHomEquiv : (tensorObj M N ⟶ P) ≃ BilinearMap M N P where
  toFun := BilinearMap.ofTensorHom
  invFun := BilinearMap.toTensorHom
  left_inv φ := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  right_inv β := by ext X x y; rfl

/-- Under the universal property, precomposition with `(tensorRight N).map α` corresponds to
restriction of a bilinear map in the first variable. -/
lemma tensorHomEquiv_comp_tensorRight_map (α : M ⟶ M') (φ : tensorObj M' N ⟶ P) :
    tensorHomEquiv ((tensorRight N).map α ≫ φ) = (tensorHomEquiv φ).compLeft α := by
  ext X x y
  rfl

/-- Under the universal property, precomposition with `tensorMapRight` corresponds to
restriction of a bilinear map in the second variable. -/
lemma tensorHomEquiv_comp_tensorMapRight (α : N ⟶ N') (φ : tensorObj M N' ⟶ P) :
    tensorHomEquiv (tensorMapRight M α ≫ φ) = (tensorHomEquiv φ).compRight α := by
  ext X x y
  rfl

end UniversalProperty

/-- A presheaf of modules is flat when tensoring on the right with it is an exact
endofunctor. -/
@[stacks 03ER "part (1), for the objectwise tensor product Stacks.tensorRight of this file, \
whose two module universes are independent of each other and of the ring universe. The tree \
carries a second objectwise tensor product, and part (1) for that one is \
AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat, which is also where parts (2) and \
(4) of the tag are registered"]
abbrev IsFlat (F : PresheafOfModules.{z} (ringPresheaf O)) : Prop :=
  exactFunctor (PresheafOfModules.{z} (ringPresheaf O)) _ (tensorRight F)


/-- If `f` corresponds to a bijection `g` under equivalences of source and target, it is
bijective. -/
private theorem bijective_of_equiv_comp {A B C D : Type*} (e₁ : A ≃ C) (e₂ : B ≃ D)
    (f : B → A) (g : D → C) (h : ∀ x, e₁ (f x) = g (e₂ x)) (hg : Function.Bijective g) :
    Function.Bijective f := by
  have : f = e₁.symm ∘ g ∘ e₂ := funext fun x ↦ by simp [← h]
  rw [this]
  exact e₁.symm.bijective.comp (hg.comp e₂.bijective)

/-- Sheafification inverts `u` if precomposition with `u` is bijective into the underlying
presheaf of modules of every sheaf of modules. -/
private lemma isIso_sheafification_map_of_bijective_precomp {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (α₀ : ringPresheaf O ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α₀] [Presheaf.IsLocallySurjective J α₀]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [HasWeakSheafify J AddCommGrpCat.{t}]
    {P Q : PresheafOfModules.{t} (ringPresheaf O)} (u : P ⟶ Q)
    (h : ∀ F : _root_.SheafOfModules.{t} R, Function.Bijective (fun
      (φ : Q ⟶ ((_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α₀).obj F)) ↦
        u ≫ φ)) :
    IsIso ((PresheafOfModules.sheafification (R := R) α₀).map u) := by
  apply isIso_of_bijective_precomp
  intro F
  exact bijective_of_equiv_comp _ _ _ _
    ((PresheafOfModules.sheafificationAdjunction (R := R) α₀).homEquiv_naturality_left u) (h F)


section Comparison

variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  (α₀ : ringPresheaf O ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α₀] [Presheaf.IsLocallySurjective J α₀]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max z₁ z}]
  [HasWeakSheafify J AddCommGrpCat.{max z₁ z}]

variable {M M' : PresheafOfModules.{z₁} (ringPresheaf O)}
  {N N' : PresheafOfModules.{z} (ringPresheaf O)}

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max z₁ z}]
  [HasWeakSheafify J AddCommGrpCat.{max z₁ z}] in
/-- Precomposition with `(tensorRight N).map α`, for `α` locally bijective, is a bijection on
morphisms from the objectwise tensor product into a presheaf of modules whose underlying
presheaf is a sheaf. -/
lemma bijective_precomp_tensorRight_map (α : M ⟶ M')
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map α)]
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map α)]
    {P : PresheafOfModules.{max z₁ z} (ringPresheaf O)}
    (hP : Presheaf.IsSheaf J P.presheaf) :
    Function.Bijective (fun (φ : tensorObj M' N ⟶ P) ↦ (tensorRight N).map α ≫ φ) := by
  exact bijective_of_equiv_comp tensorHomEquiv tensorHomEquiv _ _
    (tensorHomEquiv_comp_tensorRight_map α) (BilinearMap.compLeftEquiv (N := N) hP α).bijective

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max z₁ z}]
  [HasWeakSheafify J AddCommGrpCat.{max z₁ z}] in
/-- Precomposition with `tensorMapRight M α`, for `α` locally bijective, is a bijection on
morphisms from the objectwise tensor product into a presheaf of modules whose underlying
presheaf is a sheaf. -/
lemma bijective_precomp_tensorMapRight (α : N ⟶ N')
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map α)]
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map α)]
    {P : PresheafOfModules.{max z₁ z} (ringPresheaf O)}
    (hP : Presheaf.IsSheaf J P.presheaf) :
    Function.Bijective (fun (φ : tensorObj M N' ⟶ P) ↦ tensorMapRight M α ≫ φ) := by
  exact bijective_of_equiv_comp tensorHomEquiv tensorHomEquiv _ _
    (tensorHomEquiv_comp_tensorMapRight α) (BilinearMap.compRightEquiv (M := M) hP α).bijective

/-! ### Statements at a single module universe

The next two lemmas mention no tensor product, so their module universe `t` is free rather
than of the form `max z₁ z`. -/

omit [Presheaf.IsLocallyInjective J α₀] [Presheaf.IsLocallySurjective J α₀]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max z₁ z}]
  [HasWeakSheafify J AddCommGrpCat.{max z₁ z}] in
/-- The underlying presheaf of the value of the right adjoint of sheafification is a sheaf. -/
lemma isSheaf_forget_restrictScalars (F : _root_.SheafOfModules.{t} R) :
    Presheaf.IsSheaf J
      (((_root_.SheafOfModules.forget R ⋙
        PresheafOfModules.restrictScalars α₀).obj F).presheaf) :=
  F.isSheaf

section SingleUniverse

variable [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [HasWeakSheafify J AddCommGrpCat.{t}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max z₁ z}]
  [HasWeakSheafify J AddCommGrpCat.{max z₁ z}] in
/-- A morphism of presheaves of modules whose sheafification is an isomorphism is a
`J.W`-equivalence of the underlying presheaves of abelian groups. -/
lemma W_toPresheaf_map_of_isIso {P Q : PresheafOfModules.{t} (ringPresheaf O)}
    (u : P ⟶ Q) (h : IsIso ((PresheafOfModules.sheafification (R := R) α₀).map u)) :
    J.W ((PresheafOfModules.toPresheaf _).map u) := by
  rw [J.W_iff]
  exact inferInstanceAs
    (IsIso ((_root_.SheafOfModules.toSheaf R).map
      ((PresheafOfModules.sheafification (R := R) α₀).map u)))

end SingleUniverse

/-! ### Statements about the objectwise tensor product

Sheafifying a morphism out of `tensorObj M N` needs the sheafification instances at the
module universe `max z₁ z` that `tensorObj` lands in. -/

section TensorSheafification

/-- **Sheafification does not see a local bijection in the first tensor factor.** -/
lemma isIso_sheafification_map_tensorRight_map (α : M ⟶ M')
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map α)]
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map α)] :
    IsIso ((PresheafOfModules.sheafification (R := R) α₀).map
      ((tensorRight N).map α)) := by
  exact isIso_sheafification_map_of_bijective_precomp α₀ _
    fun F ↦ bijective_precomp_tensorRight_map α (isSheaf_forget_restrictScalars α₀ F)

/-- **Sheafification does not see a local bijection in the second tensor factor.** -/
lemma isIso_sheafification_map_tensorMapRight (α : N ⟶ N')
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map α)]
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map α)] :
    IsIso ((PresheafOfModules.sheafification (R := R) α₀).map (tensorMapRight M α)) := by
  exact isIso_sheafification_map_of_bijective_precomp α₀ _
    fun F ↦ bijective_precomp_tensorMapRight α (isSheaf_forget_restrictScalars α₀ F)

include α₀ in
variable (N) in
/-- **Tensoring preserves local injectivity in the first variable**: if `α` is locally
bijective then so is `(tensorRight N).map α`. -/
lemma isLocallyInjective_tensorRight_map (α : M ⟶ M')
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map α)]
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map α)] :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map ((tensorRight N).map α)) :=
  (W_toPresheaf_map_of_isIso α₀ _
    (isIso_sheafification_map_tensorRight_map α₀ α)).isLocallyInjective

include α₀ in
variable (N) in
/-- **Tensoring preserves local surjectivity in the first variable** (for a locally bijective
morphism). -/
lemma isLocallySurjective_tensorRight_map (α : M ⟶ M')
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map α)]
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map α)] :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map ((tensorRight N).map α)) :=
  (W_toPresheaf_map_of_isIso α₀ _
    (isIso_sheafification_map_tensorRight_map α₀ α)).isLocallySurjective

include α₀ in
variable (M) in
/-- **Tensoring preserves local injectivity in the second variable.** -/
lemma isLocallyInjective_tensorMapRight (α : N ⟶ N')
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map α)]
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map α)] :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (tensorMapRight M α)) :=
  (W_toPresheaf_map_of_isIso α₀ _
    (isIso_sheafification_map_tensorMapRight α₀ α)).isLocallyInjective

include α₀ in
variable (M) in
/-- **Tensoring preserves local surjectivity in the second variable** (for a locally bijective
morphism). -/
lemma isLocallySurjective_tensorMapRight (α : N ⟶ N')
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map α)]
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map α)] :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (tensorMapRight M α)) :=
  (W_toPresheaf_map_of_isIso α₀ _
    (isIso_sheafification_map_tensorMapRight α₀ α)).isLocallySurjective

end TensorSheafification

end Comparison


variable {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The underlying sheaf of rings of a sheaf of commutative rings.

Named `commRingSheafToRingSheaf` rather than `ringSheaf` because
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward` declares a `Stacks.ringSheaf`
in this same namespace; two declarations of one name made the two modules impossible to
co-import, which would have broken the umbrella on regeneration. -/
abbrev commRingSheafToRingSheaf (O : Sheaf J CommRingCat.{w}) : Sheaf J RingCat.{w} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj O


namespace SheafOfModules

/-- A sheaf of modules is flat when tensoring on the right with it is an exact endofunctor
on sheaves of modules. -/
@[stacks 03ER "part (3), for Stacks.sheafTensorRight, the sheafified tensor product over \
Stacks.commRingSheafToRingSheaf. Part (3) over Stacks.SheafOfModules.Tensor.ringSheaf is \
AlgebraicGeometry.SheafOfModules.IsFlat, which is also where part (4) of the tag is \
registered"]
abbrev IsFlat {O : Sheaf J CommRingCat.{w}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasWeakSheafify J AddCommGrpCat.{z}]
    (F : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) : Prop :=
  exactFunctor _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj F)

section FlatFactor

variable {O : Sheaf J CommRingCat.{w}} [HasSheafify J AddCommGrpCat.{z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Tensoring a short exact sequence of sheaves of modules by a **flat** sheaf of modules
gives a short exact sequence.

This is the direct consequence of flatness being *defined* as exactness of the tensor functor.
It is not Stacks 03EX, which instead assumes that the third term of the short exact sequence
is flat and allows the sheaf being tensored with to be arbitrary. -/
theorem sheafTensorRight_shortExact_of_flat_factor
    (S : ShortComplex (_root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (G : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hS : S.ShortExact) (hflat : IsFlat G) :
    ∃ h : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj G).map S.f ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj G).map S.g = 0,
      (ShortComplex.mk
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj G).map S.f)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj G).map S.g)
        h).ShortExact := by
  have : PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj G) := hflat.1
  have : PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj G) := hflat.2
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj G).Additive :=
    (additiveFunctor_iff _).1 (rightExactFunctor_le_additiveFunctor _ _ _
      ((rightExactFunctor_iff _).2 hflat.2))
  exact ⟨(S.map ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj G)).zero,
    hS.map_of_exact ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj G)⟩

end FlatFactor

end SheafOfModules

end Stacks
