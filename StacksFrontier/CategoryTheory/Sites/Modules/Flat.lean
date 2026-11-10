module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RingPresheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
import StacksCore.Tactic.StacksAttribute

/-!
# Flat presheaves and sheaves of modules

A presheaf or sheaf of modules is flat when tensoring with it is an exact endofunctor, and a
morphism of presheaves or sheaves of rings is flat when its target, regarded as a module over
its source, is flat.

Flatness on a site specialises to flatness of a module on a ringed space: a ringed space
supplies a sheaf of commutative rings on the site of its open sets, so its modules are a
special case.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorRight`: tensoring presheaves of
  modules on the right by a fixed presheaf of modules, objectwise.
* `AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat`: flatness of a presheaf of
  modules.
* `AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlatMap`: flatness of a morphism of
  presheaves of rings.
* `Stacks.SheafOfModules.Tensor.sheafTensor`: the native tensor bifunctor on sheaves of
  modules, whose flipped objects are the functors used to define flatness.
* `AlgebraicGeometry.SheafOfModules.IsFlat`: flatness of a sheaf of modules.
* `AlgebraicGeometry.SheafOfModules.IsFlatMap`: flatness of a morphism of sheaves of rings.

The presheaf-level and the sheaf-level notions carry the same leaf names `IsFlat` and
`IsFlatMap`; the presheaf-level ones are the two in the `PresheafOfModules` namespace, and
their arguments are presheaves, with no sheaf condition and no topology in sight.

## Implementation notes

Exactness is `CategoryTheory.exactFunctor`, so it means preservation of finite limits and of
finite colimits; this is the condition the source states, rather than the weaker preservation
of monomorphisms that right exactness makes equivalent to it. The tensor product of sheaves
of modules is the sheafification of the objectwise tensor product presheaf. Flatness of a
morphism of (pre)sheaves of rings regards the target as its rank-one module and restricts
scalars along the morphism.

The objectwise tensor functor on presheaves of modules is constructed here rather than taken
from the monoidal structure, because the monoidal instance requires the module carriers and
the ring carrier to lie in the same universe, whereas the two module universes and the ring
universe are independent here. Equal module universes give an endofunctor.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 05ND](https://stacks.math.columbia.edu/tag/05ND)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TensorProduct

universe v u w z z₁

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C]

/-! The presheaf of rings underlying a presheaf of commutative rings is **not** declared here.
`AlgebraicGeometry.SheafOfModules.ringPresheaf`, used throughout this file and by its
consumers, is the alias of `Stacks.ringPresheaf` set up in
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RingPresheaf`; the two names denote one
constant, so this flatness tower and the one over `Stacks.ringPresheaf` speak about the same
constant. -/

namespace PresheafOfModules

/-- The restriction map on the objectwise tensor product of two presheaves of
modules. -/
noncomputable def tensorMap {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (G : _root_.PresheafOfModules.{z₁} (ringPresheaf O))
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of ((ringPresheaf O).obj X)
        (G.obj X ⊗[(ringPresheaf O).obj X] F.obj X) ⟶
      (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).obj
        (ModuleCat.of ((ringPresheaf O).obj Y)
          (G.obj Y ⊗[(ringPresheaf O).obj Y] F.obj Y)) := by
  let T := (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).obj
    (ModuleCat.of ((ringPresheaf O).obj Y)
      (G.obj Y ⊗[(ringPresheaf O).obj Y] F.obj Y))
  letI : Module ((ringPresheaf O).obj X) T := T.isModule
  let l : (G.obj X ⊗[(ringPresheaf O).obj X] F.obj X) →ₗ[(ringPresheaf O).obj X] T := {
    toFun := TensorProduct.map (G.restrictₛₗ f) (F.restrictₛₗ f)
    map_add' := map_add _
    map_smul' := fun r x ↦
      (TensorProduct.map (G.restrictₛₗ f) (F.restrictₛₗ f)).map_smulₛₗ r x }
  exact ConcreteCategory.ofHom l

/-- The restriction map on the objectwise tensor product acts on a pure tensor by restricting
each factor. -/
@[simp]
lemma tensorMap_tmul {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (G : _root_.PresheafOfModules.{z₁} (ringPresheaf O))
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : G.obj X) (y : F.obj X) :
    tensorMap G F f (x ⊗ₜ[(ringPresheaf O).obj X] y) =
      G.map f x ⊗ₜ[(ringPresheaf O).obj Y] F.map f y := rfl

/-- The objectwise tensor product of two independently sized presheaves of modules. -/
@[sga "4 IV 12.10" "special case"]
noncomputable def tensorObj {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (G : _root_.PresheafOfModules.{z₁} (ringPresheaf O))
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) :
    _root_.PresheafOfModules.{max z₁ z} (ringPresheaf O) where
  obj X := ModuleCat.of ((ringPresheaf O).obj X)
    (G.obj X ⊗[(ringPresheaf O).obj X] F.obj X)
  map f := tensorMap G F f
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
    rfl

/-- Tensoring presheaves of modules on the right by `F`. The two module
universes and the ring universe are independent; the output uses the maximum
of the module universes. Equal module universes give an endofunctor. -/
@[implicit_reducible]
noncomputable def tensorRight {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) :
    _root_.PresheafOfModules.{z₁} (ringPresheaf O) ⥤
      _root_.PresheafOfModules.{max z₁ z} (ringPresheaf O) where
  obj G := tensorObj G F
  map {G H} φ := {
    app := fun X ↦ ModuleCat.ofHom (TensorProduct.map (φ.app X).hom LinearMap.id)
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
        (_root_.PresheafOfModules.naturality_apply φ f x) rfl }
  map_id G := by
    apply _root_.PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  map_comp φ ψ := by
    apply _root_.PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

/-- The objectwise tensor product of two morphisms of presheaves of modules: on each object of
the site, the tensor product of the two maps of modules.

This is the two-variable companion of `tensorRight`, whose action on morphisms is the special
case in which the second morphism is an identity (`tensorHom_id_right`). As for `tensorObj`, the
two module universes and the ring universe are independent. -/
noncomputable def tensorHom {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {G G' : _root_.PresheafOfModules.{z₁} (ringPresheaf O)}
    {F F' : _root_.PresheafOfModules.{z} (ringPresheaf O)}
    (φ : G ⟶ G') (ψ : F ⟶ F') : tensorObj G F ⟶ tensorObj G' F' where
  app X := ModuleCat.ofHom (TensorProduct.map (φ.app X).hom (ψ.app X).hom)
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    change ((tensorMap G F f ≫
      (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).map
        (ModuleCat.ofHom (TensorProduct.map (φ.app Y).hom (ψ.app Y).hom)))
          (x ⊗ₜ[(ringPresheaf O).obj X] y)) =
      ((ModuleCat.ofHom (TensorProduct.map (φ.app X).hom (ψ.app X).hom) ≫
        tensorMap G' F' f) (x ⊗ₜ[(ringPresheaf O).obj X] y))
    change φ.app Y (G.map f x) ⊗ₜ[(ringPresheaf O).obj Y] ψ.app Y (F.map f y) =
      G'.map f (φ.app X x) ⊗ₜ[(ringPresheaf O).obj Y] F'.map f (ψ.app X y)
    exact congrArg₂ (fun a b ↦ a ⊗ₜ[(ringPresheaf O).obj Y] b)
      (_root_.PresheafOfModules.naturality_apply φ f x)
      (_root_.PresheafOfModules.naturality_apply ψ f y)

/-- Tensoring two morphisms acts on a pure tensor by applying each morphism to its own
factor. -/
@[simp]
lemma tensorHom_app_tmul {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {G G' : _root_.PresheafOfModules.{z₁} (ringPresheaf O)}
    {F F' : _root_.PresheafOfModules.{z} (ringPresheaf O)}
    (φ : G ⟶ G') (ψ : F ⟶ F') (X : Cᵒᵖ) (x : G.obj X) (y : F.obj X) :
    (tensorHom φ ψ).app X (x ⊗ₜ[(ringPresheaf O).obj X] y) =
      φ.app X x ⊗ₜ[(ringPresheaf O).obj X] ψ.app X y := rfl

/-- Tensoring morphisms is functorial in both variables simultaneously. -/
lemma tensorHom_comp {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {G G' G'' : _root_.PresheafOfModules.{z₁} (ringPresheaf O)}
    {F F' F'' : _root_.PresheafOfModules.{z} (ringPresheaf O)}
    (φ : G ⟶ G') (ψ : F ⟶ F') (φ' : G' ⟶ G'') (ψ' : F' ⟶ F'') :
    tensorHom φ ψ ≫ tensorHom φ' ψ' = tensorHom (φ ≫ φ') (ψ ≫ ψ') := by
  ext X : 2
  apply TensorProduct.ext
  ext
  rfl

/-- Tensoring the two identities gives the identity of the tensor product. -/
lemma tensorHom_id {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (G : _root_.PresheafOfModules.{z₁} (ringPresheaf O))
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) :
    tensorHom (𝟙 G) (𝟙 F) = 𝟙 (tensorObj G F) := by
  ext X : 2
  apply TensorProduct.ext
  ext
  rfl

/-- Tensoring on the right with the identity of `F` is exactly the action of the functor
`tensorRight F` on morphisms. This is what keeps `tensorHom` and `tensorRight` from drifting
into parallel notions of the same thing. -/
lemma tensorHom_id_right {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {G G' : _root_.PresheafOfModules.{z₁} (ringPresheaf O)}
    (φ : G ⟶ G') (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) :
    tensorHom φ (𝟙 F) = (tensorRight F).map φ := by
  ext X : 2
  apply TensorProduct.ext
  ext
  rfl

/-- A presheaf of modules is flat when tensoring on the right with it is an
exact endofunctor. -/
@[stacks 03ER "part (1), for the objectwise tensor product \
AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorRight of this file; part (2) just \
below is stated in terms of it. Part (1) for the other objectwise tensor product in the tree, \
Stacks.tensorRight of \
StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness, is Stacks.IsFlat"]
abbrev IsFlat {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) : Prop :=
  exactFunctor (_root_.PresheafOfModules.{z} (ringPresheaf O)) _ (tensorRight F)

/-- A morphism of presheaves of rings is flat when its target ring presheaf,
viewed as a module over the source by restriction of scalars, is flat. -/
@[stacks 03ER "part (2)"]
abbrev IsFlatMap {O O' : Cᵒᵖ ⥤ CommRingCat.{w}} (f : O ⟶ O') : Prop :=
  IsFlat ((_root_.PresheafOfModules.restrictScalars
    (Functor.whiskerRight f (forget₂ CommRingCat RingCat))).obj
      (_root_.PresheafOfModules.unit (ringPresheaf O')))

end PresheafOfModules

variable {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- A sheaf of modules is flat when tensoring on the right with it is an exact
endofunctor on sheaves of modules.

This is part (3) of tag 03ER for the native tensor bifunctor, and part (4) just below
is stated in terms of it. `Stacks.SheafOfModules.IsFlat` uses the same native tensor
functor. -/
@[stacks 05ND "the definition: F is flat when G ↦ G ⊗_{O_X} F is exact",
  stacks 03ER "part (3), over Stacks.SheafOfModules.Tensor.ringSheaf; \
    cf. Stacks.SheafOfModules.IsFlat",
  stacks 08M5 "flatness over a morphism of ringed topoi: this predicate for the pullback ring",
  sga "4 V 1.1" "commutative case"]
abbrev IsFlat {O : Sheaf J CommRingCat.{w}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasWeakSheafify J AddCommGrpCat.{z}]
    (F : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) : Prop :=
  exactFunctor _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj F)

/-- A morphism of sheaves of rings is flat when its target ring sheaf, viewed
as a module over the source by restriction of scalars, is flat. -/
@[stacks 03ER "part (4)"]
abbrev IsFlatMap {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O') : Prop :=
  IsFlat ((_root_.SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O')))

end AlgebraicGeometry.SheafOfModules
