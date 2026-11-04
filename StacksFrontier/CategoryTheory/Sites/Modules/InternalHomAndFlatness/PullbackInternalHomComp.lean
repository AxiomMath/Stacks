module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompProvider
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomFlat
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The pullback of sheaves of modules along a composite of morphisms of ringed topoi

Let `X ⟶ Y ⟶ Z` be morphisms of ringed topoi between the topoi of three ringed sites. This file
constructs the comparison `(ψ ∘ φ)^* ≅ ψ^* ⋙ φ^*` of pullbacks of sheaves of modules for the
composite `AlgebraicGeometry.RingedToposHom.comp`, and proves the composition law of the
comparison of Stacks 03EL at that composite.

It also proves that the two one-variable functorial actions of the curried tensor product of
Stacks 0GMW compose to the action of the tensor bifunctor of Stacks 03EL on a pair of morphisms.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.toposCompHom`: the composite of two morphisms of ringed
  topoi between the topoi of ringed sites.
* `Stacks.SheafOfModules.InternalHom.toposPullbackCompIso`: the comparison
  `(ψ ∘ φ)^* ≅ ψ^* ⋙ φ^*` of pullbacks of sheaves of modules for that composite.
* `Stacks.SheafOfModules.InternalHom.toposPullbackTensorIso`: the comparison of Stacks 03EL,
  spelled with `toposPullback` and with the sites of the two ringed sites.

## Main results

* `Stacks.SheafOfModules.InternalHom.sheafTensor_obj_map_comp_sheafTensor_map_app`: tensoring a
  morphism into the second variable and then one into the first is the action of the tensor
  bifunctor on the pair.
* `Stacks.SheafOfModules.InternalHom.pullbackTensorIso_inv_app_toposCompHom`: the composition
  law of Stacks 03EL on the inverse comparison, at a composite of morphisms of ringed topoi.
* `Stacks.SheafOfModules.InternalHom.tensorEvaluation_comp_internalHomPre_comp_map`:
  tensoring and evaluating past a comparison in the first variable and a functorial action in
  the second at once.
* `Stacks.SheafOfModules.InternalHom.sheafTensor_map_app_comp_sheafTensor_obj_map`: the two
  one-variable actions of the curried tensor product commute.
* `Stacks.SheafOfModules.InternalHom.reassoc_of_comp_three` and
  `Stacks.SheafOfModules.InternalHom.comp_comp_of_comp_eq_id`: reassociation past a three-fold
  identity, and cancellation of a composable pair composing to the identity, in a category.
* `Stacks.SheafOfModules.InternalHom.toposPullback_tensorEvaluation_assoc`: the pullback of a
  tensor--evaluation composite, with a fourth morphism after it.
* `Stacks.SheafOfModules.InternalHom.toposPullbackCompIso_inv_app_naturality`: the comparison of
  pullbacks is natural past a morphism into the middle pullback.
* `Stacks.SheafOfModules.InternalHom.tensorSheafBifunctor_map_toposPullbackCompIso_hom_comp_inv`:
  the tensor product of two components of the comparison of pullbacks is invertible, with the
  tensor product of the two inverse components as its inverse.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)

namespace Stacks.SheafOfModules.InternalHom

universe u

section TensorBridge

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})

/-- Tensoring a morphism `b` into the second variable and then a morphism `a` into the first is
the functorial action of the tensor bifunctor on the pair `(a, b)`. -/
theorem sheafTensor_obj_map_comp_sheafTensor_map_app
    {A A' B B' : SheafOfModules.{u} (Tensor.ringSheaf O)} (a : A ⟶ A') (b : B ⟶ B') :
    ((sheafTensor O).obj A).map b ≫ ((sheafTensor O).map a).app B' =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O))).map
        (Prod.mkHom a b) :=
  ((sheafTensor O).map a).naturality b

/-- **Tensoring and evaluating past a comparison in each variable at once.** Precomposing a
morphism `χ : A ⟶ Hom_O(F, H)` with the comparison `internalHomPre O c` in the first variable
and then with the functorial action of `Hom_O(F', -)` on `h : H ⟶ H'` tensors `c` into the
second factor and postcomposes `h`. -/
theorem tensorEvaluation_comp_internalHomPre_comp_map
    {A F F' H H' : SheafOfModules.{u} (Tensor.ringSheaf O)}
    (χ : A ⟶ (internalHomSecondFunctor J O F).obj H) (c : F' ⟶ F) (h : H ⟶ H') :
    tensorEvaluation O F' H'
        (χ ≫ (internalHomPre O c).app H ≫ (internalHomSecondFunctor J O F').map h) =
      ((sheafTensor O).obj A).map c ≫ tensorEvaluation O F H χ ≫ h := by
  rw [← Category.assoc, tensorEvaluation_comp_internalHomSecondFunctor_map O h
      (χ ≫ (internalHomPre O c).app H),
    tensorEvaluation_comp_internalHomPre O c χ, Category.assoc]

/-- The two one-variable functorial actions of the curried tensor product commute: tensoring a
morphism into the first variable and then one into the second is the same as doing it the other
way round. -/
@[reassoc]
theorem sheafTensor_map_app_comp_sheafTensor_obj_map
    {A A' B B' : SheafOfModules.{u} (Tensor.ringSheaf O)} (a : A ⟶ A') (b : B ⟶ B') :
    ((sheafTensor O).map a).app B ≫ ((sheafTensor O).obj A').map b =
      ((sheafTensor O).obj A).map b ≫ ((sheafTensor O).map a).app B' :=
  (((sheafTensor O).map a).naturality b).symm

end TensorBridge

section Reassociation

variable {D : Type*} [Category* D]

/-- Reassociation past a three-fold identity: from `f ≫ g ≫ h = f' ≫ g'` conclude
`f ≫ g ≫ h ≫ k = f' ≫ g' ≫ k`. -/
theorem reassoc_of_comp_three {a b c d b' w : D} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
    {f' : a ⟶ b'} {g' : b' ⟶ d} (H : f ≫ g ≫ h = f' ≫ g') (k : d ⟶ w) :
    f ≫ g ≫ h ≫ k = f' ≫ g' ≫ k :=
  (reassoc_of% H) k

/-- Cancelling a composable pair that composes to the identity, in front of a third morphism:
from `f ≫ g = 𝟙 a` conclude `f ≫ g ≫ k = k`. -/
theorem comp_comp_of_comp_eq_id {a b c : D} {f : a ⟶ b} {g : b ⟶ a} (hfg : f ≫ g = 𝟙 a)
    (k : a ⟶ c) : f ≫ g ≫ k = k :=
  (reassoc_of% hfg) k

end Reassociation

section ToposPullbackCalculus

variable {X Y : RingedSite.{u, u, u}}
  (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))

/-- `Stacks.SheafOfModules.InternalHom.toposPullback_tensorEvaluation` with a fourth morphism
`k` after it: tensoring `φ^* a` into the first variable, then `toposPullbackEvaluation φ F' G'`
and then `k` is the inverse comparison of Stacks 03EL, then the pullback of
`tensorEvaluation Y.O F' G' a` and then `k`. -/
theorem toposPullback_tensorEvaluation_assoc
    {A F' G' : SheafOfModules.{u} (Tensor.ringSheaf Y.O)}
    (a : A ⟶ (internalHomSecondFunctor Y.J Y.O F').obj G')
    {W : SheafOfModules.{u} (Tensor.ringSheaf X.O)}
    (k : (toposPullback φ).obj G' ⟶ W) :
    ((sheafTensor X.O).map ((toposPullback φ).map a)).app ((toposPullback φ).obj F') ≫
        toposPullbackEvaluation φ F' G' ≫ k =
      (pullbackTensorIso φ.toModulesHom).inv.app (A, F') ≫
        (toposPullback φ).map (tensorEvaluation Y.O F' G' a) ≫ k :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ k) (toposPullback_tensorEvaluation φ a)).trans
      (Category.assoc _ _ _))

end ToposPullbackCalculus

section Comp

variable {X Y Z : RingedSite.{u, u, u}}

/-- The composite `ψ ∘ φ` of two morphisms of ringed topoi between the topoi of ringed sites. -/
abbrev toposCompHom
    (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
    (ψ : RingedToposHom (RingedSite.ringedTopos Y) (RingedSite.ringedTopos Z)) :
    RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Z) :=
  AlgebraicGeometry.RingedToposHom.comp
    (X := RingedSite.ringedTopos X) (Y := RingedSite.ringedTopos Y)
    (Z := RingedSite.ringedTopos Z) ψ φ

variable (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
  (ψ : RingedToposHom (RingedSite.ringedTopos Y) (RingedSite.ringedTopos Z))

/-- The comparison `(ψ ∘ φ)^* ≅ ψ^* ⋙ φ^*` of pullbacks of sheaves of modules along a
composite of morphisms of ringed topoi. -/
abbrev toposPullbackCompIso :
    toposPullback (toposCompHom φ ψ) ≅ toposPullback ψ ⋙ toposPullback φ :=
  Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom
    (toposCompHom φ ψ).toModulesHom (RingedToposHom.toModulesHomPushforwardIso φ ψ)
    (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)

/-- **Stacks 03EL for a morphism of ringed topoi between the topoi of two ringed sites.** The
comparison `φ^*(F ⊗_{O_Y} G) ≅ φ^*F ⊗_{O_X} φ^*G` of `Stacks.SheafOfModules.pullbackTensorIso`,
read with `toposPullback` and with the sites and structure sheaves of the two ringed sites in
place of those of the ringed topoi they determine. -/
def toposPullbackTensorIso
    (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
        toposPullback φ ≅
      Functor.prod (toposPullback φ) (toposPullback φ) ⋙
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)) :=
  pullbackTensorIso φ.toModulesHom

/-- **The composition law of Stacks 03EL on the inverse comparison, at a composite.**
Undoing `φ`'s comparison, then `φ^*` of `ψ`'s, then the comparison of pullbacks at
`F ⊗_{O_Z} G`, is the tensor product of the two inverse comparisons of pullbacks followed by
undoing the comparison of the composite `ψ ∘ φ`. -/
theorem pullbackTensorIso_inv_app_toposCompHom
    (F G : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    (pullbackTensorIso φ.toModulesHom).inv.app
          ((ψ.toModulesHom.pullbackModules).obj F,
            (ψ.toModulesHom.pullbackModules).obj G) ≫
        (φ.toModulesHom.pullbackModules).map
            ((pullbackTensorIso ψ.toModulesHom).inv.app (F, G)) ≫
          (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ.toModulesHom
              ψ.toModulesHom (toposCompHom φ ψ).toModulesHom
              (RingedToposHom.toModulesHomPushforwardIso φ ψ)
              (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)).inv.app
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (((Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ.toModulesHom
                ψ.toModulesHom (toposCompHom φ ψ).toModulesHom
                (RingedToposHom.toModulesHomPushforwardIso φ ψ)
                (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)).inv.app F,
            (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ.toModulesHom
                ψ.toModulesHom (toposCompHom φ ψ).toModulesHom
                (RingedToposHom.toModulesHomPushforwardIso φ ψ)
                (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)).inv.app G) :
            (((φ.toModulesHom.pullbackModules).obj
                ((ψ.toModulesHom.pullbackModules).obj F),
              (φ.toModulesHom.pullbackModules).obj
                ((ψ.toModulesHom.pullbackModules).obj G)) :
              SheafOfModules.{u} (Tensor.ringSheaf X.O) ×
                SheafOfModules.{u} (Tensor.ringSheaf X.O)) ⟶
            (((toposCompHom φ ψ).toModulesHom.pullbackModules).obj F,
              ((toposCompHom φ ψ).toModulesHom.pullbackModules).obj G)) ≫
        (pullbackTensorIso (toposCompHom φ ψ).toModulesHom).inv.app (F, G) :=
  pullbackTensorIso_inv_app_comp φ.toModulesHom ψ.toModulesHom
    (toposCompHom φ ψ).toModulesHom
    (RingedToposHom.toModulesHomPushforwardIso φ ψ)
    (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ) F G

/-- **The comparison of pullbacks is natural, past a morphism into the middle pullback.**
Pulling back `p ≫ ψ^*h` along `φ` and then comparing with the pullback along the composite is
the pullback of `p` followed by the comparison and the pullback of `h` along the composite. -/
theorem toposPullbackCompIso_inv_app_naturality
    {A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O)}
    {W : SheafOfModules.{u} (Tensor.ringSheaf Y.O)}
    (p : W ⟶ (toposPullback ψ).obj A) (h : A ⟶ B) :
    (toposPullback φ).map (p ≫ (toposPullback ψ).map h) ≫
        (toposPullbackCompIso φ ψ).inv.app B =
      (toposPullback φ).map p ≫ (toposPullbackCompIso φ ψ).inv.app A ≫
        (toposPullback (toposCompHom φ ψ)).map h :=
  (congrArg (fun z ↦ z ≫ (toposPullbackCompIso φ ψ).inv.app B)
      ((toposPullback φ).map_comp p ((toposPullback ψ).map h))).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ (toposPullback φ).map p ≫ z)
        ((toposPullbackCompIso φ ψ).inv.naturality h)))

/-- The tensor product of two components of the comparison of pullbacks, followed by the tensor
product of the two inverse components, is the identity. -/
theorem tensorSheafBifunctor_map_toposPullbackCompIso_hom_comp_inv
    (A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (Prod.mkHom ((toposPullbackCompIso φ ψ).hom.app A)
            ((toposPullbackCompIso φ ψ).hom.app B)) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (Prod.mkHom ((toposPullbackCompIso φ ψ).inv.app A)
            ((toposPullbackCompIso φ ψ).inv.app B)) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp]
  refine Eq.trans (congrArg _ ?_) (CategoryTheory.Functor.map_id _ _)
  exact Prod.hom_ext ((toposPullbackCompIso φ ψ).hom_inv_id_app A)
    ((toposPullbackCompIso φ ψ).hom_inv_id_app B)

end Comp

end Stacks.SheafOfModules.InternalHom

end
