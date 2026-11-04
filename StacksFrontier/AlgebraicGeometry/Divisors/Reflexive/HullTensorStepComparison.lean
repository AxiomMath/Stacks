module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineMulSectionTilde
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneTensorMonoid
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowers
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLeftUnitorSections

/-!
# Multiplication by a section, for the hull tensor product and for the sheaf tensor product

The transition maps of the system `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯` of [Stacks, Tag 0EBN] are
multiplication by a global section of `ℱ`, and that multiplication has two descriptions in this
library:

* `Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom`, directly on `𝒪_X`-modules: insert
  the unit and whisker, `𝒢 ⟶ 𝒪_X ⊗ 𝒢 ⟶ ℱ ⊗ 𝒢`, followed by the canonical map to the reflexive
  hull;
* in the category of coherent reflexive modules, where the hull tensor product
  `ℱ ⊗_𝒞 𝒢 = (ℱ ⊗_{𝒪_X} 𝒢)^{∨∨}` of [Stacks, Tag 0EBH] is a monoidal product in its own right:
  the left unit constraint `AlgebraicGeometry.CoherentReflexive.unitTensorObj` followed by the
  hull of the functoriality of the ordinary tensor product.

The two are the same morphism (`hullMulSection_hom_hom`).

## Main results

* `Stacks.SheafOfModules.tensorProductBraiding_unit_comp_rightUnitor`: the symmetry constraint
  of the sheaf tensor product followed by its right unit constraint is its left unit constraint.
* `Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom_eq_rightUnitor_inv_comp`: in the
  ordinary tensor product, inserting the unit on the right, exchanging the factors and then
  applying a morphism `σ : 𝒪_X ⟶ ℱ` to the first factor is `mulSectionHom σ`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom_comp_tensorSheafMap`: multiplication
  by a section is natural in the module it multiplies, in the `tensorSheafMap` spelling.
* `Stacks.AlgebraicGeometry.ReflexivePowers.hullMulSection_hom_hom`: the underlying morphism of
  `𝒪_X`-modules of the hull-tensor description of multiplication by a section is
  `mulSectionHom σ` followed by the canonical map to the reflexive hull.
* `Stacks.AlgebraicGeometry.ReflexivePowers.hullMulSection_comp_doubleDualMap`: multiplying by
  `σ` in the coherent reflexive modules and transporting along the hull of `𝟙 ⊗ e` is
  transporting along `e`, multiplying by `σ` and mapping to the reflexive hull, for an arbitrary
  morphism `e`.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

universe v u w

namespace Stacks.SheafOfModules

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

attribute [local instance_reducible] TensorSheafification.structureSheaf
  CategoryTheory.LocalizedMonoidal CategoryTheory.Localization.Monoidal.toMonoidalCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The symmetry constraint followed by the right unit constraint is the left unit
constraint**, for the fixed constraints of the tensor product sheaf of [Stacks, Tag 05NA]. -/
theorem tensorProductBraiding_unit_comp_rightUnitor
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (Invertible.tensorProductBraiding O hO
          (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) M).hom ≫
        (Invertible.tensorProductRightUnitor O hO M).hom =
      (Invertible.tensorProductLeftUnitor O hO M).hom := by
  let := sheafTensorStruct O hO
  let := sheafTensorMonoidal O hO
  let := sheafTensorSymmetric O hO
  exact braiding_rightUnitor M

end Stacks.SheafOfModules

namespace Stacks.AlgebraicGeometry.ReflexivePowers

open Stacks.SheafOfModules.TensorStalkRingedSpace
  (toTensorSheafSection tensorSheafMap_app_toTensorSheafSection)

attribute [local instance_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.sheafify
  _root_.SheafOfModules.forget _root_.PresheafOfModules.restrictScalars
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  structureSheafRing AlgebraicGeometry.Scheme.Modules TopCat.Sheaf
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

variable (Y : AlgebraicGeometry.RingedSpace.{u, u})

/-! ### The left unit constraint, as the symmetry followed by the right unit -/

/-- **The inverse of the left unit constraint of the sheaf tensor product**, in the fixed
spellings: insert the unit on the right and exchange the factors. -/
theorem leftUnitor_inv_eq_rightUnitor_inv_comp_braiding_inv
    (A : SheafOfModules.{u} (structureSheafRing Y)) :
    (λ_ A).inv =
      (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor Y.presheaf
          (structureSheafRing Y).property A).inv ≫
        (Stacks.SheafOfModules.Invertible.tensorProductBraiding Y.presheaf
          (structureSheafRing Y).property
          (SheafOfModules.unit (structureSheafRing Y)) A).inv := by
  have h : (λ_ A) =
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding Y.presheaf
          (structureSheafRing Y).property
          (SheafOfModules.unit (structureSheafRing Y)) A) ≪≫
        (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor Y.presheaf
          (structureSheafRing Y).property A) :=
    Iso.ext <| (Stacks.SheafOfModules.monoidal_leftUnitor Y A).trans
      (Stacks.SheafOfModules.tensorProductBraiding_unit_comp_rightUnitor Y.presheaf
        (structureSheafRing Y).property A).symm
  exact congrArg Iso.inv h

/-! ### Multiplication by a section, in the fixed spellings -/

/-- Whiskering on the right is the functoriality `tensorSheafMap` of the tensor product sheaf
with the identity in the second variable. -/
theorem whiskerRight_eq_tensorSheafMap {F F' : SheafOfModules.{u} (structureSheafRing Y)}
    (f : F ⟶ F') (A : SheafOfModules.{u} (structureSheafRing Y)) :
    f ▷ A = ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map ((f, (𝟙 A)) : (F, A) ⟶ (F', A))) := by
  rw [← MonoidalCategory.tensorHom_id]
  exact Stacks.SheafOfModules.OnSpace.tensor_hom_ext Y fun U a b =>
    (Stacks.SheafOfModules.OnSpace.tensorHom_tmul Y f (𝟙 A) U a b).trans
      (tensorSheafMap_app_toTensorSheafSection Y _ A _ A f (𝟙 A) U.unop a b).symm

/-- **Multiplication by a section, read through the right unit and the symmetry.**  Inserting
the unit on the right, exchanging the factors and applying `σ : 𝒪_X ⟶ ℱ` to the first factor is
`mulSectionHom σ`. -/
theorem mulSectionHom_eq_rightUnitor_inv_comp
    {F : SheafOfModules.{u} (structureSheafRing Y)}
    (A : SheafOfModules.{u} (structureSheafRing Y))
    (σ : 𝟙_ (SheafOfModules.{u} (structureSheafRing Y)) ⟶ F) :
    mulSectionHom Y (G := A) σ =
      (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor Y.presheaf
          (structureSheafRing Y).property A).inv ≫
        (Stacks.SheafOfModules.Invertible.tensorProductBraiding Y.presheaf
            (structureSheafRing Y).property
            (SheafOfModules.unit (structureSheafRing Y)) A).inv ≫
          (show (𝟙_ (SheafOfModules.{u} (structureSheafRing Y))) ⊗ A ⟶ F ⊗ A from
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨Y.presheaf, Y.IsSheaf⟩)).map
                (X := (𝟙_ (SheafOfModules.{u} (structureSheafRing Y)), A)) (Y := (F, A))
                ((σ, 𝟙 A) : (𝟙_ (SheafOfModules.{u} (structureSheafRing Y)), A) ⟶
                  (F, A))) :=
  (congrArg₂ (· ≫ ·) (leftUnitor_inv_eq_rightUnitor_inv_comp_braiding_inv Y A)
    (whiskerRight_eq_tensorSheafMap Y σ A)).trans (Category.assoc _ _ _)

/-- Whiskering on the left is the functoriality `tensorSheafMap` of the tensor product sheaf
with the identity in the first variable. -/
theorem whiskerLeft_eq_tensorSheafMap (F : SheafOfModules.{u} (structureSheafRing Y))
    {A A' : SheafOfModules.{u} (structureSheafRing Y)} (g : A ⟶ A') :
    F ◁ g = ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 F), g) : (F, A) ⟶ (F, A'))) := by
  rw [← MonoidalCategory.id_tensorHom]
  exact Stacks.SheafOfModules.OnSpace.tensor_hom_ext Y fun U a b =>
    (Stacks.SheafOfModules.OnSpace.tensorHom_tmul Y (𝟙 F) g U a b).trans
      (tensorSheafMap_app_toTensorSheafSection Y F A F A' (𝟙 F) g U.unop a b).symm

/-- `mulSectionHom_whiskerLeft` in the `tensorSheafMap` spelling of the functoriality of the
tensor product sheaf. -/
theorem mulSectionHom_comp_tensorSheafMap {F : SheafOfModules.{u} (structureSheafRing Y)}
    {A A' : SheafOfModules.{u} (structureSheafRing Y)}
    (σ : 𝟙_ (SheafOfModules.{u} (structureSheafRing Y)) ⟶ F) (g : A ⟶ A') :
    mulSectionHom Y (G := A) σ ≫
      (show F ⊗ A ⟶ F ⊗ A' from
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.presheaf, Y.IsSheaf⟩)).map (X := (F, A)) (Y := (F, A'))
            ((𝟙 F, g) : (F, A) ⟶ (F, A'))) =
      g ≫ mulSectionHom Y (G := A') σ :=
  (congrArg (fun k : F ⊗ A ⟶ F ⊗ A' => mulSectionHom Y (G := A) σ ≫ k)
    (whiskerLeft_eq_tensorSheafMap Y F g)).symm.trans (mulSectionHom_whiskerLeft Y σ g)

/-! ### Multiplication by a section in the category of coherent reflexive modules -/

section Hull

open AlgebraicGeometry.CoherentReflexive (ordinaryTensor tensorObj unitObj unitTensorObj)
open _root_.AlgebraicGeometry (hullReflection)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentModules CoherentReflexiveModules)
open Stacks.AlgebraicGeometry.ReflexiveModules (reflexiveHull toDoubleDual reflexiveHullFunctor)

variable {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
  [AlgebraicGeometry.IsLocallyNoetherian X]

/-- **Multiplication by a section, in the category of coherent reflexive modules, is
multiplication by that section followed by the canonical map to the reflexive hull.**

The left unit constraint of the hull tensor product of [Stacks, Tag 0EBH], followed by the hull
of a morphism `m` of ordinary tensor products which applies `σ : 𝒪_X ⟶ ℱ` to the first factor,
has as its underlying morphism of `𝒪_X`-modules exactly
`Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom σ` followed by
`Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual`. -/
theorem hullMulSection_hom_hom (F G : CoherentReflexiveModules X) (σ : unitObj X ⟶ F)
    (m : ordinaryTensor (unitObj X) G ⟶ ordinaryTensor F G)
    (hm : m.hom = ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map
      ((σ.hom.hom, (𝟙 G.obj.obj)) :
        ((unitObj X).obj.obj, G.obj.obj) ⟶ (F.obj.obj, G.obj.obj)))) :
    ((unitTensorObj G).inv ≫ (hullReflection X).map m).hom.hom =
      mulSectionHom X.toRingedSpace (G := G.obj.obj) σ.hom.hom ≫
        toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F.obj.obj)).obj
            (G.obj.obj))) := by
  have hexp : ((unitTensorObj G).inv ≫ (hullReflection X).map m).hom.hom =
      toDoubleDual G.obj.obj ≫
        (reflexiveHullFunctor X).map (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
            X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
            G.obj.obj).inv ≫
          (reflexiveHullFunctor X).map (Stacks.SheafOfModules.Invertible.tensorProductBraiding
              X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
              (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) G.obj.obj).inv ≫
            (reflexiveHullFunctor X).map m.hom :=
    rfl
  have hstep : (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
            X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
            G.obj.obj).inv ≫
        (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property
            (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) G.obj.obj).inv ≫
          m.hom =
      mulSectionHom X.toRingedSpace (G := G.obj.obj) σ.hom.hom := by
    rw [hm]
    exact (mulSectionHom_eq_rightUnitor_inv_comp X.toRingedSpace G.obj.obj σ.hom.hom).symm
  refine hexp.trans (Eq.trans ?_
    (Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual_naturality
      (F := G.obj.obj) (G := (ordinaryTensor F G).obj)
      (mulSectionHom X.toRingedSpace (G := G.obj.obj) σ.hom.hom)).symm)
  refine congrArg (fun k : (reflexiveHullFunctor X).obj G.obj.obj ⟶
      (reflexiveHullFunctor X).obj (ordinaryTensor F G).obj => toDoubleDual G.obj.obj ≫ k) ?_
  refine Eq.trans ?_ (congrArg (fun k : G.obj.obj ⟶ (ordinaryTensor F G).obj =>
    (reflexiveHullFunctor X).map k) hstep)
  refine Eq.trans ?_ ((reflexiveHullFunctor X).map_comp _ _).symm
  exact congrArg (fun k : (reflexiveHullFunctor X).obj (ordinaryTensor G (unitObj X)).obj ⟶
      (reflexiveHullFunctor X).obj (ordinaryTensor F G).obj =>
        (reflexiveHullFunctor X).map (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
            X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
            G.obj.obj).inv ≫ k)
    ((reflexiveHullFunctor X).map_comp _ _).symm

/-- **The transition square between the two reflexive power towers.**

With `ℱ` and `𝒢` coherent reflexive, `σ : 𝒪_X ⟶ ℱ` a global section and `e : 𝒢 ⟶ 𝒜` any
morphism of `𝒪_X`-modules: multiplying by `σ` in the category of coherent reflexive modules and
then transporting along the hull of `𝟙 ⊗ e` is transporting along `e` and then multiplying by
`σ` followed by the canonical map to the reflexive hull. -/
theorem hullMulSection_comp_doubleDualMap (F G : CoherentReflexiveModules X)
    (σ : unitObj X ⟶ F) (m : ordinaryTensor (unitObj X) G ⟶ ordinaryTensor F G)
    (hm : m.hom = ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map
      ((σ.hom.hom, (𝟙 G.obj.obj)) :
        ((unitObj X).obj.obj, G.obj.obj) ⟶ (F.obj.obj, G.obj.obj))))
    {A : AlgebraicGeometry.Scheme.Modules X} (e : G.obj.obj ⟶ A) :
    ((unitTensorObj G).inv ≫ (hullReflection X).map m).hom.hom ≫
        (reflexiveHullFunctor X).map
          (X := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F.obj.obj).obj G.obj.obj)
          (Y := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F.obj.obj).obj A)
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
              (X := (F.obj.obj, G.obj.obj)) (Y := (F.obj.obj, A))
              ((𝟙 F.obj.obj, e) : (F.obj.obj, G.obj.obj) ⟶ (F.obj.obj, A))) =
      e ≫ mulSectionHom X.toRingedSpace (G := A) σ.hom.hom ≫
        toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F.obj.obj)).obj
            (A))) :=
  (congrArg (· ≫ _) (hullMulSection_hom_hom F G σ m hm)).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
      (Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual_naturality _).symm).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _)
      (mulSectionHom_comp_tensorSheafMap X.toRingedSpace σ.hom.hom e)).trans
    (Category.assoc _ _ _)

end Hull

end Stacks.AlgebraicGeometry.ReflexivePowers

end
