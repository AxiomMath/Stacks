module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonId
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorConstructionsAgree
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartPullbackCotensorator
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalRightUnitorCompare
public import StacksFrontier.AlgebraicGeometry.SectionProduct.PullbackUnitSection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functoriality of the tensor product sheaf is the tensor product of morphisms

Three monoidal structures on the sheaves of modules over a ringed space `Z` occur in this
development, and they are not definitionally equal. Two of them localize the objectwise monoidal
structure on presheaves of modules along sheafification —
`Stacks.SheafInternalHom.monoidalCategory`, whose unit is the sheafification of the presheaf unit,
and `Stacks.SheafOfModules.monoidalCategory`, whose unit is `SheafOfModules.unit` — and the third,
`Stacks.PullbackGradedAlgebra.monoidalCategory`, is the first of those conjugated so that its
tensor product is the tensor product sheaf of [Stacks, Tag 01CA] and its unit is
`SheafOfModules.unit`, both on the nose. The coherences of [Stacks, Tag 01CD] are stated in the
third.

The objects of the first and the third are compared by
`Stacks.AmplePullbackPart1.tensorIsoTensorModules`, naturally against [Stacks, Tag 01CB]'s
functorial action `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap`. This file proves
that `tensorSheafMap` is the tensor product of morphisms of the third structure, so that a
statement proved in one of the two structures transfers to the other by conjugation, and carries
out that transfer for the compatibility of the identity law `(𝟙 Y)^* ≅ 𝟭`, the composition law
`f^* g^* ≅ (f ≫ g)^*`, the associator and the unitors with the cotensorator of
`Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackCotensorator` and the
structure-sheaf comparison `Stacks.PullbackUnitSection.unitPullbackHom`.

## Main results

* `Stacks.TensorSheafSpellingIso.tensorSheafMap_eq_tensorHom`, with
  `tensorSheafMap_id_right_eq_whiskerRight` and `tensorSheafMap_id_left_eq_whiskerLeft`: the
  functorial action of the tensor product sheaf of [Stacks, Tag 01CB] is the tensor product of
  morphisms, and its two whiskerings, of the monoidal structure of
  `Stacks.PullbackGradedAlgebra.monoidalCategory`.
* `Stacks.TensorSheafSpellingIso.unitPullbackHom_eq_pullbackUnitComparison`: the structure-sheaf
  comparison of [Stacks, Tag 01CD] read at the monoidal unit of
  `Stacks.SheafInternalHom.schemeMonoidalCategory` is
  `Stacks.PullbackTensorCoherence.pullbackUnitComparison`, conjugated by the comparison of the two
  unit objects.
* `Stacks.TensorSheafSpellingIso.tensorIsoTensorModules_naturality` and
  `tensorIsoTensorModules_inv_naturality`: naturality of the comparison of the two tensor products,
  in both directions.
* `Stacks.TensorSheafSpellingIso.isIso_pullbackCotensorator` and `pullbackCotensoratorIso`: the
  cotensorator of an inverse image is invertible, i.e. `j^*(A ⊗ B) ≅ j^*A ⊗ j^*B` for the monoidal
  structure the tensor powers are read in, for an arbitrary morphism of schemes `j`.
* `Stacks.TensorSheafSpellingIso.pullbackCotensorator_comp_tensorIso`: the cotensorator against the
  comparison of the two tensor products is the comparison of [Stacks, Tag 01CD].
* `Stacks.TensorSheafSpellingIso.pullbackCotensorator_id` and `pullbackIdIso_hom_app_tensorUnit`:
  the identity law for the pullback of sheaves of modules is compatible with the cotensorator and
  with the comparison at the unit, in the monoidal structure the tensor powers are read in.
* `Stacks.TensorSheafSpellingIso.pullbackCotensorator_comp`: the composition law for the pullback
  of sheaves of modules is compatible with the cotensorator, in the same structure.
* `Stacks.TensorSheafSpellingIso.tensorModulesAssociator` and `tensorModulesAssociator_hom_eq`: the
  associativity constraint of the tensor product sheaf, at the scheme spelling, and the
  identification of it with the monoidal associator conjugated by the comparison of the two tensor
  products.
* `Stacks.TensorSheafSpellingIso.associator_hom_tensorIsoTensorModules`: that identification
  written without inverses.
* `Stacks.TensorSheafSpellingIso.pullbackTensorModules_assoc`: the comparison of [Stacks, Tag 01CD]
  is compatible with the associativity constraint of the tensor product sheaf, in the
  `tensorModules` spelling.
* `Stacks.TensorSheafSpellingIso.pullbackCotensorator_assoc`: the cotensorator of an inverse image
  is compatible with the associator, in the monoidal structure the tensor powers are read in.
* `Stacks.TensorSheafSpellingIso.tensorModulesLeftUnitor` and `tensorModulesRightUnitor`: the two
  unit constraints of the tensor product sheaf, at the scheme spelling, with
  `leftUnitor_hom_tensorIsoTensorModules` and `rightUnitor_hom_tensorIsoTensorModules` identifying
  them with the monoidal unitors conjugated by the comparison of the two tensor products and of the
  two unit objects, and `leftUnitor_hom_eq_tensorModulesLeftUnitor` and
  `rightUnitor_hom_eq_tensorModulesRightUnitor` those identifications written without inverses.
* `Stacks.TensorSheafSpellingIso.unitComparisonPullback`: the structure-sheaf comparison of
  [Stacks, Tag 01CD] at the scheme spellings, and `unitPullbackHom_comp_unitComparison`, which is
  `unitPullbackHom_eq_pullbackUnitComparison` rearranged so that the two unit comparisons meet.
* `Stacks.TensorSheafSpellingIso.pullbackTensorModules_leftUnitor` and
  `pullbackTensorModules_rightUnitor`: the comparison of [Stacks, Tag 01CD] is compatible with the
  two unit constraints of the tensor product sheaf, in the `tensorModules` spelling.
* `Stacks.TensorSheafSpellingIso.pullbackCotensorator_leftUnitor` and
  `pullbackCotensorator_rightUnitor`: the cotensorator of an inverse image is compatible with the
  two unitors, in the monoidal structure the tensor powers are read in. With
  `pullbackCotensorator_assoc` these are the three coherences of the oplax monoidal structure on
  `j^*` for that structure, the oplax unit morphism being
  `Stacks.PullbackUnitSection.unitPullbackHom`.

## Implementation notes

A term in which an argument of type `AlgebraicGeometry.Scheme.Modules` stands where a sheaf of
modules over a differently-spelled sheaf of rings is expected is not type-correct at the
transparency the rewriting tactics check their motives at, so every `rw` in a goal containing it
fails, reporting a missing pattern, even where `rfl` closes the goal. The statements below are
therefore written with `Stacks.RelativeVeryAmple.tensorModules`,
`Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.tensorModulesMap` and
`Stacks.AmplePullbackPart1.tensorIsoTensorModules` rather than with the tensor product sheaf
applied to `Scheme.Modules` arguments, and the definitional equality is crossed once, inside a
proof given by `:=` or `exact`.

`Stacks.SheafOfModules.Strict.associator_eq` is stated with `Stacks.SheafOfModules.tensorObjIso`
rather than with `Stacks.AmplePullbackPart1.tensorIsoTensorModules`. The two are the same
isomorphism, but the equality is too expensive to re-check at every occurrence, so it is crossed
once, in `tensorIsoTensorModules_eq`, and rewritten with afterwards.

In the unitor coherences the two whiskered unit comparisons meet inside one composite, and a goal
naming both unit objects at once is not type-correct at that transparency either, so the
rebracketing cannot be done by `rw` or `simp`. It is done by `whiskerRight_comp_cancel₂`,
`whiskerLeft_comp_cancel₂`, `comp_comp_of_eq` and `comp_comp_inv_comp`, the same computations
stated in an abstract monoidal category with every object a variable; and `unitComparisonPullback`
names [Stacks, Tag 01CD]'s structure-sheaf comparison again at the scheme spellings, without which
a whiskering by it is elaborated in the ringed-space spelling of the category, where there is no
monoidal structure.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB) — the tensor product of
  sheaves of modules on a ringed space, and its functoriality.
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace

universe u

namespace Stacks.TensorSheafSpellingIso

/-! ### The functorial action of the tensor product sheaf, as a tensor product of morphisms -/

section Strict

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable (Z : RingedSpace.{u, u})

/-- The functorial action of the tensor product sheaf of [Stacks, Tag 01CB] is the tensor product
of morphisms of the monoidal structure of `Stacks.PullbackGradedAlgebra.monoidalCategory`. -/
theorem tensorSheafMap_eq_tensorHom
    {A A' B B' : SheafOfModules.{u} (structureRingSheaf Z)} (f : A ⟶ A') (g : B ⟶ B') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.presheaf, Z.IsSheaf⟩)).map (X := (A, B)) (Y := (A', B')) (f, g)
      = f ⊗ₘ g :=
  (Stacks.TensorSheafDedup.tensorSheafMap_eq_sheafifyMap Z f g).trans
    (Stacks.SheafOfModules.tensorHom_eq_sheafify_map Z.presheaf
      (structureSheafRing Z).property f g).symm

/-- The functorial action of the tensor product sheaf in its first argument alone is the right
whiskering. -/
theorem tensorSheafMap_id_right_eq_whiskerRight
    {A A' : SheafOfModules.{u} (structureRingSheaf Z)} (f : A ⟶ A')
    (B : SheafOfModules.{u} (structureRingSheaf Z)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.presheaf, Z.IsSheaf⟩)).map (X := (A, B)) (Y := (A', B)) (f, 𝟙 B)
      = f ▷ B :=
  (tensorSheafMap_eq_tensorHom Z f (𝟙 B)).trans (MonoidalCategory.tensorHom_id f B)

/-- The functorial action of the tensor product sheaf in its second argument alone is the left
whiskering. -/
theorem tensorSheafMap_id_left_eq_whiskerLeft
    (A : SheafOfModules.{u} (structureRingSheaf Z))
    {B B' : SheafOfModules.{u} (structureRingSheaf Z)} (g : B ⟶ B') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.presheaf, Z.IsSheaf⟩)).map (X := (A, B)) (Y := (A, B')) (𝟙 A, g)
      = A ◁ g :=
  (tensorSheafMap_eq_tensorHom Z (𝟙 A) g).trans (MonoidalCategory.id_tensorHom A g)

/-- The functorial action of the tensor product sheaf in its second argument alone is functorial.
-/
theorem tensorSheafMap_id_left_comp (A : SheafOfModules.{u} (structureRingSheaf Z))
    {B B' B'' : SheafOfModules.{u} (structureRingSheaf Z)} (g : B ⟶ B') (g' : B' ⟶ B'') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Z.presheaf, Z.IsSheaf⟩)).map (X := (A, B)) (Y := (A, B')) (𝟙 A, g) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Z.presheaf, Z.IsSheaf⟩)).map (X := (A, B')) (Y := (A, B'')) (𝟙 A, g')
      = (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.presheaf, Z.IsSheaf⟩)).map (X := (A, B)) (Y := (A, B'')) (𝟙 A, g ≫ g') :=
  (congrArg₂ (· ≫ ·) (tensorSheafMap_id_left_eq_whiskerLeft Z A g)
      (tensorSheafMap_id_left_eq_whiskerLeft Z A g')).trans
    ((MonoidalCategory.whiskerLeft_comp A g g').symm.trans
      (tensorSheafMap_id_left_eq_whiskerLeft Z A (g ≫ g')).symm)

/-- The functorial action of the tensor product sheaf in its first argument alone is functorial.
-/
theorem tensorSheafMap_id_right_comp
    {A A' A'' : SheafOfModules.{u} (structureRingSheaf Z)} (f : A ⟶ A') (f' : A' ⟶ A'')
    (B : SheafOfModules.{u} (structureRingSheaf Z)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Z.presheaf, Z.IsSheaf⟩)).map (X := (A, B)) (Y := (A', B)) (f, 𝟙 B) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Z.presheaf, Z.IsSheaf⟩)).map (X := (A', B)) (Y := (A'', B)) (f', 𝟙 B)
      = (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.presheaf, Z.IsSheaf⟩)).map (X := (A, B)) (Y := (A'', B)) (f ≫ f', 𝟙 B) :=
  (congrArg₂ (· ≫ ·) (tensorSheafMap_id_right_eq_whiskerRight Z f B)
      (tensorSheafMap_id_right_eq_whiskerRight Z f' B)).trans
    ((MonoidalCategory.comp_whiskerRight f f' B).symm.trans
      (tensorSheafMap_id_right_eq_whiskerRight Z (f ≫ f') B).symm)

end Strict

/-! ### The consequences at a scheme -/

section Scheme

open Stacks.AmplePullbackPart1 (tensorIsoTensorModules)
open Stacks.RelativeVeryAmple (tensorModules)
open Stacks.SectionRingGeometric (unitComparison unitModule)
open Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator
  (tensorModulesMap pullbackTensorModules pullbackCotensorator pullbackCotensorator_eq
    pullbackTensorModules_naturality)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! #### The comparison of the two tensor products is natural -/

variable (Y : Scheme.{u})

/-- The comparison of the monoidal tensor product with the tensor product sheaf is natural in each
of its two variables. -/
theorem tensorIsoTensorModules_naturality {A A' B B' : Y.Modules} (f : A ⟶ A') (g : B ⟶ B') :
    (f ⊗ₘ g) ≫ (tensorIsoTensorModules Y A' B').hom
      = (tensorIsoTensorModules Y A B).hom ≫ tensorModulesMap Y f g :=
  monoidalTensorIso_naturality Y f g

/-- The same naturality read along the inverse comparison. -/
theorem tensorIsoTensorModules_inv_naturality {A A' B B' : Y.Modules} (f : A ⟶ A') (g : B ⟶ B') :
    (tensorIsoTensorModules Y A B).inv ≫ (f ⊗ₘ g)
      = tensorModulesMap Y f g ≫ (tensorIsoTensorModules Y A' B').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← tensorIsoTensorModules_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-! #### The cotensorator is invertible -/

variable {Y' : Scheme.{u}} (j : Y' ⟶ Y)

/-- The cotensorator of an inverse image is invertible. -/
@[ega "0 4.3.3" "special case"]
instance isIso_pullbackCotensorator (A B : Y.Modules) :
    IsIso (pullbackCotensorator j A B) := by
  rw [pullbackCotensorator_eq]
  infer_instance

/-- `j^*(A ⊗ B) ≅ j^*A ⊗ j^*B` for the monoidal structure the tensor powers
`Stacks.TensorPowers.natTensorPow` are read in: the cotensorator, which is invertible. -/
def pullbackCotensoratorIso (A B : Y.Modules) :
    (Scheme.Modules.pullback j).obj (A ⊗ B) ≅
      (Scheme.Modules.pullback j).obj A ⊗ (Scheme.Modules.pullback j).obj B :=
  asIso (pullbackCotensorator j A B)

/-- The cotensorator followed by the comparison of the two tensor products on the target is the
image under `j^*` of the comparison of the two tensor products followed by the comparison of
[Stacks, Tag 01CD]. -/
theorem pullbackCotensorator_comp_tensorIso (A B : Y.Modules) :
    pullbackCotensorator j A B ≫
        (tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj A)
          ((Scheme.Modules.pullback j).obj B)).hom
      = (Scheme.Modules.pullback j).map (tensorIsoTensorModules Y A B).hom ≫
        (pullbackTensorModules j A B).hom := by
  rw [pullbackCotensorator_eq, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! #### The comparison at the unit object -/

/-- The comparison `j^*𝒪_{Y'} ≅ 𝒪_Y` at the monoidal unit is the structure-sheaf comparison of
[Stacks, Tag 01CD], conjugated by the comparison `Stacks.SectionRingGeometric.unitComparison` of
the two unit objects. -/
theorem unitPullbackHom_eq_pullbackUnitComparison :
    Stacks.PullbackUnitSection.unitPullbackHom j =
      (Scheme.Modules.pullback j).map (unitComparison Y).hom ≫
        Stacks.PullbackTensorCoherence.pullbackUnitComparison j.toLRSHom.toShHom ≫
          (unitComparison Y').inv :=
  rfl

/-! #### The identity law -/

/-- The identity law for the pullback of sheaves of modules, `(𝟙 Y)^* ≅ 𝟭`, at the
`AlgebraicGeometry.Scheme.Modules.pullback` spelling of the inverse image:
`Stacks.PullbackTensorCoherence.pullbackIdIso`. -/
def pullbackIdIso : Scheme.Modules.pullback (𝟙 Y) ≅ 𝟭 Y.Modules :=
  Stacks.PullbackTensorCoherence.pullbackIdIso Y.toRingedSpace

/-- The identity law is compatible with the comparison of [Stacks, Tag 01CD], in the
`tensorModules` spelling of the tensor product sheaf. -/
theorem pullbackIdIso_hom_app_tensorModules (A B : Y.Modules) :
    (pullbackIdIso Y).hom.app (tensorModules Y A B)
      = (pullbackTensorModules (𝟙 Y) A B).hom ≫
        tensorModulesMap Y ((pullbackIdIso Y).hom.app A) ((pullbackIdIso Y).hom.app B) :=
  (Stacks.PullbackTensorCoherence.pullbackTensorComparison_id A B).trans
    (congrArg (fun z => Stacks.PullbackTensorCoherence.pullbackTensorComparison
        (𝟙 Y.toRingedSpace) A B ≫ z)
      (tensorSheafMap_eq_tensorHom Y.toRingedSpace ((pullbackIdIso Y).hom.app A)
        ((pullbackIdIso Y).hom.app B)).symm)

/-- The identity law for the pullback of sheaves of modules is compatible with the cotensorator, in
the monoidal structure the tensor powers are read in: the cotensorator of the identity, followed by
the identity law in each factor, is the identity law at the tensor product. -/
theorem pullbackCotensorator_id (A B : Y.Modules) :
    (pullbackIdIso Y).hom.app (A ⊗ B)
      = pullbackCotensorator (𝟙 Y) A B ≫
        ((pullbackIdIso Y).hom.app A ⊗ₘ (pullbackIdIso Y).hom.app B) := by
  rw [pullbackCotensorator_eq, Category.assoc, Category.assoc,
    tensorIsoTensorModules_inv_naturality,
    ← reassoc_of% (pullbackIdIso_hom_app_tensorModules Y A B), ← Category.assoc,
    (pullbackIdIso Y).hom.naturality (tensorIsoTensorModules Y A B).hom]
  simp

/-- The identity law is compatible with the comparison at the unit object: the comparison
`(𝟙 Y)^*𝒪_Y ⟶ 𝒪_Y` at the monoidal unit is the identity law there. -/
theorem pullbackIdIso_hom_app_tensorUnit :
    (pullbackIdIso Y).hom.app (𝟙_ Y.Modules)
      = Stacks.PullbackUnitSection.unitPullbackHom (𝟙 Y) :=
  have h : (pullbackIdIso Y).hom.app (unitModule Y)
      = Stacks.PullbackTensorCoherence.pullbackUnitComparison
          (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom (𝟙 Y))) :=
    Stacks.PullbackTensorCoherence.pullbackUnitComparison_id Y.toRingedSpace
  have key : (pullbackIdIso Y).hom.app (𝟙_ Y.Modules) ≫ (unitComparison Y).hom
      = (Scheme.Modules.pullback (𝟙 Y)).map (unitComparison Y).hom ≫
        Stacks.PullbackTensorCoherence.pullbackUnitComparison
          (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom (𝟙 Y))) :=
    ((pullbackIdIso Y).hom.naturality (unitComparison Y).hom).symm.trans
      (congrArg (fun z => (Scheme.Modules.pullback (𝟙 Y)).map (unitComparison Y).hom ≫ z) h)
  ((Iso.eq_comp_inv (unitComparison Y)).mpr key).trans (Category.assoc _ _ _)

/-! #### The composition law -/

section CompLaw

variable {W W' W'' : Scheme.{u}} (f : W ⟶ W') (g : W' ⟶ W'')

/-- The composition law for the pullback of sheaves of modules, `f^* g^* ≅ (f ≫ g)^*`, at the
`AlgebraicGeometry.Scheme.Modules.pullback` spelling of the inverse image. -/
def pullbackCompIso :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f
      ≅ Scheme.Modules.pullback (f ≫ g) :=
  Stacks.PullbackTensorCoherence.pullbackCompIso
    (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f))
    (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom g))

/-- The composition law is compatible with the comparison of [Stacks, Tag 01CD], in the
`tensorModules` spelling of the tensor product sheaf. -/
theorem pullbackCompIso_hom_app_tensorModules (A B : W''.Modules) :
    (pullbackCompIso f g).hom.app (tensorModules W'' A B) ≫
        (pullbackTensorModules (f ≫ g) A B).hom
      = (Scheme.Modules.pullback f).map (pullbackTensorModules g A B).hom ≫
        (pullbackTensorModules f ((Scheme.Modules.pullback g).obj A)
            ((Scheme.Modules.pullback g).obj B)).hom ≫
          tensorModulesMap W ((pullbackCompIso f g).hom.app A)
            ((pullbackCompIso f g).hom.app B) :=
  (Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp
      (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f))
      (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom g)) A B).trans
    (congrArg (fun z => (Scheme.Modules.pullback f).map
        (Stacks.PullbackTensorCoherence.pullbackTensorComparison
          (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom g)) A B) ≫
        Stacks.PullbackTensorCoherence.pullbackTensorComparison
          (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f))
          ((Scheme.Modules.pullback g).obj A) ((Scheme.Modules.pullback g).obj B) ≫ z)
      (tensorSheafMap_eq_tensorHom W.toRingedSpace ((pullbackCompIso f g).hom.app A)
        ((pullbackCompIso f g).hom.app B)).symm)

/-- The composition law for the pullback of sheaves of modules is compatible with the cotensorator,
in the monoidal structure the tensor powers are read in: the cotensorator of a composite is the two
cotensorators in turn, followed by the composition law in each factor. -/
theorem pullbackCotensorator_comp (A B : W''.Modules) :
    (pullbackCompIso f g).hom.app (A ⊗ B) ≫ pullbackCotensorator (f ≫ g) A B
      = (Scheme.Modules.pullback f).map (pullbackCotensorator g A B) ≫
        pullbackCotensorator f ((Scheme.Modules.pullback g).obj A)
            ((Scheme.Modules.pullback g).obj B) ≫
          ((pullbackCompIso f g).hom.app A ⊗ₘ (pullbackCompIso f g).hom.app B) := by
  rw [← cancel_mono (tensorIsoTensorModules W ((Scheme.Modules.pullback (f ≫ g)).obj A)
      ((Scheme.Modules.pullback (f ≫ g)).obj B)).hom,
    Category.assoc, Category.assoc, Category.assoc,
    pullbackCotensorator_comp_tensorIso, tensorIsoTensorModules_naturality,
    reassoc_of% (pullbackCotensorator_comp_tensorIso W' f
      ((Scheme.Modules.pullback g).obj A) ((Scheme.Modules.pullback g).obj B)),
    ← Functor.map_comp_assoc, pullbackCotensorator_comp_tensorIso, Functor.map_comp_assoc,
    ← reassoc_of% ((pullbackCompIso f g).hom.naturality (tensorIsoTensorModules W'' A B).hom),
    pullbackCompIso_hom_app_tensorModules]

end CompLaw

/-! #### The associator -/

section AssocLaw

/-- The functorial action of the tensor product sheaf in its second argument alone is functorial,
at the scheme spelling. -/
theorem tensorModulesMap_id_left_comp (Z : Scheme.{u}) (A : Z.Modules)
    {B B' B'' : Z.Modules} (g : B ⟶ B') (g' : B' ⟶ B'') :
    tensorModulesMap Z (𝟙 A) g ≫ tensorModulesMap Z (𝟙 A) g'
      = tensorModulesMap Z (𝟙 A) (g ≫ g') :=
  tensorSheafMap_id_left_comp Z.toRingedSpace A g g'

/-- The functorial action of the tensor product sheaf in its first argument alone is functorial,
at the scheme spelling. -/
theorem tensorModulesMap_id_right_comp (Z : Scheme.{u})
    {A A' A'' : Z.Modules} (f : A ⟶ A') (f' : A' ⟶ A'') (B : Z.Modules) :
    tensorModulesMap Z f (𝟙 B) ≫ tensorModulesMap Z f' (𝟙 B)
      = tensorModulesMap Z (f ≫ f') (𝟙 B) :=
  tensorSheafMap_id_right_comp Z.toRingedSpace f f' B

/-- The functorial action on a pair of isomorphisms, as an isomorphism. -/
theorem tensorModulesMapIso_hom (Z : Scheme.{u}) {A A' B B' : Z.Modules} (e : A ≅ A')
    (g : B ≅ B') :
    (Stacks.RelativeVeryAmple.tensorModulesMapIso Z e g).hom = tensorModulesMap Z e.hom g.hom :=
  rfl

/-- The associator of the tensor product sheaf of [Stacks, Tag 01CA], at the scheme spelling: the
associator of the monoidal structure of `Stacks.PullbackGradedAlgebra.monoidalCategory`. -/
def tensorModulesAssociator (Z : Scheme.{u}) (A B C : Z.Modules) :
    tensorModules Z (tensorModules Z A B) C ≅ tensorModules Z A (tensorModules Z B C) :=
  @MonoidalCategoryStruct.associator _ _
    (Stacks.PullbackGradedAlgebra.monoidalCategory Z.toRingedSpace).toMonoidalCategoryStruct
    A B C

/-- The comparison of the monoidal tensor product with the tensor product sheaf is
`Stacks.SheafOfModules.tensorObjIso`, the spelling in which the structural morphisms of the tensor
product sheaf are compared with the monoidal ones. -/
theorem tensorIsoTensorModules_eq (A B : Y.Modules) :
    tensorIsoTensorModules Y A B
      = Stacks.SheafOfModules.tensorObjIso Y.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B :=
  Iso.ext rfl

/-- The associator of the tensor product sheaf is the monoidal associator conjugated by the
comparison of the two tensor products. -/
theorem tensorModulesAssociator_hom_eq (A B C : Y.Modules) :
    (tensorModulesAssociator Y A B C).hom
      = ((tensorIsoTensorModules Y (tensorModules Y A B) C).inv ≫
          ((tensorIsoTensorModules Y A B).inv ⊗ₘ 𝟙 C)) ≫
        ((α_ A B C).hom ≫
          ((𝟙 A ⊗ₘ (tensorIsoTensorModules Y B C).hom) ≫
            (tensorIsoTensorModules Y A (tensorModules Y B C)).hom)) := by
  rw [tensorIsoTensorModules_eq Y (tensorModules Y A B) C, tensorIsoTensorModules_eq Y A B,
    tensorIsoTensorModules_eq Y B C, tensorIsoTensorModules_eq Y A (tensorModules Y B C)]
  exact congrArg Iso.hom (Stacks.SheafOfModules.Strict.associator_eq Y.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B C)

/-- The monoidal associator and the associator of the tensor product sheaf agree across the
comparison of the two tensor products. -/
theorem associator_hom_tensorIsoTensorModules (A B C : Y.Modules) :
    (α_ A B C).hom ≫ (tensorIsoTensorModules Y A (B ⊗ C)).hom ≫
        tensorModulesMap Y (𝟙 A) (tensorIsoTensorModules Y B C).hom
      = (tensorIsoTensorModules Y (A ⊗ B) C).hom ≫
        tensorModulesMap Y (tensorIsoTensorModules Y A B).hom (𝟙 C) ≫
          (tensorModulesAssociator Y A B C).hom := by
  rw [← tensorIsoTensorModules_naturality,
    ← reassoc_of% tensorIsoTensorModules_naturality, tensorModulesAssociator_hom_eq]
  simp

/-- Naturality of [Stacks, Tag 01CD] in the second variable alone. -/
theorem pullbackTensorModules_naturality_left (A : Y.Modules) {B B' : Y.Modules} (b : B ⟶ B') :
    (Scheme.Modules.pullback j).map (tensorModulesMap Y (𝟙 A) b) ≫
        (pullbackTensorModules j A B').hom
      = (pullbackTensorModules j A B).hom ≫
        tensorModulesMap Y' (𝟙 ((Scheme.Modules.pullback j).obj A))
          ((Scheme.Modules.pullback j).map b) :=
  by simpa only [(Scheme.Modules.pullback j).map_id] using
    pullbackTensorModules_naturality j (𝟙 A) b

/-- Naturality of [Stacks, Tag 01CD] in the first variable alone. -/
theorem pullbackTensorModules_naturality_right {A A' : Y.Modules} (a : A ⟶ A') (B : Y.Modules) :
    (Scheme.Modules.pullback j).map (tensorModulesMap Y a (𝟙 B)) ≫
        (pullbackTensorModules j A' B).hom
      = (pullbackTensorModules j A B).hom ≫
        tensorModulesMap Y' ((Scheme.Modules.pullback j).map a)
          (𝟙 ((Scheme.Modules.pullback j).obj B)) :=
  by simpa only [(Scheme.Modules.pullback j).map_id] using
    pullbackTensorModules_naturality j a (𝟙 B)

/-- The comparison of [Stacks, Tag 01CD] is compatible with the associator of the tensor product
sheaf, in the `tensorModules` spelling. -/
theorem pullbackTensorModules_assoc (A B C : Y.Modules) :
    (Scheme.Modules.pullback j).map (tensorModulesAssociator Y A B C).hom ≫
        (pullbackTensorModules j A (tensorModules Y B C)).hom ≫
          tensorModulesMap Y' (𝟙 ((Scheme.Modules.pullback j).obj A))
            (pullbackTensorModules j B C).hom
      = (pullbackTensorModules j (tensorModules Y A B) C).hom ≫
        tensorModulesMap Y' (pullbackTensorModules j A B).hom
            (𝟙 ((Scheme.Modules.pullback j).obj C)) ≫
          (tensorModulesAssociator Y' ((Scheme.Modules.pullback j).obj A)
            ((Scheme.Modules.pullback j).obj B) ((Scheme.Modules.pullback j).obj C)).hom :=
  (congrArg (fun z => (Scheme.Modules.pullback j).map (tensorModulesAssociator Y A B C).hom ≫
      (pullbackTensorModules j A (tensorModules Y B C)).hom ≫ z)
    (tensorSheafMap_id_left_eq_whiskerLeft Y'.toRingedSpace
      ((Scheme.Modules.pullback j).obj A) (pullbackTensorModules j B C).hom)).trans
    ((Stacks.PullbackTensorCoherence.pullbackTensorComparison_associator
        (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom j)) A B C).trans
      (congrArg (fun z => (pullbackTensorModules j (tensorModules Y A B) C).hom ≫ z ≫
          (tensorModulesAssociator Y' ((Scheme.Modules.pullback j).obj A)
            ((Scheme.Modules.pullback j).obj B) ((Scheme.Modules.pullback j).obj C)).hom)
        (tensorSheafMap_id_right_eq_whiskerRight Y'.toRingedSpace
          (pullbackTensorModules j A B).hom ((Scheme.Modules.pullback j).obj C)).symm))

/-- The left-hand side of the associativity law for the cotensorator, composed with the
comparison of the two tensor products, written out in the tensor product sheaf spelling. -/
private theorem assoc_aux_left (A B C : Y.Modules) :
    (Scheme.Modules.pullback j).map (α_ A B C).hom ≫ pullbackCotensorator j A (B ⊗ C) ≫
        ((Scheme.Modules.pullback j).obj A ◁ pullbackCotensorator j B C) ≫
          (tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj A)
            ((Scheme.Modules.pullback j).obj B ⊗ (Scheme.Modules.pullback j).obj C)).hom ≫
            tensorModulesMap Y' (𝟙 ((Scheme.Modules.pullback j).obj A))
              (tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj B)
                ((Scheme.Modules.pullback j).obj C)).hom
      = (Scheme.Modules.pullback j).map (tensorIsoTensorModules Y (A ⊗ B) C).hom ≫
        (pullbackTensorModules j (A ⊗ B) C).hom ≫
          tensorModulesMap Y' (pullbackCotensorator j A B ≫
              (tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj A)
                ((Scheme.Modules.pullback j).obj B)).hom)
              (𝟙 ((Scheme.Modules.pullback j).obj C)) ≫
            (tensorModulesAssociator Y' ((Scheme.Modules.pullback j).obj A)
              ((Scheme.Modules.pullback j).obj B)
              ((Scheme.Modules.pullback j).obj C)).hom := by
  rw [← MonoidalCategory.id_tensorHom,
    reassoc_of% tensorIsoTensorModules_naturality,
    tensorModulesMap_id_left_comp,
    pullbackCotensorator_comp_tensorIso Y j B C,
    ← tensorModulesMap_id_left_comp,
    reassoc_of% (pullbackCotensorator_comp_tensorIso Y j A (B ⊗ C)),
    ← reassoc_of% pullbackTensorModules_naturality_left,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    associator_hom_tensorIsoTensorModules,
    Functor.map_comp_assoc, Functor.map_comp_assoc,
    pullbackTensorModules_assoc,
    reassoc_of% pullbackTensorModules_naturality_right,
    reassoc_of% tensorModulesMap_id_right_comp,
    ← pullbackCotensorator_comp_tensorIso Y j A B]

/-- The right-hand side of the associativity law for the cotensorator, composed with the
comparison of the two tensor products, written out in the tensor product sheaf spelling. -/
private theorem assoc_aux_right (A B C : Y.Modules) :
    pullbackCotensorator j (A ⊗ B) C ≫
        (pullbackCotensorator j A B ▷ (Scheme.Modules.pullback j).obj C) ≫
          (α_ ((Scheme.Modules.pullback j).obj A) ((Scheme.Modules.pullback j).obj B)
            ((Scheme.Modules.pullback j).obj C)).hom ≫
            (tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj A)
              ((Scheme.Modules.pullback j).obj B ⊗ (Scheme.Modules.pullback j).obj C)).hom ≫
              tensorModulesMap Y' (𝟙 ((Scheme.Modules.pullback j).obj A))
                (tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj B)
                  ((Scheme.Modules.pullback j).obj C)).hom
      = (Scheme.Modules.pullback j).map (tensorIsoTensorModules Y (A ⊗ B) C).hom ≫
        (pullbackTensorModules j (A ⊗ B) C).hom ≫
          tensorModulesMap Y' (pullbackCotensorator j A B ≫
              (tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj A)
                ((Scheme.Modules.pullback j).obj B)).hom)
              (𝟙 ((Scheme.Modules.pullback j).obj C)) ≫
            (tensorModulesAssociator Y' ((Scheme.Modules.pullback j).obj A)
              ((Scheme.Modules.pullback j).obj B)
              ((Scheme.Modules.pullback j).obj C)).hom := by
  rw [associator_hom_tensorIsoTensorModules, ← MonoidalCategory.tensorHom_id,
    reassoc_of% tensorIsoTensorModules_naturality,
    reassoc_of% tensorModulesMap_id_right_comp,
    reassoc_of% (pullbackCotensorator_comp_tensorIso Y j (A ⊗ B) C)]

/-- The associativity law for the cotensorator of an inverse image, in the monoidal structure
`Stacks.SheafInternalHom.schemeMonoidalCategory` the tensor powers are read in: the cotensorator is
compatible with the associator. -/
theorem pullbackCotensorator_assoc (A B C : Y.Modules) :
    (Scheme.Modules.pullback j).map (α_ A B C).hom ≫ pullbackCotensorator j A (B ⊗ C) ≫
        ((Scheme.Modules.pullback j).obj A ◁ pullbackCotensorator j B C)
      = pullbackCotensorator j (A ⊗ B) C ≫
        (pullbackCotensorator j A B ▷ (Scheme.Modules.pullback j).obj C) ≫ (α_ _ _ _).hom := by
  refine (cancel_mono ((tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj A)
        ((Scheme.Modules.pullback j).obj B ⊗ (Scheme.Modules.pullback j).obj C) ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso Y'
        (Iso.refl ((Scheme.Modules.pullback j).obj A))
        (tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj B)
          ((Scheme.Modules.pullback j).obj C))).hom)).mp ?_
  simp only [Iso.trans_hom, tensorModulesMapIso_hom, Iso.refl_hom, Category.assoc]
  exact (assoc_aux_left Y j A B C).trans (assoc_aux_right Y j A B C).symm

end AssocLaw

/-! #### The unitors -/

section UnitorLaws

/-- Cancelling an isomorphism at the end of a composite. -/
private theorem comp_comp_inv_comp {C : Type*} [Category C] {A B D E : C} (a : A ⟶ B) (b : B ⟶ D)
    (i : D ⟶ E) (i' : E ⟶ D) (h : i ≫ i' = 𝟙 D) : (a ≫ b ≫ i) ≫ i' = a ≫ b := by
  rw [Category.assoc, Category.assoc, h, Category.comp_id]

/-- Replacing two consecutive whiskerings by two others with the same composite. -/
private theorem whiskerRight_comp_cancel₂ {D : Type*} [Category D] [MonoidalCategory D]
    {U₀ U₁ U₂ U₃ V R : D} (a : U₀ ⟶ U₁) (b : U₁ ⟶ U₂) (c : U₀ ⟶ U₃) (d : U₃ ⟶ U₂)
    (h : a ≫ b = c ≫ d) (t : U₂ ⊗ V ⟶ R) :
    a ▷ V ≫ b ▷ V ≫ t = c ▷ V ≫ d ▷ V ≫ t := by
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, h,
    MonoidalCategory.comp_whiskerRight, Category.assoc]

/-- Replacing two consecutive whiskerings into the second variable by two others with the same
composite. -/
private theorem whiskerLeft_comp_cancel₂ {D : Type*} [Category D] [MonoidalCategory D]
    {U₀ U₁ U₂ U₃ V R : D} (a : U₀ ⟶ U₁) (b : U₁ ⟶ U₂) (c : U₀ ⟶ U₃) (d : U₃ ⟶ U₂)
    (h : a ≫ b = c ≫ d) (t : V ⊗ U₂ ⟶ R) :
    V ◁ a ≫ V ◁ b ≫ t = V ◁ c ≫ V ◁ d ≫ t := by
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, h,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- Rewriting the first two factors of a threefold composite by an equality of two-fold
composites. -/
private theorem comp_comp_of_eq {C : Type*} [Category C] {A B B' D E : C} (x : A ⟶ B) (y : B ⟶ D)
    (z : A ⟶ B') (w : B' ⟶ D) (h : x ≫ y = z ≫ w) (r : D ⟶ E) : z ≫ w ≫ r = x ≫ y ≫ r := by
  rw [← Category.assoc, ← h, Category.assoc]

/-- The left unit constraint of the tensor product sheaf of [Stacks, Tag 01CA], at the scheme
spelling: the left unitor of the monoidal structure of
`Stacks.PullbackGradedAlgebra.monoidalCategory`, whose unit object is the free rank-one sheaf
`Stacks.SectionRingGeometric.unitModule`. -/
def tensorModulesLeftUnitor (Z : Scheme.{u}) (A : Z.Modules) :
    tensorModules Z (unitModule Z) A ≅ A :=
  @MonoidalCategoryStruct.leftUnitor _ _
    (Stacks.PullbackGradedAlgebra.monoidalCategory Z.toRingedSpace).toMonoidalCategoryStruct A

/-- The left unitor of `Stacks.SheafOfModules.monoidalCategory`, written through the left unit
constraint of the tensor product sheaf. -/
private theorem leftUnitor_two_hom_eq (Z : Scheme.{u}) (A : Z.Modules) :
    (@MonoidalCategoryStruct.leftUnitor _ _
        (Stacks.SheafOfModules.monoidalCategory Z.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z)).toMonoidalCategoryStruct
        A).hom
      = (tensorIsoTensorModules Z (unitModule Z) A).hom ≫ (tensorModulesLeftUnitor Z A).hom :=
  (Stacks.SheafOfModules.leftUnitor_hom_eq Z.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z) A).trans
    (congrArg (fun z => (tensorIsoTensorModules Z (unitModule Z) A).hom ≫ z)
      (congrArg Iso.hom (Stacks.SheafOfModules.Strict_leftUnitor_eq Z.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z) A)).symm)

/-- The left unitor of `Stacks.SheafOfModules.monoidalCategory`, written through the left unitor of
`Stacks.SheafInternalHom.schemeMonoidalCategory`: the two differ by the comparison of the two unit
objects whiskered into the first variable. -/
private theorem leftUnitor_monoidalCategory_hom (Z : Scheme.{u}) (A : Z.Modules) :
    (@MonoidalCategoryStruct.leftUnitor _ _
        (Stacks.SheafOfModules.monoidalCategory Z.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z)).toMonoidalCategoryStruct
        A).hom
      = (unitComparison Z).inv ▷ A ≫ (λ_ A).hom :=
  AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom Z.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z) A

/-- The monoidal left unitor and the left unit constraint of the tensor product sheaf agree across
the comparison of the two tensor products, the two unit objects being matched by
`Stacks.SectionRingGeometric.unitComparison`. -/
theorem leftUnitor_hom_tensorIsoTensorModules (Z : Scheme.{u}) (A : Z.Modules) :
    (unitComparison Z).inv ▷ A ≫ (λ_ A).hom
      = (tensorIsoTensorModules Z (unitModule Z) A).hom ≫ (tensorModulesLeftUnitor Z A).hom :=
  (leftUnitor_monoidalCategory_hom Z A).symm.trans (leftUnitor_two_hom_eq Z A)

/-- The monoidal left unitor, written through the comparison of the two unit objects, the
comparison of the two tensor products and the left unit constraint of the tensor product sheaf. -/
theorem leftUnitor_hom_eq_tensorModulesLeftUnitor (Z : Scheme.{u}) (A : Z.Modules) :
    (λ_ A).hom = (unitComparison Z).hom ▷ A ≫
      (tensorIsoTensorModules Z (unitModule Z) A).hom ≫ (tensorModulesLeftUnitor Z A).hom := by
  rw [← leftUnitor_hom_tensorIsoTensorModules, ← Category.assoc,
    ← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id, MonoidalCategory.id_whiskerRight,
    Category.id_comp]

/-- The structure-sheaf comparison of [Stacks, Tag 01CD], `j^*𝒪_Y ⟶ 𝒪_{Y'}`, at the scheme
spellings of the inverse image and of the free rank-one sheaf. -/
def unitComparisonPullback :
    (Scheme.Modules.pullback j).obj (unitModule Y) ⟶ unitModule Y' :=
  Stacks.PullbackTensorCoherence.pullbackUnitComparison
    (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom j))

/-- The comparison of [Stacks, Tag 01CD] is compatible with the left unit constraint of the tensor
product sheaf, in the `tensorModules` spelling. -/
theorem pullbackTensorModules_leftUnitor (A : Y.Modules) :
    (Scheme.Modules.pullback j).map (tensorModulesLeftUnitor Y A).hom
      = (pullbackTensorModules j (unitModule Y) A).hom ≫
        tensorModulesMap Y' (unitComparisonPullback Y j)
            (𝟙 ((Scheme.Modules.pullback j).obj A)) ≫
          (tensorModulesLeftUnitor Y' ((Scheme.Modules.pullback j).obj A)).hom :=
  (Stacks.PullbackTensorCoherence.pullbackTensorComparison_leftUnitor
      (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom j)) A).trans
    (congrArg (fun z => (pullbackTensorModules j (unitModule Y) A).hom ≫ z ≫
        (tensorModulesLeftUnitor Y' ((Scheme.Modules.pullback j).obj A)).hom)
      (tensorSheafMap_id_right_eq_whiskerRight Y'.toRingedSpace
        (Stacks.PullbackTensorCoherence.pullbackUnitComparison
          (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom j)))
        ((Scheme.Modules.pullback j).obj A)).symm)

/-- The structure-sheaf comparison of [Stacks, Tag 01CD] read at the monoidal unit, followed by the
comparison of the two unit objects on the target, is the image of that comparison on the source
followed by `unitComparisonPullback`. -/
theorem unitPullbackHom_comp_unitComparison :
    Stacks.PullbackUnitSection.unitPullbackHom j ≫ (unitComparison Y').hom
      = (Scheme.Modules.pullback j).map (unitComparison Y).hom ≫ unitComparisonPullback Y j :=
  (congrArg (fun z => z ≫ (unitComparison Y').hom)
      (unitPullbackHom_eq_pullbackUnitComparison Y j)).trans
    (comp_comp_inv_comp _ _ _ _ (unitComparison Y').inv_hom_id)

/-- The image under `j^*` of the left unitor, written out in the tensor product sheaf spelling. -/
private theorem leftUnitor_aux_left (A : Y.Modules) :
    (Scheme.Modules.pullback j).map (λ_ A).hom
      = (Scheme.Modules.pullback j).map ((unitComparison Y).hom ▷ A) ≫
        (Scheme.Modules.pullback j).map (tensorIsoTensorModules Y (unitModule Y) A).hom ≫
          (pullbackTensorModules j (unitModule Y) A).hom ≫
            tensorModulesMap Y' (unitComparisonPullback Y j)
                (𝟙 ((Scheme.Modules.pullback j).obj A)) ≫
              (tensorModulesLeftUnitor Y' ((Scheme.Modules.pullback j).obj A)).hom := by
  rw [leftUnitor_hom_eq_tensorModulesLeftUnitor Y A, Functor.map_comp, Functor.map_comp,
    pullbackTensorModules_leftUnitor]

/-- The cotensorator at the free rank-one sheaf, followed by the structure-sheaf comparison of
[Stacks, Tag 01CD] in the first factor and by the comparison of the two tensor products, is the
comparison of [Stacks, Tag 01CD] in the first factor alone. -/
private theorem leftUnitor_aux_mid (A : Y.Modules) :
    pullbackCotensorator j (unitModule Y) A ≫
        (unitComparisonPullback Y j ▷ (Scheme.Modules.pullback j).obj A) ≫
          (tensorIsoTensorModules Y' (unitModule Y') ((Scheme.Modules.pullback j).obj A)).hom
      = (Scheme.Modules.pullback j).map (tensorIsoTensorModules Y (unitModule Y) A).hom ≫
        (pullbackTensorModules j (unitModule Y) A).hom ≫
          tensorModulesMap Y' (unitComparisonPullback Y j)
              (𝟙 ((Scheme.Modules.pullback j).obj A)) := by
  rw [← MonoidalCategory.tensorHom_id, tensorIsoTensorModules_naturality,
    reassoc_of% (pullbackCotensorator_comp_tensorIso Y j (unitModule Y) A)]

private theorem leftUnitor_aux_right (A : Y.Modules) :
    pullbackCotensorator j (𝟙_ Y.Modules) A ≫
        (Stacks.PullbackUnitSection.unitPullbackHom j ▷ (Scheme.Modules.pullback j).obj A) ≫
          (λ_ ((Scheme.Modules.pullback j).obj A)).hom
      = (Scheme.Modules.pullback j).map ((unitComparison Y).hom ▷ A) ≫
        (Scheme.Modules.pullback j).map (tensorIsoTensorModules Y (unitModule Y) A).hom ≫
          (pullbackTensorModules j (unitModule Y) A).hom ≫
            tensorModulesMap Y' (unitComparisonPullback Y j)
                (𝟙 ((Scheme.Modules.pullback j).obj A)) ≫
              (tensorModulesLeftUnitor Y' ((Scheme.Modules.pullback j).obj A)).hom :=
  (congrArg (fun z => pullbackCotensorator j (𝟙_ Y.Modules) A ≫
        (Stacks.PullbackUnitSection.unitPullbackHom j ▷ (Scheme.Modules.pullback j).obj A) ≫ z)
      (leftUnitor_hom_eq_tensorModulesLeftUnitor Y'
        ((Scheme.Modules.pullback j).obj A))).trans
    ((congrArg (fun z => pullbackCotensorator j (𝟙_ Y.Modules) A ≫ z)
        (whiskerRight_comp_cancel₂ _ _ _ _ (unitPullbackHom_comp_unitComparison Y j) _)).trans
      ((comp_comp_of_eq _ _ _ _
          (Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackCotensorator_whiskerRight
            j (unitComparison Y).hom A) _).trans
        (congrArg (fun z => (Scheme.Modules.pullback j).map ((unitComparison Y).hom ▷ A) ≫ z)
          ((Stacks.SheafOfModules.comp_assoc₃ _ _ _ _).symm.trans
            ((congrArg (fun z => z ≫
                  (tensorModulesLeftUnitor Y' ((Scheme.Modules.pullback j).obj A)).hom)
                (leftUnitor_aux_mid Y j A)).trans
              (Stacks.SheafOfModules.comp_assoc₃ _ _ _ _))))))

/-- The left unit law for the cotensorator of an inverse image, in the monoidal structure
`Stacks.SheafInternalHom.schemeMonoidalCategory` the tensor powers are read in: the cotensorator at
the unit object, followed by the structure-sheaf comparison in the first factor, is the left
unitor. -/
theorem pullbackCotensorator_leftUnitor (A : Y.Modules) :
    (Scheme.Modules.pullback j).map (λ_ A).hom
      = pullbackCotensorator j (𝟙_ Y.Modules) A ≫
        (Stacks.PullbackUnitSection.unitPullbackHom j ▷ (Scheme.Modules.pullback j).obj A) ≫
          (λ_ ((Scheme.Modules.pullback j).obj A)).hom :=
  (leftUnitor_aux_left Y j A).trans (leftUnitor_aux_right Y j A).symm

/-- The right unit constraint of the tensor product sheaf of [Stacks, Tag 01CA], at the scheme
spelling: the right unitor of the monoidal structure of
`Stacks.PullbackGradedAlgebra.monoidalCategory`. -/
def tensorModulesRightUnitor (Z : Scheme.{u}) (A : Z.Modules) :
    tensorModules Z A (unitModule Z) ≅ A :=
  @MonoidalCategoryStruct.rightUnitor _ _
    (Stacks.PullbackGradedAlgebra.monoidalCategory Z.toRingedSpace).toMonoidalCategoryStruct A

/-- The right unitor of `Stacks.SheafOfModules.monoidalCategory`, written through the right unit
constraint of the tensor product sheaf. -/
private theorem rightUnitor_two_hom_eq (Z : Scheme.{u}) (A : Z.Modules) :
    (@MonoidalCategoryStruct.rightUnitor _ _
        (Stacks.SheafOfModules.monoidalCategory Z.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z)).toMonoidalCategoryStruct
        A).hom
      = (tensorIsoTensorModules Z A (unitModule Z)).hom ≫ (tensorModulesRightUnitor Z A).hom :=
  (Stacks.SheafOfModules.rightUnitor_hom_eq Z.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z) A).trans
    (congrArg (fun z => (tensorIsoTensorModules Z A (unitModule Z)).hom ≫ z)
      (congrArg Iso.hom (Stacks.SheafOfModules.Strict_rightUnitor_eq Z.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z) A)).symm)

/-- The right unitor of `Stacks.SheafOfModules.monoidalCategory`, written through the right unitor
of `Stacks.SheafInternalHom.schemeMonoidalCategory`. -/
private theorem rightUnitor_monoidalCategory_hom (Z : Scheme.{u}) (A : Z.Modules) :
    (@MonoidalCategoryStruct.rightUnitor _ _
        (Stacks.SheafOfModules.monoidalCategory Z.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z)).toMonoidalCategoryStruct
        A).hom
      = A ◁ (unitComparison Z).inv ≫ (ρ_ A).hom :=
  AlgebraicGeometry.rightUnitor_sheafOfModulesMonoidal_hom Z A

/-- The monoidal right unitor and the right unit constraint of the tensor product sheaf agree
across the comparison of the two tensor products, the two unit objects being matched by
`Stacks.SectionRingGeometric.unitComparison`. -/
theorem rightUnitor_hom_tensorIsoTensorModules (Z : Scheme.{u}) (A : Z.Modules) :
    A ◁ (unitComparison Z).inv ≫ (ρ_ A).hom
      = (tensorIsoTensorModules Z A (unitModule Z)).hom ≫ (tensorModulesRightUnitor Z A).hom :=
  (rightUnitor_monoidalCategory_hom Z A).symm.trans (rightUnitor_two_hom_eq Z A)

/-- The monoidal right unitor, written through the comparison of the two unit objects, the
comparison of the two tensor products and the right unit constraint of the tensor product sheaf. -/
theorem rightUnitor_hom_eq_tensorModulesRightUnitor (Z : Scheme.{u}) (A : Z.Modules) :
    (ρ_ A).hom = A ◁ (unitComparison Z).hom ≫
      (tensorIsoTensorModules Z A (unitModule Z)).hom ≫ (tensorModulesRightUnitor Z A).hom := by
  rw [← rightUnitor_hom_tensorIsoTensorModules, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

/-- The comparison of [Stacks, Tag 01CD] is compatible with the right unit constraint of the tensor
product sheaf, in the `tensorModules` spelling. -/
theorem pullbackTensorModules_rightUnitor (A : Y.Modules) :
    (Scheme.Modules.pullback j).map (tensorModulesRightUnitor Y A).hom
      = (pullbackTensorModules j A (unitModule Y)).hom ≫
        tensorModulesMap Y' (𝟙 ((Scheme.Modules.pullback j).obj A))
            (unitComparisonPullback Y j) ≫
          (tensorModulesRightUnitor Y' ((Scheme.Modules.pullback j).obj A)).hom :=
  (Stacks.PullbackTensorCoherence.pullbackTensorComparison_rightUnitor
      (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom j)) A).trans
    (congrArg (fun z => (pullbackTensorModules j A (unitModule Y)).hom ≫ z ≫
        (tensorModulesRightUnitor Y' ((Scheme.Modules.pullback j).obj A)).hom)
      (tensorSheafMap_id_left_eq_whiskerLeft Y'.toRingedSpace
        ((Scheme.Modules.pullback j).obj A)
        (Stacks.PullbackTensorCoherence.pullbackUnitComparison
          (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom j)))).symm)

private theorem rightUnitor_aux_left (A : Y.Modules) :
    (Scheme.Modules.pullback j).map (ρ_ A).hom
      = (Scheme.Modules.pullback j).map (A ◁ (unitComparison Y).hom) ≫
        (Scheme.Modules.pullback j).map (tensorIsoTensorModules Y A (unitModule Y)).hom ≫
          (pullbackTensorModules j A (unitModule Y)).hom ≫
            tensorModulesMap Y' (𝟙 ((Scheme.Modules.pullback j).obj A))
                (unitComparisonPullback Y j) ≫
              (tensorModulesRightUnitor Y' ((Scheme.Modules.pullback j).obj A)).hom := by
  rw [rightUnitor_hom_eq_tensorModulesRightUnitor Y A, Functor.map_comp, Functor.map_comp,
    pullbackTensorModules_rightUnitor]

/-- The cotensorator at the free rank-one sheaf in the second variable, followed by the
structure-sheaf comparison of [Stacks, Tag 01CD] there and by the comparison of the two tensor
products, is the comparison of [Stacks, Tag 01CD] in the second variable alone. -/
private theorem rightUnitor_aux_mid (A : Y.Modules) :
    pullbackCotensorator j A (unitModule Y) ≫
        ((Scheme.Modules.pullback j).obj A ◁ unitComparisonPullback Y j) ≫
          (tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj A) (unitModule Y')).hom
      = (Scheme.Modules.pullback j).map (tensorIsoTensorModules Y A (unitModule Y)).hom ≫
        (pullbackTensorModules j A (unitModule Y)).hom ≫
          tensorModulesMap Y' (𝟙 ((Scheme.Modules.pullback j).obj A))
              (unitComparisonPullback Y j) := by
  rw [← MonoidalCategory.id_tensorHom, tensorIsoTensorModules_naturality,
    reassoc_of% (pullbackCotensorator_comp_tensorIso Y j A (unitModule Y))]

private theorem rightUnitor_aux_right (A : Y.Modules) :
    pullbackCotensorator j A (𝟙_ Y.Modules) ≫
        ((Scheme.Modules.pullback j).obj A ◁ Stacks.PullbackUnitSection.unitPullbackHom j) ≫
          (ρ_ ((Scheme.Modules.pullback j).obj A)).hom
      = (Scheme.Modules.pullback j).map (A ◁ (unitComparison Y).hom) ≫
        (Scheme.Modules.pullback j).map (tensorIsoTensorModules Y A (unitModule Y)).hom ≫
          (pullbackTensorModules j A (unitModule Y)).hom ≫
            tensorModulesMap Y' (𝟙 ((Scheme.Modules.pullback j).obj A))
                (unitComparisonPullback Y j) ≫
              (tensorModulesRightUnitor Y' ((Scheme.Modules.pullback j).obj A)).hom :=
  (congrArg (fun z => pullbackCotensorator j A (𝟙_ Y.Modules) ≫
        ((Scheme.Modules.pullback j).obj A ◁
          Stacks.PullbackUnitSection.unitPullbackHom j) ≫ z)
      (rightUnitor_hom_eq_tensorModulesRightUnitor Y'
        ((Scheme.Modules.pullback j).obj A))).trans
    ((congrArg (fun z => pullbackCotensorator j A (𝟙_ Y.Modules) ≫ z)
        (whiskerLeft_comp_cancel₂ _ _ _ _ (unitPullbackHom_comp_unitComparison Y j) _)).trans
      ((comp_comp_of_eq _ _ _ _
            (Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackCotensorator_whiskerLeft
              j A (unitComparison Y).hom) _).trans
        (congrArg (fun z => (Scheme.Modules.pullback j).map (A ◁ (unitComparison Y).hom) ≫ z)
          ((Stacks.SheafOfModules.comp_assoc₃ _ _ _ _).symm.trans
            ((congrArg (fun z => z ≫
                  (tensorModulesRightUnitor Y' ((Scheme.Modules.pullback j).obj A)).hom)
                (rightUnitor_aux_mid Y j A)).trans
              (Stacks.SheafOfModules.comp_assoc₃ _ _ _ _))))))

/-- The right unit law for the cotensorator of an inverse image, in the monoidal structure
`Stacks.SheafInternalHom.schemeMonoidalCategory` the tensor powers are read in: the cotensorator at
the unit object, followed by the structure-sheaf comparison in the second factor, is the right
unitor. -/
theorem pullbackCotensorator_rightUnitor (A : Y.Modules) :
    (Scheme.Modules.pullback j).map (ρ_ A).hom
      = pullbackCotensorator j A (𝟙_ Y.Modules) ≫
        ((Scheme.Modules.pullback j).obj A ◁ Stacks.PullbackUnitSection.unitPullbackHom j) ≫
          (ρ_ ((Scheme.Modules.pullback j).obj A)).hom :=
  (rightUnitor_aux_left Y j A).trans (rightUnitor_aux_right Y j A).symm

end UnitorLaws

end Scheme

end Stacks.TensorSheafSpellingIso

end
