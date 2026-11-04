module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat

/-!
# Associativity of the derived tensor product on a ringed site

Let `(C, O)` be a ringed site and let `T` be a derived tensor product on `D(Mod(O))`. For
objects `K`, `L`, `M` of `D(Mod(O))` there is an isomorphism

`(K ⊗^L_O L) ⊗^L_O M ≅ K ⊗^L_O (L ⊗^L_O M)`,

natural in each of the three variables separately.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso`: the tensor product of
  `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` is isomorphic to the bifunctor of a
  prescribed derived tensor product.
* `Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal`: a monoidal structure on
  `D(Mod(O))` whose tensor product is the bifunctor of a prescribed derived tensor product, on
  the nose.
* `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator`: the associativity
  isomorphism of a derived tensor product over the structure sheaf.
* `Stacks.SheafOfModules.DerivedTensorProduct.associator`: the same, for a derived tensor
  product indexed by the ringed site.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.tensor_map_zero_app`,
  `Stacks.SheafOfModules.DerivedTensorProduct.tensor_obj_map_zero`: tensoring a zero map with an
  object gives a zero map, in each variable.
* `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator_naturality_left`,
  `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator_naturality_middle`,
  `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator_naturality_right`: naturality
  of the associator in each of the three variables.
* `Stacks.SheafOfModules.DerivedTensorProduct.associator_naturality_left`,
  `Stacks.SheafOfModules.DerivedTensorProduct.associator_naturality_middle`,
  `Stacks.SheafOfModules.DerivedTensorProduct.associator_naturality_right`: the same, for a
  derived tensor product indexed by the ringed site.
* `Stacks.SheafOfModules.DerivedTensorProduct.tensor_map_obj_map_app_eq_zero`: if `ι ⊗^L 1_G`
  vanishes then so does `(1_K ⊗^L ι) ⊗^L 1_G`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry.RingedSite

variable {X : AlgebraicGeometry.RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : DerivedTensorProduct.{u, v, w, d} X)

/-- Tensoring the zero map with an object on the right gives the zero map. -/
theorem tensor_map_zero_app (K K' L : DerivedModules.{u, v, w, d} X) :
    (T.tensor.map (0 : K ⟶ K')).app L = 0 :=
  (T.tensor.flip.obj L).map_zero K K'

/-- Tensoring an object with the zero map gives the zero map. -/
theorem tensor_obj_map_zero (K L L' : DerivedModules.{u, v, w, d} X) :
    (T.tensor.obj K).map (0 : L ⟶ L') = 0 :=
  (T.tensor.obj K).map_zero L L'

/-- The two one-variable actions of the derived tensor product commute: the square built from a
map in the left variable and a map in the right variable commutes. -/
theorem tensor_map_app_naturality {K K' L L' : DerivedModules.{u, v, w, d} X} (f : K ⟶ K')
    (g : L ⟶ L') :
    (T.tensor.map f).app L ≫ (T.tensor.obj K').map g =
      (T.tensor.obj K).map g ≫ (T.tensor.map f).app L' :=
  ((T.tensor.map f).naturality g).symm

end Stacks.SheafOfModules.DerivedTensorProduct

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R)

/-- The tensor product of the monoidal structure
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` on the derived category is isomorphic, as
a bifunctor, to the bifunctor of an arbitrary derived tensor product. -/
def derivedTensorMonoidalIso :
    @curriedTensor (DerivedModules R) _ (derivedMonoidal R) ≅ T.tensor :=
  derivedTensorBifunctorIso R ≪≫ derivedBifunctorTensorIso R T

/-- The monoidal structure on the derived category of modules whose tensor product is a
prescribed derived tensor product, on the nose: the structure
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` transported along
`Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso` by
`CategoryTheory.MonoidalCategory.reseat`. -/
@[instance_reducible]
def reseatedDerivedMonoidal : MonoidalCategory (DerivedModules R) :=
  @reseat (DerivedModules R) _ (derivedMonoidal R) _ _
    (derivedTensorMonoidalIso R T) (canonicalUnitIso R)

/-- The tensor product of `Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal` is the
prescribed derived tensor bifunctor, as an equality of bifunctors. -/
theorem curriedTensor_reseatedDerivedMonoidal :
    @curriedTensor (DerivedModules R) _ (reseatedDerivedMonoidal R T) = T.tensor :=
  @curriedTensor_reseat (DerivedModules R) _ (derivedMonoidal R) _ _
    (derivedTensorMonoidalIso R T) (canonicalUnitIso R)

/-- Associativity of the derived tensor product: `(K ⊗^L L) ⊗^L M ≅ K ⊗^L (L ⊗^L M)`, the
associator of `Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal`. -/
def derivedTensorAssociator (K L M : DerivedModules R) :
    (T.tensor.obj ((T.tensor.obj K).obj L)).obj M ≅
      (T.tensor.obj K).obj ((T.tensor.obj L).obj M) :=
  letI := reseatedDerivedMonoidal R T
  α_ K L M

/-- The associator is natural in the first variable. -/
theorem derivedTensorAssociator_naturality_left {K K' : DerivedModules R} (f : K ⟶ K')
    (L M : DerivedModules R) :
    (T.tensor.map ((T.tensor.map f).app L)).app M ≫ (derivedTensorAssociator R T K' L M).hom =
      (derivedTensorAssociator R T K L M).hom ≫
        (T.tensor.map f).app ((T.tensor.obj L).obj M) :=
  @associator_naturality_left (DerivedModules R) _ (reseatedDerivedMonoidal R T) _ _ f L M

/-- The associator is natural in the second variable. -/
theorem derivedTensorAssociator_naturality_middle (K : DerivedModules R)
    {L L' : DerivedModules R} (g : L ⟶ L') (M : DerivedModules R) :
    (T.tensor.map ((T.tensor.obj K).map g)).app M ≫ (derivedTensorAssociator R T K L' M).hom =
      (derivedTensorAssociator R T K L M).hom ≫
        (T.tensor.obj K).map ((T.tensor.map g).app M) :=
  @associator_naturality_middle (DerivedModules R) _ (reseatedDerivedMonoidal R T) K _ _ g M

/-- The associator is natural in the third variable. -/
theorem derivedTensorAssociator_naturality_right (K L : DerivedModules R)
    {M M' : DerivedModules R} (h : M ⟶ M') :
    (T.tensor.obj ((T.tensor.obj K).obj L)).map h ≫ (derivedTensorAssociator R T K L M').hom =
      (derivedTensorAssociator R T K L M).hom ≫
        (T.tensor.obj K).map ((T.tensor.obj L).map h) :=
  @associator_naturality_right (DerivedModules R) _ (reseatedDerivedMonoidal R T) K L _ _ h

end Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry AlgebraicGeometry.RingedSite

variable {Y : AlgebraicGeometry.RingedSite.{u, u, u}}
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules.{u, u, u} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u, u} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (T : DerivedTensorProduct.{u, u, u, d} Y)

/-- Associativity of the derived tensor product: `(K ⊗^L L) ⊗^L M ≅ K ⊗^L (L ⊗^L M)`. -/
def associator (K L M : DerivedModules.{u, u, u, d} Y) :
    (T.tensor.obj ((T.tensor.obj K).obj L)).obj M ≅
      (T.tensor.obj K).obj ((T.tensor.obj L).obj M) :=
  DerivedMonoidal.derivedTensorAssociator Y.O (toRingedSiteDerivedTensorProduct T) K L M

/-- The associator is natural in the first variable. -/
theorem associator_naturality_left {K K' : DerivedModules.{u, u, u, d} Y} (f : K ⟶ K')
    (L M : DerivedModules.{u, u, u, d} Y) :
    (T.tensor.map ((T.tensor.map f).app L)).app M ≫ (T.associator K' L M).hom =
      (T.associator K L M).hom ≫ (T.tensor.map f).app ((T.tensor.obj L).obj M) :=
  DerivedMonoidal.derivedTensorAssociator_naturality_left Y.O
    (toRingedSiteDerivedTensorProduct T) f L M

/-- The associator is natural in the second variable. -/
theorem associator_naturality_middle (K : DerivedModules.{u, u, u, d} Y)
    {L L' : DerivedModules.{u, u, u, d} Y} (g : L ⟶ L') (M : DerivedModules.{u, u, u, d} Y) :
    (T.tensor.map ((T.tensor.obj K).map g)).app M ≫ (T.associator K L' M).hom =
      (T.associator K L M).hom ≫ (T.tensor.obj K).map ((T.tensor.map g).app M) :=
  DerivedMonoidal.derivedTensorAssociator_naturality_middle Y.O
    (toRingedSiteDerivedTensorProduct T) K g M

/-- The associator is natural in the third variable. -/
theorem associator_naturality_right (K L : DerivedModules.{u, u, u, d} Y)
    {M M' : DerivedModules.{u, u, u, d} Y} (h : M ⟶ M') :
    (T.tensor.obj ((T.tensor.obj K).obj L)).map h ≫ (T.associator K L M').hom =
      (T.associator K L M).hom ≫ (T.tensor.obj K).map ((T.tensor.obj L).map h) :=
  DerivedMonoidal.derivedTensorAssociator_naturality_right Y.O
    (toRingedSiteDerivedTensorProduct T) K L h

/-- If `ι ⊗^L 1_G = 0` then `(1_K ⊗^L ι) ⊗^L 1_G = 0`. -/
theorem tensor_map_obj_map_app_eq_zero {I O : DerivedModules.{u, u, u, d} Y} (ι : I ⟶ O)
    (K G : DerivedModules.{u, u, u, d} Y) (h : (T.tensor.map ι).app G = 0) :
    (T.tensor.map ((T.tensor.obj K).map ι)).app G = 0 :=
  zero_of_comp_mono (T.associator K O G).hom <| by
    rw [T.associator_naturality_middle, h, T.tensor_obj_map_zero, comp_zero]

end Stacks.SheafOfModules.DerivedTensorProduct

end
