module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafOverSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftKFlatResolutions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComparisonWithTheDerivedTensorProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Homology.KFlat.BifunctorTransportEquivalence

/-!
# The tensor comparison for `overEquiv`, and invertibility across it

Let `X` be a scheme and `U` an open of `X`. Mathlib's
`AlgebraicGeometry.Scheme.Modules.overEquiv U` is the equivalence

`Mod(𝒪_X|_{X/U}) ≌ Mod(𝒪_U)`

between the sheaves of modules over the structure sheaf of the *slice site* `Opens(X)/U` and
the sheaves of modules on the *open subscheme* `U`. This file supplies the comparison of the
two tensor products across it, at the abelian level and then on the derived categories, and
reads off the transport of invertibility in the reflecting direction.

## `overEquiv` is a restriction along a functor of sites, on the nose

The equality `overEquiv_functor_eq_whiskerRestriction` below holds by `rfl`:

`(overEquiv U).functor = whiskerRestriction 𝒪_{X/U} _ (Opens.overEquivalence U).inverse`,

that is, `(overEquiv U).functor` *is*
`Stacks.SheafOfModules.TensorPower.whiskerRestriction` — the pushforward of sheaves of
modules, with the identity comparison of structure sheaves, along the continuous and
cocontinuous functor of sites `Opens ↥U ⥤ Opens(X)/U`. Three identifications make it so, and
each of them is `rfl` as well:

* the structure sheaf of the slice site, `X.ringCatSheaf.over U`, is the one the tensor-product
  development indexes by, `structureSheaf ((Over.forget U).op ⋙ X.presheaf) _`;
* the pullback of that along `(Opens.overEquivalence U).inverse` is the structure sheaf of the
  open subscheme, `U.toScheme.presheaf`, and hence `U.toScheme.ringCatSheaf` is
  `structureSheaf _ _` again;
* Mathlib builds `overEquiv` out of `SheafOfModules.pushforwardPushforwardEquivalence`, whose
  functor is `SheafOfModules.pushforward φ`, and its `φ` is
  `(TopologicalSpace.Opens.overPullbackSheafEquivOver.app _).inv` with
  `overPullbackSheafEquivOver` defined as `Iso.refl`, so `φ` is the identity.

So `Stacks.SheafOfModules.OverEquivTensor.overEquivTensorIso` is
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso` with its type ascribed at the
`overEquiv` spelling.

## Main definitions

* `Stacks.SheafOfModules.OverEquivTensor.sliceRingSheaf` and `openRingSheaf`: the structure
  sheaves of the slice site `Opens(X)/U` and of the open subscheme `U`, as sheaves of
  commutative rings.
* `Stacks.SheafOfModules.OverEquivTensor.overEquivTensorIso`:
  **`e(A ⊗ B) ≅ e A ⊗ e B` for `e = (overEquiv U).functor`,** at the abelian level.
* `Stacks.SheafOfModules.OverEquivTensor.overEquivUnitIso` and `overEquivDerivedUnitIso`:
  `e` carries the structure sheaf of the slice site to the structure sheaf of `U`, before and
  after the degree-zero inclusion into the derived categories.
* `Stacks.SheafOfModules.OverEquivTensor.overEquivDerivedTensorObjIso`:
  **`e(K ⊗^𝐋 L) ≅ e K ⊗^𝐋 e L`** on arbitrary objects of the derived categories.

## Main results

* `Stacks.SheafOfModules.OverEquivTensor.overEquiv_functor_eq_whiskerRestriction`: the `rfl`
  described above.
* `Stacks.SheafOfModules.OverEquivTensor.overEquivTensorIso_naturality_left` and
  `..._naturality_right`: the abelian comparison is natural in each variable separately.
* `Stacks.SheafOfModules.OverEquivTensor.isInvertible_of_isInvertible_overEquiv_obj`: the
  transport of invertibility, **in the reflecting direction**, with the two monoidal structures
  as explicit arguments.
* `Stacks.SheafOfModules.OverEquivTensor.isInvertible_of_isInvertible_overEquiv`: the same at
  the monoidal structure of [Stacks, Tag 0FPT] on both sides — **if `e K` is an invertible
  object of `D(𝒪_U)` then `K` is an invertible object of `D(𝒪_X|_{X/U})`.**

## Implementation notes

Along the equivalence `overEquiv` the derived comparison is produced from the abelian one by
`CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence`, whose K-flatness hypotheses
hold along any equivalence.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace
open CochainComplex.KFlatBifunctor
open Stacks.SheafOfModules.Tensor (sheafTensor ringSheaf)
open Stacks.SheafOfModules.TensorPower

universe d u

namespace Stacks.SheafOfModules.OverEquivTensor

variable (X : Scheme.{u}) (U : X.Opens)

/-! ### The two sheaves of rings, each named once -/

/-- **The structure sheaf of the slice site `Opens(X)/U`**, as a sheaf of commutative rings on
`Over U`. It is `X.ringCatSheaf.over U` and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf ((Over.forget U).op ⋙ X.presheaf) _`,
by `rfl`. -/
abbrev sliceRingSheaf : Sheaf ((Opens.grothendieckTopology (X : TopCat)).over U) CommRingCat.{u} :=
  X.sheaf.over U

/-- **The structure sheaf of the open subscheme `U`**, as a sheaf of commutative rings on
`Opens ↥U`. -/
abbrev openRingSheaf : Sheaf (Opens.grothendieckTopology ↥U) CommRingCat.{u} :=
  U.toScheme.sheaf

/-! ### `overEquiv` is a restriction along a functor of sites -/

/-- **`(overEquiv U).functor` is restriction along the functor of sites
`Opens ↥U ⥤ Opens(X)/U`**, on the nose. Both are the pushforward of sheaves of modules along
`(TopologicalSpace.Opens.overEquivalence U).inverse` with the identity comparison of structure
sheaves. -/
theorem overEquiv_functor_eq_whiskerRestriction :
    (Scheme.Modules.overEquiv U).functor =
      whiskerRestriction (J' := Opens.grothendieckTopology ↥U)
        (sliceRingSheaf X U).obj (ringSheaf.{u, u, u} (sliceRingSheaf X U)).property
        U.overEquivalence.inverse :=
  rfl

/-- **The equivalence `overEquiv U`, with both of its categories named at the tensor product's
spelling.** This is `AlgebraicGeometry.Scheme.Modules.overEquiv U`, the two namings of each
category being equal by `rfl`. -/
abbrev overEquivMod : Stacks.SheafOfModules.DerivedMonoidal.Mod (sliceRingSheaf X U) ≌
    Stacks.SheafOfModules.DerivedMonoidal.Mod (openRingSheaf X U) :=
  Scheme.Modules.overEquiv U

/-- `overEquivMod` is additive, at the tensor product's naming of the two categories. -/
instance overEquivMod_functor_additive :
    @Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive
      (overEquivMod X U).functor :=
  Stacks.SheafOfModules.overEquivFunctorAdditive U

/-- The inverse of `overEquivMod` is additive, at the tensor product's naming of the two
categories. -/
instance overEquivMod_inverse_additive :
    @Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive
      (overEquivMod X U).inverse :=
  inferInstanceAs (Functor.Additive (Scheme.Modules.overEquiv U).inverse)

/-! ### The comparison of the tensor products, at the abelian level -/

/-- **`e(A ⊗ B) ≅ e A ⊗ e B` for `e = (overEquiv U).functor`**: the equivalence between the
sheaves of modules on the slice site `Opens(X)/U` and those on the open subscheme `U` carries
the tensor product to the tensor product.

This is `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso` — restriction along a
continuous and cocontinuous functor of sites commutes with the tensor product of sheaves of
modules, [Stacks, Tag 01CU] — with its type ascribed at the spellings `overEquiv` and
`Stacks.SheafOfModules.Tensor.sheafTensor` use. -/
def overEquivTensorIso
    (A B : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} (sliceRingSheaf X U))) :
    (overEquivMod X U).functor.obj
        (((sheafTensor.{u, u, u, u, u} (sliceRingSheaf X U)).obj A).obj B) ≅
      ((sheafTensor.{u, u, u, u, u} (openRingSheaf X U)).obj
          ((overEquivMod X U).functor.obj A)).obj
        ((overEquivMod X U).functor.obj B) :=
  whiskerTensorSheafIso (J' := Opens.grothendieckTopology ↥U)
    (sliceRingSheaf X U).obj (ringSheaf.{u, u, u} (sliceRingSheaf X U)).property
    U.overEquivalence.inverse A B

/-- The comparison `overEquivTensorIso` is natural in both variables at once. -/
private theorem overEquivTensorIso_naturality
    {A A' B B' : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} (sliceRingSheaf X U))}
    (f : A ⟶ A') (g : B ⟶ B') :
    (overEquivMod X U).functor.map
          (((sheafTensor.{u, u, u, u, u} (sliceRingSheaf X U)).map f).app B ≫
            ((sheafTensor.{u, u, u, u, u} (sliceRingSheaf X U)).obj A').map g) ≫
        (overEquivTensorIso X U A' B').hom =
      (overEquivTensorIso X U A B).hom ≫
        ((sheafTensor.{u, u, u, u, u} (openRingSheaf X U)).map
          ((overEquivMod X U).functor.map f)).app ((overEquivMod X U).functor.obj B) ≫
        ((sheafTensor.{u, u, u, u, u} (openRingSheaf X U)).obj
          ((overEquivMod X U).functor.obj A')).map ((overEquivMod X U).functor.map g) :=
  whiskerTensorSheafIso_naturality (J' := Opens.grothendieckTopology ↥U)
    (sliceRingSheaf X U).obj (ringSheaf.{u, u, u} (sliceRingSheaf X U)).property
    U.overEquivalence.inverse f g

/-- **The comparison is natural in the first variable.** -/
theorem overEquivTensorIso_naturality_left
    {A A' : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} (sliceRingSheaf X U))} (f : A ⟶ A')
    (B : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} (sliceRingSheaf X U))) :
    (overEquivMod X U).functor.map
          (((sheafTensor.{u, u, u, u, u} (sliceRingSheaf X U)).map f).app B) ≫
        (overEquivTensorIso X U A' B).hom =
      (overEquivTensorIso X U A B).hom ≫
        ((sheafTensor.{u, u, u, u, u} (openRingSheaf X U)).map
          ((overEquivMod X U).functor.map f)).app
            ((overEquivMod X U).functor.obj B) := by
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
    overEquivTensorIso_naturality X U f (𝟙 B)

/-- **The comparison is natural in the second variable.** -/
theorem overEquivTensorIso_naturality_right
    (A : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} (sliceRingSheaf X U)))
    {B B' : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} (sliceRingSheaf X U))} (g : B ⟶ B') :
    (overEquivMod X U).functor.map
          (((sheafTensor.{u, u, u, u, u} (sliceRingSheaf X U)).obj A).map g) ≫
        (overEquivTensorIso X U A B').hom =
      (overEquivTensorIso X U A B).hom ≫
        ((sheafTensor.{u, u, u, u, u} (openRingSheaf X U)).obj
          ((overEquivMod X U).functor.obj A)).map
            ((overEquivMod X U).functor.map g) := by
  simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] using
    overEquivTensorIso_naturality X U (𝟙 A) g

/-- **`e` carries the structure sheaf of the slice site to the structure sheaf of `U`**, on the
nose: this is `Stacks.SheafOfModules.TensorPower.whiskerUnitIso`, which is `Iso.refl`. -/
def overEquivUnitIso :
    (overEquivMod X U).functor.obj
        (_root_.SheafOfModules.unit (ringSheaf.{u, u, u} (sliceRingSheaf X U))) ≅
      _root_.SheafOfModules.unit (ringSheaf.{u, u, u} (openRingSheaf X U)) :=
  whiskerUnitIso (J' := Opens.grothendieckTopology ↥U)
    (sliceRingSheaf X U).obj (ringSheaf.{u, u, u} (sliceRingSheaf X U)).property
    U.overEquivalence.inverse

/-! ### The comparison on the derived categories, and invertibility -/

section Derived

variable
  [HasDerivedCategory.{d} (Stacks.SheafOfModules.DerivedMonoidal.Mod (sliceRingSheaf X U))]
  [HasDerivedCategory.{d} (Stacks.SheafOfModules.DerivedMonoidal.Mod (openRingSheaf X U))]

/-- **`e` carries the structure sheaf of the slice site in degree zero to the structure sheaf of
`U` in degree zero.** This is `Stacks.SheafOfModules.OverEquivTensor.overEquivUnitIso` moved
through the degree-zero inclusion by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. -/
def overEquivDerivedUnitIso :
    (overEquivMod X U).functor.mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor
            (Stacks.SheafOfModules.DerivedMonoidal.Mod (sliceRingSheaf X U)) 0).obj
          (_root_.SheafOfModules.unit (ringSheaf.{u, u, u} (sliceRingSheaf X U)))) ≅
      (DerivedCategory.singleFunctor
          (Stacks.SheafOfModules.DerivedMonoidal.Mod (openRingSheaf X U)) 0).obj
        (_root_.SheafOfModules.unit (ringSheaf.{u, u, u} (openRingSheaf X U))) :=
  (((overEquivMod X U).functor).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor
      (Stacks.SheafOfModules.DerivedMonoidal.Mod (openRingSheaf X U)) 0).mapIso
        (overEquivUnitIso X U)

/-- **`e(K ⊗^𝐋 L) ≅ e K ⊗^𝐋 e L`** on arbitrary objects of the derived categories.

This is `CochainComplex.KFlatBifunctor.derivedTransportObjIsoOfEquivalence` at
`Scheme.Modules.overEquiv U` and the abelian comparison
`Stacks.SheafOfModules.OverEquivTensor.overEquivTensorIso`. -/
def overEquivDerivedTensorObjIso
    (K L : DerivedCategory (Stacks.SheafOfModules.DerivedMonoidal.Mod (sliceRingSheaf X U))) :
    (overEquivMod X U).functor.mapDerivedCategory.obj
        (((derivedBifunctor (sheafTensor.{u, u, u, u, u} (sliceRingSheaf X U))).obj K).obj L) ≅
      ((derivedBifunctor (sheafTensor.{u, u, u, u, u} (openRingSheaf X U))).obj
          ((overEquivMod X U).functor.mapDerivedCategory.obj K)).obj
        ((overEquivMod X U).functor.mapDerivedCategory.obj L) :=
  derivedTransportObjIsoOfEquivalence (sheafTensor.{u, u, u, u, u} (sliceRingSheaf X U))
    (sheafTensor.{u, u, u, u, u} (openRingSheaf X U)) (overEquivMod X U)
    (overEquivTensorIso X U)
    (fun f B => overEquivTensorIso_naturality_left X U f B)
    (fun A {_ _} g => overEquivTensorIso_naturality_right X U A g) K L

/-- **`overEquiv` reflects invertibility on the derived categories**, with the two monoidal
structures as explicit arguments, each identified by a pairwise comparison of its tensor
product with the derived tensor bifunctor of [Stacks, Tag 06YU], and `unitε` identifying the
images of the units. -/
theorem isInvertible_of_isInvertible_overEquiv_obj
    (mS : MonoidalCategory (DerivedCategory
      (Stacks.SheafOfModules.DerivedMonoidal.Mod (sliceRingSheaf X U))))
    (mU : MonoidalCategory (DerivedCategory
      (Stacks.SheafOfModules.DerivedMonoidal.Mod (openRingSheaf X U))))
    (bS : letI := mS; BraidedCategory (DerivedCategory
      (Stacks.SheafOfModules.DerivedMonoidal.Mod (sliceRingSheaf X U))))
    (cmpS : letI := mS; ∀ A B : DerivedCategory
        (Stacks.SheafOfModules.DerivedMonoidal.Mod (sliceRingSheaf X U)),
      A ⊗ B ≅ ((derivedBifunctor (sheafTensor.{u, u, u, u, u} (sliceRingSheaf X U))).obj A).obj B)
    (cmpU : letI := mU; ∀ A B : DerivedCategory
        (Stacks.SheafOfModules.DerivedMonoidal.Mod (openRingSheaf X U)),
      A ⊗ B ≅ ((derivedBifunctor (sheafTensor.{u, u, u, u, u} (openRingSheaf X U))).obj A).obj B)
    (unitε : letI := mS; letI := mU;
      (overEquivMod X U).functor.mapDerivedCategory.obj
          (𝟙_ (DerivedCategory (Stacks.SheafOfModules.DerivedMonoidal.Mod
            (sliceRingSheaf X U)))) ≅
        𝟙_ (DerivedCategory (Stacks.SheafOfModules.DerivedMonoidal.Mod (openRingSheaf X U))))
    (K : DerivedCategory (Stacks.SheafOfModules.DerivedMonoidal.Mod (sliceRingSheaf X U)))
    (hK : letI := mU; MonoidalCategory.IsInvertible
      ((overEquivMod X U).functor.mapDerivedCategory.obj K)) :
    letI := mS; MonoidalCategory.IsInvertible K :=
  isInvertible_of_isInvertible_mapDerivedCategory
    (sheafTensor.{u, u, u, u, u} (sliceRingSheaf X U))
    (sheafTensor.{u, u, u, u, u} (openRingSheaf X U)) (overEquivMod X U)
    (overEquivTensorIso X U)
    (fun f B => overEquivTensorIso_naturality_left X U f B)
    (fun A {_ _} g => overEquivTensorIso_naturality_right X U A g)
    mS mU bS cmpS cmpU unitε K hK

/-- **`overEquiv` reflects invertibility on the derived categories**, at the symmetric monoidal
structure of [Stacks, Tag 0FPT] on both sides: if `e K` is an invertible object of `D(𝒪_U)`
then `K` is an invertible object of `D(𝒪_X|_{X/U})`. -/
theorem isInvertible_of_isInvertible_overEquiv
    (K : DerivedCategory (Stacks.SheafOfModules.DerivedMonoidal.Mod (sliceRingSheaf X U)))
    (hK : letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (openRingSheaf X U)
      MonoidalCategory.IsInvertible
        ((overEquivMod X U).functor.mapDerivedCategory.obj K)) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (sliceRingSheaf X U)
    MonoidalCategory.IsInvertible K :=
  isInvertible_of_isInvertible_overEquiv_obj X U
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (sliceRingSheaf X U))
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (openRingSheaf X U))
    (Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric
      (sliceRingSheaf X U)).toBraidedCategory
    (fun A B => ((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso
      (sliceRingSheaf X U)).app A).app B)
    (fun A B => ((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso
      (openRingSheaf X U)).app A).app B)
    ((overEquivMod X U).functor.mapDerivedCategory.mapIso
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso (sliceRingSheaf X U)) ≪≫
      overEquivDerivedUnitIso X U ≪≫
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso (openRingSheaf X U)).symm)
    K hK

end Derived

end Stacks.SheafOfModules.OverEquivTensor

end
