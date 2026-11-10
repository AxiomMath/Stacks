module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Preadditive
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject

/-!
# A two-sided tensor inverse makes a sheaf of modules invertible

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)`. There are two ways to say that a
sheaf `L` of `𝒪`-modules is invertible:

* the *two-sided inverse* form: there is a sheaf of modules `M` together with isomorphisms
  `L ⊗ M ≅ 𝒪` and `M ⊗ L ≅ 𝒪`, that is, `CategoryTheory.MonoidalCategory.IsInvertible` for the
  monoidal structure on sheaves of modules;
* the *equivalence* form: tensoring on the left by `L` is an equivalence of the category of
  sheaves of `𝒪`-modules, that is, `Stacks.SheafOfModules.IsInvertible`.

The two forms agree, and an invertible sheaf of modules is flat.

## Main definitions

* `Stacks.SheafOfModules.tensorLeftFunctorIsoTensorLeft`: the tensor functor
  `N ↦ (L.val ⊗ N.val)^#` is the left-tensoring functor of the monoidal structure on sheaves of
  modules.
* `Stacks.SheafOfModules.sheafTensorRightIsoTensorLeftFunctor`: the functors `G ↦ (G ⊗ L)^#` and
  `G ↦ (L ⊗ G)^#` are isomorphic.
* `CategoryTheory.MonoidalCategory.HasInverse.map`: the image of a two-sided tensor inverse
  under a monoidal functor.
* `CategoryTheory.MonoidalCategory.HasInverse.ofBraided`: in a braided monoidal category a
  one-sided tensor inverse is automatically two-sided.

## Main results

* `Stacks.SheafOfModules.isInvertible_of_hasInverse` and
  `Stacks.SheafOfModules.isInvertible_of_monoidalIsInvertible`: a two-sided tensor inverse makes
  tensoring by `L` an equivalence.
* `CategoryTheory.MonoidalCategory.isInvertible_of_tensorIsoUnit`: in a braided category only
  the single isomorphism `X ⊗ Y ≅ 𝟙` has to be produced.
* `Stacks.SheafOfModules.hasInverse_of_isInvertible` and
  `Stacks.SheafOfModules.isInvertible_iff_monoidalIsInvertible`: the converse, and hence the
  agreement of the two notions.
* `Stacks.SheafOfModules.isFlat_of_isInvertible_ringedSite`: an invertible sheaf of modules on a
  ringed site is flat.
* `CategoryTheory.MonoidalCategory.IsInvertible.map`: a monoidal functor sends invertible
  objects to invertible objects.

## References

* [The Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM) — the equivalent
  characterizations of an invertible object of a monoidal category.
* [The Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN) — invertible
  objects of a monoidal category.
* [The Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS) — invertible
  sheaves of modules.
* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor
  product of sheaves of modules.
* [The Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N) — an invertible
  sheaf of modules on a ringed site is flat of finite presentation.
* [The Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER) — flatness of a
  sheaf of modules on a site.
-/

@[expose] public section

open CategoryTheory

open scoped MonoidalCategory

universe v u w

namespace CategoryTheory.MonoidalCategory

section

variable {C : Type*} [Category C] [MonoidalCategory C]
  {D : Type*} [Category D] [MonoidalCategory D]

/-- The image of a two-sided tensor inverse under a monoidal functor: `F X'` is a two-sided
tensor inverse of `F X`, the isomorphisms being obtained from those of `X'` by the tensorator
and the unit isomorphism of `F`. -/
noncomputable def HasInverse.map (F : C ⥤ D) [F.Monoidal] {X : C} (h : HasInverse X) :
    HasInverse (F.obj X) where
  inv := F.obj h.inv
  isoLeft :=
    Functor.Monoidal.μIso F X h.inv ≪≫ F.mapIso h.isoLeft ≪≫ (Functor.Monoidal.εIso F).symm
  isoRight :=
    Functor.Monoidal.μIso F h.inv X ≪≫ F.mapIso h.isoRight ≪≫ (Functor.Monoidal.εIso F).symm

/-- A monoidal functor sends invertible objects to invertible objects. -/
theorem IsInvertible.map (F : C ⥤ D) [F.Monoidal] {X : C} (h : IsInvertible X) :
    IsInvertible (F.obj X) :=
  Nonempty.elim h fun hX => ⟨hX.map F⟩

/-- In a braided monoidal category a one-sided tensor inverse is automatically two-sided: the
braiding turns `X ⊗ X' ≅ 𝟙` into `X' ⊗ X ≅ 𝟙`. -/
noncomputable def HasInverse.ofBraided [BraidedCategory C] {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) :
    HasInverse X where
  inv := Y
  isoLeft := e
  isoRight := β_ Y X ≪≫ e

/-- In a braided monoidal category, an object with a one-sided tensor inverse is invertible. -/
theorem isInvertible_of_tensorIsoUnit [BraidedCategory C] {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) :
    IsInvertible X :=
  ⟨HasInverse.ofBraided e⟩

end

end CategoryTheory.MonoidalCategory

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] monoidalCategory braidedCategory

/-- The tensor functor `N ↦ (L.val ⊗ N.val)^#` of `Stacks.SheafOfModules.Tensor.sheafTensor` is the
left-tensoring functor `N ↦ L ⊗ N` of the monoidal structure on sheaves of modules. -/
noncomputable def tensorLeftFunctorIsoTensorLeft
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj L ≅
      (MonoidalCategory.tensorLeft L :) :=
  Functor.isoWhiskerLeft (SheafOfModules.forget
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      (Functor.Monoidal.commTensorLeft (sheafifyFunctor 𝒪 h𝒪) L.val).symm ≪≫
    Functor.isoWhiskerRight (forgetSheafifyIso 𝒪 h𝒪)
      (MonoidalCategory.tensorLeft ((sheafifyFunctor 𝒪 h𝒪).obj L.val)) ≪≫
    (MonoidalCategory.curriedTensor
      (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))).mapIso
        (sheafifyValIso 𝒪 h𝒪 L)

/-- Tensoring on the left by `L` is an equivalence exactly when the tensor functor
`N ↦ (L.val ⊗ N.val)^#` is. -/
theorem isEquivalence_tensorLeft_iff
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (MonoidalCategory.tensorLeft L).IsEquivalence ↔
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj
          L).IsEquivalence :=
  Functor.isEquivalence_iff_of_iso (tensorLeftFunctorIsoTensorLeft 𝒪 h𝒪 L).symm

/-- A sheaf of modules with a two-sided tensor inverse is invertible in the sense of
`Stacks.SheafOfModules.IsInvertible`, that is, tensoring by it is an equivalence of the category of
sheaves of modules. -/
theorem isInvertible_of_hasInverse
    {L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (h : MonoidalCategory.HasInverse L) : IsInvertible 𝒪 h𝒪 L :=
  (isInvertible_iff_tensorLeftFunctor_isEquivalence 𝒪 h𝒪 L).mpr
    ((isEquivalence_tensorLeft_iff 𝒪 h𝒪 L).mp h.tensorLeftEquivalence.isEquivalence_functor)

/-- A sheaf of modules which is invertible in the sense of
`CategoryTheory.MonoidalCategory.IsInvertible` is invertible in the sense of
`Stacks.SheafOfModules.IsInvertible`. -/
theorem isInvertible_of_monoidalIsInvertible
    {L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (h : MonoidalCategory.IsInvertible L) : IsInvertible 𝒪 h𝒪 L :=
  Nonempty.elim h (isInvertible_of_hasInverse 𝒪 h𝒪)

/-- An invertible sheaf of modules has a two-sided tensor inverse. -/
noncomputable def hasInverse_of_isInvertible
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      [IsInvertible 𝒪 h𝒪 L] :
    MonoidalCategory.HasInverse L :=
  have : (MonoidalCategory.tensorLeft L).IsEquivalence :=
    (isEquivalence_tensorLeft_iff 𝒪 h𝒪 L).mpr inferInstance
  MonoidalCategory.hasInverse_of_tensorLeft_isEquivalence

/-- The two forms of invertibility of a sheaf of modules agree: having a two-sided tensor
inverse is the same as tensoring by it being an equivalence. -/
theorem isInvertible_iff_monoidalIsInvertible
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    IsInvertible 𝒪 h𝒪 L ↔ MonoidalCategory.IsInvertible L :=
  ⟨fun _ => ⟨hasInverse_of_isInvertible 𝒪 h𝒪 L⟩, isInvertible_of_monoidalIsInvertible 𝒪 h𝒪⟩

section Flat

variable (O : Sheaf J CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O.obj))

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

/-- The tensor functors `G ↦ (G ⊗_O L)^#` and `G ↦ (L ⊗_O G)^#` are isomorphic, through the
braiding of the symmetric monoidal structure on presheaves of modules. -/
noncomputable def sheafTensorRightIsoTensorLeftFunctor
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O.obj hO)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj L ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor O).obj L :=
  Functor.isoWhiskerLeft _
    (Functor.isoWhiskerRight
      (FlatCoproduct.tensorRightIso O.obj L.val ≪≫
        (BraidedCategory.tensorLeftIsoTensorRight L.val).symm) _)

/-- An invertible sheaf of modules on a ringed site is flat. -/
@[stacks 0B8N "(a), the flatness half"]
theorem isFlat_of_isInvertible_ringedSite
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O.obj hO))
    (hL : IsInvertible O.obj hO L) :
    IsFlat (O := O) L := by
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj L).IsEquivalence :=
    (isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ L).mp hL
  exact (exactFunctor _ _).prop_of_iso (sheafTensorRightIsoTensorLeftFunctor O hO L).symm
    ((exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩)

end Flat

end Stacks.SheafOfModules

end
