module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.Reseat

/-!
# The monoidal category `D_QCoh(𝒪_X)`

For a scheme `X` the derived category `D(𝒪_X)` is symmetric monoidal under the derived tensor
product, [Stacks, Tag 0FPT], and the full subcategory `D_QCoh(𝒪_X)` of complexes with
quasi-coherent cohomology contains the unit `𝒪_X[0]` and is closed under the derived tensor
product, [Stacks, Tag 08DX] part (1). So `D_QCoh(𝒪_X)` is a monoidal category.

This file records that structure, re-seated so that its tensor bifunctor *is*
`Stacks.Duality.quasiCoherentDerivedTensor X` and its unit *is*
`Stacks.Duality.DerivedPushforward.derivedStructureSheaf X`, by `rfl`, so that a statement about
the monoidal category `D_QCoh(𝒪_X)` is a statement about the quasi-coherent derived tensor
product, and conversely.

## Main definitions

* `Stacks.Duality.quasiCoherentDerivedMonoidal` — the monoidal structure on `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.Duality.curriedTensor_quasiCoherentDerivedMonoidal` and
  `Stacks.Duality.tensorUnit_quasiCoherentDerivedMonoidal` — its tensor bifunctor and its unit, on
  the nose.

## Implementation notes

The ambient structure is `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal X`, whose
tensor bifunctor is the derived tensor product of [Stacks, Tag 06YU] on the nose, read at the
locally small model of `D(𝒪_X)` at which `D_QCoh(𝒪_X)` is defined here. The full subcategory
inherits it (`CategoryTheory.ObjectProperty.fullMonoidalSubcategory`), and
`CategoryTheory.MonoidalCategory.reseat` then moves its tensor bifunctor to the lifted one along
the isomorphism whose components are identities.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality

variable (X : Scheme.{u})

/-- `D_QCoh(𝒪_X)` is a monoidal subcategory of `D(𝒪_X)`: it contains `𝒪_X[0]` and is closed
under the derived tensor product ([Stacks, Tag 08DX] part (1)). -/
theorem quasiCoherent_isMonoidal :
    @ObjectProperty.IsMonoidal _ _ (Scheme.Modules.canonicalDerivedMonoidal X)
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)) :=
  let := Scheme.Modules.canonicalDerivedMonoidal X
  { prop_unit := (DerivedPushforward.derivedStructureSheaf X).property
    prop_tensor := fun K L hK hL => isQuasicoherent_homology_derivedTensor X ⟨K, hK⟩ ⟨L, hL⟩ }

/-- The lifted derived tensor product of a morphism in the second variable. -/
lemma quasiCoherentDerivedTensor_obj_map_hom (K : quasiCoherentDerivedCategory X)
    {L L' : quasiCoherentDerivedCategory X} (g : L ⟶ L') :
    (((quasiCoherentDerivedTensor X).obj K).map g).hom =
      ((derivedTensor X).obj K.obj).map g.hom := by
  have h : (((quasiCoherentDerivedTensor X).obj K).map g).hom =
      ((derivedTensor X).map (𝟙 K.obj)).app L.obj ≫ ((derivedTensor X).obj K.obj).map g.hom :=
    rfl
  rw [h, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- The lifted derived tensor product of a morphism in the first variable. -/
lemma quasiCoherentDerivedTensor_map_app_hom {K K' : quasiCoherentDerivedCategory X} (f : K ⟶ K')
    (L : quasiCoherentDerivedCategory X) :
    (((quasiCoherentDerivedTensor X).map f).app L).hom =
      ((derivedTensor X).map f.hom).app L.obj := by
  have h : (((quasiCoherentDerivedTensor X).map f).app L).hom =
      ((derivedTensor X).map f.hom).app L.obj ≫ ((derivedTensor X).obj K'.obj).map (𝟙 L.obj) :=
    rfl
  rw [h, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The tensor bifunctor of the full monoidal subcategory `D_QCoh(𝒪_X)` of
`(D(𝒪_X), canonicalDerivedMonoidal X)` is the lifted derived tensor product, up to the
isomorphism whose components are identities. -/
def quasiCoherentCurriedTensorIso :
    letI := Scheme.Modules.canonicalDerivedMonoidal X
    letI := quasiCoherent_isMonoidal X
    curriedTensor (quasiCoherentDerivedCategory X) ≅ quasiCoherentDerivedTensor X :=
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  letI := quasiCoherent_isMonoidal X
  NatIso.ofComponents
    (fun K => NatIso.ofComponents (fun L => Iso.refl _) (fun {L L'} g => by
      ext
      exact ((Category.comp_id _).trans (quasiCoherentDerivedTensor_obj_map_hom X K g).symm).trans
        (Category.id_comp _).symm))
    (fun {K K'} f => by
      ext L
      exact ((Category.comp_id _).trans (quasiCoherentDerivedTensor_map_app_hom X f L).symm).trans
        (Category.id_comp _).symm)

/-- **The monoidal category `D_QCoh(𝒪_X)`**, with the quasi-coherent derived tensor product
`Stacks.Duality.quasiCoherentDerivedTensor X` as its tensor bifunctor and
`Stacks.Duality.DerivedPushforward.derivedStructureSheaf X` as its unit, both on the nose. -/
@[instance_reducible]
def quasiCoherentDerivedMonoidal : MonoidalCategory (quasiCoherentDerivedCategory X) :=
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  letI := quasiCoherent_isMonoidal X
  @MonoidalCategory.reseat _ _ (ObjectProperty.fullMonoidalSubcategory _) _ _
    (quasiCoherentCurriedTensorIso X) (Iso.refl (DerivedPushforward.derivedStructureSheaf X))

/-- The tensor bifunctor of `Stacks.Duality.quasiCoherentDerivedMonoidal X` is
`Stacks.Duality.quasiCoherentDerivedTensor X`. -/
theorem curriedTensor_quasiCoherentDerivedMonoidal :
    @curriedTensor _ _ (quasiCoherentDerivedMonoidal X) = quasiCoherentDerivedTensor X :=
  rfl

/-- The unit of `Stacks.Duality.quasiCoherentDerivedMonoidal X` is `𝒪_X[0]`. -/
theorem tensorUnit_quasiCoherentDerivedMonoidal :
    @tensorUnit _ _ (quasiCoherentDerivedMonoidal X).toMonoidalCategoryStruct =
      DerivedPushforward.derivedStructureSheaf X :=
  rfl

end Stacks.Duality
