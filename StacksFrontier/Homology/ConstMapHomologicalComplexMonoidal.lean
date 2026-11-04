module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryConst
public import StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal

/-!
# Constant diagrams of complexes are monoidal, and the colimit of complexes is oplax monoidal

Let `J` be a category and `D` a monoidal preadditive category with a zero object, whose tensor
product commutes with the coproducts occurring in a total complex.  Then `J ⥤ D` is such a
category too, by `StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits`, so both
`HomologicalComplex D c` and `HomologicalComplex (J ⥤ D) c` carry the total tensor product of
`Mathlib.Algebra.Homology.Monoidal`, and this file records that

  `(Functor.const J).mapHomologicalComplex c :
      HomologicalComplex D c ⥤ HomologicalComplex (J ⥤ D) c`

is a monoidal functor between them, while its left adjoint

  `(colim).mapHomologicalComplex c :
      HomologicalComplex (J ⥤ D) c ⥤ HomologicalComplex D c`

is oplax monoidal.  The latter is the canonical comparison morphism
`colim (K₁ ⊗ K₂) ⟶ colim K₁ ⊗ colim K₂` for complexes; no hypothesis making it invertible is
assumed, and none is claimed.

This is the complex-level form of the statement that lower shriek along the projection of a
chaotic site to a point is compatible with the tensor product.  The derived form, Stacks
08QC, is *not* obtained here: passing from complexes to the derived category requires
descending through the homotopy localization and then through the K-flat localization, and
neither descent is performed in this file.  See the implementation notes.

## Main definitions

* `CategoryTheory.Functor.const_additive`: `Functor.const J : D ⥤ (J ⥤ D)` is additive.
  Mathlib has this only for `J = Cᵒᵖ`
  (the unnamed instance in `Mathlib/CategoryTheory/Sites/Abelian.lean`).
* `CategoryTheory.Functor.constMapHomologicalComplexMonoidal`: constant diagrams of
  complexes form a monoidal functor.
* `CategoryTheory.Limits.colimMapHomologicalComplexAdjunction`: the adjunction
  `colim.mapHomologicalComplex c ⊣ (Functor.const J).mapHomologicalComplex c`.
* `CategoryTheory.Limits.colimMapHomologicalComplexOplaxMonoidal`: **the colimit of complexes
  is oplax monoidal.**

## Implementation notes

`Functor.constMapHomologicalComplexMonoidal` is `inferInstance`: it is
`CategoryTheory.Functor.mapHomologicalComplexMonoidal` of
`StacksFrontier.Homology.MapHomologicalComplexMonoidal` instantiated at `Functor.const J`, and
every hypothesis of that instance is discharged by typeclass inference once `J ⥤ D` is known
to be monoidal preadditive with a tensor product commuting with coproducts.  That is the only
reason the definition is short, and it is why it is recorded by name: the instantiation is the
content.

The oplax structure on `colim.mapHomologicalComplex c` comes from the adjunction, so its
comparison map is the mate of the identity; `colim.mapHomologicalComplex c` is a left adjoint
of a monoidal, hence lax monoidal, functor, and `Adjunction.leftAdjointOplaxMonoidal` applies.
It is *not* strong monoidal: that would say the colimit of a tensor product of complexes is
the tensor product of the colimits, which is false in general.

What is missing for the derived statement is a lax monoidal structure on
`(Functor.const J).mapDerivedCategory`.  Getting one from
`Functor.constMapHomologicalComplexMonoidal` means applying
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` twice, once for the homotopy
category and once for the K-flat localization of `CochainComplex.KFlatMonoidal.derivedMonoidal`,
and the second application needs `Functor.const J` to send K-flat complexes to K-flat
complexes.  That is a mathematical statement about K-flatness in a functor category, not a
formal consequence of anything here, and it is not proved in this repository.
-/

@[expose] public noncomputable section

universe w v₁ u₁ v₂ u₂ u

namespace CategoryTheory

open Limits MonoidalCategory

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D]

/-- **`Functor.const J : D ⥤ (J ⥤ D)` is additive**: addition of natural transformations in
`J ⥤ D` is computed objectwise, and `Functor.const` is the identity on morphisms in every
component.

Mathlib records this only for the special case `J = Cᵒᵖ`, in
`Mathlib/CategoryTheory/Sites/Abelian.lean`, where it is stated in a shape that typeclass
inference cannot use for a general `J`. -/
instance Functor.const_additive [Preadditive D] :
    (Functor.const J : D ⥤ (J ⥤ D)).Additive where
  map_add := by
    intro _ _ _ _
    ext _
    rfl

/-- **The colimit functor `(J ⥤ D) ⥤ D` is additive** whenever `D` is preadditive and has the
colimits: it is a left adjoint of the additive functor `Functor.const J`.

`CategoryTheory.DeltaFunctor.colim_additive` is the same statement proved directly, but only
for an abelian target. -/
instance Limits.colim_additive [Preadditive D] [HasColimitsOfShape J D] :
    (colim (J := J) (C := D)).Additive :=
  (colimConstAdj (J := J) (C := D)).left_adjoint_additive

section

variable [MonoidalCategory D] [Preadditive D] [MonoidalPreadditive D] [HasZeroObject D]
  {I : Type u} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]
  [HasCoproducts.{u} D] [HasColimitsOfSize.{u, u} D] [HasInitial D]
  [∀ X : D, PreservesColimitsOfSize.{u, u} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{u, u} (tensorRight X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]

/-- **Constant diagrams of complexes form a monoidal functor**

`(Functor.const J).mapHomologicalComplex c :
    HomologicalComplex D c ⥤ HomologicalComplex (J ⥤ D) c`

for the total tensor product on each side.  This is
`CategoryTheory.Functor.mapHomologicalComplexMonoidal` applied to the strong monoidal functor
`Functor.const J` of `CategoryTheory.Functor.constMonoidal`; the graded-object conditions it
requires for the functor category `J ⥤ D` are supplied by
`StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits`. -/
@[instance_reducible]
def Functor.constMapHomologicalComplexMonoidal :
    (((Functor.const J : D ⥤ (J ⥤ D))).mapHomologicalComplex c).Monoidal :=
  inferInstance

variable [HasColimitsOfShape J D]

/-- The adjunction `colim.mapHomologicalComplex c ⊣ (Functor.const J).mapHomologicalComplex c`,
obtained degreewise from `CategoryTheory.Limits.colimConstAdj`. -/
def Limits.colimMapHomologicalComplexAdjunction :
    (colim (J := J) (C := D)).mapHomologicalComplex c ⊣
      (Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex c :=
  Adjunction.mapHomologicalComplexAdjunction (colimConstAdj (J := J) (C := D)) c

/-- **The colimit of complexes is oplax monoidal**: there is a canonical comparison morphism

`colim (K₁ ⊗ K₂) ⟶ colim K₁ ⊗ colim K₂`

of complexes, natural and compatible with the associator and the unitors, for the total
tensor product on each side.

It is the mate of the identity under
`CategoryTheory.Limits.colimMapHomologicalComplexAdjunction`, whose right adjoint is monoidal
by `CategoryTheory.Functor.constMapHomologicalComplexMonoidal`.  No hypothesis making the
comparison invertible is assumed, and the functor is not claimed to be strong monoidal. -/
@[instance_reducible]
def Limits.colimMapHomologicalComplexOplaxMonoidal :
    ((colim (J := J) (C := D)).mapHomologicalComplex c).OplaxMonoidal :=
  letI := Functor.constMapHomologicalComplexMonoidal (J := J) (D := D) (c := c)
  (Limits.colimMapHomologicalComplexAdjunction (J := J) (D := D) (c := c)).leftAdjointOplaxMonoidal

end

end CategoryTheory

end
