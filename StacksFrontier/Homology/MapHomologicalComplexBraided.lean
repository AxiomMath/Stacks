module

public import StacksFrontier.Algebra.Homology.KoszulSymmetric
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal

/-!
# A lax braided functor acts in a braided way on cochain complexes

Let `C` and `D` be symmetric monoidal preadditive categories with enough coproducts for the
total tensor product of `Mathlib.Algebra.Homology.Monoidal` to exist on `CochainComplex C ℤ` and
`CochainComplex D ℤ`, and equip both with the Koszul symmetry of
`StacksFrontier.Algebra.Homology.KoszulSymmetric`.  If `F : C ⥤ D` is additive and braided (and
preserves the antidiagonal coproducts occurring in a total complex), then

  `F.mapHomologicalComplex (ComplexShape.up ℤ) : CochainComplex C ℤ ⥤ CochainComplex D ℤ`

is monoidal by `StacksFrontier.Homology.MapHomologicalComplexMonoidal`, and this file shows that it
is moreover *lax braided* for the Koszul symmetries: its tensorator commutes with the Koszul
braiding.

The Koszul sign is no obstruction.  On the summand of bidegree `(p, q)` of the source both sides
of the identity acquire the sign `(-1)^(p * q)`: the braiding of complexes moves the summand
`(p, q)` to the summand `(q, p)` on both sides at once, so the two signs are the *same* sign and
cancel, leaving exactly the lax braided identity `Functor.LaxBraided.braided` of `F` in degrees
`p` and `q`.

## Main results

* `CategoryTheory.Functor.mapHomologicalComplexTensorator_braiding`: the tensorator of
  `F.mapHomologicalComplex (ComplexShape.up ℤ)` commutes with the Koszul braiding.

## Implementation notes

The Koszul symmetry is not a global instance (see the documentation of
`StacksFrontier.Algebra.Homology.KoszulSymmetric`), so it is brought in here by
`attribute [local instance] CochainComplex.symmetricCategory`.  With that instance in force the
monoidal-category notation `β_` on `CochainComplex C ℤ` means `CochainComplex.koszulBraiding`,
but only up to unfolding two structure projections; since every rewrite in the proof has to be
syntactic, `CochainComplex.ιTensorObj_braiding` restates
`CochainComplex.ιTensorObj_koszulBraiding` at exactly the `β_` spelling the goal presents, and
it is that restatement which is rewritten with.

The identity itself is proved by extensionality on the summands of its *source*, which is the
total complex `F K ⊗ F L` in `D` and therefore a coproduct on the nose: the image `F (K ⊗ L)`,
which is a coproduct only because `F` preserves these coproducts, never has to be taken apart.
Both `F`'s tensorator and the Koszul braiding are characterised on such a summand
(`Functor.ι_mapHomologicalComplexTensorator_hom` and `CochainComplex.ιTensorObj_braiding`), and
the `ℤˣ`-scalar is pulled through `F.map` by `Functor.map_units_smul`, available because an
additive functor is `ℤ`-linear.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v v' u u'

attribute [local instance] CochainComplex.symmetricCategory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [SymmetricCategory C] [HasZeroObject C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The braiding of `CochainComplex C ℤ` on homogeneous summands.

This is `CochainComplex.ιTensorObj_koszulBraiding` restated with the monoidal-category notation
`β_` for the braiding of `CochainComplex.symmetricCategory`, and with the proof that
`q + p = n` taken as an argument, so that the statement is written at exactly the spelling a
goal about `β_` presents. -/
@[reassoc]
public lemma ιTensorObj_braiding (K L : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n)
    (h' : q + p = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (β_ K L).hom.f n =
      ((p * q).negOnePow : ℤˣ) • ((β_ (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιTensorObj L K q p n h') :=
  ιTensorObj_koszulBraiding K L p q n h

end CochainComplex

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [MonoidalCategory D] [Preadditive C] [Preadditive D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D]
  [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ X₁ : D, ((curriedTensor D).obj X₁).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ : GradedObject ℤ D), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ D, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ D, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ D, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (F : C ⥤ D) [F.Additive] [F.Braided]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) F]

/-- **A lax braided functor acts in a braided way on cochain complexes**: the tensorator of
`F.mapHomologicalComplex (ComplexShape.up ℤ)` commutes with the Koszul braiding. -/
public lemma mapHomologicalComplexTensorator_braiding (K L : CochainComplex C ℤ) :
    (mapHomologicalComplexTensorator F K L).hom ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (β_ K L).hom =
      (β_ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).hom ≫
        (mapHomologicalComplexTensorator F L K).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have h : p + q = n := hpq
  have h' : q + p = n := by omega
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [ι_mapHomologicalComplexTensorator_hom_assoc, ← F.map_comp,
    CochainComplex.ιTensorObj_braiding K L p q n h h', F.map_units_smul, F.map_comp,
    Linear.comp_units_smul, CochainComplex.ιTensorObj_braiding_assoc
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) p q n h h',
    Linear.units_smul_comp, Category.assoc, ι_mapHomologicalComplexTensorator_hom,
    Functor.LaxBraided.braided_assoc]
  rfl

end CategoryTheory.Functor

end
