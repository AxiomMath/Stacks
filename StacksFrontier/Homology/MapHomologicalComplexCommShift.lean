module

public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
public import StacksFrontier.Homology.MapHomologicalComplexMonoidalTensorator
public import StacksFrontier.Homology.TotalComplexTransportShift
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift

/-!
# The tensorator of a degreewise monoidal functor commutes with the shift

Let `F : C ⥤ D` be an additive monoidal functor between monoidal preadditive categories whose
tensor products commute with the coproducts occurring in a total complex, so that
`StacksFrontier.Homology.MapHomologicalComplexMonoidal` makes

`F.mapHomologicalComplex (ComplexShape.up ℤ) : CochainComplex C ℤ ⥤ CochainComplex D ℤ`

a monoidal functor for the total tensor product on each side.  Both cochain complex categories
carry the shift by `ℤ`, the degreewise functor commutes with it
(`CategoryTheory.Functor.commShiftMapCochainComplex`), and each `K ⊗ -` and `- ⊗ L` commutes with
it too.  This file proves that the tensorator

`F K ⊗ F L ⟶ F (K ⊗ L)`

is compatible with those commutations in each variable, i.e. that the degreewise functor satisfies
`CategoryTheory.Functor.LaxMonoidal.CommShift`.

That is the Koszul sign bookkeeping of the total tensor complex, and it is the complex-level
content of the assertion that the tensorator of a derived monoidal functor commutes with the
shift.

## Main definitions

* `CochainComplex.Monoidal.tensorLeft_commShift` and
  `CochainComplex.Monoidal.tensorRight_commShift`: **`K ⊗ -` and `- ⊗ L` on `CochainComplex C ℤ`
  commute with the shift**, for the total tensor product of `Mathlib.Algebra.Homology.Monoidal`.

## Main results

* `CategoryTheory.Functor.commShift_μNatTransFst_mapHomologicalComplex` and
  `commShift_μNatTransSnd_mapHomologicalComplex`: the tensorator of
  `F.mapHomologicalComplex (ComplexShape.up ℤ)`, read in one variable at a time, commutes with the
  shift.
* `CategoryTheory.Functor.mapHomologicalComplexLaxMonoidalCommShift`: **the tensorator commutes
  with the shift in each variable**, as a
  `CategoryTheory.Functor.LaxMonoidal.CommShift` instance.

## Implementation notes

**The two one-variable shift commutations of the total tensor product are Mathlib's, read through
`map₂CochainComplex`.**  `MonoidalCategory.tensorLeft K` on `CochainComplex C ℤ` is
`(curriedTensor C).map₂CochainComplex.obj K` and `tensorRight L` is
`(curriedTensor C).map₂CochainComplex.flip.obj L`, definitionally but not syntactically, so the two
instances here are `inferInstanceAs` at the `map₂CochainComplex` spelling where
`Mathlib/Algebra/Homology/BifunctorShift.lean` supplies them.  Their commutation isomorphisms are
`CochainComplex.mapBifunctorShift₁Iso` (no sign) and `mapBifunctorShift₂Iso` (the sign
`(p * y).negOnePow` on the summand indexed by `(p, q)`), which is what
`tensorLeft_commShiftIso_hom_app` and `tensorRight_commShiftIso_hom_app` record.

**Why the sign is not an obstruction, and where the work actually happened.**  The tensorator of
`F.mapHomologicalComplex` is, by `CategoryTheory.Functor.mapHomologicalComplexTensorator`, the
inverse of `CategoryTheory.Functor.mapBifunctorTotalIso` at `Φ₁ = Φ₂ = Φ = F` and at the
degreewise comparison `CategoryTheory.Functor.mapHomologicalComplexTensorComparison`, and that
comparison's compatibility with the two shifts is
`CategoryTheory.Functor.mapBifunctorTotalIso_commShift₁` and `_commShift₂` of
`StacksFrontier/Homology/TotalComplexTransportShift.lean`.  The Koszul sign on the summand `(p, q)`
is `(p * y).negOnePow` on *both* sides of the square -- it is a function of the first index and the
shift only, not of the category -- and it passes through `F.map` because `F` is additive.  So the
signs cancel, and what is left is the transport comparison on the summand `(p, q + y)`.  The
first variable carries no sign at all.  Nothing here recomputes that; the two theorems below are
the two halves of `CategoryTheory.NatTrans.CommShift` written out and matched against those
lemmas.

**What has to be moved across the equation.**  The commutation square of
`mapBifunctorTotalIso_commShift₁`/`₂` is stated for the `hom` of the transport comparison, i.e.
for `F (K ⊗ L) ⟶ F K ⊗ F L`, while the tensorator is its `inverse`.  So each proof moves the
comparison at the shifted pair to the other side (`CategoryTheory.Iso.eq_inv_comp`), cancels the
shifted comparison at the unshifted pair against its inverse, and is then the cited lemma
reassociated.  The two `whiskerRight`/`whiskerLeft` bridge lemmas of
`StacksFrontier/Homology/MapHomologicalComplexMonoidal.lean` identify the
`HomologicalComplex.mapBifunctorMap` in which the cited lemma phrases the whiskered commutation
with the monoidal whiskering the class uses.

The final `rfl` of each proof crosses `(tensorRight L).obj K` versus
`CochainComplex.mapBifunctor K L (curriedTensor C)`: the monoidal structure of
`HomologicalComplex` is the total complex of `curriedTensor`, so the two are the same object, but
`MonoidalCategory.tensorObj` goes through the `MonoidalCategoryStruct` instance and no rewriting
tactic crosses that.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v v' u u'

/-! ### The tensor product of cochain complexes commutes with the shift in each variable -/

namespace CochainComplex.Monoidal

variable {E : Type u} [Category.{v} E] [MonoidalCategory E] [Preadditive E] [HasZeroObject E]
  [(curriedTensor E).Additive] [∀ X₁ : E, ((curriedTensor E).obj X₁).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ E), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : E, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).obj X₁)]
  [∀ X₂ : E, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ E, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ E, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ E, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- **`K ⊗ -` on `CochainComplex E ℤ` commutes with the shift**, for the total tensor product.
`MonoidalCategory.tensorLeft K` is `(curriedTensor E).map₂CochainComplex.obj K`, where
`Mathlib/Algebra/Homology/BifunctorShift.lean` supplies the commutation; the commutation
isomorphisms are `CochainComplex.mapBifunctorShift₂Iso`, which carry the Koszul sign. -/
instance tensorLeft_commShift (K : CochainComplex E ℤ) : (tensorLeft K).CommShift ℤ :=
  inferInstanceAs (((curriedTensor E).map₂CochainComplex.obj K).CommShift ℤ)

/-- **`- ⊗ L` on `CochainComplex E ℤ` commutes with the shift**, for the total tensor product.
The companion of `CochainComplex.Monoidal.tensorLeft_commShift`, at
`(curriedTensor E).map₂CochainComplex.flip.obj L`; its commutation isomorphisms are
`CochainComplex.mapBifunctorShift₁Iso`, which carry no sign. -/
instance tensorRight_commShift (L : CochainComplex E ℤ) : (tensorRight L).CommShift ℤ :=
  inferInstanceAs (((curriedTensor E).map₂CochainComplex.flip.obj L).CommShift ℤ)

/-- The commutation of `K ⊗ -` with the shift is `CochainComplex.mapBifunctorShift₂Iso`. -/
lemma tensorLeft_commShiftIso_hom_app (K L : CochainComplex E ℤ) (a : ℤ) :
    ((tensorLeft K).commShiftIso a).hom.app L =
      (CochainComplex.mapBifunctorShift₂Iso K L (curriedTensor E) a).hom := rfl

/-- The commutation of `- ⊗ L` with the shift is `CochainComplex.mapBifunctorShift₁Iso`. -/
lemma tensorRight_commShiftIso_hom_app (L K : CochainComplex E ℤ) (a : ℤ) :
    ((tensorRight L).commShiftIso a).hom.app K =
      (CochainComplex.mapBifunctorShift₁Iso K L (curriedTensor E) a).hom := rfl

end CochainComplex.Monoidal

/-! ### The tensorator of a degreewise monoidal functor -/

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [MonoidalCategory D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ X₁ : D, ((curriedTensor D).obj X₁).Additive]
  (F : C ⥤ D) [F.Additive] [F.Monoidal]
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
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) F]

/-- **The transport comparison `F (K ⊗ L) ≅ F K ⊗ F L` whose inverse is the tensorator.**  This is
`CategoryTheory.Functor.mapBifunctorTotalIso` at `Φ₁ = Φ₂ = Φ = F` and at the degreewise
comparison `CategoryTheory.Functor.mapHomologicalComplexTensorComparison`; it is named here only
so that the shift compatibilities of
`StacksFrontier/Homology/TotalComplexTransportShift.lean` can be quoted at one spelling. -/
abbrev mapHomologicalComplexTensoratorTotalIso (K L : CochainComplex C ℤ) :=
  mapBifunctorTotalIso (curriedTensor C) (curriedTensor D) F F F
    (mapHomologicalComplexTensorComparison F) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (mapHomologicalComplexTensorComparison_naturality_left F)
    (mapHomologicalComplexTensorComparison_naturality_right F) K L

/-- The tensorator of `F.mapHomologicalComplex (ComplexShape.up ℤ)` is the inverse of the
transport comparison. -/
lemma mu_mapHomologicalComplex_eq (K L : CochainComplex C ℤ) :
    μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L =
      (mapHomologicalComplexTensoratorTotalIso F K L).inv := rfl

/-- **The tensorator of `F.mapHomologicalComplex (ComplexShape.up ℤ)`, read in the first variable,
commutes with the shift.**  Neither the commutation of `- ⊗ L` with the shift nor the commutation
of the degreewise functor carries a sign, so this is
`CategoryTheory.Functor.mapBifunctorTotalIso_commShift₁` with the transport comparison at the
shifted pair moved to the other side of the equation. -/
theorem commShift_μNatTransFst_mapHomologicalComplex (L : CochainComplex C ℤ) :
    NatTrans.CommShift
      (μNatTransFst (F.mapHomologicalComplex (ComplexShape.up ℤ)) L) ℤ := by
  constructor
  intro a
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, μNatTransFst_app]
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app]
  have hV : HomologicalComplex.mapBifunctorMap
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso a).hom.app K)
        (𝟙 ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) (curriedTensor D)
        (ComplexShape.up ℤ) =
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso a).hom.app K ▷
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L := by
    rfl
  have key := mapBifunctorTotalIso_commShift₁ (curriedTensor C) (curriedTensor D) F F F
    (mapHomologicalComplexTensorComparison F)
    (mapHomologicalComplexTensorComparison_naturality_left F)
    (mapHomologicalComplexTensorComparison_naturality_right F) K L a
  rw [hV] at key
  rw [mu_mapHomologicalComplex_eq, mu_mapHomologicalComplex_eq,
    CochainComplex.Monoidal.tensorRight_commShiftIso_hom_app,
    CochainComplex.Monoidal.tensorRight_commShiftIso_hom_app]
  dsimp only [Functor.flip_obj_map, curriedTensor_map_app]
  rw [Iso.eq_inv_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% key]
  simp
  rfl

/-- **The tensorator of `F.mapHomologicalComplex (ComplexShape.up ℤ)`, read in the second variable,
commutes with the shift.**  This is the half carrying the Koszul sign: the commutation of `K ⊗ -`
with the shift is `CochainComplex.mapBifunctorShift₂Iso`, whose component on the summand indexed
by `(p, q)` is `(p * a).negOnePow` times the index shift.  That unit is the same on both sides of
the square and passes through `F.map`, so after it cancels the statement is
`CategoryTheory.Functor.mapBifunctorTotalIso_commShift₂`, again with the transport comparison at
the shifted pair moved across. -/
theorem commShift_μNatTransSnd_mapHomologicalComplex (K : CochainComplex C ℤ) :
    NatTrans.CommShift
      (μNatTransSnd (F.mapHomologicalComplex (ComplexShape.up ℤ)) K) ℤ := by
  constructor
  intro a
  apply NatTrans.ext
  funext L
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, μNatTransSnd_app]
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app]
  have hV : HomologicalComplex.mapBifunctorMap
        (𝟙 ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso a).hom.app L)
        (curriedTensor D) (ComplexShape.up ℤ) =
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ◁
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso a).hom.app L := by
    rfl
  have key := mapBifunctorTotalIso_commShift₂ (curriedTensor C) (curriedTensor D) F F F
    (mapHomologicalComplexTensorComparison F)
    (mapHomologicalComplexTensorComparison_naturality_left F)
    (mapHomologicalComplexTensorComparison_naturality_right F) K L a
  rw [hV] at key
  rw [mu_mapHomologicalComplex_eq, mu_mapHomologicalComplex_eq,
    CochainComplex.Monoidal.tensorLeft_commShiftIso_hom_app,
    CochainComplex.Monoidal.tensorLeft_commShiftIso_hom_app]
  dsimp only [curriedTensor_obj_map]
  rw [Iso.eq_inv_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% key]
  simp
  rfl

/-- **The tensorator of a degreewise monoidal functor on cochain complexes commutes with the shift
in each variable.**  The two halves are
`CategoryTheory.Functor.commShift_μNatTransFst_mapHomologicalComplex` and
`commShift_μNatTransSnd_mapHomologicalComplex`, and together they are the complex-level content of
the assertion that a derived monoidal functor's tensorator commutes with the shift. -/
instance mapHomologicalComplexLaxMonoidalCommShift :
    Functor.LaxMonoidal.CommShift (F.mapHomologicalComplex (ComplexShape.up ℤ)) ℤ where
  commShift_μNatTransFst L := commShift_μNatTransFst_mapHomologicalComplex F L
  commShift_μNatTransSnd K := commShift_μNatTransSnd_mapHomologicalComplex F K

end CategoryTheory.Functor

end
