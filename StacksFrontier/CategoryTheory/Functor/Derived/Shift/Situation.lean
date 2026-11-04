module

import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Functor.Derived.Morphisms
public import StacksFrontier.CategoryTheory.Localization.Saturated.Closure
public import StacksFrontier.CategoryTheory.Localization.Saturated.Defs
import StacksCore.Tactic.EgaSgaAttribute


/-!
# Derived functors and shifts: the situation and the fraction categories

The bundled Situation 13.14.1 (Tag 05S8), the categories `X/S` and `S/X` as full subcategories
of `Under X` and `Over X` with their defining diagrams, and their comparison with the canonical
comma categories `S.Under ⊤ X` and `S.Over ⊤ X`, used for [Stacks, Tag 05SY].

## References

* [Stacks, Tag 05SY](https://stacks.math.columbia.edu/tag/05SY)
-/

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-
# Problem Description

This is Lemma 13.14.11 of the Stacks Project, Tag 05SY
(https://stacks.math.columbia.edu/tag/05SY).

We work in the setting of derived functors "in general" on triangulated categories
(Stacks Chapter 13, Section 13.14).

## Situation (Stacks 13.14.1, Tag 05S8)

Let `F : D ⥤ D'` be an exact functor of triangulated categories, and let `S` be a
saturated multiplicative system in `D` that is compatible with the triangulated
structure on `D`. In particular `S` satisfies the (left and right) calculus of
fractions axioms and is stable under the shift functors: `s ∈ S ↔ s⟦n⟧ ∈ S`.

We write `⟦n⟧` (`n : ℤ`) for the `n`-fold shift (translation) auto-equivalence on `D`
and on `D'`. Because `F` is exact it commutes with shifts, i.e. there are functorial
isomorphisms `F(X⟦n⟧) ≅ F(X)⟦n⟧`.

For an object `X` of `D`, the category `X/S` has as objects the morphisms `s : X ⟶ X'`
with `s ∈ S` (used to form right derived functors); the category `S/X` has as objects
the morphisms `s : X' ⟶ X` with `s ∈ S` (used for left derived functors).

## Definitions used

These are the project's formalizations of the source's notions, not redefined here.

* Stacks 4.22.1 (Tag 05PU): a (co)filtered diagram is *essentially constant*
  with respect to a chosen (co)cone (`EssentiallyConstantInd.IsEssentiallyConstantWith`).
* Stacks 13.14.2 (Tag 05S9, `CategoryTheory.Functor.IsRightDerivedValueAt`): the right (resp. left)
  derived functor `RF` (resp. `LF`) is *defined at* `X` if the ind-object `(s : X ⟶ X') ↦ F(X')`
  (resp. the pro-object `(s : X' ⟶ X) ↦ F(X')`) is essentially constant; its value is `RF(X)`
  (resp. `LF(X)`). In that case there is a canonical map `F(X) → RF(X)` (resp. `LF(X) → F(X)`)
  coming from the object `id_X` of the index category.
* Stacks 13.14.10 (Tag 05SX, `CategoryTheory.Functor.ComputesRightDerived`): `X` *computes* `RF`
  (resp. `LF`) if `RF` (resp. `LF`) is defined at `X` and the canonical map `F(X) → RF(X)` (resp.
  `LF(X) → F(X)`) is an isomorphism.

## Main Statement (Stacks 13.14.11, Tag 05SY)

Let `X` be an object of `D` and `n : ℤ`.
1. `X` computes `RF` if and only if `X⟦n⟧` computes `RF`.
2. `X` computes `LF` if and only if `X⟦n⟧` computes `LF`.
-/

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace Stacks.DerivedFunctor.Shift

/-! ## The Situation (Stacks 13.14.1, Tag 05S8) -/

-- The universes `u`, `u'`, `v`, `v'` only occur together in the structure's sort
-- (they are always used as the object/hom universes of the bundled `D`, `D'`); this is
-- the same benign situation handled with this flag elsewhere in the project.
/-- Stacks Situation 13.14.1, Tag 05S8. The data of an exact functor `F : D ⥤ D'` between
triangulated categories together with a saturated multiplicative system `S` in `D`
compatible with the triangulated structure. We additionally record (it is part of
"compatible with the triangulated structure") that `S` is stable under the shift functors.

Note: `D` and `D'` carry pretriangulated structures, `F` commutes with shifts
(`Functor.CommShift`) and is triangulated (`Functor.IsTriangulated`), which is the
Mathlib notion of an exact functor of triangulated categories. -/
structure Situation where
  /-- Source triangulated category. -/
  {D : Type u}
  [categoryD : Category.{v} D]
  [zeroD : HasZeroObject D]
  [shiftD : HasShift D ℤ]
  [preadditiveD : Preadditive D]
  [shiftAdditiveD : ∀ n : ℤ, (shiftFunctor D n).Additive]
  [pretriangulatedD : Pretriangulated D]
  /-- Target triangulated category. -/
  {D' : Type u'}
  [categoryD' : Category.{v'} D']
  [zeroD' : HasZeroObject D']
  [shiftD' : HasShift D' ℤ]
  [preadditiveD' : Preadditive D']
  [shiftAdditiveD' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
  [pretriangulatedD' : Pretriangulated D']
  /-- The functor `F`. -/
  F : D ⥤ D'
  [commShiftF : F.CommShift ℤ]
  [triangulatedF : F.IsTriangulated]
  /-- The saturated multiplicative system `S`. -/
  S : MorphismProperty D
  saturatedS : S.IsSaturated
  [shiftCompatibleS : S.IsCompatibleWithShift ℤ]
  compatibleTriangulationS : S.IsCompatibleWithTriangulation

namespace Situation

attribute [instance] categoryD zeroD shiftD preadditiveD shiftAdditiveD pretriangulatedD
  categoryD' zeroD' shiftD' preadditiveD' shiftAdditiveD' pretriangulatedD'
  commShiftF triangulatedF shiftCompatibleS

variable (sit : Situation)

/-- The saturated system `S` admits a calculus of left fractions. -/
instance : sit.S.HasLeftCalculusOfFractions :=
  sit.saturatedS.hasLeftCalculusOfFractions

/-- The saturated system `S` admits a calculus of right fractions. -/
instance : sit.S.HasRightCalculusOfFractions :=
  sit.saturatedS.hasRightCalculusOfFractions

/-- The saturated system `S` is multiplicative. -/
instance : sit.S.IsMultiplicative :=
  sit.saturatedS.isMultiplicative

/-! ### The comma categories `X/S` and `S/X` and their (co)diagrams -/

/-- The object property on `StructuredArrow X (𝟭 D)` selecting those arrows
`s : X ⟶ X'` with `s ∈ S`. -/
@[implicit_reducible]
def rightFractionProp (X : sit.D) : ObjectProperty (StructuredArrow X (𝟭 sit.D)) :=
  fun A => sit.S A.hom

/-- The comma-type category `X/S` whose objects are arrows `s : X ⟶ X'` with `s ∈ S`. -/
abbrev RightFractions (X : sit.D) : Type _ := (sit.rightFractionProp X).FullSubcategory

/-- The ind-object diagram `X/S ⥤ D'`, sending `(s : X ⟶ X') ↦ F(X')`. -/
@[implicit_reducible]
def rightDiagram (X : sit.D) : sit.RightFractions X ⥤ sit.D' :=
  (sit.rightFractionProp X).ι ⋙ StructuredArrow.proj X (𝟭 sit.D) ⋙ sit.F

/-- The distinguished object `id_X : X ⟶ X` of `X/S` (it lies in `X/S` since `S` contains
identities). Its image under the ind-diagram is (definitionally) `F(X)`. -/
@[implicit_reducible]
def rightId (X : sit.D) : sit.RightFractions X :=
  ⟨StructuredArrow.mk (𝟙 X), sit.S.id_mem X⟩

/-- The object property on `CostructuredArrow (𝟭 D) X` selecting those arrows
`s : X' ⟶ X` with `s ∈ S`. -/
@[implicit_reducible]
def leftFractionProp (X : sit.D) : ObjectProperty (CostructuredArrow (𝟭 sit.D) X) :=
  fun A => sit.S A.hom

/-- The comma-type category `S/X` whose objects are arrows `s : X' ⟶ X` with `s ∈ S`. -/
abbrev LeftFractions (X : sit.D) : Type _ := (sit.leftFractionProp X).FullSubcategory

/-- The pro-object diagram `S/X ⥤ D'`, sending `(s : X' ⟶ X) ↦ F(X')`. -/
@[implicit_reducible]
def leftDiagram (X : sit.D) : sit.LeftFractions X ⥤ sit.D' :=
  (sit.leftFractionProp X).ι ⋙ CostructuredArrow.proj (𝟭 sit.D) X ⋙ sit.F

/-- The distinguished object `id_X : X ⟶ X` of `S/X`. Its image under the pro-diagram is
(definitionally) `F(X)`. -/
@[implicit_reducible]
def leftId (X : sit.D) : sit.LeftFractions X :=
  ⟨CostructuredArrow.mk (𝟙 X), sit.S.id_mem X⟩

/-! The constructions below bridge this file's full-subcategory presentation to the
canonical comma categories `S.Under ⊤ X` and `S.Over ⊤ X` of Tag 05S9, on which
`CategoryTheory.Functor.ComputesRightDerived` and `ComputesLeftDerived` (Tag 05SX) are stated. -/

/-- Forget the full-subcategory packaging of `X/S` in favour of Mathlib's canonical
`S.Under ⊤ X`. -/
def rightFractionsToCanonical (X : sit.D) :
    sit.RightFractions X ⥤ sit.S.Under ⊤ X where
  obj A := MorphismProperty.Under.mk ⊤ A.obj.hom A.property
  map f := MorphismProperty.Under.homMk f.hom.right (StructuredArrow.w f.hom)
  map_id A := by ext; rfl
  map_comp f g := by ext; rfl

/-- The legacy-to-canonical right-fraction functor is fully faithful. -/
def rightFractionsToCanonicalFullyFaithful (X : sit.D) :
    (sit.rightFractionsToCanonical X).FullyFaithful where
  preimage f :=
    ObjectProperty.homMk
      (StructuredArrow.homMk f.right (MorphismProperty.Under.w f))
  map_preimage f := by ext; rfl

/-- The legacy-to-canonical right-fraction functor is essentially surjective. -/
abbrev rightFractionsToCanonicalEssSurj (X : sit.D) :
    (sit.rightFractionsToCanonical X).EssSurj where
  mem_essImage A := by
    refine ⟨⟨StructuredArrow.mk A.hom, show sit.S A.hom from A.prop⟩, ⟨?_⟩⟩
    exact MorphismProperty.Under.isoMk (B := A) (Iso.refl _)
      (by simp [rightFractionsToCanonical])

/-- The full-subcategory and canonical comma-category presentations of `X/S` are
equivalent. -/
noncomputable def rightFractionsEquivCanonical (X : sit.D) :
    sit.RightFractions X ≌ sit.S.Under ⊤ X := by
  let ff := rightFractionsToCanonicalFullyFaithful sit X
  let es := rightFractionsToCanonicalEssSurj sit X
  letI : (sit.rightFractionsToCanonical X).IsEquivalence :=
    { faithful := ff.faithful, full := ff.full, essSurj := es }
  exact (sit.rightFractionsToCanonical X).asEquivalence

/-- Forget the full-subcategory packaging of `S/X` in favour of Mathlib's canonical
`S.Over ⊤ X`. -/
def leftFractionsToCanonical (X : sit.D) :
    sit.LeftFractions X ⥤ sit.S.Over ⊤ X where
  obj A := MorphismProperty.Over.mk ⊤ A.obj.hom A.property
  map f := MorphismProperty.Over.homMk f.hom.left (CostructuredArrow.w f.hom)
  map_id A := by ext; rfl
  map_comp f g := by ext; rfl

/-- The legacy-to-canonical left-fraction functor is fully faithful. -/
def leftFractionsToCanonicalFullyFaithful (X : sit.D) :
    (sit.leftFractionsToCanonical X).FullyFaithful where
  preimage f :=
    ObjectProperty.homMk
      (CostructuredArrow.homMk f.left (MorphismProperty.Over.w f))
  map_preimage f := by ext; rfl

/-- The legacy-to-canonical left-fraction functor is essentially surjective. -/
abbrev leftFractionsToCanonicalEssSurj (X : sit.D) :
    (sit.leftFractionsToCanonical X).EssSurj where
  mem_essImage A := by
    refine ⟨⟨CostructuredArrow.mk A.hom, show sit.S A.hom from A.prop⟩, ⟨?_⟩⟩
    exact MorphismProperty.Over.isoMk (B := A) (Iso.refl _)
      (by simp [leftFractionsToCanonical])

/-- The full-subcategory and canonical comma-category presentations of `S/X` are
equivalent. -/
noncomputable def leftFractionsEquivCanonical (X : sit.D) :
    sit.LeftFractions X ≌ sit.S.Over ⊤ X := by
  let ff := leftFractionsToCanonicalFullyFaithful sit X
  let es := leftFractionsToCanonicalEssSurj sit X
  letI : (sit.leftFractionsToCanonical X).IsEquivalence :=
    { faithful := ff.faithful, full := ff.full, essSurj := es }
  exact (sit.leftFractionsToCanonical X).asEquivalence

/-- The ind-object on `RightFractions X` agrees with the ind-object of Tag 05S9 on
`S.Under ⊤ X` after reindexing along `rightFractionsEquivCanonical`. -/
def rightDiagramCanonicalIso (X : sit.D) :
    sit.rightDiagram X ≅
      (sit.rightFractionsEquivCanonical X).functor ⋙
        (MorphismProperty.Under.forget sit.S ⊤ X ⋙ Under.forget X ⋙ sit.F) :=
  Iso.refl _

/-- The pro-object on `LeftFractions X` agrees with the pro-object of Tag 05S9 on
`S.Over ⊤ X` after reindexing along `leftFractionsEquivCanonical`. -/
def leftDiagramCanonicalIso (X : sit.D) :
    sit.leftDiagram X ≅
      (sit.leftFractionsEquivCanonical X).functor ⋙
        (MorphismProperty.Over.forget sit.S ⊤ X ⋙ Over.forget X ⋙ sit.F) :=
  Iso.refl _

/-! ### Passing between `S.Under ⊤ X` and `RightFractions X`

`X` computes `RF` (Tag 05SX, `CategoryTheory.Functor.ComputesRightDerived`) when some essentially
constant cocone on the ind-object over `S.Under ⊤ X` has an invertible coprojection at `𝟙 X`.
The shift and isomorphism invariance below are proved on the full-subcategory presentation
`RightFractions X`, and the two lemmas here carry that condition across the equivalence
`rightFractionsEquivCanonical`. Dually for `LF`. -/

/-- The computing condition on `S.Under ⊤ X` gives the same condition on `RightFractions X`. -/
private lemma rightFractions_of_canonical (X : sit.D)
    (h : ∃ c : Cocone (MorphismProperty.Under.forget sit.S ⊤ X ⋙ Under.forget X ⋙ sit.F),
      (∃ i r, EssentiallyConstantInd.IsEssentiallyConstantWith _ c i r) ∧
        IsIso (c.ι.app (MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem sit.S X)))) :
    ∃ c : Cocone (sit.rightDiagram X),
      (∃ i r, EssentiallyConstantInd.IsEssentiallyConstantWith _ c i r) ∧
        IsIso (c.ι.app (sit.rightId X)) :=
  EssentiallyConstantInd.exists_isIso_of_equivalence (sit.rightFractionsEquivCanonical X).functor
    (𝟭 _) (sit.rightDiagramCanonicalIso X ≪≫
      Functor.isoWhiskerLeft _ (Functor.rightUnitor _).symm) (Iso.refl _) h

/-- The computing condition on `RightFractions X` gives the same condition on `S.Under ⊤ X`. -/
private lemma canonical_of_rightFractions (X : sit.D)
    (h : ∃ c : Cocone (sit.rightDiagram X),
      (∃ i r, EssentiallyConstantInd.IsEssentiallyConstantWith _ c i r) ∧
        IsIso (c.ι.app (sit.rightId X))) :
    ∃ c : Cocone (MorphismProperty.Under.forget sit.S ⊤ X ⋙ Under.forget X ⋙ sit.F),
      (∃ i r, EssentiallyConstantInd.IsEssentiallyConstantWith _ c i r) ∧
        IsIso (c.ι.app (MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem sit.S X))) :=
  EssentiallyConstantInd.exists_isIso_of_equivalence (sit.rightFractionsEquivCanonical X).inverse
    (𝟭 _) ((Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (sit.rightFractionsEquivCanonical X).counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        ((sit.rightDiagramCanonicalIso X).symm ≪≫ (Functor.rightUnitor _).symm))
    ((sit.rightFractionsEquivCanonical X).unitIso.app (sit.rightId X)).symm h

/-- The computing condition on `S.Over ⊤ X` gives the same condition on `LeftFractions X`. -/
private lemma leftFractions_of_canonical (X : sit.D)
    (h : ∃ c : Cone (MorphismProperty.Over.forget sit.S ⊤ X ⋙ Over.forget X ⋙ sit.F),
      (∃ i r, EssentiallyConstantPro.IsEssentiallyConstantWith _ c i r) ∧
        IsIso (c.π.app (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem sit.S X)))) :
    ∃ c : Cone (sit.leftDiagram X),
      (∃ i r, EssentiallyConstantPro.IsEssentiallyConstantWith _ c i r) ∧
        IsIso (c.π.app (sit.leftId X)) :=
  EssentiallyConstantPro.exists_isIso_of_equivalence (sit.leftFractionsEquivCanonical X).functor
    (𝟭 _) (Functor.isoWhiskerLeft _ (Functor.rightUnitor _) ≪≫
      (sit.leftDiagramCanonicalIso X).symm) (Iso.refl _) h

/-- The computing condition on `LeftFractions X` gives the same condition on `S.Over ⊤ X`. -/
private lemma canonical_of_leftFractions (X : sit.D)
    (h : ∃ c : Cone (sit.leftDiagram X),
      (∃ i r, EssentiallyConstantPro.IsEssentiallyConstantWith _ c i r) ∧
        IsIso (c.π.app (sit.leftId X))) :
    ∃ c : Cone (MorphismProperty.Over.forget sit.S ⊤ X ⋙ Over.forget X ⋙ sit.F),
      (∃ i r, EssentiallyConstantPro.IsEssentiallyConstantWith _ c i r) ∧
        IsIso (c.π.app (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem sit.S X))) :=
  EssentiallyConstantPro.exists_isIso_of_equivalence (sit.leftFractionsEquivCanonical X).inverse
    (𝟭 _) (Functor.isoWhiskerLeft _ ((Functor.rightUnitor _) ≪≫ sit.leftDiagramCanonicalIso X) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (sit.leftFractionsEquivCanonical X).counitIso _ ≪≫
      Functor.leftUnitor _)
    ((sit.leftFractionsEquivCanonical X).unitIso.app (sit.leftId X)).symm h
end Situation

end Stacks.DerivedFunctor.Shift

end

end
