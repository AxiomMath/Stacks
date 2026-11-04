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
# Derived functors and shifts: values

Values of the right and left derived functors in Situation 13.14.1 are compatible with shifts
and invariant under isomorphisms of objects ([Stacks, Tag 05SU]).

## References

* [Stacks, Tag 05SU](https://stacks.math.columbia.edu/tag/05SU)
-/

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-
# Problem Description

Stacks Project, Lemma 13.14.5 (Tag 05SU): "Derived functors are compatible with shifts."

We work in Situation 13.14.1 (Tag 05S7): `F : D ⥤ D'` is an exact functor of
triangulated categories, and `S` is a saturated multiplicative system in `D`
compatible with the triangulated structure on `D`.

For an object `X` of `D`:
* the right derived functor `RF` is *defined at* `X` if the ind-object
  `(X/S) ⥤ D'`, `(s : X ⟶ X') ↦ F(X')`, is essentially constant; the value is `RF(X)`;
* the left derived functor `LF` is *defined at* `X` if the pro-object
  `(S/X) ⥤ D'`, `(s : X' ⟶ X) ↦ F(X')`, is essentially constant; the value is `LF(X)`.

Here `X/S` is the (filtered) category of arrows `s : X ⟶ X'` in `S` with source `X`,
and `S/X` is the (cofiltered) category of arrows `s : X' ⟶ X` in `S` with target `X`.

Main statements (for `X` an object of `D` and `n : ℤ`):
1. `RF` is defined at `X` iff `RF` is defined at `X[n]`; and there is a canonical
   isomorphism `RF(X)[n] ≅ RF(X[n])` between the values.
2. `LF` is defined at `X` iff `LF` is defined at `X[n]`; and there is a canonical
   isomorphism `LF(X)[n] ≅ LF(X[n])` between the values.

## Remarks on the formalization

"Defined at" and "value" are those of Tag 05S9: a value of `RF` at `X` is a cocone `c` on the
ind-object over `S.Under ⊤ X` with `CategoryTheory.Functor.IsRightDerivedValueAt F S X c`, i.e.
carrying the essential-constancy data of Tag 05PU(1), and `c.pt` is `RF(X)`; dually for `LF`. A
value is a colimit (resp. limit) cocone (resp. cone), so it is unique up to unique isomorphism,
and the canonical isomorphism of the lemma is the comparison of colimits.

## Remarks on the "canonical isomorphism" of values

The mathematical heart of Lemma 13.14.5 is that the shift `[n]` carries the diagram
defining `RF` at `X` (up to the canonical natural isomorphism `F(X'[n]) ≅ F(X')[n]`
coming from `F.CommShift`) to the diagram defining `RF` at `X[n]`.  Consequently, if `c`
exhibits a value of `RF` at `X`, then `shiftCocone` exhibits `c.pt[n]` as a value of `RF` at
`X[n]` (`isRightDerivedValueAt_shiftCocone`).  Combined with the uniqueness of the value,
this produces the **canonical isomorphism** `RF(X)[n] ≅ RF(X[n])` of Lemma 13.14.5, here
returned as genuine `Iso` *data* by the `noncomputable def`s `rightDerived_value_shift_iso` /
`leftDerived_value_shift_iso`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe v v' u u'

namespace StacksDerivedShift

/-- A saturated multiplicative system contains all isomorphisms. -/
theorem isSaturated_mem_of_isIso {D : Type u} [Category.{v} D]
    {S : MorphismProperty D} (hSsat : S.IsSaturatedMultiplicative) {X Y : D} (f : X ⟶ Y) [IsIso f] :
    S f := by
  have h1 : S (inv f ≫ f) := by rw [IsIso.inv_hom_id]; exact hSsat.id_mem Y
  have h2 : S (f ≫ inv f) := by rw [IsIso.hom_inv_id]; exact hSsat.id_mem X
  exact hSsat.mem_of_comp_mem_comp (inv f) f (inv f) h1 h2

/-- A saturated multiplicative system respects isomorphisms. -/
theorem isSaturated_respectsIso {D : Type u} [Category.{v} D]
    {S : MorphismProperty D} (hSsat : S.IsSaturatedMultiplicative) : S.RespectsIso := by
  have hL : S.RespectsLeft (CategoryTheory.MorphismProperty.isomorphisms D) :=
    ⟨fun i hi f hf => by
      have : IsIso i := hi
      exact hSsat.comp_mem _ _ (isSaturated_mem_of_isIso hSsat i) hf⟩
  have hR : S.RespectsRight (CategoryTheory.MorphismProperty.isomorphisms D) :=
    ⟨fun i hi f hf => by
      have : IsIso i := hi
      exact hSsat.comp_mem _ _ hf (isSaturated_mem_of_isIso hSsat i)⟩
  exact ⟨⟩

/-!
## The categories `X/S` and `S/X` and the defining diagrams (Stacks, Definition 13.14.2)

The shift and isomorphism invariance below are proved on the presentation of `X/S`, resp. `S/X`,
as the full subcategory of `Under X`, resp. `Over X`, cut out by `S`. The values of `RF` and `LF`
in the sense of Tag 05S9 (`CategoryTheory.Functor.IsRightDerivedValueAt`,
`CategoryTheory.Functor.IsLeftDerivedValueAt`) live on the canonical comma categories
`S.Under ⊤ X` and `S.Over ⊤ X`; the equivalences `rightFractionCatEquiv`, `leftFractionCatEquiv`
identify the two presentations, the diagrams agreeing on the nose.
-/

section Diagrams

variable {D : Type u} [Category.{v} D] {D' : Type u'} [Category.{v'} D']

/-- The category `X/S`: arrows `s : X ⟶ X'` in `S` with source `X`, realized as the
full subcategory of `Under X` of those objects `f` with `S f.hom`. -/
@[sga "4½ Etat_0 2.6.4"]
abbrev RightFractionCat (S : MorphismProperty D) (X : D) : Type _ :=
  ObjectProperty.FullSubcategory (fun f : Under X => S f.hom)

/-- The category `S/X`: arrows `s : X' ⟶ X` in `S` with target `X`, realized as the
full subcategory of `Over X` of those objects `f` with `S f.hom`. -/
@[sga "4 I 8.7.5" "more general",
  sga "4 VI 6.5",
  sga "4½ Etat_0 2.3.2" "denominator category S_X",
  sga "4½ Etat_0 2.6.4"]
abbrev LeftFractionCat (S : MorphismProperty D) (X : D) : Type _ :=
  ObjectProperty.FullSubcategory (fun f : Over X => S f.hom)

/-- The diagram `(X/S) ⥤ D'`, `(s : X ⟶ X') ↦ F(X')`, defining `RF` at `X`. -/
@[implicit_reducible]
noncomputable def rightDiagram (F : D ⥤ D') (S : MorphismProperty D) (X : D) :
    RightFractionCat S X ⥤ D' :=
  ObjectProperty.ι _ ⋙ Under.forget X ⋙ F

/-- `rightDiagram F S X` sends an object `s : X ⟶ X'` of `X/S` to `F(X')`. -/
@[simp] lemma rightDiagram_obj (F : D ⥤ D') (S : MorphismProperty D) (X : D)
    (a : RightFractionCat S X) : (rightDiagram F S X).obj a = F.obj a.1.right := rfl

/-- The diagram `(S/X) ⥤ D'`, `(s : X' ⟶ X) ↦ F(X')`, defining `LF` at `X`. -/
@[implicit_reducible]
noncomputable def leftDiagram (F : D ⥤ D') (S : MorphismProperty D) (X : D) :
    LeftFractionCat S X ⥤ D' :=
  ObjectProperty.ι _ ⋙ Over.forget X ⋙ F

/-- `leftDiagram F S X` sends an object `s : X' ⟶ X` of `S/X` to `F(X')`. -/
@[simp] lemma leftDiagram_obj (F : D ⥤ D') (S : MorphismProperty D) (X : D)
    (a : LeftFractionCat S X) : (leftDiagram F S X).obj a = F.obj a.1.left := rfl

variable (S : MorphismProperty D)

/-- The full-subcategory presentation of `X/S` maps to the canonical `S.Under ⊤ X`. -/
def rightFractionCatToUnder (X : D) : RightFractionCat S X ⥤ S.Under ⊤ X where
  obj A := MorphismProperty.Under.mk ⊤ A.obj.hom A.property
  map f := MorphismProperty.Under.homMk f.hom.right (Under.w f.hom)

/-- The two presentations of `X/S` are equivalent. -/
noncomputable def rightFractionCatEquiv (X : D) : RightFractionCat S X ≌ S.Under ⊤ X :=
  letI : (rightFractionCatToUnder S X).IsEquivalence :=
    { faithful := ⟨fun h => ObjectProperty.hom_ext _ (Under.UnderMorphism.ext
        (congrArg (fun g => g.right) h))⟩
      full := ⟨fun f => ⟨ObjectProperty.homMk (Under.homMk f.right (MorphismProperty.Under.w f)),
        rfl⟩⟩
      essSurj := ⟨fun A => ⟨⟨Under.mk A.hom, A.prop⟩,
        ⟨MorphismProperty.Under.isoMk (Iso.refl _) (by simp [rightFractionCatToUnder])⟩⟩⟩ }
  (rightFractionCatToUnder S X).asEquivalence

/-- The full-subcategory presentation of `S/X` maps to the canonical `S.Over ⊤ X`. -/
def leftFractionCatToOver (X : D) : LeftFractionCat S X ⥤ S.Over ⊤ X where
  obj A := MorphismProperty.Over.mk ⊤ A.obj.hom A.property
  map f := MorphismProperty.Over.homMk f.hom.left (Over.w f.hom)

/-- The two presentations of `S/X` are equivalent. -/
noncomputable def leftFractionCatEquiv (X : D) : LeftFractionCat S X ≌ S.Over ⊤ X :=
  letI : (leftFractionCatToOver S X).IsEquivalence :=
    { faithful := ⟨fun h => ObjectProperty.hom_ext _ (Over.OverMorphism.ext
        (congrArg (fun g => g.left) h))⟩
      full := ⟨fun f => ⟨ObjectProperty.homMk (Over.homMk f.left (MorphismProperty.Over.w f)),
        rfl⟩⟩
      essSurj := ⟨fun A => ⟨⟨Over.mk A.hom, A.prop⟩,
        ⟨MorphismProperty.Over.isoMk (Iso.refl _) (by simp [leftFractionCatToOver])⟩⟩⟩ }
  (leftFractionCatToOver S X).asEquivalence

variable (F : D ⥤ D')

/-- The diagram on `RightFractionCat S X` is the ind-object of Tag 05S9 reindexed along
`rightFractionCatEquiv`. -/
noncomputable def rightDiagramIso (X : D) :
    rightDiagram F S X ≅ (rightFractionCatEquiv S X).functor ⋙
      (MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X ⋙ F) :=
  Iso.refl _

/-- The ind-object of Tag 05S9 is the diagram on `RightFractionCat S X` reindexed along the
inverse of `rightFractionCatEquiv`. -/
noncomputable def underDiagramIso (X : D) :
    MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X ⋙ F ≅
      (rightFractionCatEquiv S X).inverse ⋙ rightDiagram F S X :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (rightFractionCatEquiv S X).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (rightDiagramIso S F X).symm

/-- The diagram on `LeftFractionCat S X` is the pro-object of Tag 05S9 reindexed along
`leftFractionCatEquiv`. -/
noncomputable def leftDiagramIso (X : D) :
    (leftFractionCatEquiv S X).functor ⋙
      (MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F) ≅ leftDiagram F S X :=
  Iso.refl _

/-- The pro-object of Tag 05S9 is the diagram on `LeftFractionCat S X` reindexed along the
inverse of `leftFractionCatEquiv`. -/
noncomputable def overDiagramIso (X : D) :
    (leftFractionCatEquiv S X).inverse ⋙ leftDiagram F S X ≅
      MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F :=
  Functor.isoWhiskerLeft _ (leftDiagramIso S F X).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (leftFractionCatEquiv S X).counitIso _ ≪≫ Functor.leftUnitor _

/-- `RF` is defined at `X` iff the diagram on `RightFractionCat S X` is essentially constant. -/
theorem exists_isRightDerivedValueAt_iff_rightDiagram (X : D) :
    (∃ c, F.IsRightDerivedValueAt S X c) ↔
      EssentiallyConstantInd.IsEssentiallyConstantInd (rightDiagram F S X) := by
  rw [Functor.exists_isRightDerivedValueAt_iff]
  exact ⟨fun h => h.of_equivalence (rightFractionCatEquiv S X).functor (𝟭 D')
      (rightDiagramIso S F X ≪≫ Functor.isoWhiskerLeft _ (Functor.rightUnitor _).symm),
    fun h => h.of_equivalence (rightFractionCatEquiv S X).inverse (𝟭 D')
      (underDiagramIso S F X ≪≫ Functor.isoWhiskerLeft _ (Functor.rightUnitor _).symm)⟩

/-- `LF` is defined at `X` iff the diagram on `LeftFractionCat S X` is essentially constant. -/
theorem exists_isLeftDerivedValueAt_iff_leftDiagram (X : D) :
    (∃ c, F.IsLeftDerivedValueAt S X c) ↔
      EssentiallyConstantPro.IsEssentiallyConstantPro (leftDiagram F S X) := by
  rw [Functor.exists_isLeftDerivedValueAt_iff]
  exact ⟨fun h => h.of_equivalence (leftFractionCatEquiv S X).functor (𝟭 D')
      (Functor.isoWhiskerLeft _ (Functor.rightUnitor _) ≪≫ leftDiagramIso S F X),
    fun h => h.of_equivalence (leftFractionCatEquiv S X).inverse (𝟭 D')
      (Functor.isoWhiskerLeft _ (Functor.rightUnitor _) ≪≫ overDiagramIso S F X)⟩

end Diagrams

/-!
## Situation 13.14.1 (Tag 05S7) and the main lemma (Tag 05SU)

`D`, `D'` are triangulated categories, `F : D ⥤ D'` is an exact (triangulated) functor:
it is `Additive`, commutes with the shift (`F.CommShift ℤ`), and sends distinguished
triangles to distinguished triangles (`F.IsTriangulated`).  `S` is a saturated
multiplicative system in `D` compatible with the triangulated structure.
-/

/-- A property of objects that is stable under shifts and isomorphisms holds at `X` iff it holds
at `X⟦n⟧`. -/
private theorem iff_shift_of_shift_of_iso {D : Type u} [Category.{v} D] [HasShift D ℤ]
    (P : D → Prop) (hshift : ∀ (X : D) (n : ℤ), P X → P (X⟦n⟧))
    (hiso : ∀ {X' X : D}, (X' ≅ X) → P X' → P X) (X : D) (n : ℤ) : P X ↔ P (X⟦n⟧) :=
  ⟨hshift X n, fun h =>
    hiso ((shiftFunctorCompIsoId D n (-n) (by simp)).app X) (hshift _ (-n) h)⟩

section Situation

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type u'} [Category.{v'} D'] [Preadditive D'] [HasZeroObject D']
  [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
variable (F : D ⥤ D') [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
variable (S : MorphismProperty D) [S.IsMultiplicative] [S.IsCompatibleWithShift ℤ]
variable (hSsat : S.IsSaturatedMultiplicative) (hS : S.IsCompatibleWithTriangulation)

include hSsat hS

/-- **Reindexing equivalence of fraction categories (right/ind case).**
The shift autoequivalence `⟦n⟧ : D ≌ D` sends an object `(s : X⟦n⟧ ⟶ X')` of `(X⟦n⟧)/S`
to `(s⟦-n⟧ : X ⟶ X'⟦-n⟧)`... — more precisely it induces an equivalence of comma
categories `Under (X⟦n⟧) ≌ Under X` (apply `⟦-n⟧` and use `X⟦n⟧⟦-n⟧ ≅ X`), and since `S`
is compatible with the shift (`MorphismProperty.IsCompatibleWithShift.iff`) this restricts
to the full subcategories cut out by `S`, giving `(X⟦n⟧)/S ≌ X/S`.

PROOF STRATEGY (formal phase): build the underlying `Under (X⟦n⟧) ≌ Under X` from the
autoequivalence `shiftEquiv D (-n) : D ≌ D` together with the canonical iso
`(X⟦n⟧)⟦-n⟧ ≅ X` (`shiftEquiv`/`shiftFunctorCompIsoId`), realized as a map of `Comma`
categories (`Comma.mapLeft`/`Comma.map` or `Under.map` along the structure morphisms,
then upgraded to an equivalence by `Comma.mapLeftIso`/`Equivalence.mk`).  Then restrict to
the `S`-full subcategories: an arrow `s` lies in `S` iff `s⟦-n⟧` does, by
`MorphismProperty.IsCompatibleWithShift.iff S _ (-n)` (and its converse via `⟦n⟧`).  Use
`ObjectProperty.lift`/`FullSubcategory.map` + `Equivalence.mk` to assemble the restricted
equivalence.  This is pure 2-categorical bookkeeping with the shift autoequivalence; it
does NOT use triangulated structure beyond `S.IsCompatibleWithShift`. -/
noncomputable def rightFractionCat_shiftEquiv (X : D) (n : ℤ) :
    RightFractionCat S (X⟦n⟧) ≌ RightFractionCat S X := by
  haveI : S.RespectsIso := isSaturated_respectsIso hSsat
  -- base equivalence on `Under`
  let e : Under (X⟦n⟧) ≌ Under X := (Under.postEquiv X (shiftEquiv D n)).symm
  -- the two `S`-properties on `Under (X⟦n⟧)` and `Under X`
  let P₁ : ObjectProperty (Under (X⟦n⟧)) := fun f => S f.hom
  let P₂ : ObjectProperty (Under X) := fun f => S f.hom
  -- forward functor preserves the property
  have hF : ∀ A : ObjectProperty.FullSubcategory P₁, P₂ (e.functor.obj A.1) := by
    intro A
    have key := (MorphismProperty.IsCompatibleWithShift.iff S A.1.hom (-n)).2 A.2
    dsimp [e, Under.postEquiv, Under.post, Under.map, shiftEquiv]
    exact (MorphismProperty.cancel_left_of_respectsIso S
      ((shiftFunctorCompIsoId D n (-n) (by simp)).inv.app X)
      ((shiftFunctor D (-n)).map A.1.hom)).2 key
  -- inverse functor preserves the property
  have hG : ∀ B : ObjectProperty.FullSubcategory P₂, P₁ (e.inverse.obj B.1) := by
    intro B
    dsimp [e, Under.postEquiv, Under.post, shiftEquiv]
    exact (MorphismProperty.IsCompatibleWithShift.iff S B.1.hom n).2 B.2
  let Fwd : ObjectProperty.FullSubcategory P₁ ⥤ ObjectProperty.FullSubcategory P₂ :=
    ObjectProperty.lift P₂ (ObjectProperty.ι P₁ ⋙ e.functor) hF
  let Inv : ObjectProperty.FullSubcategory P₂ ⥤ ObjectProperty.FullSubcategory P₁ :=
    ObjectProperty.lift P₁ (ObjectProperty.ι P₂ ⋙ e.inverse) hG
  exact
    { functor := Fwd
      inverse := Inv
      unitIso := NatIso.ofComponents
        (fun A => P₁.isoMk (e.unitIso.app A.1))
        (by
          intro A B f
          apply (ObjectProperty.ι P₁).map_injective
          simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk])
      counitIso := NatIso.ofComponents
        (fun B => P₂.isoMk (e.counitIso.app B.1))
        (by
          intro A B f
          apply (ObjectProperty.ι P₂).map_injective
          simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk])
      functor_unitIso_comp := by
        intro A
        apply (ObjectProperty.ι P₂).map_injective
        simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk] }

/-- **The shifted defining diagram agrees with the diagram at `X⟦n⟧` (right/ind case).**
Transporting the diagram `rightDiagram F S X : X/S ⥤ D'` first by post-composition with
the shift `⟦n⟧ : D' ≌ D'` and then by the reindexing equivalence `(X⟦n⟧)/S ≌ X/S` yields,
up to canonical natural isomorphism, the diagram `rightDiagram F S (X⟦n⟧)`.

This is the mathematical heart: on an object `(s : X⟦n⟧ ⟶ X')` of `(X⟦n⟧)/S`, the left
side evaluates to `F(X'⟦-n⟧)⟦n⟧` (apply reindex, sending it to `X'⟦-n⟧`, then `F`, then
`⟦n⟧`), while the right side evaluates to `F(X')`.  These are canonically isomorphic via
`F.commShiftIso n` (giving `F(X'⟦-n⟧)⟦n⟧ ≅ F(X'⟦-n⟧⟦n⟧)`) composed with `F` applied to the
counit iso `X'⟦-n⟧⟦n⟧ ≅ X'`.  Naturality in `s` is naturality of `commShiftIso` and of the
shift counit.

PROOF STRATEGY (formal phase): `NatIso.ofComponents`, components from `F.commShiftIso`
(`Functor.CommShift.commShiftIso`) and the shift counit `shiftFunctorCompIsoId` /
`shiftEquiv` unit-counit; naturality by `simp [rightDiagram, ...]` plus
`commShiftIso_hom_naturality`. Alternatively assemble from `Functor.isoWhiskerLeft`/
`Functor.isoWhiskerRight` on the constituent functors `ObjectProperty.ι`, `Under.forget`,
`F`, `shiftFunctor`. Uses `F.CommShift ℤ` essentially. -/
noncomputable def rightDiagram_shift_natIso (X : D) (n : ℤ) :
    (rightFractionCat_shiftEquiv S hSsat X n).functor ⋙
        (rightDiagram F S X ⋙ shiftFunctor D' n) ≅ rightDiagram F S (X⟦n⟧) :=
  NatIso.ofComponents
    (fun A =>
      ((F.commShiftIso n).app ((shiftFunctor D (-n)).obj A.obj.right)).symm ≪≫
        F.mapIso ((shiftFunctorCompIsoId D (-n) n (by simp)).app A.obj.right))
    (by
      intro A B f
      dsimp [rightDiagram, rightFractionCat_shiftEquiv, ObjectProperty.lift,
        Under.postEquiv, Under.post, Under.map, shiftEquiv]
      rw [← Category.assoc, Functor.commShiftIso_inv_naturality F
          ((shiftFunctor D (-n)).map (Under.Hom.right f.hom)) n, Category.assoc, Category.assoc,
        ← F.map_comp, ← F.map_comp]
      congr 1
      exact congrArg F.map
        ((shiftFunctorCompIsoId D (-n) n (by simp)).hom.naturality (Under.Hom.right f.hom)))

/-- **The shifted value.** The cocone on the ind-object at `X⟦n⟧` obtained from a cocone `c` on
the ind-object at `X` by applying `⟦n⟧` and reindexing along `(X⟦n⟧)/S ≌ X/S`; its vertex is
`c.pt⟦n⟧`. -/
noncomputable def shiftCocone (X : D) (n : ℤ)
    (c : Cocone (MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X ⋙ F)) :
    Cocone (MorphismProperty.Under.forget S ⊤ (X⟦n⟧) ⋙ Under.forget (X⟦n⟧) ⋙ F) :=
  (Cocone.precompose (underDiagramIso S F (X⟦n⟧)).hom).obj <|
    Cocone.whisker (rightFractionCatEquiv S (X⟦n⟧)).inverse <|
    (Cocone.precompose (rightDiagram_shift_natIso F S hSsat X n).inv).obj <|
    Cocone.whisker (rightFractionCat_shiftEquiv S hSsat X n).functor <|
    (shiftFunctor D' n).mapCocone <|
    (Cocone.precompose (rightDiagramIso S F X).hom).obj <|
    Cocone.whisker (rightFractionCatEquiv S X).functor c

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasZeroObject D'] [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.Additive] [F.IsTriangulated] [S.IsMultiplicative] [Preadditive D] [Preadditive D'] hS in
/-- **Statement (1) — the shifted value is a value at `X[n]`.** If `c` exhibits `c.pt` as a
value of `RF` at `X`, then `shiftCocone` exhibits `c.pt⟦n⟧` as a value of `RF` at `X[n]`: the
autoequivalence `[n]` carries the ind-object at `X` (up to the natural isomorphism coming from
`F.CommShift`) to the ind-object at `X[n]`, and essential constancy is carried along. -/
theorem isRightDerivedValueAt_shiftCocone (X : D) (n : ℤ)
    {c : Cocone (MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X ⋙ F)}
    (hc : F.IsRightDerivedValueAt S X c) :
    F.IsRightDerivedValueAt S (X⟦n⟧) (shiftCocone F S hSsat X n c) := by
  rw [Functor.isRightDerivedValueAt_iff] at hc ⊢
  obtain ⟨i, r, h⟩ := hc
  exact ⟨_, _, ((((((h.whisker_of_essSurj _).precompose (rightDiagramIso S F X)).map
    (shiftFunctor D' n)).whisker_of_essSurj _).precompose
    (rightDiagram_shift_natIso F S hSsat X n).symm).whisker_of_essSurj _).precompose
    (underDiagramIso S F (X⟦n⟧))⟩

/-- **Reindexing equivalence of fraction categories along an arbitrary iso of the base.**
An isomorphism `φ : X' ≅ X` in `D` induces an equivalence `Under X' ≌ Under X`
(`Under.mapIso φ.symm`), which restricts to the `S`-full subcategories because `S`
respects isomorphisms (it is saturated), giving `(X'/S) ≌ (X/S)`.  This is the analogue
of `rightFractionCat_shiftEquiv` for a general iso instead of a shift. -/
noncomputable def rightFractionCat_isoEquiv {X' X : D} (φ : X' ≅ X) :
    RightFractionCat S X' ≌ RightFractionCat S X := by
  haveI : S.RespectsIso := isSaturated_respectsIso hSsat
  let e : Under X' ≌ Under X := Under.mapIso (id φ.symm)
  let P₁ : ObjectProperty (Under X') := fun f => S f.hom
  let P₂ : ObjectProperty (Under X) := fun f => S f.hom
  have hF : ∀ A : ObjectProperty.FullSubcategory P₁, P₂ (e.functor.obj A.1) := by
    intro A
    change S (φ.inv ≫ A.1.hom)
    exact (MorphismProperty.cancel_left_of_respectsIso S φ.inv A.1.hom).2 A.2
  have hG : ∀ B : ObjectProperty.FullSubcategory P₂, P₁ (e.inverse.obj B.1) := by
    intro B
    change S (φ.hom ≫ B.1.hom)
    exact (MorphismProperty.cancel_left_of_respectsIso S φ.hom B.1.hom).2 B.2
  let Fwd : ObjectProperty.FullSubcategory P₁ ⥤ ObjectProperty.FullSubcategory P₂ :=
    ObjectProperty.lift P₂ (ObjectProperty.ι P₁ ⋙ e.functor) hF
  let Inv : ObjectProperty.FullSubcategory P₂ ⥤ ObjectProperty.FullSubcategory P₁ :=
    ObjectProperty.lift P₁ (ObjectProperty.ι P₂ ⋙ e.inverse) hG
  exact
    { functor := Fwd
      inverse := Inv
      unitIso := NatIso.ofComponents
        (fun A => P₁.isoMk (e.unitIso.app A.1))
        (by
          intro A B f
          apply (ObjectProperty.ι P₁).map_injective
          simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk])
      counitIso := NatIso.ofComponents
        (fun B => P₂.isoMk (e.counitIso.app B.1))
        (by
          intro A B f
          apply (ObjectProperty.ι P₂).map_injective
          simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk])
      functor_unitIso_comp := by
        intro A
        apply (ObjectProperty.ι P₂).map_injective
        simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk] }

/-- **The defining diagram is invariant (up to natural iso) under reindexing by an iso of
the base.**  Reindexing `rightDiagram F S X'` along `(rightFractionCat_isoEquiv φ).symm`
yields, up to canonical natural iso, `rightDiagram F S X`.  On objects the two diagrams
agree on the nose (the forgetful object `.right` is unchanged by `Under.map`), so the
components are identities. -/
noncomputable def rightDiagram_iso_natIso {X' X : D} (φ : X' ≅ X) :
    (rightFractionCat_isoEquiv S hSsat φ).symm.functor ⋙ rightDiagram F S X' ≅
      rightDiagram F S X :=
  NatIso.ofComponents
    (fun A => Iso.refl _)
    (by
      intro A B f
      dsimp [rightDiagram, rightFractionCat_isoEquiv, ObjectProperty.lift,
        Under.mapIso, Under.map, Comma.mapLeft]
      simp)

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasZeroObject D'] [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] [S.IsMultiplicative]
  [S.IsCompatibleWithShift ℤ] [Preadditive D] [HasShift D ℤ] [Preadditive D'] [HasShift D' ℤ] hS in
/-- **Definedness is invariant under an iso of the base object.**
If `φ : X' ≅ X` and `RF` is defined at `X'`, then `RF` is defined at `X`. -/
theorem rightDerived_definedAt_of_iso {X' X : D} (φ : X' ≅ X)
    (h : ∃ c, F.IsRightDerivedValueAt S X' c) : ∃ c, F.IsRightDerivedValueAt S X c := by
  rw [exists_isRightDerivedValueAt_iff_rightDiagram] at h ⊢
  exact h.of_equivalence (rightFractionCat_isoEquiv S hSsat φ).symm.functor (𝟭 D')
    ((rightDiagram_iso_natIso F S hSsat φ).symm ≪≫
      Functor.isoWhiskerLeft _ (Functor.rightUnitor _).symm)

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasZeroObject D'] [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.Additive] [F.IsTriangulated] [S.IsMultiplicative] [Preadditive D] [Preadditive D'] hS in
/-- **Statement (1) — `RF` and shifts (definedness biconditional).**
`RF` is defined at `X` if and only if `RF` is defined at `X[n]`. -/
@[stacks 05SU "(1)"]
theorem rightDerived_definedAt_iff_shift (X : D) (n : ℤ) :
    (∃ c, F.IsRightDerivedValueAt S X c) ↔ ∃ c, F.IsRightDerivedValueAt S (X⟦n⟧) c := by
  exact iff_shift_of_shift_of_iso (fun X => ∃ c, F.IsRightDerivedValueAt S X c)
    (fun X n ⟨_, hc⟩ => ⟨_, isRightDerivedValueAt_shiftCocone F S hSsat X n hc⟩)
    (rightDerived_definedAt_of_iso F S hSsat) X n

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasZeroObject D'] [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.Additive] [F.IsTriangulated] [S.IsMultiplicative] [Preadditive D] [Preadditive D'] hS in
/-- **Statement (1) — canonical isomorphism of values `RF(X)[n] ≅ RF(X[n])`.**
Given a value `c` of `RF` at `X` and a value `d` of `RF` at `X[n]`, this is the canonical
isomorphism `c.pt⟦n⟧ ≅ d.pt`, returned as genuine `Iso` *data*: `shiftCocone` exhibits
`c.pt⟦n⟧` as a value at `X[n]`, a value is a colimit cocone, and the isomorphism is the
comparison of the two colimit cocones. -/
@[stacks 05SU "(1)"]
noncomputable def rightDerived_value_shift_iso (X : D) (n : ℤ)
    {c : Cocone (MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X ⋙ F)}
    (hc : F.IsRightDerivedValueAt S X c)
    {d : Cocone (MorphismProperty.Under.forget S ⊤ (X⟦n⟧) ⋙ Under.forget (X⟦n⟧) ⋙ F)}
    (hd : F.IsRightDerivedValueAt S (X⟦n⟧) d) :
    c.pt⟦n⟧ ≅ d.pt :=
  (isRightDerivedValueAt_shiftCocone F S hSsat X n hc).isColimit.coconePointUniqueUpToIso
    hd.isColimit

/-- **Reindexing equivalence of fraction categories (left/pro case).**
Dual of `rightFractionCat_shiftEquiv`.  The shift autoequivalence on `D` induces an
equivalence `S/(X⟦n⟧) ≌ S/X` of the cofiltered fraction categories.

PROOF STRATEGY (formal phase): build `S/(X⟦n⟧) ≌ S/X` exactly as in the right case but
with `Over`/`Over.forget` in place of `Under`/`Under.forget` (the shift autoequivalence
`⟦-n⟧` carries `Over (X⟦n⟧)` to `Over X` via `X⟦n⟧⟦-n⟧ ≅ X`, restricting to `S` by
`MorphismProperty.IsCompatibleWithShift.iff`). -/
noncomputable def leftFractionCat_shiftEquiv (X : D) (n : ℤ) :
    LeftFractionCat S (X⟦n⟧) ≌ LeftFractionCat S X := by
  haveI : S.RespectsIso := isSaturated_respectsIso hSsat
  let e : Over (X⟦n⟧) ≌ Over X := (Over.postEquiv X (shiftEquiv D n)).symm
  let P₁ : ObjectProperty (Over (X⟦n⟧)) := fun f => S f.hom
  let P₂ : ObjectProperty (Over X) := fun f => S f.hom
  have hF : ∀ A : ObjectProperty.FullSubcategory P₁, P₂ (e.functor.obj A.1) := by
    intro A
    have key := (MorphismProperty.IsCompatibleWithShift.iff S A.1.hom (-n)).2 A.2
    dsimp [e, Over.postEquiv, Over.post, Over.map, shiftEquiv]
    exact (MorphismProperty.cancel_right_of_respectsIso S
      ((shiftFunctor D (-n)).map A.1.hom)
      ((shiftFunctorCompIsoId D n (-n) (by simp)).hom.app X)).2 key
  have hG : ∀ B : ObjectProperty.FullSubcategory P₂, P₁ (e.inverse.obj B.1) := by
    intro B
    dsimp [e, Over.postEquiv, Over.post, shiftEquiv]
    exact (MorphismProperty.IsCompatibleWithShift.iff S B.1.hom n).2 B.2
  let Fwd : ObjectProperty.FullSubcategory P₁ ⥤ ObjectProperty.FullSubcategory P₂ :=
    ObjectProperty.lift P₂ (ObjectProperty.ι P₁ ⋙ e.functor) hF
  let Inv : ObjectProperty.FullSubcategory P₂ ⥤ ObjectProperty.FullSubcategory P₁ :=
    ObjectProperty.lift P₁ (ObjectProperty.ι P₂ ⋙ e.inverse) hG
  exact
    { functor := Fwd
      inverse := Inv
      unitIso := NatIso.ofComponents
        (fun A => P₁.isoMk (e.unitIso.app A.1))
        (by
          intro A B f
          apply (ObjectProperty.ι P₁).map_injective
          simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk])
      counitIso := NatIso.ofComponents
        (fun B => P₂.isoMk (e.counitIso.app B.1))
        (by
          intro A B f
          apply (ObjectProperty.ι P₂).map_injective
          simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk])
      functor_unitIso_comp := by
        intro A
        apply (ObjectProperty.ι P₂).map_injective
        simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk] }

/-- **The shifted defining diagram agrees with the diagram at `X⟦n⟧` (left/pro case).**
Dual of `rightDiagram_shift_natIso`: transporting `leftDiagram F S X` by post-composition with
the shift `⟦n⟧` and reindexing by `leftFractionCat_shiftEquiv` yields, up to the canonical
natural iso built from `F.commShiftIso n` and the shift counit, `leftDiagram F S (X⟦n⟧)`. -/
noncomputable def leftDiagram_shift_natIso (X : D) (n : ℤ) :
    (leftFractionCat_shiftEquiv S hSsat X n).functor ⋙
        (leftDiagram F S X ⋙ shiftFunctor D' n) ≅ leftDiagram F S (X⟦n⟧) :=
  NatIso.ofComponents
    (fun A =>
      ((F.commShiftIso n).app ((shiftFunctor D (-n)).obj A.obj.left)).symm ≪≫
        F.mapIso ((shiftFunctorCompIsoId D (-n) n (by simp)).app A.obj.left))
    (by
      intro A B f
      dsimp [leftDiagram, leftFractionCat_shiftEquiv, ObjectProperty.lift,
        Over.postEquiv, Over.post, Over.map, shiftEquiv]
      rw [← Category.assoc, Functor.commShiftIso_inv_naturality F
          ((shiftFunctor D (-n)).map (Over.Hom.left f.hom)) n, Category.assoc, Category.assoc,
        ← F.map_comp, ← F.map_comp]
      congr 1
      exact congrArg F.map
        ((shiftFunctorCompIsoId D (-n) n (by simp)).hom.naturality (Over.Hom.left f.hom)))

/-- **The shifted value (left/pro case).** The cone on the pro-object at `X⟦n⟧` obtained from a
cone `c` on the pro-object at `X` by applying `⟦n⟧` and reindexing along `S/(X⟦n⟧) ≌ S/X`; its
vertex is `c.pt⟦n⟧`. -/
noncomputable def shiftCone (X : D) (n : ℤ)
    (c : Cone (MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)) :
    Cone (MorphismProperty.Over.forget S ⊤ (X⟦n⟧) ⋙ Over.forget (X⟦n⟧) ⋙ F) :=
  (Cone.postcompose (overDiagramIso S F (X⟦n⟧)).hom).obj <|
    Cone.whisker (leftFractionCatEquiv S (X⟦n⟧)).inverse <|
    (Cone.postcompose (leftDiagram_shift_natIso F S hSsat X n).hom).obj <|
    Cone.whisker (leftFractionCat_shiftEquiv S hSsat X n).functor <|
    (shiftFunctor D' n).mapCone <|
    (Cone.postcompose (leftDiagramIso S F X).hom).obj <|
    Cone.whisker (leftFractionCatEquiv S X).functor c

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasZeroObject D'] [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.Additive] [F.IsTriangulated] [S.IsMultiplicative] [Preadditive D] [Preadditive D'] hS in
/-- **Statement (2) — the shifted value is a value at `X[n]`.** If `c` exhibits `c.pt` as a
value of `LF` at `X`, then `shiftCone` exhibits `c.pt⟦n⟧` as a value of `LF` at `X[n]`. Dual to
`isRightDerivedValueAt_shiftCocone`. -/
theorem isLeftDerivedValueAt_shiftCone (X : D) (n : ℤ)
    {c : Cone (MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)}
    (hc : F.IsLeftDerivedValueAt S X c) :
    F.IsLeftDerivedValueAt S (X⟦n⟧) (shiftCone F S hSsat X n c) := by
  rw [Functor.isLeftDerivedValueAt_iff] at hc ⊢
  obtain ⟨i, r, h⟩ := hc
  exact ⟨_, _, ((((((h.whisker_of_essSurj _).postcompose (leftDiagramIso S F X)).map
    (shiftFunctor D' n)).whisker_of_essSurj _).postcompose
    (leftDiagram_shift_natIso F S hSsat X n)).whisker_of_essSurj _).postcompose
    (overDiagramIso S F (X⟦n⟧))⟩

/-- **Reindexing equivalence of fraction categories along an arbitrary iso of the base
(left/pro case).**  Dual of `rightFractionCat_isoEquiv`.  An isomorphism `φ : X' ≅ X` in `D`
induces an equivalence `Over X' ≌ Over X` (`Over.mapIso φ`), which restricts to the `S`-full
subcategories because `S` respects isomorphisms (it is saturated). -/
noncomputable def leftFractionCat_isoEquiv {X' X : D} (φ : X' ≅ X) :
    LeftFractionCat S X' ≌ LeftFractionCat S X := by
  haveI : S.RespectsIso := isSaturated_respectsIso hSsat
  let e : Over X' ≌ Over X := Over.mapIso φ
  let P₁ : ObjectProperty (Over X') := fun f => S f.hom
  let P₂ : ObjectProperty (Over X) := fun f => S f.hom
  have hF : ∀ A : ObjectProperty.FullSubcategory P₁, P₂ (e.functor.obj A.1) := by
    intro A
    change S (A.1.hom ≫ φ.hom)
    exact (MorphismProperty.cancel_right_of_respectsIso S A.1.hom φ.hom).2 A.2
  have hG : ∀ B : ObjectProperty.FullSubcategory P₂, P₁ (e.inverse.obj B.1) := by
    intro B
    change S (B.1.hom ≫ φ.inv)
    exact (MorphismProperty.cancel_right_of_respectsIso S B.1.hom φ.inv).2 B.2
  let Fwd : ObjectProperty.FullSubcategory P₁ ⥤ ObjectProperty.FullSubcategory P₂ :=
    ObjectProperty.lift P₂ (ObjectProperty.ι P₁ ⋙ e.functor) hF
  let Inv : ObjectProperty.FullSubcategory P₂ ⥤ ObjectProperty.FullSubcategory P₁ :=
    ObjectProperty.lift P₁ (ObjectProperty.ι P₂ ⋙ e.inverse) hG
  exact
    { functor := Fwd
      inverse := Inv
      unitIso := NatIso.ofComponents
        (fun A => P₁.isoMk (e.unitIso.app A.1))
        (by
          intro A B f
          apply (ObjectProperty.ι P₁).map_injective
          simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk])
      counitIso := NatIso.ofComponents
        (fun B => P₂.isoMk (e.counitIso.app B.1))
        (by
          intro A B f
          apply (ObjectProperty.ι P₂).map_injective
          simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk])
      functor_unitIso_comp := by
        intro A
        apply (ObjectProperty.ι P₂).map_injective
        simp [Fwd, Inv, ObjectProperty.lift, ObjectProperty.isoMk] }

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasZeroObject D'] [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] [S.IsMultiplicative]
  [S.IsCompatibleWithShift ℤ] [Preadditive D] [HasShift D ℤ] [Preadditive D'] [HasShift D' ℤ] hS in
/-- **Definedness is invariant under an iso of the base object (left/pro case).**
If `φ : X' ≅ X` and `LF` is defined at `X'`, then `LF` is defined at `X`.  Dual to
`rightDerived_definedAt_of_iso`; on objects the two diagrams agree on the nose. -/
theorem leftDerived_definedAt_of_iso {X' X : D} (φ : X' ≅ X)
    (h : ∃ c, F.IsLeftDerivedValueAt S X' c) : ∃ c, F.IsLeftDerivedValueAt S X c := by
  rw [exists_isLeftDerivedValueAt_iff_leftDiagram] at h ⊢
  refine h.of_equivalence (leftFractionCat_isoEquiv S hSsat φ).symm.functor (𝟭 D')
    (Functor.isoWhiskerLeft _ (Functor.rightUnitor _) ≪≫ NatIso.ofComponents (fun A => Iso.refl _)
      (fun f => ?_))
  dsimp [leftDiagram, leftFractionCat_isoEquiv, ObjectProperty.lift,
    Over.mapIso, Over.map, Comma.mapRight]
  simp

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasZeroObject D'] [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.Additive] [F.IsTriangulated] [S.IsMultiplicative] [Preadditive D] [Preadditive D'] hS in
/-- **Statement (2) — `LF` and shifts (definedness biconditional).**
`LF` is defined at `X` if and only if `LF` is defined at `X[n]`. -/
@[stacks 05SU "(2)"]
theorem leftDerived_definedAt_iff_shift (X : D) (n : ℤ) :
    (∃ c, F.IsLeftDerivedValueAt S X c) ↔ ∃ c, F.IsLeftDerivedValueAt S (X⟦n⟧) c := by
  exact iff_shift_of_shift_of_iso (fun X => ∃ c, F.IsLeftDerivedValueAt S X c)
    (fun X n ⟨_, hc⟩ => ⟨_, isLeftDerivedValueAt_shiftCone F S hSsat X n hc⟩)
    (leftDerived_definedAt_of_iso F S hSsat) X n

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasZeroObject D'] [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.Additive] [F.IsTriangulated] [S.IsMultiplicative] [Preadditive D] [Preadditive D'] hS in
/-- **Statement (2) — canonical isomorphism of values `LF(X)[n] ≅ LF(X[n])`.**
Given a value `c` of `LF` at `X` and a value `d` of `LF` at `X[n]`, this is the canonical
isomorphism `c.pt⟦n⟧ ≅ d.pt`: `shiftCone` exhibits `c.pt⟦n⟧` as a value at `X[n]`, a value is a
limit cone, and the isomorphism is the comparison of the two limit cones. -/
@[stacks 05SU "(2)"]
noncomputable def leftDerived_value_shift_iso (X : D) (n : ℤ)
    {c : Cone (MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)}
    (hc : F.IsLeftDerivedValueAt S X c)
    {d : Cone (MorphismProperty.Over.forget S ⊤ (X⟦n⟧) ⋙ Over.forget (X⟦n⟧) ⋙ F)}
    (hd : F.IsLeftDerivedValueAt S (X⟦n⟧) d) :
    c.pt⟦n⟧ ≅ d.pt :=
  (isLeftDerivedValueAt_shiftCone F S hSsat X n hc).isLimit.conePointUniqueUpToIso hd.isLimit

end Situation

end StacksDerivedShift

end

end
