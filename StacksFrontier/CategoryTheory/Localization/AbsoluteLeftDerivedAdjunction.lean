module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions

/-!
# Derived adjunction when the right adjoint is exact

Let `L ⊣ R` be an adjunction of additive functors between abelian categories with derived
categories, with `R` exact. A left derived functor of the degreewise `L` on the unbounded homotopy
category which is absolute, that is, remains a left derived functor after post-composition with
the functor `R.mapDerivedCategory` induced by `R`, is left adjoint to `R.mapDerivedCategory`. A
left derived functor computed by a resolving class of objects is absolute, so the adjunction holds
whenever the left derived functor of `L` is computed by resolutions.

## Main results

* `CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_comp_of_resolutions`: a left
  derived functor computed by resolutions is absolute.
* `CategoryTheory.Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact` and
  `CategoryTheory.Functor.isRightDerivedFunctor_mapDerivedCategory_comp_of_exact`: the derived
  functor of an exact functor is an absolute right derived functor.
* `CategoryTheory.Adjunction.derivedMapDerivedCategoryOfAbsolute`: the derived adjunction, given
  absoluteness of the left-hand derived functor.
* `CategoryTheory.Adjunction.derivedMapDerivedCategoryOfResolutions`: the derived adjunction with
  no absoluteness hypothesis at all, from a resolving class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.LeftDerivedByResolutions

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LeftDerivedByResolutions

/-- **A left derived functor computed by resolutions is absolute.** If `P` is a resolving class
for `W` and `F` inverts the morphisms of `W` between objects satisfying `P`, then a left derived
functor `LF` of `F` stays a left derived functor after post-composition with an arbitrary functor
`Ψ`, the comparison being the whiskered one. -/
public lemma isLeftDerivedFunctor_comp_of_resolutions
    {C : Type u₁} [Category.{v₁} C]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ (Y : C) (_ : P Y) (s : Y ⟶ X), W s)
    {H D H' : Type*} [Category H] [Category D] [Category H'] (F : C ⥤ H)
    (hF : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (F.map s))
    (L : C ⥤ D) [L.IsLocalization W] (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor α W] (Ψ : H ⥤ H') :
    (LF ⋙ Ψ).IsLeftDerivedFunctor ((L.associator LF Ψ).inv ≫ whiskerRight α Ψ) W := by
  refine isLeftDerivedFunctor_of_isIso_on_resolutions W P hP (F ⋙ Ψ)
    (fun s hs hX hY => by
      have := hF s hs hX hY
      dsimp
      infer_instance)
    L (LF ⋙ Ψ) _ (fun X hX => ?_)
  have := isIso_app_of_resolutions W P hP F hF L LF α X hX
  dsimp
  infer_instance

end CategoryTheory.LeftDerivedByResolutions

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]

namespace Functor

variable (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- The functor induced by an exact functor on unbounded derived categories is the right derived
functor of its degreewise action on the homotopy category. -/
public lemma isRightDerivedFunctor_mapDerivedCategory_of_exact :
    R.mapDerivedCategory.IsRightDerivedFunctor R.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ R.mapDerivedCategoryFactorsh

/-- The degreewise action of an exact functor on the homotopy category, followed by the
localization, inverts quasi-isomorphisms. -/
public lemma isInvertedBy_mapHomotopyCategory_comp_Qh_of_exact :
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).IsInvertedBy
      (R.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) := by
  rw [← MorphismProperty.IsInvertedBy.iff_of_iso _ R.mapDerivedCategoryFactorsh]
  exact MorphismProperty.IsInvertedBy.of_comp _ _
    (Localization.inverts DerivedCategory.Qh _) _

/-- The right derived functor of an exact functor is **absolute**: it remains one after
post-composition with an arbitrary functor. -/
public lemma isRightDerivedFunctor_mapDerivedCategory_comp_of_exact
    {H : Type*} [Category H] (Ψ : DerivedCategory A ⥤ H) :
    (R.mapDerivedCategory ⋙ Ψ).IsRightDerivedFunctor
      (whiskerRight R.mapDerivedCategoryFactorsh.inv Ψ ≫
        (DerivedCategory.Qh.associator R.mapDerivedCategory Ψ).hom)
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) :=
  (Functor.isRightDerivedFunctor_iff_of_inverts _ _
    (MorphismProperty.IsInvertedBy.of_comp _ _
      (isInvertedBy_mapHomotopyCategory_comp_Qh_of_exact R) _)).2 inferInstance

end Functor

namespace Adjunction

variable {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- **The derived adjunction for an exact right adjoint.** Let `L ⊣ R` be an adjunction of
additive functors between abelian categories with derived categories, with `R` exact. Let `LL`
with comparison `α` be a left derived functor of the degreewise `L` on the unbounded homotopy
category, and assume it is absolute, in the single instance needed. Then `LL` is left adjoint to
the functor induced by `R` on derived categories. -/
public def derivedMapDerivedCategoryOfAbsolute (adj : L ⊣ R)
    {LL : DerivedCategory A ⥤ DerivedCategory B}
    (α : DerivedCategory.Qh ⋙ LL ⟶
      L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LL.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [(LL ⋙ R.mapDerivedCategory).IsLeftDerivedFunctor
      ((DerivedCategory.Qh.associator LL R.mapDerivedCategory).inv ≫
        whiskerRight α R.mapDerivedCategory)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    LL ⊣ R.mapDerivedCategory :=
  letI := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact R
  letI := Functor.isRightDerivedFunctor_mapDerivedCategory_comp_of_exact R LL
  (adj.mapHomotopyCategoryAdjunction (ComplexShape.up ℤ)).derived
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
    α R.mapDerivedCategoryFactorsh.inv

/-- **The derived adjunction for an exact right adjoint, from a resolving class.** Let `L ⊣ R` be
an adjunction of additive functors between abelian categories with derived categories, with `R`
exact. Let `P` be a class of objects of the unbounded homotopy category of `A` such that every
object receives a quasi-isomorphism from an object satisfying `P`, and such that the degreewise
`L` carries the quasi-isomorphisms between objects satisfying `P` to isomorphisms of `D(B)`. Then
the total left derived functor of `L` is left adjoint to the functor induced by `R`. -/
public def derivedMapDerivedCategoryOfResolutions (adj : L ⊣ R)
    (P : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)))
    (hP : ∀ X, ∃ (Y : HomotopyCategory A (ComplexShape.up ℤ)) (_ : P Y) (s : Y ⟶ X),
      HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s)
    (hL : ∀ {X Y : HomotopyCategory A (ComplexShape.up ℤ)} (s : X ⟶ Y),
      HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s → P X → P Y →
      IsIso ((L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map s)) :
    letI : (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
        hasPointwiseLeftDerivedFunctor_of_resolutions _ P hP _ hL
    (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerived
        DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊣
      R.mapDerivedCategory :=
  letI : (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
      hasPointwiseLeftDerivedFunctor_of_resolutions _ P hP _ hL
  let α := (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit
      DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  letI := isLeftDerivedFunctor_comp_of_resolutions
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) P hP
    (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hL
    DerivedCategory.Qh _ α R.mapDerivedCategory
  derivedMapDerivedCategoryOfAbsolute adj α

end Adjunction

end CategoryTheory

end
