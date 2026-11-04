module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor

/-!
# Values of a total right derived functor on K-injective complexes

A total right derived functor `RG : D(A) ⥤ D(B)` of an additive functor `G : A ⥤ B` is
computed on a K-injective complex `I` by applying `G` degreewise: the comparison
transformation of the derivation is invertible there, so `RG(I) ≅ G(I)` in `D(B)`.  This file
records that isomorphism as a term, together with the companion fact that a K-injective
complex which is acyclic is carried by *every* additive functor to an acyclic complex — an
acyclic K-injective complex is null-homotopic, and a null-homotopy is preserved by any additive
functor.

Both statements are purely homological: they are stated for arbitrary abelian categories with
chosen derived categories, with the existence of K-injective resolutions taken as an explicit
hypothesis rather than through a Grothendieck-abelian instance.

## Main results

* `Stacks.Perfect.KInjectiveValues.objIsoOfKInjective`: `RG(I) ≅ G(I)` for `I` K-injective.
* `Stacks.Perfect.KInjectiveValues.isZero_quotient_obj_of_isKInjective`: an acyclic K-injective
  complex is zero in the homotopy category.
* `Stacks.Perfect.KInjectiveValues.isZero_Q_obj_mapHomologicalComplex`: an additive functor
  carries an acyclic K-injective complex to an acyclic complex.

## Implementation notes

The comparison transformation is inverted at `I` by
`Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective`, and the two sides are
rewritten into the stated shape with `CategoryTheory.Functor.mapHomotopyCategoryFactors` and
`DerivedCategory.quotientCompQhIso`.

That an acyclic K-injective complex is zero in the homotopy category is immediate from the
definition of K-injectivity, in the form `CochainComplex.IsKInjective.homotopyZero`: the
identity of the complex is a morphism out of an acyclic complex, hence homotopic to zero, so it
is zero in the homotopy category.

## References

* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 08BR](https://stacks.math.columbia.edu/tag/08BR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Perfect.KInjectiveValues

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- **A total right derived functor is computed degreewise on K-injective complexes.**  For an
additive `G : A ⥤ B` with total right derived functor `RG` and comparison `β`, and for a
K-injective complex `I` of objects of `A`, the object `RG(I)` of `D(B)` is the complex obtained
by applying `G` to `I` degreewise. -/
public def objIsoOfKInjective (G : A ⥤ B) [G.Additive]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    [RG.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
    RG.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective G RG β
    hres I hI
  RG.mapIso ((DerivedCategory.quotientCompQhIso A).app I).symm ≪≫
    (asIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))).symm ≪≫
    DerivedCategory.Qh.mapIso ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I) ≪≫
    (DerivedCategory.quotientCompQhIso B).app _

omit [HasDerivedCategory A] in
/-- **An acyclic K-injective complex is zero in the homotopy category.**  Its identity is a
morphism from an acyclic complex into a K-injective one, hence homotopic to zero. -/
public theorem isZero_quotient_obj_of_isKInjective (I : CochainComplex A ℤ) (hI : I.IsKInjective)
    (hac : I.Acyclic) :
    IsZero ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) := by
  let _ := hI
  refine (IsZero.iff_id_eq_zero _).2 ?_
  have h : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (𝟙 I) =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map 0 :=
    HomotopyCategory.eq_of_homotopy _ _ (CochainComplex.IsKInjective.homotopyZero (𝟙 I) hac)
  simpa using h

omit [HasDerivedCategory A] in
/-- **An additive functor carries an acyclic K-injective complex to an acyclic complex.**  The
complex is null-homotopic, and a null-homotopy survives an additive functor. -/
public theorem isZero_Q_obj_mapHomologicalComplex (G : A ⥤ B) [G.Additive]
    (I : CochainComplex A ℤ) (hI : I.IsKInjective)
    (hac : I.Acyclic) :
    IsZero (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  have h₁ : IsZero ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
    Functor.map_isZero _ (isZero_quotient_obj_of_isKInjective I hI hac)
  have h₂ : IsZero ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    h₁.of_iso ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I).symm
  exact (Functor.map_isZero DerivedCategory.Qh h₂).of_iso
    ((DerivedCategory.quotientCompQhIso B).app _).symm

end Stacks.Perfect.KInjectiveValues

end
