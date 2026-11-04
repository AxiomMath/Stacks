module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.KInjectiveTowerCocone

/-!
# Countable products of a derived category are preserved, from K-injective resolutions

Let `F : A ⥤ B` be an exact functor of abelian categories preserving countable products, and
suppose that every cochain complex over `A` admits a quasi-isomorphism to a K-injective complex
and that `F` carries K-injective complexes to K-injective complexes. Then the induced functor
`F.mapDerivedCategory : D(A) ⥤ D(B)` preserves countable products.

No exactness of the countable products of `A` or `B` (Grothendieck's axiom AB4*) is assumed.

## Main results

* `CategoryTheory.Limits.isIso_piComparison_of_iso`: the product comparison maps of two
  componentwise isomorphic families are isomorphisms together.
* `CategoryTheory.Functor.preservesProducts_mapDerivedCategory_of_isKInjective`: the induced
  functor of derived categories preserves countable products.

## References

* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

/-- The product comparison map is an isomorphism at one family of objects as soon as it is at a
componentwise isomorphic family. -/
theorem isIso_piComparison_of_iso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : Type} [HasProductsOfShape J C] [HasProductsOfShape J D] (F : C ⥤ D) {X Y : J → C}
    (e : ∀ j, X j ≅ Y j) (h : IsIso (piComparison F X)) :
    IsIso (piComparison F Y) := by
  have hi : IsIso (Pi.map fun j ↦ (e j).hom) := by
    change IsIso (Pi.mapIso e).hom
    infer_instance
  have hj : IsIso (Pi.map fun j ↦ F.map (e j).hom) := by
    change IsIso (Pi.mapIso fun j ↦ F.mapIso (e j)).hom
    infer_instance
  have hc : IsIso (F.map (Pi.map fun j ↦ (e j).hom) ≫ piComparison F Y) := by
    rw [← Stacks.DerivedProducts.piComparison_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (Pi.map fun j ↦ (e j).hom)) _

end CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  [HasProductsOfShape ℕ A] [HasProductsOfShape ℕ B]
  [HasProductsOfShape ℕ (DerivedCategory A)] [HasProductsOfShape ℕ (DerivedCategory B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesLimitsOfShape (Discrete ℕ) F]

/-- The comparison map of `F.mapDerivedCategory` is an isomorphism at a family of K-injective
complexes. -/
theorem isIso_piComparison_mapDerivedCategory_of_isKInjective
    (hKInj : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (I : ℕ → CochainComplex A ℤ) (hI : ∀ n, (I n).IsKInjective) :
    IsIso (piComparison F.mapDerivedCategory fun n ↦ DerivedCategory.Q.obj (I n)) := by
  have hcomplex : IsIso (piComparison
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) I) := by
    rw [Stacks.DerivedProducts.piComparison_comp_eq]
    have h₂ : IsIso (piComparison DerivedCategory.Q
        fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)) :=
      Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective _ fun n ↦ hKInj _ (hI n)
    infer_instance
  have : PreservesLimit (Discrete.functor I)
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) :=
    PreservesProduct.of_iso_comparison _ I
  have : PreservesLimit (Discrete.functor I)
      (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimit_of_natIso _ F.mapDerivedCategoryFactors.symm
  have hcomp : IsIso (piComparison (DerivedCategory.Q ⋙ F.mapDerivedCategory) I) :=
    inferInstance
  rw [Stacks.DerivedProducts.piComparison_comp_eq] at hcomp
  have hQ : IsIso (piComparison (DerivedCategory.Q (C := A)) I) :=
    Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective I hI
  exact IsIso.of_isIso_comp_left
    (F.mapDerivedCategory.map (piComparison (DerivedCategory.Q (C := A)) I)) _

/-- An exact functor preserving countable products and K-injectivity, on an abelian category whose
complexes have K-injective resolutions, induces a functor of derived categories preserving
countable products. No exactness of countable products is assumed. -/
theorem preservesProducts_mapDerivedCategory_of_isKInjective
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hKInj : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    PreservesLimitsOfShape (Discrete ℕ) F.mapDerivedCategory := by
  apply Stacks.DerivedProducts.preservesLimitsOfShape_discrete_of_isIso_piComparison
  intro X
  choose I f hI hf using fun n : ℕ ↦ hres (DerivedCategory.Q.objPreimage (X n))
  have hiso (n : ℕ) : IsIso (DerivedCategory.Q.map (f n)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A (f n)).2 (hf n)
  exact isIso_piComparison_of_iso _
    (fun n ↦ (asIso (DerivedCategory.Q.map (f n))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso (X n))
    (isIso_piComparison_mapDerivedCategory_of_isKInjective F hKInj I hI)

end CategoryTheory.Functor

end
