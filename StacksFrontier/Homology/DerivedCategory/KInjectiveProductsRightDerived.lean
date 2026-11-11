module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.KInjectiveTowerCocone
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProductsFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# A right derived functor preserves countable products, from K-injective resolutions

Let `F : A ⥤ B` be an additive functor of abelian categories preserving countable products and
carrying K-injective complexes to K-injective complexes, and let `RF : D(A) ⥤ D(B)` be a right
derived functor of `K(A) --F--> K(B) --Q_h--> D(B)` whose comparison `α` is invertible on
K-injective complexes. Then `RF` preserves countable products. The statements are proved for
products indexed by an arbitrary `T : Type`, countable products being the case `T = ℕ`.

This is the right-derived counterpart of
`CategoryTheory.Functor.preservesProducts_mapDerivedCategory_of_isKInjective`, which says the
same for the functor an *exact* `F` induces on derived categories. A direct image of sheaves of
modules is not exact, so that statement does not reach `Rf_*`; the hypotheses below are the ones
`Rf_*` does satisfy.

Like its exact counterpart, this assumes **no exactness of the countable products** of either
abelian category — Grothendieck's axiom AB4\*, the hypothesis of [Stacks, Tag 07KC] and of
`Stacks.Injectives.preservesLimit_discrete_of_isRightDerivedFunctor`, which is what fails for
sheaves of modules on a site, a countable product of epimorphisms of sheaves need not be an
epimorphism.

## Main results

All in the namespace `Stacks.KInjectiveProductsRightDerived`.

* `derivedUnitOnComplexes`: the comparison `α`, read as a natural transformation
  `F.mapHomologicalComplex _ ⋙ Q ⟶ Q ⋙ RF` of functors on cochain complexes.
* `isIso_piComparison_of_natTrans`: a natural transformation invertible at a family and at its
  product carries invertibility of the one product comparison to the other.
* `isIso_piComparison_of_isKInjective`: the product comparison of `RF` is invertible at a
  countable family of images of K-injective complexes.
* `preservesProducts_of_isKInjective`: **`RF` preserves countable products.**

## Implementation notes

The three isomorphisms `Functor.mapHomotopyCategoryFactors` and `DerivedCategory.quotientCompQhIso`
are not identities, so `α`, whose components sit at objects of the homotopy category, is first
assembled into `derivedUnitOnComplexes`, a transformation between functors on cochain complexes;
its components at K-injective complexes are then invertible because all four factors are.

The invertibility of `α` on K-injective complexes is a hypothesis rather than a consequence of
the existence of K-injective resolutions, which is the second hypothesis: at the point of use it
is the K-injective computation of the derived direct image, already available there, and asking
for it directly avoids having to re-derive it from
`Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective`.

## References

* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace Stacks.KInjectiveProductsRightDerived

/-- **A natural transformation transports invertibility of the product comparison.** If `β` is
invertible at every member of a family and at its product, then the product comparison of its
target is invertible as soon as that of its source is: the two comparisons sit in the square
whose other two sides are `β` at the product and the product of `β` at the members, and that
square commutes by naturality of `β` at the projections. -/
theorem isIso_piComparison_of_natTrans {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {T : Type} [HasProductsOfShape T C] [HasProductsOfShape T D]
    {G₁ G₂ : C ⥤ D} (β : G₁ ⟶ G₂) (X : T → C) (h₀ : IsIso (β.app (∏ᶜ X)))
    (h : ∀ t, IsIso (β.app (X t))) (h₁ : IsIso (piComparison G₁ X)) :
    IsIso (piComparison G₂ X) := by
  have key : piComparison G₁ X ≫ (Limits.Pi.map fun t ↦ β.app (X t)) =
      β.app (∏ᶜ X) ≫ piComparison G₂ X := by
    ext t
    simp
  have : IsIso (β.app (∏ᶜ X) ≫ piComparison G₂ X) := by
    rw [← key]
    infer_instance
  exact IsIso.of_isIso_comp_left (β.app (∏ᶜ X)) _

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)

/-- The comparison `α` of a right derived functor, read on cochain complexes: a natural
transformation from degreewise application of `F` followed by localization into localization
followed by `RF`.

It is `α` conjugated by the three canonical isomorphisms
`DerivedCategory.quotientCompQhIso` (on both sides) and
`CategoryTheory.Functor.mapHomotopyCategoryFactors`. -/
def derivedUnitOnComplexes :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
  Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso B).inv ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (ComplexShape.up ℤ)) α ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom RF

/-- At a complex on which the comparison of the right derived functor is invertible, so is
`derivedUnitOnComplexes`: the other three factors are isomorphisms at every complex. -/
theorem isIso_derivedUnitOnComplexes_app (K : CochainComplex A ℤ)
    (hK : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))) :
    IsIso ((derivedUnitOnComplexes F RF α).app K) := by
  rw [derivedUnitOnComplexes]
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

end

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {T : Type} [HasProductsOfShape T A] [HasProductsOfShape T B]
  [HasProductsOfShape T (DerivedCategory A)] [HasProductsOfShape T (DerivedCategory B)]
  (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete T) F]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)

/-- **The product comparison of a right derived functor is invertible at a family of images of
K-injective complexes**, indexed by any `T : Type` (countable products being the case
`T = ℕ`). The termwise product of the family is K-injective ([Stacks, Tag 0BK6]) and so are its
images under `F`, so localization turns both termwise
products into the products of the derived categories; `F` preserves the termwise product because
products of complexes are computed degreewise; and the comparison of `RF` is invertible at all
the complexes in sight. -/
theorem isIso_piComparison_of_isKInjective
    (hα : ∀ K : CochainComplex A ℤ, K.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)))
    (hKInj : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (I : T → CochainComplex A ℤ) (hI : ∀ n, (I n).IsKInjective) :
    IsIso (piComparison RF fun n ↦ DerivedCategory.Q.obj (I n)) := by
  -- the comparison of `RF`, on complexes, is invertible at the family and at its product
  have hβ : ∀ K : CochainComplex A ℤ, K.IsKInjective →
      IsIso ((derivedUnitOnComplexes F RF α).app K) := fun K hK ↦
    isIso_derivedUnitOnComplexes_app F RF α _ (hα _ hK)
  -- degreewise `F` followed by localization preserves the countable product
  have hsrc : IsIso (piComparison
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) I) := by
    rw [Stacks.DerivedProducts.piComparison_comp_eq]
    have h₂ : IsIso (piComparison DerivedCategory.Q
        fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)) :=
      Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective _ fun n ↦ hKInj _ (hI n)
    infer_instance
  -- hence so does localization followed by `RF`
  have htgt : IsIso (piComparison (DerivedCategory.Q ⋙ RF) I) :=
    isIso_piComparison_of_natTrans (derivedUnitOnComplexes F RF α) I
      (hβ _ (Stacks.Injectives.KInjectiveProduct.product_isKInjective I hI))
      (fun n ↦ hβ _ (hI n)) hsrc
  -- divide out the comparison of localization alone, invertible since the `I n` are K-injective
  rw [Stacks.DerivedProducts.piComparison_comp_eq] at htgt
  have hQ : IsIso (piComparison (DerivedCategory.Q (C := A)) I) :=
    Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective I hI
  exact IsIso.of_isIso_comp_left (RF.map (piComparison (DerivedCategory.Q (C := A)) I)) _

/-- **A right derived functor preserves products indexed by any `T : Type`** (in particular
countable ones), when the functor it derives preserves them and K-injectivity and its
comparison is invertible on K-injective complexes. No exactness of the countable products of
either abelian category is assumed, and none is available for sheaves of modules on a site.

Every object of `D(A)` is isomorphic to the image of a K-injective complex, and at a family of
those the product comparison is invertible by `isIso_piComparison_of_isKInjective`; comparisons
of componentwise isomorphic families are invertible together. -/
theorem preservesProducts_of_isKInjective
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hα : ∀ K : CochainComplex A ℤ, K.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)))
    (hKInj : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    PreservesLimitsOfShape (Discrete T) RF := by
  apply Stacks.DerivedProducts.preservesLimitsOfShape_discrete_of_isIso_piComparison
  intro X
  choose I f hI hf using fun n : T ↦ hres (DerivedCategory.Q.objPreimage (X n))
  have hiso (n : T) : IsIso (DerivedCategory.Q.map (f n)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A (f n)).2 (hf n)
  exact CategoryTheory.Limits.isIso_piComparison_of_iso _
    (fun n ↦ (asIso (DerivedCategory.Q.map (f n))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso (X n))
    (isIso_piComparison_of_isKInjective F RF α hα hKInj I hI)

end

end Stacks.KInjectiveProductsRightDerived

end
