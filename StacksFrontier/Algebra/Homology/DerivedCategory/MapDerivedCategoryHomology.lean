module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# An exact functor commutes with the homology of the derived category

Let `F : C₁ ⥤ C₂` be an exact additive functor between abelian categories, and let
`F.mapDerivedCategory : D(C₁) ⥤ D(C₂)` be the induced functor. We construct the natural
isomorphism `F.mapDerivedCategory ⋙ Hⁿ ≅ Hⁿ ⋙ F`, i.e. `Hⁿ(F(K)) ≅ F(Hⁿ(K))` naturally in
`K : D(C₁)`, and deduce that a morphism of `D(C₁)` is carried to an isomorphism by
`F.mapDerivedCategory` exactly when `F` carries each of its homology maps to an isomorphism.

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`: the isomorphism
  `F.mapDerivedCategory ⋙ Hⁿ ≅ Hⁿ ⋙ F`.

## Main results

* `CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff`: `F.mapDerivedCategory.map φ` is an
  isomorphism if and only if `F.map (Hⁿ(φ))` is an isomorphism for every `n`.
-/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂ t

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {ι : Type t} {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Applying `F` to a homological complex degreewise and then extracting the short complex in
degrees `c.prev n, n, c.next n` is extracting that short complex and then applying `F` to it. -/
noncomputable def mapHomologicalComplexShortComplexIso (c : ComplexShape ι) (n : ι) :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.shortComplexFunctor C₂ c n ≅
      HomologicalComplex.shortComplexFunctor C₁ c n ⋙ F.mapShortComplex :=
  Iso.refl _

section Derived

variable [HasDerivedCategory.{w₁} C₁] [HasDerivedCategory.{w₂} C₂]

/-- The natural isomorphism `(F.mapHomologicalComplex (up ℤ) ⋙ Q) ⋙ Hⁿ ≅ Q ⋙ Hⁿ ⋙ F` of
functors from cochain complexes in `C₁`, induced by `mapHomologicalComplexHomologyIso` in degree
`n`. -/
noncomputable def mapDerivedCategoryHomologyIsoAux (n : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        DerivedCategory.homologyFunctor C₂ n ≅
      DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C₁ n ⋙ F :=
  associator .. ≪≫
    isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors C₂ n) ≪≫
    F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n ≪≫
    isoWhiskerRight (DerivedCategory.homologyFunctorFactors C₁ n).symm F ≪≫
    associator ..

/-- For an exact additive functor `F : C₁ ⥤ C₂` between abelian categories, the induced functor
`F.mapDerivedCategory : D(C₁) ⥤ D(C₂)` satisfies `Hⁿ(F(K)) ≅ F(Hⁿ(K))` naturally in
`K : D(C₁)`. -/
noncomputable def mapDerivedCategoryHomologyIso (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n ≅
      DerivedCategory.homologyFunctor C₁ n ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
      DerivedCategory.homologyFunctor C₂ n)
    (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C₁ n ⋙ F)
    (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n)
    (DerivedCategory.homologyFunctor C₁ n ⋙ F)
    (F.mapDerivedCategoryHomologyIsoAux n)

/-- For a morphism `φ` of `D(C₁)`, `Hⁿ(F.mapDerivedCategory.map φ)` is an isomorphism if and only
if `F.map (Hⁿ(φ))` is. -/
lemma isIso_homologyFunctor_map_mapDerivedCategory_map_iff {K L : DerivedCategory C₁} (φ : K ⟶ L)
    (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategory.map φ)) ↔
      IsIso (F.map ((DerivedCategory.homologyFunctor C₁ n).map φ)) :=
  NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyIso n) φ

/-- An exact additive functor carries a morphism of `D(C₁)` to an isomorphism exactly when it
carries each of that morphism's homology maps to an isomorphism. -/
lemma isIso_mapDerivedCategory_map_iff {K L : DerivedCategory C₁} (φ : K ⟶ L) :
    IsIso (F.mapDerivedCategory.map φ) ↔
      ∀ n : ℤ, IsIso (F.map ((DerivedCategory.homologyFunctor C₁ n).map φ)) :=
  (DerivedCategory.isIso_iff _ (F.mapDerivedCategory.map φ)).trans <|
    forall_congr' fun n => F.isIso_homologyFunctor_map_mapDerivedCategory_map_iff φ n

end Derived

end CategoryTheory.Functor

end
