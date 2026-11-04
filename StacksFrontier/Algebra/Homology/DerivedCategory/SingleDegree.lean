module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Objects of a derived category concentrated in a single degree

An object `X` of the derived category of an abelian category whose homology vanishes outside a
single degree `n` is isomorphic to its own homology `Hⁿ(X)` placed in degree `n`. An exact functor
between abelian categories commutes with homology on derived categories.

## Main definitions

* `DerivedCategory.liftingHomologyFunctor`: the homology functor on the derived category lifts the
  homology functor on cochain complexes through `DerivedCategory.Q`.
* `CategoryTheory.Functor.mapHomologicalComplexHomologyFunctorIso`: for an exact functor `F`, the
  natural isomorphism `F.mapHomologicalComplex ⋙ Hʲ ≅ Hʲ ⋙ F` on cochain complexes.
* `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`: for an exact functor `F`, the
  natural isomorphism `F.mapDerivedCategory ⋙ Hʲ ≅ Hʲ ⋙ F`.

## Main results

* `DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor`: an object which is both `≥ n` and
  `≤ n` for the canonical t-structure is isomorphic to `Hⁿ` of itself placed in degree `n`.
* `DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero`: the same conclusion from
  the vanishing of `Hʲ` for every `j ≠ n`.
* `CategoryTheory.Functor.isZero_homologyFunctor_mapDerivedCategory_obj`: an exact functor
  preserves the vanishing of `Hʲ` of an object of the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace DerivedCategory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]

/-- An object of the derived category which is both `≥ n` and `≤ n` for the canonical t-structure
is isomorphic to its degree-`n` homology, placed in degree `n`. -/
public theorem nonempty_iso_singleFunctor_homologyFunctor
    (X : DerivedCategory C) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    Nonempty (X ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj X)) := by
  obtain ⟨Y, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  exact ⟨e ≪≫ (singleFunctor C n).mapIso
    (((singleFunctorCompHomologyFunctorIso C n).app Y).symm ≪≫ (homologyFunctor C n).mapIso e.symm)⟩

/-- An object of the derived category whose homology vanishes in every degree other than `n` is
isomorphic to its degree-`n` homology, placed in degree `n`. -/
public theorem nonempty_iso_singleFunctor_homologyFunctor_of_isZero
    (X : DerivedCategory C) (n : ℤ)
    (hX : ∀ j : ℤ, j ≠ n → IsZero ((homologyFunctor C j).obj X)) :
    Nonempty (X ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj X)) := by
  have : X.IsGE n := (X.isGE_iff n).2 fun j hj ↦ hX j hj.ne
  have : X.IsLE n := (X.isLE_iff n).2 fun j hj ↦ hX j hj.ne'
  exact X.nonempty_iso_singleFunctor_homologyFunctor n

/-- The homology functor on the derived category lifts the homology functor on cochain complexes
through the localization functor `DerivedCategory.Q`. -/
public instance liftingHomologyFunctor (j : ℤ) :
    Localization.Lifting (Q (C := C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) j)
      (homologyFunctor C j) :=
  ⟨homologyFunctorFactors C j⟩

end DerivedCategory

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor commutes with the homology of cochain complexes. -/
public def mapHomologicalComplexHomologyFunctorIso (j : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) j ≅
      HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) j ⋙ F :=
  NatIso.ofComponents (fun K ↦ (K.sc j).mapHomologyIso F)
    (fun f ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C₁ (ComplexShape.up ℤ) j).map f) F)

/-- An exact functor commutes with the homology functors of derived categories. -/
public def mapDerivedCategoryHomologyFunctorIso (j : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ j ≅
      DerivedCategory.homologyFunctor C₁ j ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
      DerivedCategory.homologyFunctor C₂ j)
    (HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) j ⋙ F) _ _
    (associator _ _ _ ≪≫
      isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors C₂ j) ≪≫
      F.mapHomologicalComplexHomologyFunctorIso j)

/-- For an exact functor `F`, if `Hʲ(X)` vanishes for an object `X` of the derived category, then
so does `Hʲ(F.mapDerivedCategory.obj X)`. -/
public theorem isZero_homologyFunctor_mapDerivedCategory_obj
    (X : DerivedCategory C₁) (j : ℤ)
    (hX : IsZero ((DerivedCategory.homologyFunctor C₁ j).obj X)) :
    IsZero ((DerivedCategory.homologyFunctor C₂ j).obj (F.mapDerivedCategory.obj X)) :=
  IsZero.of_iso (F.map_isZero hX) ((F.mapDerivedCategoryHomologyFunctorIso j).app X)

end CategoryTheory.Functor

end
