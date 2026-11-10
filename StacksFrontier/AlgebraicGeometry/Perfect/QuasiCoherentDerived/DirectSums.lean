module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts

/-!
# Direct sums in the derived category with quasi-coherent cohomology

For a scheme `X`, consider the full subcategory of the unbounded derived category of
`𝒪_X`-modules consisting of objects whose cohomology sheaves are quasi-coherent in every degree.
This category admits arbitrary direct sums.

The proof is the standard one: a direct sum in the derived category is computed termwise, so its
cohomology is the direct sum of the cohomologies, and quasi-coherence is stable under direct
sums.

## Main definitions

* `AlgebraicGeometry.QuasicoherentDerivedCategory`: the full subcategory of the derived category
  whose objects have quasi-coherent cohomology in every degree.

## Main results

* `AlgebraicGeometry.hasCoproducts_quasicoherentDerivedCategory`: this category has arbitrary
  coproducts.

## Implementation notes

The subcategory is expressed using `DerivedCategoryB.derivedCategoryB`, the general construction
of the full subcategory of the derived category cut out by a property of all cohomology objects.
Direct sums are represented by categorical coproducts.

That the degree-`n` cohomology functor preserves coproducts is assembled from two facts: the
localization functor `Q` preserves them (Stacks 07D9), and cohomology of a cochain complex is
computed by a colimit-preserving functor in any abelian category with exact colimits of that
shape. The latter is proved here degreewise, through the short complex around a degree and the
homology of short complexes.

## References

* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- Homology of short complexes commutes with colimits of a shape for which colimits are
exact. -/
private lemma shortComplexHomology_preservesColimitsOfShape
    {A : Type*} [Category A] [Abelian A] {J : Type*} [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor A) := by
  refine ⟨fun {E} => preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone E) ?_⟩
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (Stacks.HomologyColimit.compHomologyFunctorIso E)
      (colimit.cocone ((ShortComplex.FunctorEquivalence.inverse J A).obj E).homology)).symm
      (colimit.isColimit _))
    (Cocone.ext (((ShortComplex.FunctorEquivalence.inverse J A).obj E).mapHomologyIso
      (colim : (J ⥤ A) ⥤ A)).symm (fun j => ?_))
  set T := (ShortComplex.FunctorEquivalence.inverse J A).obj E
  let ι : (evaluation J A).obj j ⟶ (colim : (J ⥤ A) ⥤ A) :=
    { app := fun X => colimit.ι X j
      naturality := fun X Y f => by simp }
  have key : ι.app T.homology = (T.mapHomologyIso ((evaluation J A).obj j)).inv ≫
      ShortComplex.homologyMap (T.mapNatTrans ι) ≫ (T.mapHomologyIso colim).hom :=
    NatTrans.app_homology ι T
  change ((T.mapHomologyIso ((evaluation J A).obj j)).hom ≫ ι.app T.homology) ≫
      (T.mapHomologyIso (colim : (J ⥤ A) ⥤ A)).inv =
    ShortComplex.homologyMap (T.mapNatTrans ι)
  rw [key]
  simp

/-- The short complex around a degree of a cochain complex preserves colimits, because it is
computed from three evaluations. -/
private lemma complexShortComplex_preservesColimitsOfShape
    {A : Type*} [Category A] [Abelian A] {J : Type*} [Category J]
    [HasColimitsOfShape J A] (i : ℤ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i) :=
  ⟨fun {_} => ⟨fun hs =>
    have h := fun k => isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) k) hs
    ⟨ShortComplex.isColimitOfIsColimitπ _ (h _) (h _) (h _)⟩⟩⟩

/-- Cohomology of cochain complexes in a degree commutes with colimits of a shape for which
colimits are exact. -/
private lemma complexHomology_preservesColimitsOfShape
    {A : Type*} [Category A] [Abelian A] {J : Type*} [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] (i : ℤ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i) :=
  have := complexShortComplex_preservesColimitsOfShape (A := A) (J := J) i
  have := shortComplexHomology_preservesColimitsOfShape (A := A) (J := J)
  preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso A (ComplexShape.up ℤ) i).symm

/-- The full subcategory of the derived category of `𝒪_X`-modules consisting of objects whose
cohomology sheaves are quasi-coherent in every degree. -/
@[sga "4 XVII 5.5.32" "partial"]
abbrev QuasicoherentDerivedCategory (X : Scheme.{u}) : Type (u + 1) :=
  (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory

/-- The derived category of `𝒪_X`-modules with quasi-coherent cohomology has direct sums. -/
@[stacks 08DT]
instance hasCoproducts_quasicoherentDerivedCategory (X : Scheme.{u}) :
    HasCoproducts.{u} (QuasicoherentDerivedCategory X) := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  have (I : Type u) : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape X
  let A := SheafOfModules.{u} X.ringCatSheaf
  have hH (I : Type u) (n : ℤ) :
      PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n) := by
    let : PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) :=
      Stacks.Injectives.derivedCategoryQ_preservesCoproducts A I
    let := complexHomology_preservesColimitsOfShape
      (A := A) (J := Discrete I) n
    have : PreservesColimitsOfShape (Discrete I)
        (DerivedCategory.Q (C := A) ⋙ DerivedCategory.homologyFunctor A n) :=
      preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors A n).symm
    exact preservesColimitsOfShape_discrete_of_essSurj_comp
      (DerivedCategory.Q (C := A)) (DerivedCategory.homologyFunctor A n) I
  let Q := DerivedCategoryB.derivedCategoryB P
  have (I : Type u) : Q.IsClosedUnderColimitsOfShape (Discrete I) :=
    ⟨fun _ ⟨c⟩ n ↦
      have := hH I n
      P.prop_of_isColimit
        (isColimitOfPreserves (DerivedCategory.homologyFunctor A n) c.isColimit)
        (fun j ↦ c.prop_diag_obj j n)⟩
  change HasCoproducts.{u} Q.FullSubcategory
  intro I
  have : HasColimitsOfShape (Discrete I) (DerivedCategory A) :=
    Stacks.Injectives.hasCoproducts_derivedCategory A I
  exact hasColimitsOfShape_of_closedUnderColimits (Discrete I) Q

end AlgebraicGeometry

end
