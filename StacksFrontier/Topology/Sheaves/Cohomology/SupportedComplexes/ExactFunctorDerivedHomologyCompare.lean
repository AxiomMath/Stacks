module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompare
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPushforward

/-!
# The third descent of "an exact functor commutes with `Hⁿ`"

`Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso` is a third copy of the
natural isomorphism `F.mapDerivedCategory ⋙ Hⁿ ≅ Hⁿ ⋙ F`, alongside
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` and
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`, which
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso`
already identifies with each other.  The implementation note on
`Stacks.Perfect.AbelianCechCokernelPassage.forgetDerivedHomologyIso` records that no two of the
three are `rfl`-equal.  This file closes the triangle.

## Main results

* `Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso_eq`: the third copy is the
  first one.

## Implementation notes

As for the other pair, both are `CategoryTheory.Localization.liftNatIso` along
`DerivedCategory.Q`, so `CategoryTheory.Localization.natTrans_ext` reduces the equality to the
images of cochain complexes.  The two differ in where the comparison
`CategoryTheory.Functor.mapDerivedCategoryFactors` is placed — inside the descended
transformation here, inside the `Localization.Lifting` instance there — and in the spelling of
the complex-level comparison, which is the same morphism twice:
`CategoryTheory.ShortComplex.mapHomologyIso` at the short complex `K.sc n`.
-/

@[expose] public noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory Category Limits

namespace Stacks.Cohomology.SupportedComplexes

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] in
/-- The complex-level comparison used by `exactFunctorDerivedHomologyIso` is the one used by
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`: at a complex `K` both are
`CategoryTheory.ShortComplex.mapHomologyIso` at `K.sc n`. -/
theorem exactFunctorHomologyIso_hom_app_eq (n : ℤ) (K : CochainComplex C₁ ℤ) :
    (exactFunctorHomologyIso F n).hom.app K =
      (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K := rfl

/-- **The third descent of "an exact functor commutes with `Hⁿ`" is the first one.** -/
theorem exactFunctorDerivedHomologyIso_eq (n : ℤ) :
    exactFunctorDerivedHomologyIso F n = F.mapDerivedCategoryHomologyIso n := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun K => ?_)
  simp [exactFunctorDerivedHomologyIso, Functor.mapDerivedCategoryHomologyIso,
    Functor.mapDerivedCategoryHomologyIsoAux, exactFunctorHomologyIso_hom_app_eq,
    Functor.lifting_iso_mapDerivedCategory]

end Stacks.Cohomology.SupportedComplexes

end
