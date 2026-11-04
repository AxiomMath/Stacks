module

public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransportApp
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Derived extension of scalars at the standard and at the locally small model

For `f : R →+* A`, the chosen total derived extension of scalars
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars f` can be taken at the
standard model of `D(R)` and `D(A)` or at the locally small one. The two are compared by the
shrinking equivalences of `Stacks.Injectives.grothendieckModelEquiv`, both being total left derived
functors of termwise extension of scalars.

## Main definitions

* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso`: the isomorphism
  between the total derived extension of scalars at the standard model followed by the comparison
  of models, and the comparison of models followed by the one at the locally small model.

## Main results

* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso_hom_app_comparison`:
  the comparison is pinned by the two comparisons with termwise extension of scalars.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CochainComplex.DerivedExtensionScalars

/-- For `F : C₁ ⥤ C₂` and `e : G ⋙ H ≅ K`, the component at `X` of the associator of `F`, `G`, `H`
followed by the left whiskering of `e` by `F` is the component of `e` at `F.obj X`. -/
theorem associator_trans_isoWhiskerLeft_hom_app {C₁ C₂ C₃ C₄ : Type*} [Category* C₁]
    [Category* C₂] [Category* C₃] [Category* C₄] (F : C₁ ⥤ C₂) {G : C₂ ⥤ C₃} {H : C₃ ⥤ C₄}
    {K : C₂ ⥤ C₄} (e : G ⋙ H ≅ K) (X : C₁) :
    (Functor.associator F G H ≪≫ Functor.isoWhiskerLeft F e).hom.app X = e.hom.app (F.obj X) := by
  simp

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

/-- The total derived extension of scalars at the standard model, followed by the comparison of
models, is the comparison of models followed by the total derived extension of scalars at the
locally small model. -/
def totalDerivedExtensionScalarsModelIso :
    @TotalDerivedExtensionScalars.functor.{u, u, u} R A _ _ f (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) (@totalDerivedExtensionScalars.{u, u, u} R A _ _ f
            (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)) ⋙
        (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R)).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u, u, u} f).functor :=
  have := @TotalDerivedExtensionScalars.isLeftDerived.{u, u, u} R A _ _ f
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (@totalDerivedExtensionScalars.{u, u, u} R A _ _ f
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))
  have := (totalDerivedExtensionScalars.{u, u, u, u, u} f).isLeftDerived
  StacksDraft.DerivedModel.leftDerivedModelIso
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (@TotalDerivedExtensionScalars.comparison.{u, u, u} R A _ _ f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) (@totalDerivedExtensionScalars.{u, u, u} R A _ _ f
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)))
    (totalDerivedExtensionScalars.{u, u, u, u, u} f).comparison
    (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} R)))
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} A))))

/-- **The comparison of the two models of derived extension of scalars on complexes**: after the
comparison with termwise extension of scalars at the locally small model, it is the comparison at
the standard model. -/
theorem totalDerivedExtensionScalarsModelIso_hom_app_comparison
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (totalDerivedExtensionScalarsModelIso f).hom.app
        (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) |>.obj P) ≫
      (totalDerivedExtensionScalars.{u, u, u, u, u} f).functor.map
        ((eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} R))).hom.app P) ≫
      (totalDerivedExtensionScalars.{u, u, u, u, u} f).comparison.app P =
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.map
          ((@TotalDerivedExtensionScalars.comparison.{u, u, u} R A _ _ f
            (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
            (@totalDerivedExtensionScalars.{u, u, u} R A _ _ f
              (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))).app P) ≫
        (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} A))).hom.app
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            P) := by
  have := @TotalDerivedExtensionScalars.isLeftDerived.{u, u, u} R A _ _ f
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (@totalDerivedExtensionScalars.{u, u, u} R A _ _ f
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))
  have := (totalDerivedExtensionScalars.{u, u, u, u, u} f).isLeftDerived
  refine (StacksDraft.DerivedModel.leftDerivedModelIso_hom_app_comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (@TotalDerivedExtensionScalars.comparison.{u, u, u} R A _ _ f (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) (@totalDerivedExtensionScalars.{u, u, u} R A _ _ f
            (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)))
    (totalDerivedExtensionScalars.{u, u, u, u, u} f).comparison
    (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} R)))
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} A)))) P).trans ?_
  exact congrArg (_ ≫ ·) (associator_trans_isoWhiskerLeft_hom_app _ _ P)

end CochainComplex.DerivedExtensionScalars
