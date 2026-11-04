module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.RestrictionCollapseChosenResolutions
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationOnResolutions

/-!
# The collapse of a restriction followed by a direct image, at chosen resolutions

Let `f : X ⟶ Y` be a morphism of ringed spaces, `V ⊆ Y` an open, `M` a sheaf of modules on `X`
and `P` an additive functor out of the modules on `V`. The collapse of [Stacks, Tag 01E1]

`R ᵖ ((-|_{f⁻¹V}) ⋙ (f ∣ V)_* ⋙ P) ≅ (-|_{f⁻¹V}) ⋙ R ᵖ ((f ∣ V)_* ⋙ P)`

is computed at `M` on the chosen injective resolutions of `M` and of `M|_{f⁻¹V}`, through the
comparison `Stacks.Cohomology.HigherDirectImage.restrictChosenResolutionComparison` between them.

## Main results

* `Stacks.Cohomology.HigherDirectImage.restrictChosenResolutionComparison_ι_f_zero`: the
  degree-zero component of `restrictChosenResolutionComparison`, precomposed with the
  augmentation of the chosen resolution of `M|_{f⁻¹V}`, is the augmentation of the image under
  restriction of the chosen resolution of `M`.
* `Stacks.Cohomology.HigherDirectImage.compRightDerivedNatIso_inv_app_chosenResolution`: the
  component at `M` of the inverse of the collapse is the computation of the right-hand side on
  the chosen resolution of `M|_{f⁻¹V}`, then the degree-`p` homology of `(f ∣ V)_* ⋙ P` applied
  to `restrictChosenResolutionComparison`, then the inverse of the computation of the left-hand
  side on the chosen resolution of `M`.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction (modulePushforward)
open Stacks.Cohomology.DerivedCompTransport

universe u

namespace Stacks.Cohomology.HigherDirectImage

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)
  (M : SheafOfModules.{u} (structureSheafRing X))

/-- The degree-zero component of the comparison of the two chosen resolutions, precomposed with
the augmentation of the chosen resolution of `M|_{f⁻¹V}`, is the augmentation of the image under
restriction of the chosen resolution of `M`. -/
theorem restrictChosenResolutionComparison_ι_f_zero :
    (injectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M)).ι.f 0 ≫
        (restrictChosenResolutionComparison f V M).f 0 =
      (Stacks.Cohomology.CompositeRightDerived.mapInjRes (moduleRestriction X (preimageOpen f V))
        (injectiveResolution M)).ι.f 0 :=
  (InjectiveResolution.desc_mapOfPreservesInjectives_f_zero _ _ _).trans
    (mapInjRes_ι_f_zero (moduleRestriction X (preimageOpen f V)) (injectiveResolution M)).symm

variable {W : Type*} [Category* W] [Abelian W]
  (P : SheafOfModules.{u} (structureSheafRing (restrictToOpen Y V)) ⥤ W) [P.Additive]

/-- For a morphism of ringed spaces `f : X ⟶ Y`, an open `V ⊆ Y`, a sheaf of modules `M` on `X`,
an additive functor `P` out of the modules on `V` and a degree `p`, the inverse of the component
at `M` of the collapse of [Stacks, Tag 01E1]

`R ᵖ ((-|_{f⁻¹V}) ⋙ (f ∣ V)_* ⋙ P) ≅ (-|_{f⁻¹V}) ⋙ R ᵖ ((f ∣ V)_* ⋙ P)`

is the computation of `R ᵖ ((f ∣ V)_* ⋙ P)` on the chosen injective resolution of `M|_{f⁻¹V}`,
then the degree-`p` homology of `(f ∣ V)_* ⋙ P` applied to
`Stacks.Cohomology.HigherDirectImage.restrictChosenResolutionComparison`, then the inverse of the
computation of `R ᵖ ((-|_{f⁻¹V}) ⋙ (f ∣ V)_* ⋙ P)` on the chosen injective resolution of `M`. -/
theorem compRightDerivedNatIso_inv_app_chosenResolution (p : ℕ) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
        (moduleRestriction X (preimageOpen f V))
        (modulePushforward (restrictedMorphism f V) ⋙ P) p).inv.app M =
      ((injectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M)).isoRightDerivedObj
          (modulePushforward (restrictedMorphism f V) ⋙ P) p).hom ≫
        ((modulePushforward (restrictedMorphism f V) ⋙ P).mapHomologicalComplex
              (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor W (ComplexShape.up ℕ) p).map
          (restrictChosenResolutionComparison f V M) ≫
          ((injectiveResolution M).isoRightDerivedObj
            (moduleRestriction X (preimageOpen f V) ⋙
              modulePushforward (restrictedMorphism f V) ⋙ P) p).inv := by
  rw [compRightDerivedNatIso_inv_app_eq _ _ p (injectiveResolution M),
    isoRightDerivedObj_hom_eq (modulePushforward (restrictedMorphism f V) ⋙ P) p
      (injectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M))
      (Stacks.Cohomology.CompositeRightDerived.mapInjRes
        (moduleRestriction X (preimageOpen f V)) (injectiveResolution M))
      (restrictChosenResolutionComparison f V M)
      (restrictChosenResolutionComparison_ι_f_zero f V M)]
  exact Category.assoc _ _ _

end Stacks.Cohomology.HigherDirectImage

end
