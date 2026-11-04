module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Comparison

/-!
# The natural comparison of the Čech model is the transpose of the augmentation

`StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle/Comparison.lean` builds the natural
isomorphism `Stacks.LocalCohomology.localCohomologyIsoCech` between `RΓ_{V(I)}(-⟦0⟧)` and the
extended alternating Čech complex of Stacks 0A6R. Its components are obtained from
`Equiv.ofBijective` applied to a universal property, hence through `Function.surjInv`, so the
underlying morphisms are opaque: nothing can be computed from them beyond the characterizing
equations.

This file identifies the inverse component with
`Stacks.LocalCohomology.extendedCechObjectToLocalCohomology`, the transpose of the Čech
augmentation along the local-cohomology adjunction of Stacks 0A6Q. That morphism is built from
the adjunction's hom-equivalence and uses no choice, so the identification makes the natural
isomorphism concrete in both directions.

## Main results

* `Stacks.LocalCohomology.cechComparisonInv_eq` — the comparison from the Čech object to local
  cohomology is the transpose of the augmentation.
* `Stacks.LocalCohomology.localCohomologyIsoCech_inv_app_eq` — the same for the component of the
  natural isomorphism.

## Main definitions

* `Stacks.LocalCohomology.cechHomologyIsoLocalCohomologyNatIso` — the comparison on homology, as
  an isomorphism of functors from `R`-modules to `R`-modules, in every integer degree.

## Implementation notes

Both morphisms lift the augmentation along the counit, and composing with the counit is injective
on morphisms out of an object with `I`-power-torsion cohomology, so they agree. The homology-level
natural isomorphism is the derived-category one whiskered with the homology functor, together with
`CategoryTheory.DerivedCategory.homologyFunctorFactors`.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (I : Ideal R) (hI : I.FG)
  (hIf : Ideal.span (Set.range f) = I) (M : ModuleCat.{max u v} R)

/-- **The natural comparison is the transpose of the augmentation.** The component of
`Stacks.LocalCohomology.localCohomologyIsoCech` from the Čech object to local cohomology, built
through `Equiv.ofBijective`, equals the choice-free transpose of the Čech augmentation along the
local-cohomology adjunction. -/
theorem cechComparisonInv_eq :
    cechComparisonInv.{v} f I hI hIf M = extendedCechObjectToLocalCohomology f M I hI hIf := by
  refine (bijective_comp_localCohomologyCounit I hI
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)
    (extendedCechObject f M)
    (derivedPowerTorsionProperty_extendedCechObject f M I hI hIf)).injective ?_
  show cechComparisonInv.{v} f I hI hIf M ≫ (localCohomologyCounit.{v} I hI).app M =
    extendedCechObjectToLocalCohomology f M I hI hIf ≫
      (Dualizing.localCohomologyAdjunction R I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)
  rw [cechComparisonInv_comp_counit, extendedCechObjectToLocalCohomology_comp_counit,
    cechAugmentationHom_app]

/-- The inverse component of the natural comparison is the transpose of the augmentation. -/
theorem localCohomologyIsoCech_inv_app_eq :
    (localCohomologyIsoCech.{v} f I hI hIf).inv.app M =
      extendedCechObjectToLocalCohomology f M I hI hIf :=
  cechComparisonInv_eq.{v} f I hI hIf M

/-- The forward component of the natural comparison is the inverse of the transpose of the
augmentation. -/
theorem localCohomologyIsoCech_hom_app_eq :
    (localCohomologyIsoCech.{v} f I hI hIf).hom.app M =
      (extendedCechObjectIsoLocalCohomology f M I hI hIf).inv :=
  (Iso.inv_eq_inv ((localCohomologyIsoCech.{v} f I hI hIf).app M)
      (extendedCechObjectIsoLocalCohomology f M I hI hIf).symm).1
    (localCohomologyIsoCech_inv_app_eq.{v} f I hI hIf M)

/-- **Čech cohomology is local cohomology, naturally and in every degree.** For an ideal
`I = (f₁, …, f_r)` the functor sending an `R`-module `M` to `H^i_{V(I)}(M)` is naturally
isomorphic to the degree-`i` cohomology of `C^•(f₁, …, f_r; M)`, as functors valued in
`R`-modules. -/
def cechHomologyIsoLocalCohomologyNatIso (i : ℤ) :
    localCohomologyOnModules.{u, max u v} R I hI ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i ≅
      extendedCechFunctor.{v} f ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℤ) i :=
  Functor.isoWhiskerRight (localCohomologyIsoCech.{v} f I hI hIf)
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i) ≪≫
    Functor.isoWhiskerLeft (extendedCechFunctor.{v} f)
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) i)

/-- **The comparison on homology is natural in the module.** -/
theorem cechHomologyIsoLocalCohomologyNatIso_naturality {M N : ModuleCat.{max u v} R}
    (g : M ⟶ N) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map
          ((localCohomologyOnModules R I hI).map g) ≫
        (cechHomologyIsoLocalCohomologyNatIso.{v} f I hI hIf i).hom.app N =
      (cechHomologyIsoLocalCohomologyNatIso.{v} f I hI hIf i).hom.app M ≫
        HomologicalComplex.homologyMap (extendedCechComplexMap f g) i :=
  (cechHomologyIsoLocalCohomologyNatIso.{v} f I hI hIf i).hom.naturality g

end Stacks.LocalCohomology

end
