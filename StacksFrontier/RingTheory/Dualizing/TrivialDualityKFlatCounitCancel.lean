module

public import StacksFrontier.RingTheory.Dualizing.TrivialDualityKFlatNatTrans
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityPerfectTensor

/-!
# Cancelling the counit of Stacks 0A70 from the comparison of Stacks 0BZE

`StacksFrontier/RingTheory/Dualizing/TrivialDualityKFlat.lean` reduces Stacks 0BZE to invertibility
of `Stacks0BZE.comparison` at the K-flat complexes, and characterizes that morphism by
`Stacks0BZE.restrictScalars_comparison_comp_counit`: restricted to `R` and followed by the counit
of Stacks 0A70, it is `Stacks0BZE.restrictedComparison`. That characterization cannot be used
directly, because the counit is not a monomorphism: an equation between two morphisms of `D(R)`
composed with it does not determine the two morphisms.

This file records the one shape in which the counit *is* cancellable. The transpose of the
adjunction of Stacks 0A70 is a bijection, and its inverse is "restrict and follow with the
counit"; so two morphisms of `D(A)` whose restrictions agree after the counit are equal. Hence
to prove the comparison invertible at a K-flat complex it suffices to exhibit a single
isomorphism of `D(A)` whose restriction, followed by the counit, is the restricted comparison —
the comparison is then that isomorphism, with no further computation.

What this isolates is where the content of the remaining invertibility sits.
`Stacks0BZE.restrictedComparison` is `Stacky0BZE.underlyingNatTrans` followed by the tensored
counit `Stacks0BZE.tensorCounit`, and `Stacks0BZE.isIso_underlyingNatTrans_app` below shows the
first factor is invertible at a K-flat complex. So the hypothesis to be met is an equation
between the tensored counit, transported along that invertible factor, and the restriction of a
morphism of `D(A)`. The invertible factor is assembled from the field `directTensorUnderlying` of
the derived change-of-rings bundle of Stacks 06Y6, and
`Stacks0BZE.comparisonOfBundle_twistUnderlying` of
`StacksFrontier/RingTheory/Dualizing/TrivialDualityKFlatBundleFree.lean` shows that no axiom of that
interface constrains it; the hypothesis below therefore cannot be met from the interface alone.

## Main results

* `Stacks0BZE.isIso_underlyingNatTrans_app`: the three structural comparisons of the derived
  change-of-rings bundle assembling `Stacks0BZE.underlyingNatTrans` are all invertible at a
  K-flat complex.
* `Stacks0BZE.isIso_comparison_of_exists_restricted_iso`: **the comparison of Stacks 0BZE is
  invertible at a K-flat complex as soon as one isomorphism of `D(A)` restricts, after the counit
  of Stacks 0A70, to `Stacks0BZE.restrictedComparison`.**

## References

* [The Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [The Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [The Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Stacks0BZE

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

/-- At a K-flat complex all three structural comparisons assembling
`Stacks0BZE.underlyingNatTrans` are invertible: the counit `alphaF` of the derived change-of-rings
bundle is invertible there, and the factorization of restriction of scalars through the derived
categories and the field `directTensorUnderlying` are isomorphisms everywhere. -/
theorem isIso_underlyingNatTrans_app (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    IsIso ((underlyingNatTrans.{u, v} f).app K) := by
  have e : (underlyingNatTrans.{u, v} f).app K =
      ((resDerived f).mapIso
          (@asIso _ _ _ _ _ ((bundle.{u, v} f).isIso_alphaF K hK)) ≪≫
        (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.app
          ((bundle.{u, v} f).directTensor.obj K) ≪≫
        DerivedCategory.Q.mapIso
          ((bundle.{u, v} f).directTensorUnderlying.app K)).hom := rfl
  rw [e]
  infer_instance

/-- **The reduction that makes the counit of Stacks 0A70 cancellable.** To prove the comparison of
Stacks 0BZE invertible at a K-flat complex it suffices to exhibit one isomorphism of `D(A)` whose
restriction to `R`, followed by the counit of Stacks 0A70, is
`Stacks0BZE.restrictedComparison`; the comparison is then that isomorphism.

The transpose of the adjunction of Stacks 0A70 is a bijection whose inverse is restriction
followed by the counit, so the counit may be cancelled from an equation between two morphisms
that are both restrictions of morphisms of `D(A)`. The restricted comparison is not itself of
that form, which is why the hypothesis has to be supplied rather than derived. -/
theorem isIso_comparison_of_exists_restricted_iso
    (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K)
    (b : (bundle.{u, v} f).F.obj (DerivedCategory.Q.obj K) ≅
      (Dualizing.derivedHom.{u, v} f).obj (DerivedCategory.Q.obj K))
    (hb : (resDerived f).map b.hom ≫
        (Dualizing.derivedHomAdjunction.{u, u, v} f).counit.app (DerivedCategory.Q.obj K) =
      restrictedComparison.{u, v} f K hK) :
    IsIso (comparison.{u, v} f K hK) := by
  have hbe : comparison.{u, v} f K hK = b.hom := by
    rw [comparison_eq]
    exact (Equiv.eq_symm_apply _).mp
      (((Dualizing.derivedHomAdjunction.{u, u, v} f).homEquiv_counit
        (g := b.hom)).trans hb).symm
  rw [hbe]
  infer_instance

end Stacks0BZE

end
