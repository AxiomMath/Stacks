module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesIsomFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusQuasiCompact

/-!
# `Isom(E, E')` is an algebraic space of finite presentation over `T`, unconditionally

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces
(Situation 0DLE) and let `(T, E)`, `(T, E')` be two objects of `Complexes_{X/Y}` over the same test
scheme `T`. Every open of `T` characterised as in Stacks 0DLC, part (1), for `Ext^{<0}(E, E')`
is quasi-compact over `T`, and `Isom(E, E')` is an algebraic space of finite presentation over `T`
(the corrected form of Stacks 0DPW).

## Main results

* `negativeExtLociQuasiCompact_proved`: the opens of Stacks 0DLC, part (1), between objects over
  one test scheme are quasi-compact over it.
* `isFinitePresentationAlgebraicSpaceOver_complexesIsom_proved`: `Isom(E, E')` is an algebraic
  space of finite presentation over `T`.

## References

* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The opens of Stacks 0DLC, part (1), between two objects of `Complexes_{X/Y}` over one test
scheme are quasi-compact over it**, i.e. `NegativeExtLociQuasiCompact` holds. -/
theorem negativeExtLociQuasiCompact_proved (D : ComplexesSituation B S hS) :
    D.NegativeExtLociQuasiCompact :=
  fun T E E' hE hX hE' _ W hW =>
    isQuasiCompact_openSubspaceImmersion_negativeExtLocus (⟨T, E, hE, hX⟩ : ComplexesObject D) E'
      hE' W hW

/-- **`Isom(E, E')` is an algebraic space of finite presentation over `T`.** For two objects
`(T, E)` and `(T, E')` of `Complexes_{X/Y}` over the same test scheme, the functor
`T' ↦ {isomorphisms E_{T'} ≅ E'_{T'}}` on the test schemes over `T` is an algebraic space of
finite presentation over `T`, for `E'` relatively perfect (`h₁`) with no negative fibre
`Ext` (`h₂`). -/
theorem isFinitePresentationAlgebraicSpaceOver_complexesIsom_proved
    {D : ComplexesSituation B S hS} (A : ComplexesObject D)
    (E' : derivedModules B S hS (D.space A.T))
    (h₁ : D.IsRelativelyPerfect A.T E') (h₂ : D.HasNoNegativeFibreExt A.T E') :
    IsFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj A.T.left)
      (relativeDerivedIsomFunctor (D.projection A.T) A.E E') :=
  isFinitePresentationAlgebraicSpaceOver_complexesIsom (negativeExtLociQuasiCompact_proved D) A E'
    h₁ h₂

end AlgebraicGeometry.Space.ComplexesSituation

end
