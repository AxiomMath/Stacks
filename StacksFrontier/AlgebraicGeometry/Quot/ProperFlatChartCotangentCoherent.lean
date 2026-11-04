module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesChartDeformation
public import StacksFrontier.Cotangent.Spaces.ModelCotangentDerivedCoherent

/-!
# The cotangent complex of a chart of proper flat spaces over a Noetherian ring

Let `x` be an object of the stack of flat proper algebraic spaces lying over `Spec A`, with
structure morphism `X → Spec A` (`AlgebraicGeometry.Space.ProperFlatLift.chartStructureMap`),
`A` Noetherian. If `X → Spec A` is locally of finite type, then `L_{X/A}`, formed on the model of
the small étale site of `X`, is the image under the Comparison Lemma of an object of
`D^-_{Coh}(𝒪_X)`. This is the case of
`AlgebraicGeometry.Space.exists_isCoherent_homology_isBoundedAbove_cotangentComplexDerived` for
this morphism.

## Main results

* `exists_isCoherent_homology_isBoundedAbove_cotangentComplexDerived_chartStructureMap`:
  `L_{X/A} ∈ D^-_{Coh}(𝒪_X)` for a chart `X → Spec A` locally of finite type, `A` Noetherian.

## References

* [Stacks Project, Tag 08PZ](https://stacks.math.columbia.edu/tag/08PZ)
* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe t t' u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  [HasDerivedCategory.{t} (Modules.{u, u} B S hS x.obj.obj.left.1 x.obj.obj.left.2)]
  [HasDerivedCategory.{t'} (modelModules x.obj.obj.left)]

/-- If `X → Spec A` is locally of finite type and `A` is Noetherian, then `L_{X/A}` is the image
of an object of `D^-_{Coh}(𝒪_X)`: one with coherent cohomology sheaves which is bounded above. -/
theorem exists_isCoherent_homology_isBoundedAbove_cotangentComplexDerived_chartStructureMap
    [IsNoetherianRing A] (hf : IsLocallyOfFiniteType B S hS (chartStructureMap x hx).hom) :
    ∃ (E : DerivedCategory (Modules.{u, u} B S hS x.obj.obj.left.1 x.obj.obj.left.2))
      (_ : (modelModulesEquiv B S hS x.obj.obj.left).functor.mapDerivedCategory.obj E ≅
        (modelRingedToposHom (chartStructureMap x hx)).cotangentComplexDerived),
      (∀ q : ℤ, IsCoherent B S hS x.obj.obj.left.1 x.obj.obj.left.2
        ((DerivedCategory.homologyFunctor _ q).obj E)) ∧
        DerivedCategoryB.IsBoundedAbove E := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (algebraOver A B S hS toS hA)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have : IsNoetherianRing (baseRing B S hS (algebraOver A B S hS toS hA)) :=
    isNoetherianRing_of_ringEquiv A
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  exact exists_isCoherent_homology_isBoundedAbove_cotangentComplexDerived
    (chartStructureMap x hx) hf inferInstance

end AlgebraicGeometry.Space.ProperFlatLift

end
