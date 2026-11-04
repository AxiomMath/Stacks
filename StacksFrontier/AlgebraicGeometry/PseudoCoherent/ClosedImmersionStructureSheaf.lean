module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.HigherRank.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedCohomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentModule

/-!
# The structure sheaf of a closed subscheme of a locally Noetherian scheme

Let `i : Z ⟶ T` be a closed immersion of schemes with `T` locally Noetherian. The direct image
`i_* 𝒪_Z`, placed in degree zero, is a pseudo-coherent object of `D(𝒪_T)` whose cohomology is
supported on the image of `i`.

## Main results

* `AlgebraicGeometry.isPseudoCoherent_singleFunctor_pushforward_unit_of_isClosedImmersion`:
  `i_* 𝒪_Z` in degree zero is pseudo-coherent.
* `AlgebraicGeometry.cohomologySupportedOn_singleFunctor_pushforward_unit`: its cohomology is
  supported on `Set.range i.base`.

## References

* [Stacks Project, Tag 0CSJ](https://stacks.math.columbia.edu/tag/0CSJ)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {Z T : Scheme.{u}} (i : Z ⟶ T)

/-! ### Pseudo-coherence -/

/-- For a closed immersion `i : Z ⟶ T` into a locally Noetherian scheme, the complex with
`i_* 𝒪_Z` in degree zero is a pseudo-coherent object of `D(𝒪_T)`. -/
theorem isPseudoCoherent_singleFunctor_pushforward_unit_of_isClosedImmersion
    [IsClosedImmersion i] [IsLocallyNoetherian T] :
    RingedSpace.IsPseudoCoherent (X := T.toRingedSpace)
      ((DerivedCategory.singleFunctor T.Modules 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) :=
  (RingedSpace.isPseudoCoherent_iff_forall (X := T.toRingedSpace) _).2 fun m =>
    isPseudoCoherentFrom_singleFunctor_zero_of_isCoherent T _
      (Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent
        (ClosedImmersionCoherentImage.isCoherent_pushforward_unit i)) m

/-! ### Support of the cohomology -/

/-- For a closed immersion `i : Z ⟶ T`, the cohomology of the complex with `i_* 𝒪_Z` in degree zero
is supported on the image of `i`. -/
theorem cohomologySupportedOn_singleFunctor_pushforward_unit [IsClosedImmersion i] :
    CohomologySupportedOn T.ringCatSheaf (Set.range i.base)
      ((DerivedCategory.singleFunctor T.Modules 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) := by
  intro n x hx
  rcases eq_or_ne n 0 with rfl | hn
  · refine (Stacks.AlgebraicGeometry.Tag01YMHigherRank.isZero_stalk_pushforward_of_notMem_range
      i (SheafOfModules.unit Z.ringCatSheaf) x hx).of_iso ?_
    exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((toAb T.ringCatSheaf).mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _))
  · let _ : HasZeroMorphisms (TopCat.Presheaf AddCommGrpCat.{u} T.toTopCat) :=
      inferInstanceAs (HasZeroMorphisms ((Opens T.toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{u}))
    have hpres : (toAb T.ringCatSheaf).PreservesZeroMorphisms := by
      show (SheafOfModules.forget T.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf T.ringCatSheaf.obj).PreservesZeroMorphisms
      infer_instance
    let _ := hpres
    refine Functor.map_isZero _ (Functor.map_isZero (toAb T.ringCatSheaf) ?_)
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ n).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _))
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ n).app _)
    exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn

end AlgebraicGeometry

end
