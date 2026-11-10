module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeAssembly

/-!
# The open equality of Stacks 0E23 reduced to the local identity

For a cartesian square `i' ≫ f = g ≫ i` of schemes with `i` a closed immersion, the residual
identity `Stacks.Cohomology.ClosedImmersionBaseChange.LocalBaseChangeIdentityAt` between the four
local rings of the square implies the open equality
`Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEqQAt` of Stacks 0E23 below
`DerivedCategory.Q`.

## Main results

* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkBaseChangeEqQAt_of_local`: the open
  equality below `DerivedCategory.Q`, at one point and one complex, follows from the local
  identity.

## Implementation notes

The adjoint of the derived base change map is never written out as a composite:
`AlgebraicGeometry.derivedStalk_transposeSplit_comp_derivedStalkPushforward` takes the three
factors the transpose splits into as separate arguments, assigned by unification.

The transpose is described by `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq_split`,
not `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq`: the kernel cannot convert the
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` factor of the latter into a copy
elaborated here (see `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_adjoint_split`),
while the split form carries it as
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` and a
`CategoryTheory.eqToHom`, which do convert.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

noncomputable section

universe u

namespace Stacks.Cohomology.ClosedImmersionBaseChange

attribute [local instance] HasDerivedCategory.standard

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

attribute [local instance] isLeftDerived_alphaG isLeftDerived_alphaH

open Stacks.Cohomology.DerivedBaseChange Stacks.DerivedPullback.Composition
  StacksDraft.DerivedStalkAssemblyChase in
/-- The local identity `LocalBaseChangeIdentityAt` at `w` and `P` implies the open equality
`DerivedStalkBaseChangeEqQAt` of Stacks 0E23 below `DerivedCategory.Q` at `w` and `P`. -/
theorem derivedStalkBaseChangeEqQAt_of_local (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z') (P : CochainComplex Z.Modules ℤ)
    (hloc : LocalBaseChangeIdentityAt sq w P) :
    DerivedStalkBaseChangeEqQAt sq w P := by
  have := isClosedImmersion_of_isPullback sq
  have h1 := AlgebraicGeometry.derivedStalk_transposeSplit_comp_derivedStalkPushforward i' w
    (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
      f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) (DerivedCategory.Q.obj P))
    _ _ _
    (derivedBaseChangeMap_eq_split g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
      f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) (DerivedCategory.Q.obj P)
      (derivedPullback_diagonal_obj_eq sq
        ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))))
    (AlgebraicGeometry.pullbackComparisonOnComplex g P)
  have key := lhsKeyChaseGeom sq w P (splitHead
    ((AlgebraicGeometry.derivedStalkFunctor w).map_comp
      ((derivedPullbackCompIsoCanonical i'.toLRSHom.toShHom f.toLRSHom.toShHom).hom.app
        ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)))
      (eqToHom (derivedPullback_diagonal_obj_eq sq
        ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)))))
    ((AlgebraicGeometry.derivedStalkFunctor w).map
        ((derivedPullbackCompIsoCanonical g.toLRSHom.toShHom i.toLRSHom.toShHom).inv.app
          ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
      (AlgebraicGeometry.derivedStalkFunctor w).map
          ((derivedPullback g.toLRSHom.toShHom).map
            ((derivedAdjunction i.toLRSHom.toShHom).counit.app (DerivedCategory.Q.obj P))) ≫
        (AlgebraicGeometry.derivedStalkFunctor w).map
          (AlgebraicGeometry.pullbackComparisonOnComplex g P)))
  have h9 := (Adjunction.unit_naturality
    (AlgebraicGeometry.derivedStalkGermAdjunction i' w)
      ((AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).hom.app
        ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)))).symm
  refine combine _ _ _ _ _ _ _ _ _ _ _ ?_ (rhsChaseGeom (i' := i') (f := f) (i := i) w P) hloc
  exact lhsChaseUnit _ _ _ _ _ _ _ _
    (lhsChaseEm _ _ _ _ _ _ _ _ _ (lhsChaseMid _ _ _ _ _ _ _ _ _ _ h1 key)) h9

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
