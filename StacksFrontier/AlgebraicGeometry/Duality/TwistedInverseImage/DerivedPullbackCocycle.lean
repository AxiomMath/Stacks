module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeCompositionOnRingedTopoi

/-!
# The cocycle identity for the composition comparison of derived pullback

For composable morphisms `f`, `g` of ringed spaces, [Stacks, Tag 0D5S] provides a canonical
isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of derived pullbacks,
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`, whose underlying map is the
comparison `derivedPullbackCompComparisonCanonical` the universal property of the left derived
functor along `f ≫ g` produces. This file proves that the comparison satisfies the cocycle
identity: for three composable morphisms the two ways of identifying the threefold composite of
derived pullbacks with the derived pullback along the threefold composite agree.

The identity is proved at an **arbitrary** model of the three derived categories, which is what
makes it usable for schemes: `Stacks.Duality.derivedPullback` is this derived pullback at the
locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, whereas
`Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc` is
stated only at `CategoryTheory.HasDerivedCategory.standard`. Since
`CategoryTheory.HasDerivedCategory` carries the localization as data, neither model's statement
transports to the other.

## Main results

All in the namespace `Stacks.Duality`.

* `modulePushforwardComp_cocycle` — the cocycle identity for `f_* ⋙ g_* ≅ (f ≫ g)_*` of
  degreewise pushforward of sheaves of modules. Its components are identity morphisms.
* `modulePullbackComp_cocycle` — the cocycle identity for `g^* ⋙ f^* ≅ (f ≫ g)^*` of degreewise
  pullback, obtained from the previous one because pullback is the left adjoint of pushforward.
* `pullbackOnHomotopyCompIso_cocycle` — the same on the unbounded homotopy categories of cochain
  complexes.
* `derivedPullbackCompComparison_cocycle` — the cocycle identity for the comparison of
  [Stacks, Tag 0D5S].

## Implementation notes

The first step is `RingedSpaceModuleAdjunction.modulePushforwardComp_hom_app`: degreewise
pushforward is strictly multiplicative. The second is Mathlib's
`CategoryTheory.Adjunction.leftAdjointCompIso_assoc`, which carries a cocycle identity from a
family of compositors of right adjoints to the compositors of the left adjoints; this is how
`Stacks.DerivedPullback.Composition.modulePullbackComp` was defined, so no new comparison of
pullbacks is introduced here. The third is
`Stacks.Cohomology.DerivedBaseChangeComposition.mapHomotopyCategoryCompIso_assoc`, and the
fourth is `Stacks.Cohomology.DerivedBaseChangeComposition.leftDerived_comparison_assoc`, the
universal property of the left derived functor; both are stated for arbitrary data and are used
here without change.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open RingedSpaceModuleAdjunction (ModuleSheaves modulePushforward modulePullback
  modulePushforwardComp modulePullbackPushforwardAdjunction)
open Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPullbackComparison)

universe w₁ w₂ w₃ w₄ u

namespace Stacks.Duality

variable {X Y Z W : RingedSpace.{u, u}} (p : X ⟶ Y) (q : Y ⟶ Z) (r : Z ⟶ W)

/-- **The cocycle identity for the composition isomorphism of degreewise pushforward** of sheaves
of modules on ringed spaces. Every component of
`RingedSpaceModuleAdjunction.modulePushforwardComp` is an identity morphism, so both composites
are the identity. -/
theorem modulePushforwardComp_cocycle :
    Functor.isoWhiskerLeft (modulePushforward p) (modulePushforwardComp q r) ≪≫
        modulePushforwardComp p (q ≫ r) =
      (Functor.associator (modulePushforward p) (modulePushforward q)
          (modulePushforward r)).symm ≪≫
        Functor.isoWhiskerRight (modulePushforwardComp p q) (modulePushforward r) ≪≫
          modulePushforwardComp (p ≫ q) r :=
  Iso.ext (NatTrans.ext (funext fun _ => rfl))

/-- **The cocycle identity for the composition isomorphism of degreewise pullback** of sheaves of
modules on ringed spaces, in the orientation `g^* ⋙ f^* ≅ (f ≫ g)^*` of
`Stacks.DerivedPullback.Composition.modulePullbackComp`. That isomorphism is the mate of
`RingedSpaceModuleAdjunction.modulePushforwardComp` under the pullback-pushforward adjunctions,
so this is `CategoryTheory.Adjunction.leftAdjointCompIso_assoc` applied to
`Stacks.Duality.modulePushforwardComp_cocycle`. -/
theorem modulePullbackComp_cocycle :
    Functor.isoWhiskerLeft (modulePullback r) (modulePullbackComp p q) ≪≫
        modulePullbackComp (p ≫ q) r =
      (Functor.associator (modulePullback r) (modulePullback q) (modulePullback p)).symm ≪≫
        Functor.isoWhiskerRight (modulePullbackComp q r) (modulePullback p) ≪≫
          modulePullbackComp p (q ≫ r) :=
  Adjunction.leftAdjointCompIso_assoc (modulePullbackPushforwardAdjunction r)
    (modulePullbackPushforwardAdjunction q) (modulePullbackPushforwardAdjunction p)
    (modulePullbackPushforwardAdjunction (q ≫ r)) (modulePullbackPushforwardAdjunction (p ≫ q))
    (modulePullbackPushforwardAdjunction (p ≫ q ≫ r)) _ _ _ _
    (modulePushforwardComp_cocycle p q r)

/-- **The cocycle identity for the pullback composition isomorphism on the unbounded homotopy
categories** of cochain complexes of sheaves of modules. A composition isomorphism of additive
functors induces one on homotopy categories, componentwise on complexes, and the induced family
satisfies the cocycle identity as soon as the original family does. -/
theorem pullbackOnHomotopyCompIso_cocycle :
    Functor.whiskerLeft ((modulePullback r).mapHomotopyCategory (ComplexShape.up ℤ))
          (pullbackOnHomotopyCompIso p q).hom ≫
        (pullbackOnHomotopyCompIso (p ≫ q) r).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (pullbackOnHomotopyCompIso q r).hom
          ((modulePullback p).mapHomotopyCategory (ComplexShape.up ℤ)) ≫
        (pullbackOnHomotopyCompIso p (q ≫ r)).hom :=
  Stacks.Cohomology.DerivedBaseChangeComposition.mapHomotopyCategoryCompIso_assoc
    (modulePullbackComp q r) (modulePullbackComp p q) (modulePullbackComp (p ≫ q) r)
    (modulePullbackComp p (q ≫ r))
    (by
      have h := congrArg Iso.hom (modulePullbackComp_cocycle p q r)
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom] at h
      exact h)
    (ComplexShape.up ℤ)

/-- **The cocycle identity for the composition comparison of derived pullback**, [Stacks, Tag
0D5S], at an arbitrary model of the derived categories. Each comparison is the map that the
universal property of the left derived functor along the composite produces out of the comparison
on the homotopy categories, so two such composites agree as soon as the two corresponding
composites on the homotopy categories do, which is
`Stacks.Duality.pullbackOnHomotopyCompIso_cocycle`. -/
theorem derivedPullbackCompComparison_cocycle
    [HasDerivedCategory.{w₁} (ModuleSheaves X)] [HasDerivedCategory.{w₂} (ModuleSheaves Y)]
    [HasDerivedCategory.{w₃} (ModuleSheaves Z)] [HasDerivedCategory.{w₄} (ModuleSheaves W)] :
    Functor.whiskerLeft (derivedPullback r) (derivedPullbackCompComparisonCanonical p q) ≫
        derivedPullbackCompComparisonCanonical (p ≫ q) r =
      (Functor.associator (derivedPullback r) (derivedPullback q) (derivedPullback p)).inv ≫
        Functor.whiskerRight (derivedPullbackCompComparisonCanonical q r) (derivedPullback p) ≫
          derivedPullbackCompComparisonCanonical p (q ≫ r) := by
  let : (derivedPullback (p ≫ q ≫ r)).IsLeftDerivedFunctor
      (derivedPullbackComparison ((p ≫ q) ≫ r))
      (HomotopyCategory.quasiIso (ModuleSheaves W) (ComplexShape.up ℤ)) :=
    inferInstanceAs ((derivedPullback (p ≫ q ≫ r)).IsLeftDerivedFunctor
      (derivedPullbackComparison (p ≫ q ≫ r))
      (HomotopyCategory.quasiIso (ModuleSheaves W) (ComplexShape.up ℤ)))
  exact Stacks.Cohomology.DerivedBaseChangeComposition.leftDerived_comparison_assoc
    (derivedPullbackComparison r) (derivedPullbackComparison q) (derivedPullbackComparison p)
    (derivedPullbackComparison (q ≫ r)) (derivedPullbackComparison (p ≫ q))
    (derivedPullbackComparison (p ≫ q ≫ r))
    (HomotopyCategory.quasiIso (ModuleSheaves W) (ComplexShape.up ℤ))
    (pullbackOnHomotopyCompIso q r).hom (pullbackOnHomotopyCompIso p q).hom
    (pullbackOnHomotopyCompIso (p ≫ q) r).hom (pullbackOnHomotopyCompIso p (q ≫ r)).hom
    (derivedPullbackCompComparisonCanonical q r)
    (derivedPullbackCompComparisonCanonical p q)
    (derivedPullbackCompComparisonCanonical (p ≫ q) r)
    (derivedPullbackCompComparisonCanonical p (q ≫ r))
    (fun M => Functor.leftDerived_fac_app _ _ _ _ _ M)
    (fun M => Functor.leftDerived_fac_app _ _ _ _ _ M)
    (fun M => Functor.leftDerived_fac_app _ _ _ _ _ M)
    (fun M => Functor.leftDerived_fac_app _ _ _ _ _ M)
    (pullbackOnHomotopyCompIso_cocycle p q r)

end Stacks.Duality

end
