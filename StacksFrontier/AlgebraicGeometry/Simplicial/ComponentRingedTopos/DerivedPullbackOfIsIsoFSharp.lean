module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescent
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor

/-!
# Derived pullback along a morphism of ringed topoi with invertible structure map

For a morphism of ringed topoi `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` whose structure map
`f^{-1}O_D ⟶ O_C` is invertible, pullback of modules `f^*` is the exact inverse image functor, so
the derived pullback `Lf^*` (`AlgebraicGeometry.RingedToposHom.leftDerivedPullbackOfIsIsoFSharp`)
is the functor `f^*` induces degreewise on derived categories.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.derivedPullbackNatIsoOfIsIsoFSharp`:
  `Lf^* ≅ f^*.mapDerivedCategory`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]

attribute [local instance] pullbackModules_preservesFiniteLimits_of_isIso_fSharp
  pullbackModules_preservesFiniteColimits_of_adjunction

/-- **`Lf^*` is the functor induced by the exact `f^*`, naturally**, for a morphism of ringed
topoi with invertible structure map: both are left derived functors of degreewise pullback, the
second because `f^*` is exact and so inverts the quasi-isomorphisms. -/
def derivedPullbackNatIsoOfIsIsoFSharp :
    (leftDerivedPullbackOfIsIsoFSharp f).functor ≅
      f.toModulesHom.pullbackModules.mapDerivedCategory :=
  haveI := (leftDerivedPullbackOfIsIsoFSharp f).isLeftDerivedFunctor
  Stacks.Homology.leftDerivedIsoMapDerivedCategory _ _
    (leftDerivedPullbackOfIsIsoFSharp f).comparison

end AlgebraicGeometry.RingedToposHom

end
