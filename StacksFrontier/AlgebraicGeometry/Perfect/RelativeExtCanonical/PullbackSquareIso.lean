module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.PerfectStageBaseChangeCore
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.RestrictRelativeExt

/-!
# Derived pullback around a commutative square, at the standard model

For morphisms of ringed spaces with `a ≫ b = c ≫ d`, the derived pullbacks satisfy
`La^*(Lb^*E) ≅ Lc^*(Ld^*E)`, naturally in `E`: both are `L(a ≫ b)^*E`. For an open immersion of
schemes `j`, the restriction `D(j^*)` of `Stacks.Cohomology.RelativeExt.restrictDerived` is the
derived pullback `Lj^*`. The statements are at the standard model, through
`Stacks.Cohomology.RelativeExtCanonical.stdPullback`.

## Main definitions

* `Stacks.Cohomology.RelativeExtCanonical.stdPullbackSquareIso`
* `Stacks.Cohomology.RelativeExtCanonical.restrictDerivedIsoStdPullback`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard

/-- **`La^*(Lb^*E) ≅ Lc^*(Ld^*E)` for `a ≫ b = c ≫ d`.** -/
def stdPullbackSquareIso {A B C D : RingedSpace.{u, u}} (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C)
    (d : C ⟶ D) (w : a ≫ b = c ≫ d) :
    stdPullback b ⋙ stdPullback a ≅ stdPullback d ⋙ stdPullback c :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a b ≪≫
    eqToIso (congrArg (fun k : A ⟶ D ↦ stdPullback k) w) ≪≫
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical c d).symm

/-- **Restriction to an open subscheme is the derived pullback.** -/
def restrictDerivedIsoStdPullback {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    restrictDerived j ≅ stdPullback j.toLRSHom.toShHom :=
  haveI : SheafedSpace.IsOpenImmersion j.toLRSHom.toShHom := (inferInstance : IsOpenImmersion j)
  (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
    j.toLRSHom.toShHom).symm

end Stacks.Cohomology.RelativeExtCanonical

end
