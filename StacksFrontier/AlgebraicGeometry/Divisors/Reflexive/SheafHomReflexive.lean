module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalHom
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullCoherentReflexive
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.LocalKernel
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic

/-!
# The internal Hom into a reflexive coherent module is reflexive

On an integral locally Noetherian scheme, if `𝒢` is a reflexive coherent module then
`SheafHom(ℱ, 𝒢)` is reflexive for every coherent `ℱ`.

## Main results

* `AlgebraicGeometry.sheafHom_isReflexive`: the internal Hom into a reflexive coherent module
  is reflexive.

## References

* [Stacks Project, Tag 0AY4](https://stacks.math.columbia.edu/tag/0AY4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.InternalHom
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry

/-- On an integral locally Noetherian scheme, the internal Hom `SheafHom(ℱ, 𝒢)` of coherent modules
is reflexive as soon as `𝒢` is. -/
@[stacks 0AY4]
theorem sheafHom_isReflexive (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (F G : X.Modules) [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G]
    (hG : IsReflexive G) :
    IsReflexive (sheafInternalHom (spaceRingedSite X.sheaf) F G) := by
  let H : X.Modules := sheafInternalHom (spaceRingedSite X.sheaf) F G
  let finitePresentation : F.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent F
  let : G.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent G
  let : _root_.SheafOfModules.IsCoherent (dualSheaf G) := isCoherent_dualSheaf G
  let : (dualSheaf G).IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent _
  let : _root_.SheafOfModules.IsCoherent H :=
    @isCoherent_sheafInternalHom'.{u} X inferInstance X.sheaf F G finitePresentation
      (inferInstance : _root_.SheafOfModules.IsCoherent G)
  let : H.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent H
  let : _root_.SheafOfModules.IsCoherent (dualSheaf H) := isCoherent_dualSheaf H
  let : (dualSheaf H).IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent _
  let : F.IsFiniteType := _root_.IsCoherent.toIsFiniteType F
  let : G.IsFiniteType := _root_.IsCoherent.toIsFiniteType G
  refine isReflexive_of_forall_isReflexive_stalk H fun x => ?_
  let : Module.Finite ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
    Stacks.StalkFiniteType.finite_stalk F x
  let : Module.Finite ↑(X.presheaf.stalk x) ↑(G.presheaf.stalk x) :=
    Stacks.StalkFiniteType.finite_stalk G x
  let : Module.IsReflexive ↑(X.presheaf.stalk x) ↑(G.presheaf.stalk x) :=
    isReflexive_stalk_of_isReflexive G hG x
  let : Module.IsReflexive ↑(X.presheaf.stalk x)
      (↑(F.presheaf.stalk x) →ₗ[↑(X.presheaf.stalk x)] ↑(G.presheaf.stalk x)) :=
    isReflexive_linearMap inferInstance
  let e : (↑(F.presheaf.stalk x) →ₗ[↑(X.presheaf.stalk x)] ↑(G.presheaf.stalk x))
      ≃ₗ[↑(X.presheaf.stalk x)] ↑(H.presheaf.stalk x) :=
    (sheafHomStalkLinearEquivOfFinitePresentation
      (internalSheafHom X.toTopCat X.sheaf F G) x).equiv.symm
  exact Module.equiv e

end AlgebraicGeometry

end
