module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksCore.Tactic.StacksAttribute

/-!
# The functor of formal glueing for quasi-coherent modules, with no inverse-image hypothesis

In the formal glueing situation of Stacks 0AEV, the functor of Stacks 0AEW is
`QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)`, sending a quasi-coherent module to its restriction to the open
complement `U`, its pullback to `Y`, and the canonical comparison of the two on the overlap `V`.
Since pullback along an arbitrary morphism of algebraic spaces preserves quasi-coherence (Stacks
03GA), the functor is defined with no hypothesis beyond the situation.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingModulesUnconditional`: the functor
  `QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)` of formal glueing.

## Main results

* `isQuasicoherentOnSite_quasicoherentGlueingDiagram_obj_left_unconditional` and
  `isQuasicoherentOnSite_quasicoherentGlueingDiagram_obj_right_unconditional`: the two outer
  components of the triple of a quasi-coherent module are quasi-coherent.
* `glueingModulesUnconditional_obj_obj` and `glueingModulesUnconditional_map_hom`: the functor
  is the triple construction on objects and on morphisms.

## References

* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 0AEW](https://stacks.math.columbia.edu/tag/0AEW)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS)

/-- The restriction to the open complement `U` of a quasi-coherent `𝒪_X`-module is
quasi-coherent. -/
theorem isQuasicoherentOnSite_quasicoherentGlueingDiagram_obj_left_unconditional
    (M : QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    (D.quasicoherentGlueingDiagram.obj M).left.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.openImmersion
    M.obj M.property

/-- The pullback to `Y` of a quasi-coherent `𝒪_X`-module is quasi-coherent. -/
theorem isQuasicoherentOnSite_quasicoherentGlueingDiagram_obj_right_unconditional
    (M : QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    (D.quasicoherentGlueingDiagram.obj M).right.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.ambientMorphism
    M.obj M.property

/-- The functor `QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)` of formal glueing: a quasi-coherent `𝒪_X`-module
goes to its restriction to the open complement `U`, its pullback to `Y`, and the canonical
comparison of the two on the overlap `V`. -/
@[stacks 0AEW]
def glueingModulesUnconditional :
    QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2 ⥤ D.moduleGlueingData :=
  D.glueingModulesFunctor

/-- The triple attached by `glueingModulesUnconditional` to a quasi-coherent module `M` is
`quasicoherentGlueingDiagram.obj M`. -/
@[simp]
theorem glueingModulesUnconditional_obj_obj
    (M : QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    (D.glueingModulesUnconditional.obj M).obj = D.quasicoherentGlueingDiagram.obj M := rfl

/-- The morphism of triples attached by `glueingModulesUnconditional` to a morphism `a` of
quasi-coherent modules is `quasicoherentGlueingDiagram.map a`. -/
@[simp]
theorem glueingModulesUnconditional_map_hom
    {M N : QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2} (a : M ⟶ N) :
    InducedCategory.Hom.hom (D.glueingModulesUnconditional.map a) =
      D.quasicoherentGlueingDiagram.map a :=
  rfl

end AlgebraicGeometry.Space.FormalGlueingSituation

end
