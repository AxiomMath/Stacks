module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartConormalSections
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartProblemSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.ProblemIdealSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.BaseExtensionConormalClassSets

/-!
# Generators of the ideal of the extension problem at a chart

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart and `D`
a square-zero thickening `Spec A ⊂ Spec A'` of Situation 07YX with ideal `I`. For `k ∈ I`, the
function `k` on `Spec A'` vanishes on `Spec A`; its class in the conormal module of
`Spec A ⊂ Spec A'` (`AlgebraicGeometry.Space.ProperFlatLift.chartConormalClass`), pulled back to
`X`, is a section `σ_k` of the ideal of the extension problem of `x` along `D`
(`AlgebraicGeometry.Space.ProperFlatLift.chartIdealGenerator`). These generate the ideal; they are
the sections on which the prescribed maps of the problems at a chart are compared along a morphism
of thickenings (Remark 0D1P).

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

/-- File-local shortcut: the inverse image of a morphism of topoi preserves finite products
(instance search through the generic paths times out). -/
local instance (priority := high) preservesFiniteProducts_inverseImage_properFlatChartIdealGenerators
    {E : Type*} [Category E] {F : Type*} [Category F] (f : MorphismOfTopoi E F) :
    PreservesFiniteProducts f.inverseImage :=
  haveI := f.preservesFiniteLimits
  inferInstance

/-- File-local shortcut: the inverse image of a morphism of topoi preserves the terminal
object (instance search through the generic paths times out). -/
local instance (priority := high) isIso_terminalComparison_inverseImage_properFlatChartIdealGenerators
    {E : Type*} [Category E] {F : Type*} [Category F] [HasTerminal E] [HasTerminal F]
    (f : MorphismOfTopoi E F) : IsIso (terminalComparison f.inverseImage) :=
  haveI := f.preservesFiniteLimits
  inferInstance

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The cast `g^*𝒞 = g'^*𝒞` along `g = g'`, on the model, carries the pulled-back section `g^*t`
to `g'^*t`, on the unit section. -/
theorem eqToHom_val_app_modulePullbackGlobalSection {Y' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS Y'.1} {X : AlgebraicSpaces B S hS}
    {g g' : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)} (h : g = g')
    (t : SheafOfModules.unit (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ :
      AlgebraicSpaces B S hS)) ⟶ conormalModule B S hS Y' Z)
    (U : (SmallModel.{u} (SmallEtale B S hS X.1))ᵒᵖ) :
    (eqToHom (congrArg (fun g => (Deformation.AlgebraExtension.moduleRes
        (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse
        (smallEtaleRingedTopos B S hS X).O).obj
          (FlatThickeningDeformation.pulledBackConormal (Z := Z) g)) h)).val.app U
        ((modulePullbackGlobalSection B S hS g t).val.app
          (Opposite.op ((smallEtaleModelEquiv B S hS X).inverse.obj U.unop))
          (1 : chartRing B S hS X.1 X.2 ((smallEtaleModelEquiv B S hS X).inverse.obj U.unop))) =
      (modulePullbackGlobalSection B S hS g' t).val.app
          (Opposite.op ((smallEtaleModelEquiv B S hS X).inverse.obj U.unop))
          (1 : chartRing B S hS X.1 X.2 ((smallEtaleModelEquiv B S hS X).inverse.obj U.unop)) := by
  subst h
  rfl

namespace ProperFlatLift

open Deformation.Artin Deformation.ToposThickening

variable {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  {A' : Type u} [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A')

/-- **The class of `k ∈ I` in the conormal module of `Spec A ⊂ Spec A'`**: the pullback to the
closed subspace of the function `k` on `Spec A'`, a section of its ideal sheaf. -/
abbrev chartConormalClass (k : D.kernel) :=
  squareZeroConormalSection B S hS D.arrow (isSquareZeroClosedImmersion_arrow D)
    ((thickeningKernelIdealIso D).hom.hom k)

/-- **The section `σ_k` of the ideal of the problem of `x` along `D`**, on the small étale site of
`X`: the inverse image of the conormal class of `k`. -/
abbrev chartIdealGenerator (k : D.kernel) :=
  FlatThickeningDeformation.problemIdealSection
    (isFirstOrderThickening_squareZeroSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D))
    (chartStructureMap x hx ≫ (chartRangeIso D).hom) (chartConormalClass D k)

/-- The value of `σ_k` over the object of the small étale site of `X` underlying an object `U` of
the model. -/
abbrev chartIdealGeneratorSection (k : D.kernel)
    (U : (SmallModel.{u} (SmallEtale B S hS x.obj.obj.left.1))ᵒᵖ) :
    (problemOnChart x hx D).I.val.obj U :=
  (chartIdealGenerator x hx D k).val.app
    (Opposite.op ((smallEtaleModelEquiv B S hS x.obj.obj.left).inverse.obj U.unop))
    (1 : (Stacks.Sheaves.ToposPullback.pullbackRingSheaf
      (SmallEtale.topology B S hS x.obj.obj.left.1)
      (smallEtaleRingedToposHom B S hS
        (chartStructureMap x hx ≫ (chartRangeIso D).hom)).toToposHom.inverseImage
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS
        (⟨(squareZeroSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
          (squareZeroSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ :
            AlgebraicSpaces B S hS)).O)).obj.obj
      (Opposite.op ((smallEtaleModelEquiv B S hS x.obj.obj.left).inverse.obj U.unop)))

end ProperFlatLift

end AlgebraicGeometry.Space
