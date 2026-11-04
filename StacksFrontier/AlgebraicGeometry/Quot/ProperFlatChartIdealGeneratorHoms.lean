module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartIdealGenerators
public import StacksFrontier.Tactic.DefinitionArguments
public import StacksFrontier.Deformation.ToposThickening.RebaseSiteTransportGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.ProblemIdealGenerators

/-!
# The generators of the ideal of the extension problem at a chart, as global sections

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart and `D`
a square-zero thickening `Spec A ⊂ Spec A'` of Situation 07YX with ideal `I`. For `k ∈ I`, the
pulled-back conormal class of `k` gives:

* a global section `σ_k` of the ideal of the problem of `x` along `D` on the model of the small
  étale site of `X` (`AlgebraicGeometry.Space.ProperFlatLift.chartModelIdealGenerator`), and of
  the ideal of `AlgebraicGeometry.Space.ProperFlatLift.problemOnChart x hx D`, read over `Spec A`
  (`AlgebraicGeometry.Space.ProperFlatLift.chartIdealGeneratorHom`);
* a global section of the prescribed module of the problem of `x` along `D` on the model
  (`AlgebraicGeometry.Space.ProperFlatLift.chartConormalGeneratorModel`), and the section `1 ⊗ k`
  of `𝒪_X ⊗_A I` (`AlgebraicGeometry.Space.ProperFlatLift.chartTensorGenerator`).

All of them are morphisms out of the free module of rank one, typed by the fields of the problems
themselves.

## Main results

In the namespace `AlgebraicGeometry.Space.ProperFlatLift`:

* `chartModelIdealGenerator_comp_c`: the prescribed map of the problem on the model carries `σ_k`
  to the pulled-back conormal class of `k`.
* `chartIdealGeneratorHom_comp_c_eq_comp_chartModelProblemGIso`: the prescribed map of
  `problemOnChart x hx D` on `σ_k`.

## Implementation notes

The definitions read the problem and its arguments off the bodies of `chartModelProblem` and
`problemOnChart` (`unfold_arg%`, `arg_of%`, `pull_app%` of
`StacksFrontier.Tactic.DefinitionArguments`) instead of elaborating them again: a second elaboration
has its own abstracted proofs, and the kernel would compare the two copies of the problem field by
field. The two equations are stated through named propositions (`ChartModelIdealGeneratorCompC`,
`ChartIdealGeneratorHomCompProblemOnChartC`), elaborated once inside a definition.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.SheafOfModules.ChangeOfRings (unitToRestrictScalarsUnit)
open Stacks.Cohomology.SiteModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

open Deformation.ToposThickening

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The cast `g^*𝒞 = g'^*𝒞` along `g = g'`, restricted to the model, carries the restriction of the
pulled-back section `g^*t` to that of `g'^*t`. -/
theorem moduleResUnitHom_modulePullbackGlobalSection_comp_eqToHom {Y' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS Y'.1} {X : AlgebraicSpaces B S hS}
    {g g' : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)} (h : g = g')
    (t : SheafOfModules.unit (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ :
      AlgebraicSpaces B S hS)) ⟶ conormalModule B S hS Y' Z) :
    moduleResUnitHom (X := smallEtaleRingedTopos B S hS X) (T := (smallEtaleRingedTopos B S hS X).O)
        (smallEtaleModelTopology B S hS X.1)
        (smallEtaleModelEquiv B S hS X) (modulePullbackGlobalSection B S hS g t) ≫
      eqToHom (congrArg (fun g => (Deformation.AlgebraExtension.moduleRes
        (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse
        (smallEtaleRingedTopos B S hS X).O).obj
          (FlatThickeningDeformation.pulledBackConormal (Z := Z) g)) h) =
      moduleResUnitHom (X := smallEtaleRingedTopos B S hS X)
        (T := (smallEtaleRingedTopos B S hS X).O) (smallEtaleModelTopology B S hS X.1)
        (smallEtaleModelEquiv B S hS X) (modulePullbackGlobalSection B S hS g' t) := by
  subst h
  exact Category.comp_id _

namespace ProperFlatLift

open Deformation.Artin

variable {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  {A' : Type u} [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A')

/-- **The pulled-back conormal class of `k`**, as a global section of the prescribed module of the
problem of `x` along `D`, on the model. -/
def chartConormalGeneratorModel (k : D.kernel) :
    SheafOfModules.unit ((sheafCompose (modelTopos x.obj.obj.left).J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (modelTopos x.obj.obj.left).O) ⟶
      (chartModelProblem x hx D).G :=
  (pull_app% (chartModelProblem x hx D) moduleResUnitHom)
    (FlatThickeningDeformation.problemConormalGenerator
      (Z := arg_of% (unfold_arg% (chartModelProblem x hx D) S) Z)
      (arg_of% (unfold_arg% (chartModelProblem x hx D) S) hZ)
      (arg_of% (unfold_arg% (chartModelProblem x hx D) S) f) (chartConormalClass D k))

/-- **The section `1 ⊗ k` of `𝒪_X ⊗_A I`** on the model, as a morphism out of the free module of
rank one. -/
abbrev chartTensorGenerator (k : D.kernel) :
    SheafOfModules.unit ((sheafCompose (modelTopos x.obj.obj.left).J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (modelTopos x.obj.obj.left).O) ⟶
      (modelTensorFunctor (chartBaseRingHom x hx)).obj D.kernel :=
  (SheafOfModules.unitHomEquiv _).symm
    ((baseRingTensorUnit.{u, u, u, u} (chartBaseRingHom x hx) D.kernel).hom k)

/-- The generator `σ_k` of the ideal of the problem of `x` along `D`, on the model. -/
def chartModelIdealGenerator (k : D.kernel) :
    SheafOfModules.unit ((sheafCompose (modelTopos x.obj.obj.left).J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor (chartModelProblem x hx D).f.toToposHom).obj
          (smallEtaleRingedTopos B S hS
            (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
              (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ :
                AlgebraicSpaces B S hS)).O)) ⟶
      (chartModelProblem x hx D).I :=
  (pull_app% (chartModelProblem x hx D) RingedToposExtensionProblem.siteTransportIdealGenerator)
    (FlatThickeningDeformation.problemIdealGenerator
      (Z := arg_of% (unfold_arg% (chartModelProblem x hx D) S) Z)
      (arg_of% (unfold_arg% (chartModelProblem x hx D) S) hZ)
      (arg_of% (unfold_arg% (chartModelProblem x hx D) S) f) (chartConormalClass D k))

/-- **The generator `σ_k` of the ideal of `problemOnChart x hx D`**, as a global section: the
pulled-back conormal class of `k` (`AlgebraicGeometry.Space.ProperFlatLift.chartIdealGenerator`),
restricted to the model of the small étale site of `X` and read over `f⁻¹𝒪_{Spec A}`. -/
def chartIdealGeneratorHom (k : D.kernel) :
    SheafOfModules.unit ((sheafCompose (modelTopos x.obj.obj.left).J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor (problemOnChart x hx D).f.toToposHom).obj
          (smallEtaleRingedTopos B S hS (schemeSpace (algebraOver A B S hS toS hA))).O)) ⟶
      (problemOnChart x hx D).I :=
  (pull_app% (problemOnChart x hx D) RingedToposExtensionProblem.rebaseIdealGenerator)
    (chartModelIdealGenerator x hx D k)

/-- The proposition that the prescribed map of the problem of `x` along `D` on the model carries
`σ_k` to the pulled-back conormal class of `k`. -/
def ChartModelIdealGeneratorCompC (k : D.kernel) : Prop :=
    chartModelIdealGenerator x hx D k ≫ (chartModelProblem x hx D).c =
      unitToRestrictScalarsUnit ((sheafCompose (modelTopos x.obj.obj.left).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map
            (chartModelProblem x hx D).f.fSharpInverseImage) ≫
        (SheafOfModules.restrictScalars ((sheafCompose (modelTopos x.obj.obj.left).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map
            (chartModelProblem x hx D).f.fSharpInverseImage)).map
          (chartConormalGeneratorModel x hx D k)

/-- The prescribed map of the problem of `x` along `D` on the model carries `σ_k` to the
pulled-back conormal class of `k`. -/
theorem chartModelIdealGenerator_comp_c (k : D.kernel) :
    ChartModelIdealGeneratorCompC x hx D k := by
  have h := FlatThickeningDeformation.problemIdealGenerator_comp_c
    (Z := arg_of% (unfold_arg% (chartModelProblem x hx D) S) Z)
    (arg_of% (unfold_arg% (chartModelProblem x hx D) S) hZ)
    (arg_of% (unfold_arg% (chartModelProblem x hx D) S) f) (chartConormalClass D k)
  exact (pull_app% (chartModelProblem x hx D)
    RingedToposExtensionProblem.siteTransportIdealGenerator_comp_c) _ _ h

/-- The proposition that the prescribed map of `problemOnChart x hx D` carries `σ_k` to the
pulled-back conormal class of `k` followed by `f^*𝒞 ≅ 𝒪_X ⊗_A I`. -/
def ChartIdealGeneratorHomCompProblemOnChartC (k : D.kernel) : Prop :=
    chartIdealGeneratorHom x hx D k ≫ (problemOnChart x hx D).c =
      unitToRestrictScalarsUnit ((sheafCompose (modelTopos x.obj.obj.left).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map
            (problemOnChart x hx D).f.fSharpInverseImage) ≫
        (SheafOfModules.restrictScalars ((sheafCompose (modelTopos x.obj.obj.left).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map
            (problemOnChart x hx D).f.fSharpInverseImage)).map
          (chartConormalGeneratorModel x hx D k ≫ (chartModelProblemGIso x hx D).hom)

/-- The prescribed map of `problemOnChart x hx D` carries the generator `σ_k` to the pulled-back
conormal class of `k` on the model, followed by `f^*𝒞 ≅ 𝒪_X ⊗_A I`. -/
theorem chartIdealGeneratorHom_comp_c_eq_comp_chartModelProblemGIso
    (k : D.kernel) :
    ChartIdealGeneratorHomCompProblemOnChartC x hx D k :=
  (pull_app% (problemOnChart x hx D)
      RingedToposExtensionProblem.rebaseIdealGenerator_comp_rebase_c)
    (chartModelIdealGenerator x hx D k) (chartConormalGeneratorModel x hx D k)
    (chartModelIdealGenerator_comp_c x hx D k)

end ProperFlatLift

end AlgebraicGeometry.Space
