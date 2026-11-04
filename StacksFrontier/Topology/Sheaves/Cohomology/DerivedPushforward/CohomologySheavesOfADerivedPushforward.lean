module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology sheaves of an unbounded derived pushforward

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `K` be an object of the
unbounded derived category `D(𝒪_X)`. Then the `i`-th cohomology sheaf of `Rf_* K` is the sheaf
associated to the presheaf

`V ↦ H^i(f⁻¹ V, K) = H^i(V, Rf_* K)`.

The presheaf is `derivedPreimageCohomologyPresheaf`, the degree-`i` cohomology of the derived
sections of `Rf_* K` over all opens of `Y`, with its restriction maps. All three statements below
are natural isomorphisms of functors on `D(𝒪_X)`.

## Main definitions

* `Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageCohomologyPresheaf`: the presheaf
  `V ↦ H^i(f⁻¹ V, K)` on `Y`, with its restriction maps.

## Main results

* `Stacks.Cohomology.UnboundedHigherDirectImage.preimageCohomologyIso`: the displayed equality
  `H^i(f⁻¹ V, K) = H^i(V, Rf_* K)`, as a natural isomorphism in `K`.
* `Stacks.Cohomology.UnboundedHigherDirectImage.preimageCohomologyEvaluationIso`: the value of
  `derivedPreimageCohomologyPresheaf` on an open `V` is `H^i(f⁻¹ V, K)`.
* `Stacks.Cohomology.UnboundedHigherDirectImage.higherDirectImageIsoSheafifyPreimageCohomology`:
  the `i`-th cohomology sheaf of `Rf_* K` is the sheafification of that presheaf.

## References

* [Stacks Project, Tag 0D5X](https://stacks.math.columbia.edu/tag/0D5X)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedSectionsOverOpen derivedPreimageSections derivedSectionsPushforwardIso)

namespace Stacks.Cohomology.UnboundedHigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Sheaves of modules on a ringed space form a Grothendieck abelian category, in the module
universe of the space. -/
@[ega "0 12.4.1" "more general"]
local instance isGrothendieckAbelian_moduleSheaves (Y : RingedSpace.{u, u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing Y)) :=
  SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing Y)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The presheaf `V ↦ H^i(f⁻¹ V, K)` on `Y`, together with its restriction maps: the degree-`i`
cohomology presheaf of `Rf_* K`. -/
abbrev derivedPreimageCohomologyPresheaf
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ) :
    PresheafOfModules.{u} (structureSheafRing Y).obj :=
  (DerivedCategory.homologyFunctor (PresheafOfModules.{u} (structureSheafRing Y).obj) i).obj
    ((Stacks.Cohomology.HypercohomologyEdge.derivedSectionsPresheaf (structureSheafRing Y)).obj
      ((derivedPushforward f).obj K))

/-- Cohomology over the inverse image `f⁻¹ V` agrees with cohomology over `V` after derived
pushforward: `H^i(f⁻¹ V, K) = H^i(V, Rf_* K)`, naturally in `K`. -/
@[stacks 0D5X "preimage formula"]
def preimageCohomologyIso (V : Opens Y.carrier) (i : ℤ) :
    derivedPreimageSections f V ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i ≅
      derivedPushforward f ⋙ derivedSectionsOverOpen Y V ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i :=
  Functor.isoWhiskerRight (derivedSectionsPushforwardIso f V).symm
    (DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i)

/-- The value on an open `V ⊆ Y` of the presheaf `derivedPreimageCohomologyPresheaf` is the
hypercohomology `H^i(f⁻¹ V, K)` of `K` over the inverse image of `V`, naturally in `K`. -/
@[stacks 0D5X "values on opens"]
def preimageCohomologyEvaluationIso (V : Opens Y.carrier) (i : ℤ) :
    derivedPushforward f ⋙
        Stacks.Cohomology.HypercohomologyEdge.derivedSectionsPresheaf (structureSheafRing Y) ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u} (structureSheafRing Y).obj) i ⋙
        PresheafOfModules.evaluation (structureSheafRing Y).obj (op V) ≅
      derivedPreimageSections f V ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i :=
  Functor.isoWhiskerLeft (derivedPushforward f)
      (Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso (structureSheafRing Y) V i) ≪≫
    Functor.isoWhiskerRight (derivedSectionsPushforwardIso f V)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i)

/-- The `i`-th cohomology sheaf of `Rf_* K` is the sheaf associated to the presheaf
`V ↦ H^i(f⁻¹ V, K)`, naturally in `K`. -/
@[stacks 0D5X "associated sheaf"]
def higherDirectImageIsoSheafifyPreimageCohomology (i : ℤ) :
    derivedPushforward f ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) i ≅
      derivedPushforward f ⋙
        Stacks.Cohomology.HypercohomologyEdge.derivedSectionsPresheaf (structureSheafRing Y) ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u} (structureSheafRing Y).obj) i ⋙
        PresheafOfModules.sheafification (𝟙 (structureSheafRing Y).obj) :=
  (Functor.isoWhiskerLeft (derivedPushforward f)
    (Stacks.Cohomology.HypercohomologyEdge.sheafificationCohomologyPresheafIso
      (structureSheafRing Y) i)).symm

end Stacks.Cohomology.UnboundedHigherDirectImage

end
