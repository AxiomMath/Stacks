module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived

/-!
# The tensor-Hom comparison map for sheaf Hom with exact support

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that `i_*` is exact and
`R ℰom(𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_Z)` is its right adjoint on unbounded derived categories
([Stacks, Tag 0A76]). For two objects `K` and `M` of `D(𝒪_X)` there is a canonical map

`R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M ⟶ R ℰom(𝒪_Z, K ⊗^L_{𝒪_X} M)`

in `D(𝒪_Z)`, described by an adjunction: it is the map corresponding, under
`i_* ⊣ R ℰom(𝒪_Z, -)`, to the composite

`i_*(R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M) = i_* R ℰom(𝒪_Z, K) ⊗^L_{𝒪_X} M ⟶ K ⊗^L_{𝒪_X} M`,

whose first step is the inverse of the projection-formula map, an isomorphism for a closed
embedding, and whose second is the counit of `i_* ⊣ R ℰom(𝒪_Z, -)` at `K` tensored with the
identity of `M`. [Stacks, Tag 0E2N] asserts that this map is an isomorphism when `i` is a
pseudo-coherent closed immersion of schemes, `M` locally has Tor amplitude in `[a, ∞)` and `K`
lies in `D⁺_QCoh(𝒪_X)`.

## Main definitions

* `Stacks.Duality.TensorHomTorAmplitude.derivedSheafHomTensorPullback`: the functor
  `M ↦ R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M`, the source of the map.
* `Stacks.Duality.TensorHomTorAmplitude.derivedSheafHomTensor`: the functor
  `M ↦ R ℰom(𝒪_Z, K ⊗^L_{𝒪_X} M)`, the target of the map.
* `Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMateMap`: the displayed composite.
* `Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap`: the canonical map, adjoint to
  the displayed composite.

## Main results

* `Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap_mate`: the adjunction equation
  characterizing the canonical map.
* `Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap_unique`: a morphism satisfying
  that equation is the canonical map.

## References

* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

/-- The comparison isomorphism between the two models of derived pushforward along `i`: the
functor induced on derived categories by the exact functor `i_*`, and the total right derived
functor `Ri_*`. -/
abbrev derivedPushforwardComparison (S : ClosedQuotientMorphismOfRingedSpaces.{u}) :
    (modulePushforward S.i).mapDerivedCategory ≅ derivedPushforward S.i :=
  Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived (modulePushforward S.i)

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

namespace Stacks.Duality.TensorHomTorAmplitude

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-! ### The source and the target of the comparison map -/

/-- The source of the tensor-Hom comparison map, as a functor `D(𝒪_X) ⥤ D(𝒪_Z)`:

`M ↦ R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M`. -/
abbrev derivedSheafHomTensorPullback
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)) :=
  derivedPullback S.i ⋙
    (derivedTensorProductFunctor S.Z.sheaf).obj (S.derivedSheafHomExactSupport.obj K)

/-- The target of the tensor-Hom comparison map, as a functor `D(𝒪_X) ⥤ D(𝒪_Z)`:

`M ↦ R ℰom(𝒪_Z, K ⊗^L_{𝒪_X} M)`. -/
abbrev derivedSheafHomTensor
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)) :=
  (derivedTensorProductFunctor S.X.sheaf).obj K ⋙ S.derivedSheafHomExactSupport

/-! ### Invertibility of the projection-formula map -/

/-- For all `K` and `M` in `D(𝒪_X)` the projection-formula map

`Ri_*(R ℰom(𝒪_Z, K)) ⊗^L_{𝒪_X} M ⟶ Ri_*(R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M)`

is an isomorphism. -/
theorem isIso_projectionFormulaMap_derivedSheafHomExactSupport
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    IsIso (projectionFormulaMap S.i (S.derivedSheafHomExactSupport.obj K) M) :=
  Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding
    S.i S.isClosedEmbedding (S.derivedSheafHomExactSupport.obj K) M

/-! ### The displayed composite and the canonical map -/

/-- The composite

`i_*(R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M) = i_* R ℰom(𝒪_Z, K) ⊗^L_{𝒪_X} M ⟶ K ⊗^L_{𝒪_X} M`

that the tensor-Hom comparison map is adjoint to: the comparison to `Ri_*`, the inverse of the
projection-formula map, the comparison back, and the counit of `i_* ⊣ R ℰom(𝒪_Z, -)` at `K`
tensored with the identity of `M`. -/
def tensorDerivedSheafHomMateMap
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (modulePushforward S.i).mapDerivedCategory.obj
        ((derivedSheafHomTensorPullback S K).obj M) ⟶
      ((derivedTensorProductFunctor S.X.sheaf).obj K).obj M :=
  S.derivedPushforwardComparison.hom.app _ ≫
    CategoryTheory.inv (I := isIso_projectionFormulaMap_derivedSheafHomExactSupport S K M)
      (projectionFormulaMap S.i (S.derivedSheafHomExactSupport.obj K) M) ≫
    ((derivedTensorProductFunctor S.X.sheaf).map
      (S.derivedPushforwardComparison.inv.app (S.derivedSheafHomExactSupport.obj K))).app M ≫
    ((derivedTensorProductFunctor S.X.sheaf).map
      (S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app K)).app M

/-- The canonical map

`R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M ⟶ R ℰom(𝒪_Z, K ⊗^L_{𝒪_X} M)`

in `D(𝒪_Z)`: the map corresponding to `tensorDerivedSheafHomMateMap` under the adjunction
`i_* ⊣ R ℰom(𝒪_Z, -)`. -/
def tensorDerivedSheafHomMap
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (derivedSheafHomTensorPullback S K).obj M ⟶ (derivedSheafHomTensor S K).obj M :=
  (S.derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv _ _)
    (tensorDerivedSheafHomMateMap S K M)

/-- The adjunction equation characterizing the canonical map: pushing it forward and composing
with the counit of `i_* ⊣ R ℰom(𝒪_Z, -)` gives `tensorDerivedSheafHomMateMap`. -/
theorem tensorDerivedSheafHomMap_mate
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (modulePushforward S.i).mapDerivedCategory.map (tensorDerivedSheafHomMap S K M) ≫
        S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
          (((derivedTensorProductFunctor S.X.sheaf).obj K).obj M) =
      tensorDerivedSheafHomMateMap S K M :=
  (Adjunction.homEquiv_counit _ _ _ _).symm.trans
    ((S.derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv _ _).symm_apply_apply _)

/-- The adjunction equation determines the canonical map: a morphism satisfying the equation of
`tensorDerivedSheafHomMap_mate` is `tensorDerivedSheafHomMap`. -/
theorem tensorDerivedSheafHomMap_unique
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))
    (τ : (derivedSheafHomTensorPullback S K).obj M ⟶ (derivedSheafHomTensor S K).obj M)
    (hτ : (modulePushforward S.i).mapDerivedCategory.map τ ≫
        S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
          (((derivedTensorProductFunctor S.X.sheaf).obj K).obj M) =
      tensorDerivedSheafHomMateMap S K M) :
    τ = tensorDerivedSheafHomMap S K M :=
  Equiv.symm_apply_eq _ |>.mp ((Adjunction.homEquiv_counit _ _ _ _).trans hτ)

end Stacks.Duality.TensorHomTorAmplitude

end
