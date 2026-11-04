module

public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedHomPushforward
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.TensorHomTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived

/-!
# The canonical map `Li^*K ⊗^L R ℰom(𝒪_Z, 𝒪_X) ⟶ R ℰom(𝒪_Z, K)`

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that `i_*` is exact and
`R ℰom(𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_Z)` is its right adjoint on unbounded derived categories
([Stacks, Tag 0A76]). For an effective Cartier divisor `D ⊂ X` with inclusion `i : D ⟶ X` this
is the setting of [Stacks, Tag 0B4C], where `R ℰom(𝒪_Z, -)` is written `R𝓗om(𝒪_D, -)`, and the
labelled display of that tag is a **map**, not an equality: for every `K` in `D(𝒪_X)` there is a
canonical

`Li^*K ⊗^L_{𝒪_Z} R ℰom(𝒪_Z, 𝒪_X) ⟶ R ℰom(𝒪_Z, K)`

in `D(𝒪_Z)`. The source describes it by an adjunction: it is the map corresponding, under
`i_* ⊣ R ℰom(𝒪_Z, -)`, to the composite

`i_*(Li^*K ⊗^L_{𝒪_Z} R ℰom(𝒪_Z, 𝒪_X)) = K ⊗^L_{𝒪_X} R ℰom_{𝒪_X}(i_*𝒪_Z, 𝒪_X) ⟶ K`,

whose first step is the projection formula of [Stacks, Tag 0B53] — invertible here by
[Stacks, Tag 0B55] — and whose second step is induced by `𝒪_X ⟶ i_*𝒪_Z`. That second step is
the counit of the adjunction of [Stacks, Tag 0A76] at `𝒪_X`, by the identification
`i_* R ℰom(𝒪_Z, -) ≅ R ℰom_{𝒪_X}(i_*𝒪_Z, -)` of [Stacks, Tag 0A77].

All names below live in the namespace
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

## Main definitions

* `derivedSheafHomStructureSheaf` is `R ℰom(𝒪_Z, 𝒪_X)`, the value of the right adjoint of
  [Stacks, Tag 0A76] on the structure sheaf in degree zero.
* `derivedPullbackTensorSheafHom` is the source of the map, as a functor
  `K ↦ Li^*K ⊗^L_{𝒪_Z} R ℰom(𝒪_Z, 𝒪_X)`, with the tensor factors in the order of the source's
  display.
* `derivedPullbackTensorSheafHomMateMap` is the displayed composite the map is adjoint to.
* `derivedPullbackTensorSheafHomMap` is the canonical map itself.

## Main results

* `derivedPullbackTensorSheafHomMap_mate` is the adjunction equation that characterizes the
  canonical map, and `derivedPullbackTensorSheafHomMap_unique` says that the equation determines
  it.
* `isIso_projectionFormulaMap_derivedSheafHomStructureSheaf` is [Stacks, Tag 0B55] at the one
  projection-formula map the construction needs.

## Implementation notes

**Scope.** The tag asserts that the displayed map exists, is canonical, is functorial in `K` and
is compatible with distinguished triangles. The declarations below give the map together with
the adjunction equation that pins it down and its uniqueness subject to that equation;
functoriality in `K` and compatibility with distinguished triangles are not formalized here.

**[Stacks, Tag 0B55].** The construction needs the projection-formula map of
[Stacks, Tag 0B53] at `R ℰom(𝒪_Z, 𝒪_X)` and `K` to be invertible. That is [Stacks, Tag 0B55],
whose hypothesis — that the morphism be a homeomorphism onto a closed subset — is
`ClosedQuotientMorphismOfRingedSpaces.isClosedEmbedding`; it is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding`, and
`isIso_projectionFormulaMap_derivedSheafHomStructureSheaf` records the instance the construction
needs. Invertibility is a `Prop`, so the construction chooses no data from it: the inverse of an
invertible morphism is its unique two-sided inverse, and `CategoryTheory.inv` names that morphism.

**The two models of pushforward.** The projection formula of [Stacks, Tag 0B53] is stated for
`Rf_*`, the total right derived functor, while the adjunction of [Stacks, Tag 0A76] uses the
functor induced on derived categories by the exact functor `i_*`. The two are identified by
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`, which is [Stacks, Tag 0E2K];
the composite below passes through it in both directions, once to reach the projection formula
and once to come back to the counit.

**The order of the tensor factors.** The source is written `Li^*K ⊗^L R ℰom(𝒪_Z, 𝒪_X)`, which
is the order of the source's display, with the pullback first. The projection formula puts the
pulled-back factor second, so the commutativity constraint of [Stacks, Tag 0FPT] is applied
once on `D(𝒪_Z)`; the final cancellation of the structure sheaf is then the unit constraint on
the left.

## References

* [Stacks Project, Tag 0B4C](https://stacks.math.columbia.edu/tag/0B4C)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
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

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-! ### The objects and functors of the display -/

/-- The structure sheaf `𝒪_X` of the ambient ringed space, as an object of `D(𝒪_X)` in degree
zero. It is the unit of the derived tensor product of [Stacks, Tag 06YU]. -/
abbrev ambientStructureSheafObject : DerivedModules S.ambientSite.O :=
  unitObject S.ambientSite

/-- `R ℰom(𝒪_Z, 𝒪_X)`, the value on the structure sheaf of the right adjoint of
[Stacks, Tag 0A76]. This is the object the source of [Stacks, Tag 0B4C] writes
`R𝓗om(𝒪_D, 𝒪_X)`; for an effective Cartier divisor it is the shifted normal sheaf `𝒩[-1]`, by
[Stacks, Tag 0B4B]. -/
abbrev derivedSheafHomStructureSheaf :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)) :=
  S.derivedSheafHomExactSupport.obj S.ambientStructureSheafObject

/-- The derived adjunction `Ri_* ⊣ R ℰom(𝒪_Z, -)` of [Stacks, Tag 0A76]. -/
abbrev derivedSheafHomAdjunction :
    (modulePushforward S.i).mapDerivedCategory ⊣ S.derivedSheafHomExactSupport :=
  S.derivedModulePushforwardSheafHomExactSupportAdjunction

/-- The source of the map of [Stacks, Tag 0B4C], as a functor `D(𝒪_X) ⥤ D(𝒪_Z)`:

`K ↦ Li^*K ⊗^L_{𝒪_Z} R ℰom(𝒪_Z, 𝒪_X)`,

with the tensor factors in the order of the source's display. The derived pullback is the one of
[Stacks, Tag 06YJ] and the derived tensor product is the one of [Stacks, Tag 06YU]; the flip
places the pullback in the first tensor slot. -/
abbrev derivedPullbackTensorSheafHom :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)) :=
  derivedPullback S.i ⋙
    (derivedTensorProductFunctor S.Z.sheaf).flip.obj S.derivedSheafHomStructureSheaf

/-! ### [Stacks, Tag 0B55] at the projection-formula map the construction needs -/

/-- **[Stacks, Tag 0B55] at `R ℰom(𝒪_Z, 𝒪_X)` and `K`.** The projection-formula map of
[Stacks, Tag 0B53]

`Ri_*(R ℰom(𝒪_Z, 𝒪_X)) ⊗^L_{𝒪_X} K ⟶ Ri_*(R ℰom(𝒪_Z, 𝒪_X) ⊗^L_{𝒪_Z} Li^*K)`

is an isomorphism, for every `K` in `D(𝒪_X)`. This is the equality of the display of
[Stacks, Tag 0B4C], read as the invertibility of a canonical map; it is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding` at
the closed embedding `ClosedQuotientMorphismOfRingedSpaces.isClosedEmbedding`. -/
theorem isIso_projectionFormulaMap_derivedSheafHomStructureSheaf
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    IsIso (projectionFormulaMap S.i S.derivedSheafHomStructureSheaf K) :=
  Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding
    S.i S.isClosedEmbedding S.derivedSheafHomStructureSheaf K

/-! ### The displayed composite and the canonical map -/

/-- The composite

`i_*(Li^*K ⊗^L_{𝒪_Z} R ℰom(𝒪_Z, 𝒪_X)) = K ⊗^L_{𝒪_X} R ℰom_{𝒪_X}(i_*𝒪_Z, 𝒪_X) ⟶ K`

that the map of [Stacks, Tag 0B4C] is adjoint to.  The equality of the display is the
invertibility of the projection-formula map of [Stacks, Tag 0B53], which is [Stacks, Tag 0B55]
and is supplied by `isIso_projectionFormulaMap_derivedSheafHomStructureSheaf`.

Reading the factors in order: the commutativity constraint of [Stacks, Tag 0FPT] moves the
pullback into the second tensor slot; `derivedPushforwardComparison` passes to the total right
derived pushforward; the inverse of the projection-formula map of [Stacks, Tag 0B53] is the
equality of the display; `derivedPushforwardComparison` comes back; the counit of
[Stacks, Tag 0A76] at `𝒪_X` is the arrow `R ℰom_{𝒪_X}(i_*𝒪_Z, 𝒪_X) ⟶ 𝒪_X` induced by
`𝒪_X ⟶ i_*𝒪_Z`, by [Stacks, Tag 0A77]; and the unit constraint of [Stacks, Tag 0FPT] cancels
the structure sheaf. -/
def derivedPullbackTensorSheafHomMateMap
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (modulePushforward S.i).mapDerivedCategory.obj
        (S.derivedPullbackTensorSheafHom.obj K) ⟶ K :=
  (modulePushforward S.i).mapDerivedCategory.map
      ((canonicalDerivedTensorProduct S.Z.sheaf).braidingIso S.closedSite
        ((derivedPullback S.i).obj K) S.derivedSheafHomStructureSheaf).hom ≫
    S.derivedPushforwardComparison.hom.app _ ≫
    CategoryTheory.inv (I := S.isIso_projectionFormulaMap_derivedSheafHomStructureSheaf K)
      (projectionFormulaMap S.i S.derivedSheafHomStructureSheaf K) ≫
    ((derivedTensorProductFunctor S.X.sheaf).map
      (S.derivedPushforwardComparison.inv.app S.derivedSheafHomStructureSheaf)).app K ≫
    ((derivedTensorProductFunctor S.X.sheaf).map
      (S.derivedSheafHomAdjunction.counit.app S.ambientStructureSheafObject)).app K ≫
    ((canonicalDerivedTensorProduct S.X.sheaf).leftUnitIso S.ambientSite K).hom

/-- **Stacks Project, Tag 0B4C.** The canonical map

`Li^*K ⊗^L_{𝒪_Z} R ℰom(𝒪_Z, 𝒪_X) ⟶ R ℰom(𝒪_Z, K)`

in `D(𝒪_Z)`: the map corresponding to `derivedPullbackTensorSheafHomMateMap` under the
adjunction `i_* ⊣ R ℰom(𝒪_Z, -)` of [Stacks, Tag 0A76]. -/
@[stacks 0B4C "the canonical map, unconditionally; not functoriality in the complex and not \
  compatibility with distinguished triangles"]
def derivedPullbackTensorSheafHomMap
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    S.derivedPullbackTensorSheafHom.obj K ⟶ S.derivedSheafHomExactSupport.obj K :=
  (S.derivedSheafHomAdjunction.homEquiv _ _) (S.derivedPullbackTensorSheafHomMateMap K)

/-- **Stacks Project, Tag 0B4C.** The adjunction equation characterizing the canonical map:
pushing it forward and composing with the counit of [Stacks, Tag 0A76] gives the displayed
composite. This is what "adjoint to" means in the source. -/
@[stacks 0B4C "the adjunction equation characterizing the canonical map"]
theorem derivedPullbackTensorSheafHomMap_mate
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (modulePushforward S.i).mapDerivedCategory.map
          (S.derivedPullbackTensorSheafHomMap K) ≫
        S.derivedSheafHomAdjunction.counit.app K =
      S.derivedPullbackTensorSheafHomMateMap K :=
  (Adjunction.homEquiv_symm_apply S.derivedSheafHomAdjunction
        (S.derivedPullbackTensorSheafHom.obj K) K
        (S.derivedPullbackTensorSheafHomMap K)).symm.trans
    ((S.derivedSheafHomAdjunction.homEquiv _ K).symm_apply_apply _)

/-- **Stacks Project, Tag 0B4C.** The adjunction equation determines the canonical map: no
other morphism of that type satisfies it. Together with
`derivedPullbackTensorSheafHomMap_mate` this is the canonicality the source asserts. -/
@[stacks 0B4C "uniqueness of the canonical map subject to the adjunction equation"]
theorem derivedPullbackTensorSheafHomMap_unique
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))
    (τ : S.derivedPullbackTensorSheafHom.obj K ⟶ S.derivedSheafHomExactSupport.obj K)
    (hτ : (modulePushforward S.i).mapDerivedCategory.map τ ≫
        S.derivedSheafHomAdjunction.counit.app K =
      S.derivedPullbackTensorSheafHomMateMap K) :
    τ = S.derivedPullbackTensorSheafHomMap K :=
  Equiv.symm_apply_eq _ |>.mp
    ((Adjunction.homEquiv_symm_apply S.derivedSheafHomAdjunction
      (S.derivedPullbackTensorSheafHom.obj K) K τ).trans hτ)

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
