module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapForExt
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct
import StacksCore.Tactic.StacksAttribute

/-!
# The derived pushforward of a derived internal hom

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `K, L ∈ D(𝒪_X)`.  There is
a canonical map

`Rf_*R𝓗om_{𝒪_X}(L, K) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, Rf_*K)`

in `D(𝒪_Y)`, Stacks 0B69.  It is built the way the source builds it: by the
tensor–internal-hom bijection of Stacks 08DI the map is the same datum as a map

`Rf_*R𝓗om(L, K) ⊗^L_{𝒪_Y} Rf_*L ⟶ Rf_*K`,

and that datum is the relative cup product of Stacks 0B68 followed by `Rf_*` of the evaluation
`R𝓗om(L, K) ⊗^L_{𝒪_X} L ⟶ K` of Stacks 0A8V.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPushforward.pushforwardSheafHomDatum`: the map
  `Rf_*R𝓗om(L, K) ⊗^L_{𝒪_Y} Rf_*L ⟶ Rf_*K`, the relative cup product followed by the
  pushforward of the evaluation.
* `Stacks.Cohomology.DerivedInternalHomPushforward.pushforwardSheafHomMap`: **Stacks 0B69**,
  the canonical map `Rf_*R𝓗om(L, K) ⟶ R𝓗om(Rf_*L, Rf_*K)`.

## Implementation notes

*Two derived tensor products meet here.*  The relative cup product of Stacks 0B68 is stated
over `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, while the derived internal
hom and its bijection of Stacks 08DI are stated over
`Stacks.SheafOfModules.derivedTensorProductFunctor` of the associated ringed site.  Both are
derived tensor products in the sense of Stacks 06YU, and
`Stacks.Cohomology.DerivedKunnethExt.tensorBridge` is the comparison of the two; it appears at
the single point where the bijection of Stacks 08DI is applied, exactly as it does in the
pullback map of Stacks 08I3 in the same spelling.

*The evaluation is not rebuilt here.*  `Stacks.Cohomology.DerivedKunnethExt.sheafHomEval` is
the transpose of the identity of `R𝓗om(L, K)` under the bijection of Stacks 08DI, which is the
evaluation morphism of Stacks 0A8V with `𝒪_X` in one of its spots.

*No hypothesis beyond the source's.*  The construction is for arbitrary `K, L ∈ D(𝒪_X)` and an
arbitrary morphism of ringed spaces; the sheafification binders are the ones the derived tensor
product of Stacks 06YU is stated under, and both are inhabited for every ringed space.

*The transpose equation is not stated.*  By construction the bijection of Stacks 08DI carries
`pushforwardSheafHomMap` to `pushforwardSheafHomDatum`, so that equation holds by
`Equiv.apply_symm_apply`; but writing it down names the bijection applied to
`pushforwardSheafHomMap`, and type-checking that application exhausts the recursion budget,
also when the bijection is written as a bare `Equiv` rather than an additive one.
The budget is not raised.  The same obstruction arises for the transpose equation
of the pullback comparison of Stacks 08I3.

## References

* [Stacks Project, Tag 0B69](https://stacks.math.columbia.edu/tag/0B69)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.SheafOfModules.DerivedMonoidal
open Stacks.Cohomology.DerivedKunnethExt

namespace Stacks.Cohomology.DerivedInternalHomPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

-- The relative cup product names the structure sheaf of a ringed space by
-- `structureSheafRing` and the derived internal hom by
-- `Stacks.SheafOfModules.Tensor.ringSheaf`.  The two are the same sheaf of rings by `rfl`, and
-- every statement below mixes them, since the relative cup product is named at the first
-- spelling and the derived internal hom at the second.
attribute [local implicit_reducible] structureSheafRing
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The transpose datum of Stacks 0B69**
`Rf_*R𝓗om_{𝒪_X}(L, K) ⊗^L_{𝒪_Y} Rf_*L ⟶ Rf_*K`: the relative cup product of Stacks 0B68 at the
pair `(R𝓗om(L, K), L)`, followed by the derived pushforward of the evaluation
`R𝓗om(L, K) ⊗^L_{𝒪_X} L ⟶ K`. -/
def pushforwardSheafHomDatum (K L : DerivedCategory (Mod X.sheaf)) :
    tensorObj Y ((derivedPushforward f).obj (sheafHomObj X L K))
        ((derivedPushforward f).obj L) ⟶
      (derivedPushforward f).obj K :=
  Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f (sheafHomObj X L K) L ≫
    (derivedPushforward f).map (sheafHomEval X L K)

/-- **Stacks 0B69: the canonical map `Rf_*R𝓗om_{𝒪_X}(L, K) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, Rf_*K)`** for a
morphism of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and objects `K, L` of `D(𝒪_X)`.

By the tensor–internal-hom bijection of Stacks 08DI it is the same datum as a map
`Rf_*R𝓗om(L, K) ⊗^L_{𝒪_Y} Rf_*L ⟶ Rf_*K`, and that datum is the relative cup product of
Stacks 0B68 followed by the derived pushforward of the evaluation map. -/
@[stacks 0B69]
def pushforwardSheafHomMap (K L : DerivedCategory (Mod X.sheaf)) :
    (derivedPushforward f).obj (sheafHomObj X L K) ⟶
      sheafHomObj Y ((derivedPushforward f).obj L) ((derivedPushforward f).obj K) :=
  (Stacks.SheafOfModules.derivedSheafHomTensorEquiv Y.sheaf
      ((derivedPushforward f).obj (sheafHomObj X L K))
      ((derivedPushforward f).obj L) ((derivedPushforward f).obj K)).symm
    (((tensorBridge Y).hom.app ((derivedPushforward f).obj (sheafHomObj X L K))).app
        ((derivedPushforward f).obj L) ≫
      pushforwardSheafHomDatum f K L)

end Stacks.Cohomology.DerivedInternalHomPushforward

end
