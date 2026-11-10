module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Spectral.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Connected.ComponentSpace
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocallyConstantFunctions
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.PullbackFiber
public import StacksFrontier.Topology.Profinite.Defs
public import StacksFrontier.Topology.Separation.FibreProduct
public import StacksFrontier.Topology.Spectral.ComponentSpace
public import StacksFrontier.Topology.Spectral.ConstructiblyClosed
public import StacksFrontier.Topology.Spectral.Products

/-!
# Profinite base change of the component map

Let `X` be a spectral space, let `T` be a profinite space and let `T → π₀(X)` be a continuous
map to the space of connected components of `X`. The fibre product `Y = X ×_{π₀(X)} T` is again
spectral, and the projection `Y → T` identifies `π₀(Y)` with `T`.

## Main definitions

* `AlgebraicGeometry.ProEtale.ProfiniteBaseChangeOfComponentMap`: the standing situation,
  packaging `X`, `T`, their hypotheses and the map `T → π₀(X)`.
* `AlgebraicGeometry.ProEtale.ProfiniteBaseChangeOfComponentMap.componentMap`: the canonical map
  `X → π₀(X)`.
* `AlgebraicGeometry.ProEtale.ProfiniteBaseChangeOfComponentMap.Y`: the fibre product
  `X ×_{π₀(X)} T`, with projections `toX` and `toT`.

## Main results

* `AlgebraicGeometry.ProEtale.spectralSpace_pullback`: the fibre product is spectral.
* `AlgebraicGeometry.ProEtale.isHomeomorph_connectedComponentsLift_toT`: the canonical map
  `π₀(Y) → T` induced by the projection is a homeomorphism.

## Implementation notes

Topological spaces and continuous maps are bundled in `TopCat`, and `Y` is Mathlib's chosen
categorical pullback, so its topology and both canonical projections come with the construction.
The profinite hypothesis on `T` supplies its compact, Hausdorff and totally disconnected space
instances.

## References

* [Stacks Project, Tag 096C](https://stacks.math.columbia.edu/tag/096C)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- A spectral space `X`, a profinite space `T`, and a continuous map `T → π₀(X)`. -/
structure ProfiniteBaseChangeOfComponentMap where
  /-- The spectral space. -/
  X : TopCat.{u}
  /-- The profinite space. -/
  T : TopCat.{u}
  /-- The spectral-space hypothesis on `X`. -/
  spectralSpace : SpectralSpace X
  /-- The profiniteness hypothesis on `T`. -/
  profinite : IsProfiniteStacks T
  /-- The given continuous map from `T` to the space of connected components of `X`. -/
  toConnectedComponents : T ⟶ TopCat.of (ConnectedComponents X)

namespace ProfiniteBaseChangeOfComponentMap

/-- The space `X` is a spectral space. -/
instance (S : ProfiniteBaseChangeOfComponentMap.{u}) : SpectralSpace S.X :=
  S.spectralSpace

/-- The profinite space `T` is compact. -/
instance (S : ProfiniteBaseChangeOfComponentMap.{u}) : CompactSpace S.T :=
  (compact_t2_totallyDisconnected_of_isProfiniteStacks _ S.profinite).1

/-- The profinite space `T` is Hausdorff. -/
instance (S : ProfiniteBaseChangeOfComponentMap.{u}) : T2Space S.T :=
  (compact_t2_totallyDisconnected_of_isProfiniteStacks _ S.profinite).2.1

/-- The profinite space `T` is totally disconnected. -/
instance (S : ProfiniteBaseChangeOfComponentMap.{u}) :
    TotallyDisconnectedSpace S.T :=
  (compact_t2_totallyDisconnected_of_isProfiniteStacks _ S.profinite).2.2

/-- The space `π₀(X)` of connected components, with its quotient topology. -/
abbrev componentSpace (S : ProfiniteBaseChangeOfComponentMap.{u}) : TopCat.{u} :=
  TopCat.of (ConnectedComponents S.X)

/-- The canonical continuous map `X → π₀(X)`. -/
def componentMap (S : ProfiniteBaseChangeOfComponentMap.{u}) :
    S.X ⟶ S.componentSpace :=
  TopCat.ofHom ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩

/-- The fibre product `Y = X ×_{π₀(X)} T` in the category of topological spaces. -/
noncomputable abbrev Y (S : ProfiniteBaseChangeOfComponentMap.{u}) : TopCat.{u} :=
  pullback S.componentMap S.toConnectedComponents

/-- The canonical projection `Y → X`. -/
noncomputable abbrev toX (S : ProfiniteBaseChangeOfComponentMap.{u}) : S.Y ⟶ S.X :=
  pullback.fst S.componentMap S.toConnectedComponents

/-- The canonical projection `Y → T`. -/
noncomputable abbrev toT (S : ProfiniteBaseChangeOfComponentMap.{u}) : S.Y ⟶ S.T :=
  pullback.snd S.componentMap S.toConnectedComponents

end ProfiniteBaseChangeOfComponentMap

/-- A profinite base change of the component map of a spectral space is spectral. -/
@[stacks 096C "pullback_spectral"]
instance spectralSpace_pullback (S : ProfiniteBaseChangeOfComponentMap) :
    SpectralSpace S.Y := by
  have hT : SpectralSpace S.T := by
    have hpre : PrespectralSpace S.T := PrespectralSpace.of_isTopologicalBasis
      isTopologicalBasis_isClopen (fun _ hU => hU.1.isCompact)
    exact SpectralSpace.mk
  have hpi : T2Space (ConnectedComponents S.X) :=
    (connectedComponents_isProfinite S.X).1
  let f : S.X → ConnectedComponents S.X := S.componentMap.hom
  let g : S.T → ConnectedComponents S.X := S.toConnectedComponents.hom
  have hprod : SpectralSpace (S.X × S.T) := prod_spectralSpace S.X S.T
  have hfib : SpectralSpace (fibreProduct f g) :=
    spectralSpace_of_isClosed_constructibleTopology _
      ((fibreProduct_isClosed S.componentMap.hom.continuous
        S.toConnectedComponents.hom.continuous).isClosed_constructibleTopology)
  let e : S.Y ≃ₜ fibreProduct f g :=
    TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype S.componentMap S.toConnectedComponents)
  have hcompact : CompactSpace S.Y := e.symm.compactSpace
  exact Topology.IsOpenEmbedding.spectralSpace (f := e) e.isOpenEmbedding

/-- The fibre of the projection `Y → T` over a point is connected. -/
private theorem projectionFiber_isConnected (S : ProfiniteBaseChangeOfComponentMap.{u})
    (t : S.T) : IsConnected {y : S.Y | S.toT y = t} := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (S.toConnectedComponents t)
  have hset : {x' : S.X | S.componentMap x' = S.toConnectedComponents t} =
      connectedComponent x := by
    ext x'
    change ((x' : ConnectedComponents S.X) = S.toConnectedComponents t) ↔
      x' ∈ connectedComponent x
    rw [← hx]
    exact ConnectedComponents.coe_eq_coe'
  have hX : IsConnected {x' : S.X | S.componentMap x' = S.toConnectedComponents t} := by
    simpa only [hset] using (isConnected_connectedComponent (x := x))
  exact isConnected_iff_connectedSpace.mpr
    ((fiber_pullback_snd_homeomorphic_fiber S.componentMap
      S.toConnectedComponents t).connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp hX))

/-- The canonical map `π₀(Y) → T` induced by the pullback projection is a
homeomorphism. -/
@[stacks 096C "pullback_components"]
theorem isHomeomorph_connectedComponentsLift_toT
    (S : ProfiniteBaseChangeOfComponentMap.{u}) :
    IsHomeomorph S.toT.hom.continuous.connectedComponentsLift := by
  have hcompact : CompactSpace (ConnectedComponents S.Y) :=
    (connectedComponents_isProfinite S.Y).2.1
  refine isHomeomorph_iff_continuous_bijective.mpr
    ⟨S.toT.hom.continuous.connectedComponentsLift_continuous, ?_, ?_⟩
  · intro a b hab
    obtain ⟨y₁, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y₂, rfl⟩ := ConnectedComponents.surjective_coe b
    apply (ConnectedComponents.coe_eq_coe'.2 ?_).symm
    exact (projectionFiber_isConnected S (S.toT y₁)).subset_connectedComponent (by simp)
      (by simpa using hab.symm)
  · intro t
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (S.toConnectedComponents t)
    let e := fiber_pullback_snd_homeomorphic_fiber S.componentMap S.toConnectedComponents t
    exact ⟨ConnectedComponents.mk (e.symm ⟨x, hx⟩).1, (e.symm ⟨x, hx⟩).2⟩

end AlgebraicGeometry.ProEtale
