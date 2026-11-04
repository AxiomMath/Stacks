module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.PhToFppfComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfLe

/-!
# The comparison morphism from the fppf site of a fibred category to a coarser site

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category over the big fppf category of schemes over `S`. Each
of the five topologies of `AlgebraicGeometry.SiteKind` gives `𝒳` an associated site
(Stacks 06TP), and the `τ`-site is coarser than the fppf site for every `τ`
(`AlgebraicGeometry.BigFppfOver.associatedTopology_le_fppf`). This file assembles from that
inequality the *comparison morphism of topoi*

`ε : Sh(𝒳_fppf) ⟶ Sh(𝒳_τ)`,

whose direct image is the identity on underlying presheaves — an fppf sheaf *is* a `τ` sheaf —
and whose inverse image is fppf sheafification. At `τ = .etale` this is the `ε` that
**Stacks 075R** (1) compares `Rε_*` with `ε_*`, and the `ε` of **Stacks 07B8**.

Nothing here is new mathematics: the morphism of topoi attached to a refinement of topologies
on one category is `CategoryTheory.changeOfTopologyMorphism`, and the continuity of the identity
functor it needs is `CategoryTheory.Functor.isContinuous_id_of_le`. What this file adds is the
instantiation at the associated sites of a fibred category, which is where the consumers of
Stacks 075R, 07A8 and 07B8 need it, together with the two identifications that pin down which
functors `ε_*` and `ε⁻¹` actually are.

## Main definitions

* `AlgebraicGeometry.FibredSite.comparisonMorphismOfTopoi`: the morphism of topoi `ε`.
* `AlgebraicGeometry.FibredSite.comparisonInverseImageIso`: its inverse image is fppf
  sheafification of the underlying presheaf.

## Main results

* `AlgebraicGeometry.FibredSite.comparisonPushforward_comp_sheafToPresheaf`: `ε_*` does not move
  the underlying presheaf.
* `AlgebraicGeometry.FibredSite.fullyFaithful_comparisonPushforward`: `ε_*` is fully faithful, so
  `ε` does not collapse the fppf topos into the coarser one.

## Implementation notes

The coefficient category is `Type (u + 1)`, the universe in which the objects of the associated
site of a category fibred in groupoids over `(Sch/S)_fppf` live; this is the coefficient universe
at which `CategoryTheory.changeOfTopologyMorphism` and
`AlgebraicGeometry.Stack.FlatFppf.toposMorphism` are both stated, and it is the one an algebraic
stack supplies, its object category being a `Type (u + 1)` with morphisms in `Type u`.

The direct image is stated for an arbitrary `τ : AlgebraicGeometry.SiteKind` rather than only for
the étale topology, since the inequality of topologies it rests on holds for all five and no step
distinguishes them.

The identification of the two structure sheaves that makes `ε_*` on modules be
`Stacks.SheafOfModules.comparisonPushforward` is not restated here. It is
`AlgebraicGeometry.FibredSite.ringOfLe_ringStructureSheafCore` of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteComparison`, where it is proved for an
arbitrary universe of the objects and of the morphisms of `𝒳` rather than only at the
`Type (u + 1)` seating used here.

## References

* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 07B8](https://stacks.math.columbia.edu/tag/07B8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The identity functor is continuous from the `τ`-site of `𝒳` to its fppf site, because the
`τ` topology is coarser (`AlgebraicGeometry.BigFppfOver.associatedTopology_le_fppf`) and so an
fppf sheaf is a `τ` sheaf. -/
public instance isContinuous_id_associatedTopology (τ : SiteKind) :
    (𝟭 𝒳).IsContinuous (BigFppfOver.associatedTopology B S hS p τ)
      (BigFppfOver.associatedTopology B S hS p .fppf) :=
  Functor.isContinuous_id_of_le _ _ (BigFppfOver.associatedTopology_le_fppf B S hS p τ)

/-- **The comparison morphism of topoi `ε : Sh(𝒳_fppf) ⟶ Sh(𝒳_τ)`** of a category over the big
fppf category of schemes over `S`, for any of the five topologies.

At `τ = .etale` this is the `ε` of **Stacks 075R** (1) and of **Stacks 07B8**. It is
`CategoryTheory.changeOfTopologyMorphism` at the two associated topologies: the direct image is
restriction along the identity functor, the inverse image is fppf sheafification, and the
left exactness of the inverse image is
`CategoryTheory.Functor.preservesFiniteLimits_id_sheafPullback`. -/
public def comparisonMorphismOfTopoi (τ : SiteKind) :
    MorphismOfTopoi
      (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) (Type (u + 1)))
      (Sheaf (BigFppfOver.associatedTopology B S hS p τ) (Type (u + 1))) :=
  changeOfTopologyMorphism 𝒳 (BigFppfOver.associatedTopology B S hS p τ)
    (BigFppfOver.associatedTopology B S hS p .fppf)

/-- **`ε_*` does not move the underlying presheaf**: the direct image of the comparison morphism
is restriction along the identity functor, so an fppf sheaf and its image on the `τ`-site have
the same sections and the same restriction maps. -/
public theorem comparisonPushforward_comp_sheafToPresheaf (τ : SiteKind) :
    (comparisonMorphismOfTopoi B S hS p τ).pushforward ⋙
        sheafToPresheaf (BigFppfOver.associatedTopology B S hS p τ) (Type (u + 1)) =
      sheafToPresheaf (BigFppfOver.associatedTopology B S hS p .fppf) (Type (u + 1)) :=
  changeOfTopologyMorphism_pushforward_comp_sheafToPresheaf 𝒳 _ _

/-- **`ε⁻¹` is fppf sheafification** of the underlying presheaf of a `τ` sheaf. In particular the
inverse image is not the identity: it is a genuine localization, left adjoint to `ε_*`. -/
public def comparisonInverseImageIso (τ : SiteKind) :
    (comparisonMorphismOfTopoi B S hS p τ).inverseImage ≅
      sheafToPresheaf (BigFppfOver.associatedTopology B S hS p τ) (Type (u + 1)) ⋙
        presheafToSheaf (BigFppfOver.associatedTopology B S hS p .fppf) (Type (u + 1)) :=
  changeOfTopologyMorphism_inverseImageIso 𝒳 _ _

/-- `ε_*` is faithful, being the identity on underlying presheaves. -/
public instance faithful_comparisonPushforward (τ : SiteKind) :
    (comparisonMorphismOfTopoi B S hS p τ).pushforward.Faithful := by
  have h : ((comparisonMorphismOfTopoi B S hS p τ).pushforward ⋙
      sheafToPresheaf (BigFppfOver.associatedTopology B S hS p τ) (Type (u + 1))).Faithful := by
    rw [comparisonPushforward_comp_sheafToPresheaf]; infer_instance
  exact Functor.Faithful.of_comp _
    (sheafToPresheaf (BigFppfOver.associatedTopology B S hS p τ) (Type (u + 1)))

/-- `ε_*` is full, being the identity on underlying presheaves. -/
public instance full_comparisonPushforward (τ : SiteKind) :
    (comparisonMorphismOfTopoi B S hS p τ).pushforward.Full := by
  have h : ((comparisonMorphismOfTopoi B S hS p τ).pushforward ⋙
      sheafToPresheaf (BigFppfOver.associatedTopology B S hS p τ) (Type (u + 1))).Full := by
    rw [comparisonPushforward_comp_sheafToPresheaf]; infer_instance
  exact Functor.Full.of_comp_faithful _
    (sheafToPresheaf (BigFppfOver.associatedTopology B S hS p τ) (Type (u + 1)))

/-- **`ε_*` is fully faithful**, so `Sh(𝒳_fppf)` sits inside `Sh(𝒳_τ)` as the full subcategory of
the `τ` sheaves which are fppf sheaves. This is the non-degeneracy of the comparison morphism:
`ε` identifies the fppf topos with a full subcategory of the coarser one rather than collapsing
either. -/
public def fullyFaithful_comparisonPushforward (τ : SiteKind) :
    (comparisonMorphismOfTopoi B S hS p τ).pushforward.FullyFaithful :=
  .ofFullyFaithful _

end AlgebraicGeometry.FibredSite

end
