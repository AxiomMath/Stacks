module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiModulePushforward
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictionOfUniv
public import StacksFrontier.Topology.Simplicial.ComponentSliceSite

/-!
# The components of a quasi-coherent module on the total Zariski site are quasi-coherent

Let `X` be a simplicial scheme and `F` a sheaf of `𝒪_X`-modules on its total Zariski site. The
degree-`n` component `F_n` of `F` is the restriction of `F` along the inclusion of the open-set
site of the scheme `X_n` into the total site
(`AlgebraicGeometry.SimplicialScheme.componentModule`). This file proves that if `F` is
quasi-coherent in the sense of Stacks 03DL (6) then every `F_n` is a quasi-coherent
`𝒪_{X_n}`-module in the same sense.

This is one half of the forward implication of Stacks 0D7M, which asserts that `F` is
quasi-coherent on the total site if and only if `F` is cartesian and every `F_n` is
quasi-coherent. The other half of that implication — that `F` is cartesian — is not proved, so
nothing here carries an attribute for 0D7M; see the implementation notes.

## Main results

* `AlgebraicGeometry.SimplicialScheme.isIso_componentStructureHom`: the identification of the
  degree-`n` component of `𝒪_X` with the structure sheaf of `X_n` is an isomorphism of sheaves of
  rings.
* `AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_componentModule`: **the degree-`n`
  component of a quasi-coherent module on the total Zariski site is a quasi-coherent
  `𝒪_{X_n}`-module.**

## Implementation notes

The source deduces quasi-coherence of the components from the general statement that a pullback
of a quasi-coherent module is quasi-coherent (Stacks 03DO), applied to the component morphism of
topoi `g_n` of Stacks 09WG. The route taken here is that statement read as a *restriction*: the
inclusion of a simplicial degree is continuous and cocontinuous
(`Stacks.Topology.Simplicial.levelFunctor_isContinuous` and `levelFunctor_isCocontinuous`), and
restriction of modules along such a functor carries quasi-coherence, which is Stacks 03DM. Since
the inverse image of `g_n` *is* that restriction, this is the source's argument, with the
morphism of topoi presented by the functor of sites that makes its inverse image a restriction
rather than a sheafified left Kan extension.

The library's form of that transport, `Stacks.SheafOfModules.isQuasicoherentOnSite_pushforward`,
does not apply: it asks for two sites in one pair of universes, while the total Zariski site has
its objects in `Type u` and its morphisms in `Type 0`, and the open-set site of `X_n` has both in
`Type u`. The form used is
`Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_pushforward_ofUniv`, with the two
pairs independent. It asks in addition for the localization of the inclusion at an open of the
degree to be continuous, which is
`Stacks.Topology.Simplicial.levelFunctor_overPost_isContinuous`.

The structure morphism it is applied to is `componentStructureHom`, the identification of the
degree-`n` component of `𝒪_X` with the structure sheaf of `X_n`, so that the conclusion is about
`componentModule` on the nose; that it is an isomorphism is `isIso_componentStructureHom`, where
both the inverse and the two identities are read off the fact that on sections over every open
of `X_n` it is the identity.

The topology of the total site is spelled `zariskiTopology X` rather than as the projection
`(zariskiRingedTopos X).J`, which instance search does not unfold, and the topology of the
degree-`n` site is spelled through `zariskiSpace` rather than through the scheme: the continuity
and cocontinuity instances are indexed by the topologies, so the spellings have to be the ones
they are stated in.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 09W0](https://stacks.math.columbia.edu/tag/09W0)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Topology.Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable (X : SimplicialObject Scheme.{u}) (n : SimplexCategoryᵒᵖ)

/-- The inclusion of one simplicial degree into the total Zariski site is cocontinuous, by
Stacks 09W0; this is the spelling of the two topologies that the component functor uses. -/
public instance levelFunctor_isCocontinuous_zariski :
    (levelFunctor (zariskiSpace X) n).IsCocontinuous
      (Opens.grothendieckTopology ((zariskiSpace X).obj n)) (zariskiTopology X) :=
  levelFunctor_isCocontinuous (zariskiSpace X) n

/-- **The degree-`n` component of `𝒪_X` is the structure sheaf of `X_n`.** The comparison
`componentStructureHom` is an isomorphism of sheaves of rings: on sections over every open of
`X_n` both it and its inverse are the identity. -/
public instance isIso_componentStructureHom : IsIso (componentStructureHom X n) := by
  refine ⟨⟨⟨Functor.whiskerRight (structureComponentIso X n).hom
      (forget₂ CommRingCat RingCat.{u})⟩, ?_, ?_⟩⟩ <;>
    refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_)) <;>
    rfl

/-- **The components of a quasi-coherent module on the total Zariski site are quasi-coherent.**
If a sheaf of `𝒪_X`-modules `F` on the total Zariski site of a simplicial scheme is
quasi-coherent in the sense of Stacks 03DL (6), then its degree-`n` component `F_n` is a
quasi-coherent `𝒪_{X_n}`-module.

This is the quasi-coherence of the components in the forward implication of Stacks 0D7M. The
other half of that implication, that `F` is cartesian, is not proved, so this carries no
attribute for 0D7M. -/
public theorem isQuasicoherentOnSite_componentModule (F : Modules X)
    (hF : F.IsQuasicoherentOnSite) :
    ((componentModule X n).obj F).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_pushforward_ofUniv.{u, 0, u, u, u, u}
    (J := zariskiTopology X) (K := Opens.grothendieckTopology ((zariskiSpace X).obj n))
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)
    (levelFunctor (zariskiSpace X) n) (componentStructureHom X n)
    (isIso_componentStructureHom X n) F hF

end AlgebraicGeometry.SimplicialScheme

end
