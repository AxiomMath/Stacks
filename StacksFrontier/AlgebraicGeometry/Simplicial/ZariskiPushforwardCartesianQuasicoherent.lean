module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiPushforwardIsCartesian
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiQuasicoherentComponents
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# The direct image of a cartesian quasi-coherent module on the total Zariski site

Let `f : V ⟶ U` be a cartesian morphism of simplicial schemes whose base has flat face maps and
whose components are quasi-compact and quasi-separated, and let `G` be a quasi-coherent sheaf of
`𝒪_V`-modules on the total Zariski site of `V` which is cartesian. Then `f_*G` is cartesian on
the total Zariski site of `U`, and each of its components `(f_*G)_k` is a quasi-coherent
`𝒪_{U_k}`-module on the site of its degree.

The cartesian half is `AlgebraicGeometry.SimplicialScheme.isCartesianModule_modulePushforward`,
which asks for quasi-coherence of the components of `G` in Mathlib's sense; the components of a
module that is quasi-coherent on the total site are quasi-coherent on the site of their degree
(`AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_componentModule`), and on a site whose
objects, morphisms and sections all live in the universe of the schemes the two readings of
quasi-coherence agree.

## Main results

* `SimplicialScheme.isQuasicoherent_componentModule`: the components of a quasi-coherent module
  on the total Zariski site are quasi-coherent in Mathlib's sense.
* `SimplicialScheme.isCartesianModule_modulePushforward_of_isQuasicoherentOnSite`: the direct
  image of a cartesian quasi-coherent module is cartesian.
* `SimplicialScheme.isQuasicoherentOnSite_componentModule_modulePushforward`: the components of
  the direct image of a quasi-coherent module are quasi-coherent on the site of their degree.
* `SimplicialScheme.isCartesianWithQuasicoherentComponents_modulePushforward`: the two
  together, the right-hand side of Stacks 0D7M for the direct image.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07TJ](https://stacks.math.columbia.edu/tag/07TJ)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Topology.Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

/-- **The components of a quasi-coherent module on the total Zariski site are quasi-coherent in
Mathlib's sense too.** The site of a simplicial degree has its objects, its morphisms and its
sections all in the universe of the schemes, so the two readings of quasi-coherence agree there
by `SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite`, whose size hypothesis is
`UnivLE.{u, u}`. -/
public theorem isQuasicoherent_componentModule (X : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) (F : Modules X) (hF : F.IsQuasicoherentOnSite) :
    ((componentModule X n).obj F).IsQuasicoherent :=
  (isQuasicoherentOnSite_componentModule X n F hF).isQuasicoherent

/-- **The direct image of a cartesian quasi-coherent module is cartesian.** The same statement
with the quasi-coherence of the components of `G` replaced by quasi-coherence of `G` itself on
the total Zariski site, which is the hypothesis Stacks 07TJ states; the components are then
quasi-coherent by `AlgebraicGeometry.SimplicialScheme.isQuasicoherent_componentModule`. -/
public theorem isCartesianModule_modulePushforward_of_isQuasicoherentOnSite
    {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) (hf : NatTrans.Equifibered f)
    (hflat : ∀ (k : ℕ) (j : Fin (k + 2)), Flat (U.δ j))
    (hqc : ∀ k : SimplexCategoryᵒᵖ, QuasiCompact (f.app k))
    (hqs : ∀ k : SimplexCategoryᵒᵖ, QuasiSeparated (f.app k))
    (G : Modules V) (hG : IsCartesianModule V G) (hGqc : G.IsQuasicoherentOnSite) :
    IsCartesianModule U ((modulePushforward f).obj G) :=
  isCartesianModule_modulePushforward f hf hflat hqc hqs G hG
    (fun k ↦ isQuasicoherent_componentModule V k G hGqc)

/-- **The components of the direct image of a quasi-coherent module are quasi-coherent on the
site of their degree**, in the sense of Stacks 03DL (6). This is
`AlgebraicGeometry.SimplicialScheme.isQuasicoherent_componentModule_modulePushforward` read
through `SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent`, so that it can be paired with
the cartesian half into the right-hand side of Stacks 0D7M. -/
public theorem isQuasicoherentOnSite_componentModule_modulePushforward
    {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) (k : SimplexCategoryᵒᵖ)
    (hqc : QuasiCompact (f.app k)) (hqs : QuasiSeparated (f.app k))
    (G : Modules V) (hGqc : G.IsQuasicoherentOnSite) :
    ((componentModule U k).obj ((modulePushforward f).obj G)).IsQuasicoherentOnSite := by
  have := hqc
  have := hqs
  have := isQuasicoherent_componentModule V k G hGqc
  have := isQuasicoherent_componentModule_modulePushforward f k G
  exact SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent _

/-- **The right-hand side of Stacks 0D7M for the direct image, under the hypotheses of
Stacks 07TJ.** Let `f : V ⟶ U` be a cartesian morphism of simplicial schemes whose base has flat
face maps and whose components are quasi-compact and quasi-separated, and let `G` be a
quasi-coherent sheaf of `𝒪_V`-modules on the total Zariski site of `V` which is cartesian. Then
`f_*G` is cartesian on the total Zariski site of `U` and every component `(f_*G)_k` is a
quasi-coherent `𝒪_{U_k}`-module.

This is everything the source's proof of Stacks 07TJ establishes before its final appeal to
Stacks 0D7M. Passing from here to quasi-coherence of `f_*G` on the total Zariski site is the
right-to-left direction of Stacks 0D7M, and the hypothesis that `G` is cartesian is what the
left-to-right direction supplies from quasi-coherence of `G`; both are
`isQuasicoherentOnSite_iff_isCartesianModule_and_components`, and the assembly is Stacks 07TJ,
`isQuasicoherentOnSite_modulePushforward`. The statement is therefore left untagged: it is an
intermediate step of 07TJ, not a result the source delimits. -/
public theorem isCartesianWithQuasicoherentComponents_modulePushforward
    {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) (hf : NatTrans.Equifibered f)
    (hflat : ∀ (k : ℕ) (j : Fin (k + 2)), Flat (U.δ j))
    (hqc : ∀ k : SimplexCategoryᵒᵖ, QuasiCompact (f.app k))
    (hqs : ∀ k : SimplexCategoryᵒᵖ, QuasiSeparated (f.app k))
    (G : Modules V) (hG : IsCartesianModule V G) (hGqc : G.IsQuasicoherentOnSite) :
    IsCartesianModule U ((modulePushforward f).obj G) ∧
      ∀ k : SimplexCategoryᵒᵖ,
        ((componentModule U k).obj ((modulePushforward f).obj G)).IsQuasicoherentOnSite :=
  ⟨isCartesianModule_modulePushforward_of_isQuasicoherentOnSite f hf hflat hqc hqs G hG hGqc,
    fun k ↦ isQuasicoherentOnSite_componentModule_modulePushforward f k (hqc k) (hqs k) G hGqc⟩

end AlgebraicGeometry.SimplicialScheme

end
