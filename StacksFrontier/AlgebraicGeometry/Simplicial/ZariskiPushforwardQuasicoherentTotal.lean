module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiPushforwardCartesianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiQuasicoherentCartesian
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07TJ: the pushforward of a quasi-coherent module on the total Zariski site

Let `f : V ⟶ U` be a cartesian morphism of simplicial schemes such that every face map of `U` is
flat and every component `f_n : V_n ⟶ U_n` is quasi-compact and quasi-separated. Stacks 07TJ
asserts that the direct image `f_*G` of a quasi-coherent module `G` on the total Zariski site of
`V` is a quasi-coherent module on the total Zariski site of `U`. That is the statement proved
here.

## Main results

* `AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_modulePushforward`: **Stacks 07TJ.**

## The route

The source's route, taken here: by Stacks 0D7M quasi-coherence on a total site is cartesianness
together with quasi-coherence of the components, so

* the hypothesis gives that `G` is cartesian and that its components `G_n` are quasi-coherent,
  by the forward direction of 0D7M
  (`isQuasicoherentOnSite_iff_isCartesianModule_and_components`);
* `AlgebraicGeometry.SimplicialScheme.isCartesianWithQuasicoherentComponents_modulePushforward`
  then gives that `f_*G` is cartesian — this is where Stacks 02KH, the flatness of the face maps
  of `U` and the cartesian hypothesis on `f` enter — and that its components `(f_*G)_n` are
  quasi-coherent — this is the identification `(f_*G)_n = f_{n,*}G_n` of Stacks 09VP together
  with Stacks 01LC, which is where quasi-compactness and quasi-separatedness of the components
  of `f` enter;
* the converse direction of 0D7M turns that back into quasi-coherence of `f_*G` on the total
  Zariski site of `U`.

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 07TJ](https://stacks.math.columbia.edu/tag/07TJ)
* [Stacks Project, Tag 09VP](https://stacks.math.columbia.edu/tag/09VP)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {V U : SimplicialObject Scheme.{u}}

/-- **Stacks 07TJ.** Let `f : V ⟶ U` be a cartesian morphism of simplicial schemes, assume that
the face maps `d^n_j` of `U` are flat and that the components `f_n : V_n ⟶ U_n` are quasi-compact
and quasi-separated. Then for a quasi-coherent module `G` on the total Zariski site of `V` the
direct image `f_*G` is a quasi-coherent module on the total Zariski site of `U`. -/
@[stacks 07TJ]
public theorem isQuasicoherentOnSite_modulePushforward (f : V ⟶ U)
    (hcart : NatTrans.Equifibered f)
    (hflat : ∀ (k : ℕ) (j : Fin (k + 2)), Flat (U.δ j))
    (hqc : ∀ k : SimplexCategoryᵒᵖ, QuasiCompact (f.app k))
    (hqs : ∀ k : SimplexCategoryᵒᵖ, QuasiSeparated (f.app k))
    (G : Modules V) (hG : G.IsQuasicoherentOnSite) :
    ((modulePushforward f).obj G).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_isCartesianModule_and_components U
      ((modulePushforward f).obj G)).2
    (isCartesianWithQuasicoherentComponents_modulePushforward f hcart hflat hqc hqs G
      ((isQuasicoherentOnSite_iff_isCartesianModule_and_components V G).1 hG).1 hG)

end AlgebraicGeometry.SimplicialScheme

end
