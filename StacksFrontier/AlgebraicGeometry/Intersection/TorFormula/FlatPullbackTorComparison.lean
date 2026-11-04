module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullbackTorSheaf

/-!
# Flat pullback of the intersection product, with the Tor comparison supplied

Let `f : X ⟶ Y` be a flat morphism of nonsingular varieties over a field and let
`e = dim X - dim Y`. For coherent `𝒪_Y`-modules `ℱ` and `𝒢` the flat pullback of their
intersection product is the intersection product of their pullbacks:

`f^*(∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_Y}(ℱ, 𝒢)]_k) = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(f^*ℱ, f^*𝒢)]_{k+e}`.

`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullback` proves this identity, and
the dimension bound it needs, from the comparison `f^*Torᵢ^{𝒪_Y}(ℱ, 𝒢) ≅ Torᵢ^{𝒪_X}(f^*ℱ, f^*𝒢)`
as an input `hTor`. That comparison is `AlgebraicGeometry.TorFormula.pullbackTorSheafIso` of
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullbackTorSheaf`, which runs the
source's argument from Stacks 079U on K-flat representatives. Supplying it gives the two
statements below, which have no input beyond the hypotheses of Stacks 0B0Y.

## Main results

* `Stacks.Intersection.FlatPullback.schemeDeltaDimension_torSheaf_flatPullback_le`
  — the support of `Torᵢ^{𝒪_X}(f^*ℱ, f^*𝒢)` has delta-dimension at most `k + e`.
* `Stacks.Intersection.FlatPullback.flatPullback_intersectionProductCycleGroup_eq_pullbackSheaves`
  — **Tag 0B0Y**, flat pullback commutes with the intersection product.

## References

* [Stacks Project, Lemma 43.21.1 (Tag 0B0Y)](https://stacks.math.columbia.edu/tag/0B0Y)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Intersection.FlatPullback

open Stacks.Chow AlgebraicGeometry.TorFormula

/-- The dimension bound that the intersection product of the pulled-back sheaves needs: the
support of `Torᵢ^{𝒪_X}(f^*ℱ, f^*𝒢)` has delta-dimension at most `k + e`. It is the bound for the
support of `f^*Torᵢ^{𝒪_Y}(ℱ, 𝒢)`, which is Stacks 02RE part (2), transported along the Tor
comparison `AlgebraicGeometry.TorFormula.pullbackTorSheafIso`. This is
`Stacks.Intersection.FlatPullback.schemeDeltaDimension_reducedSupport_torSheaf_pullback_le` with
that comparison supplied. -/
theorem schemeDeltaDimension_torSheaf_flatPullback_le (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (F G : Y.Modules) (hF : _root_.SheafOfModules.IsCoherent F)
    (hG : _root_.SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY F G hF hG i
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf Y F G i)).subschemeι ≫ sY) ≤ (k : EInt))
    (i : ℕ) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI := isCoherent_torSheaf_of_isRegular X hX ((Scheme.Modules.pullback f).obj F)
      ((Scheme.Modules.pullback f).obj G) (isCoherent_pullback f F) (isCoherent_pullback f G) i
    schemeDeltaDimension (fieldChowSituation K)
      ((reducedSupport (torSheaf X ((Scheme.Modules.pullback f).obj F)
        ((Scheme.Modules.pullback f).obj G) i)).subschemeι ≫ sX)
        ≤ ((k + (e : ℤ) : ℤ) : EInt) :=
  schemeDeltaDimension_reducedSupport_torSheaf_pullback_le K sX sY hX hY f hbase e he F G hF hG
    k hFk (fun i => pullbackTorSheafIso f F G i) i

/-- **Stacks Project, Tag 0B0Y.** Let `f : X ⟶ Y` be a flat morphism of nonsingular varieties
over a field and let `e = dim X - dim Y`. For coherent `𝒪_Y`-modules `ℱ` and `𝒢` the flat
pullback of their intersection product is the intersection product of their pullbacks:

`f^*(∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_Y}(ℱ, 𝒢)]_k) = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(f^*ℱ, f^*𝒢)]_{k+e}`.

Taking `k = r + s - dim Y`, for supports of dimension at most `r` and `s`, this is
`f^*([ℱ]_r · [𝒢]_s) = [f^*ℱ]_{r+e} · [f^*𝒢]_{s+e}`.

This is `Stacks.Intersection.FlatPullback.flatPullback_intersectionProductCycleGroup` with the
comparison `f^*Torᵢ^{𝒪_Y}(ℱ, 𝒢) ≅ Torᵢ^{𝒪_X}(f^*ℱ, f^*𝒢)` supplied by
`AlgebraicGeometry.TorFormula.pullbackTorSheafIso`. -/
@[stacks 0B0Y "the intersection-product identity \
`f^*([ℱ]_r · [𝒢]_s) = [f^*ℱ]_{r+e} · [f^*𝒢]_{s+e}`, with the product read as the Tor formula \
`∑ᵢ (-1)ⁱ [Torᵢ(ℱ, 𝒢)]_{r+s-dim Y}` of Stacks 0AZR, which is how this library defines it. As \
in the source, flat pullback passes through the alternating sum, on each summand it is the \
cycle identity `f^*[Torᵢ]_k = [f^*Torᵢ]_{k+e}` of Stacks 0AZF, and the Tor comparison \
`f^*Torᵢ^{𝒪_Y}(ℱ, 𝒢) = Torᵢ^{𝒪_X}(f^*ℱ, f^*𝒢)` is \
`AlgebraicGeometry.TorFormula.pullbackTorSheafIso`, which runs the source's argument from \
Stacks 079U on K-flat representatives. The properness clause of the tag is \
`Stacks.Intersection.FlatPullback.intersectProperly_coherentSheafCycle_pullback`"]
theorem flatPullback_intersectionProductCycleGroup_eq_pullbackSheaves (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y)
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (F G : Y.Modules) (hF : _root_.SheafOfModules.IsCoherent F)
    (hG : _root_.SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY F G hF hG i
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf Y F G i)).subschemeι ≫ sY) ≤ (k : EInt)) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) k
        (intersectionProductCycleGroup (fieldChowSituation K) sY hY F G hF hG k hFk) =
      intersectionProductCycleGroup (fieldChowSituation K) sX hX
        ((Scheme.Modules.pullback f).obj F) ((Scheme.Modules.pullback f).obj G)
        (isCoherent_pullback f F) (isCoherent_pullback f G) (k + (e : ℤ))
        (schemeDeltaDimension_torSheaf_flatPullback_le K sX sY hX hY f hbase e he
          F G hF hG k hFk) :=
  flatPullback_intersectionProductCycleGroup K sX sY hX hY f hbase e he F G hF hG k hFk
    (fun i => pullbackTorSheafIso f F G i)

end Stacks.Intersection.FlatPullback

end
