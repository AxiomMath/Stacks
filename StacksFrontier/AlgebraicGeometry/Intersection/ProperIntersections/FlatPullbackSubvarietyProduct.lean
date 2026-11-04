module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackCycles
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullbackTorComparison

/-!
# Flat pullback of the product of two closed subvarieties

Let `f : X ⟶ Y` be a flat morphism of nonsingular varieties over a field with
`dim X = dim Y + e`, and let `V` and `W` be closed subvarieties of `Y` — the reduced closures of
two points — whose `Tor` sheaves are supported closely enough for the Section 43.14 product
`V · W = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_Y}(𝒪_V, 𝒪_W)]_n` to be an `n`-cycle. Then

`f^*(V · W) = [f^*𝒪_V]_{n+e} · [f^*𝒪_W]_{n+e}`,

the Tor-formula product of the two pulled-back structure sheaves.

## Main results

* `Stacks.Intersection.CycleFlatPullback.flatPullback_torSubvarietyProductOfBound` — the
  identity above.

## Implementation notes

The product `V · W` of Section 43.14 is
`AlgebraicGeometry.TorFormula.torSubvarietyProductOfBound`, which is by definition the
Tor-formula product `AlgebraicGeometry.TorFormula.intersectionProductCycle` of the two structure
sheaves `𝒪_V` and `𝒪_W`. The statement is therefore
`Stacks.Intersection.FlatPullback.flatPullback_intersectionProductCycleGroup_eq_pullbackSheaves`
— Tag 0B0Y — at `ℱ = 𝒪_V` and `𝒢 = 𝒪_W`, read on the underlying cycle.

### What this does and does not give for Tag 0B0Z

Tag 0B0Z asserts `f^*(α · β) = f^*α · f^*β` for cycles `α` and `β` intersecting properly, with
`α · β` the bilinear extension
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct` of Tag 0B08:

`α · β = ∑_{(v, w)} α(v) β(w) • (V · W)`.

Flat pullback is additive and passes through that sum, and on each summand it is the identity
proved here, so

`f^*(α · β) = ∑_{(v, w)} α(v) β(w) • ([f^*𝒪_V]_{r+e} · [f^*𝒪_W]_{s+e})`.

That step is carried out, from the identity proved here, in
`StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackCycleProduct`, as
`Stacks.Intersection.CycleFlatPullback.flatPullback_torFormulaCycleIntersectionProduct`.

The other side is a sum over pairs of components *upstairs*: by Tag 0AZF
`(f^*α)(v') = ∑_v α(v) · [f^*𝒪_V](v')`, so

`f^*α · f^*β = ∑_{(v, w)} α(v) β(w) • cycleIntersectionProduct([f^*𝒪_V]_{r+e}, [f^*𝒪_W]_{s+e})`.

The two therefore differ by exactly

`[ℱ]_r · [𝒢]_s = cycleIntersectionProduct([ℱ]_r, [𝒢]_s)`,

the statement that the Tor-formula product of two coherent sheaves depends only on their
associated cycles, which is [Stacks, Tag 0B0W] (Lemma 43.19.4) at `ℱ = f^*𝒪_V` and
`𝒢 = f^*𝒪_W`, available here as `Stacks.Intersection.ReductionToDiagonal.torFormula`. The
product conclusion of Tag 0B0Z is assembled from this module in
`StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackWhole`. Reducing by
linearity passes through cycles of coherent sheaves rather than prime cycles: `f^*[V]` is not a
prime cycle even when `[V]` is, but it is `[f^*𝒪_V]_{r+e}` by Tag 0AZF, and the Section 43.17
product is bilinear in arbitrary cycles, which is all the reduction needs.

## References

* [Stacks Project, Lemma 43.21.2 (Tag 0B0Z)](https://stacks.math.columbia.edu/tag/0B0Z)
* [Stacks Project, Lemma 43.21.1 (Tag 0B0Y)](https://stacks.math.columbia.edu/tag/0B0Y)
* [Stacks Project, Tag 0AZF](https://stacks.math.columbia.edu/tag/0AZF)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 0B0W](https://stacks.math.columbia.edu/tag/0B0W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.CycleFlatPullback

attribute [local instance 100000] HasDerivedCategory.standard

/-- **Stacks Project, Tag 0B0Z, the product conclusion on a single pair of subvarieties.** Let
`f : X ⟶ Y` be a flat morphism of nonsingular varieties over a field `K` with
`dim X = dim Y + e`, and let `V` and `W` be the reduced closures of two points of `Y` whose
Section 43.14 product `V · W = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_Y}(𝒪_V, 𝒪_W)]_n` is an `n`-cycle. Then

`f^*(V · W) = [f^*𝒪_V]_{n+e} · [f^*𝒪_W]_{n+e}`.

This is Tag 0B0Y at the structure sheaves of `V` and `W`, read on the underlying cycle: the
Section 43.14 product is by definition the Tor-formula product of those two sheaves.

This is the identity on a single summand of the double sum `α · β = ∑ᵢⱼ nᵢ mⱼ (Vᵢ · Wⱼ)`
defining the product, proved unconditionally. Tag 0B0Z is registered on the statement of both
of its clauses,
`Stacks.Intersection.CycleFlatPullback.flatPullback_torFormulaCycleIntersectionProduct_eq`.
-/
theorem flatPullback_torSubvarietyProductOfBound (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y)
    [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (n : ℤ) (v w : Y)
    (h : haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      TorSupportBound (fieldChowSituation K) sY hY n v w) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) n
          ⟨torSubvarietyProductOfBound (fieldChowSituation K) sY hY n h,
            intersectionProductCycle_mem_cyclesOfDimension (fieldChowSituation K) sY hY
              (structureSheafAt v) (structureSheafAt w) (isCoherent_structureSheafAt v)
              (isCoherent_structureSheafAt w) n h⟩).1 =
      intersectionProductCycle (fieldChowSituation K) sX hX
        ((Scheme.Modules.pullback f).obj (structureSheafAt v))
        ((Scheme.Modules.pullback f).obj (structureSheafAt w))
        (isCoherent_pullback f (structureSheafAt v))
        (isCoherent_pullback f (structureSheafAt w)) (n + (e : ℤ))
        (Stacks.Intersection.FlatPullback.schemeDeltaDimension_torSheaf_flatPullback_le
          K sX sY hX hY f hbase e he (structureSheafAt v) (structureSheafAt w)
          (isCoherent_structureSheafAt v) (isCoherent_structureSheafAt w) n h) :=
  by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  exact congrArg Subtype.val
    (Stacks.Intersection.FlatPullback.flatPullback_intersectionProductCycleGroup_eq_pullbackSheaves
      K sX sY hX hY f hbase e he (structureSheafAt v) (structureSheafAt w)
      (isCoherent_structureSheafAt v) (isCoherent_structureSheafAt w) n h)

end Stacks.Intersection.CycleFlatPullback

end
