module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiRingedTopos
public import StacksFrontier.Topology.Simplicial.SliceSite

/-!
# The slice of the total Zariski site of a simplicial scheme

For a simplicial scheme `X` the total Zariski site has as objects the pairs `(n, W)` of a
simplicial degree and an open subset of the scheme `X_n`. Its slice at `(n, W)` is *not*
`Opens(X_n)/W`: an object of the slice is a simplex map `φ : m ⟶ n` together with an open subset
of `(X φ)⁻¹W ⊆ X_m`. So the slice is the total Zariski site of the *over-simplicial-space* at
`(n, W)`: the diagram of spaces indexed by the simplicial degrees over `n` whose space at
`φ : m ⟶ n` is the open subspace `(X φ)⁻¹W` of `X_m`.

This file is the instantiation at the total Zariski site of
`Stacks.Topology.Simplicial.SimplicialOpen.sliceEquivalence`.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.zariskiOverSpace`: the over-simplicial-space at an object
  of the total Zariski site.
* `AlgebraicGeometry.SimplicialScheme.zariskiSliceEquivalence`: the slice of the total Zariski
  site at `(n, W)`, as the total site of the over-simplicial-space.
* `AlgebraicGeometry.SimplicialScheme.zariskiSheafSliceEquivalence`: the induced equivalence of
  sheaf categories.

## Main results

* the `IsDenseSubsite` instances of
  `Stacks.Topology.Simplicial.SimplicialOpen.sliceEquivalence` specialize here, so the slice
  topology of the total Zariski site corresponds to the topology of levelwise Zariski open
  coverings on the total site of the over-simplicial-space.

## Implementation notes

The total Zariski site is the total site of the underlying simplicial space, so there is nothing
to do beyond naming the instances: `AlgebraicGeometry.SimplicialScheme.ZariskiOpen` and
`.zariskiTopology` are abbreviations for `Stacks.Topology.Simplicial.SimplicialOpen` and its
topology of levelwise open coverings.

The over-simplicial-space is a diagram of *spaces*, not of schemes, even though the opens
`(X φ)⁻¹W` are open subschemes: the total site of the diagram only ever uses the underlying
spaces, and the structure sheaf of the slice is the restriction of `𝒪_X`, so nothing is gained
by carrying the scheme structure through the comparison. The scheme structure is needed only for
the *component* functor on the slice.

The two readings of an object of the slice —
`Stacks.Topology.Simplicial.SimplicialOpen.sliceEquivalence_functor_obj_index` and `_toOpens` —
are stated generically and not restated here: at the concrete types of the total Zariski site
the definitional unfolding they ask for exhausts the heartbeat budget of a single declaration,
while generically it is immediate.

## References

* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 00XZ](https://stacks.math.columbia.edu/tag/00XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Topology.Simplicial

universe u v w

namespace AlgebraicGeometry.SimplicialScheme

variable (X : SimplicialObject Scheme.{u}) (W : ZariskiOpen X)

/-- **The over-simplicial-space at an object of the total Zariski site.** At a simplex map
`φ : m ⟶ n` of the slice category it is the open subspace `(X φ)⁻¹W` of the space of `X_m`. -/
public abbrev zariskiOverSpace : Over W.degree ⥤ TopCat.{u} :=
  overSpace (zariskiSpace X) ((simplicialOpenEquiv (zariskiSpace X)).functor.obj W)

/-- **The slice of the total Zariski site at `(n, W)` is the total Zariski site of the
over-simplicial-space.** An object of the slice — an object `(m, V)` of the total site together
with an arrow into `(n, W)` — is a simplex map `φ : m ⟶ n` together with an open subset of the
space `(X φ)⁻¹W`. -/
public def zariskiSliceEquivalence : Over W ≌ DiagramOpen (zariskiOverSpace X W) :=
  SimplicialOpen.sliceEquivalence (zariskiSpace X) W

/-- **The slice comparison of the total Zariski site is an equivalence of sites.** -/
public instance zariskiSliceEquivalence_functor_isDenseSubsite :
    (zariskiSliceEquivalence X W).functor.IsDenseSubsite ((zariskiTopology X).over W)
      (DiagramOpen.grothendieckTopology (zariskiOverSpace X W)) :=
  SimplicialOpen.sliceEquivalence_functor_isDenseSubsite (zariskiSpace X) W

/-- **The slice comparison of the total Zariski site is an equivalence of sites, inverse
direction.** -/
public instance zariskiSliceEquivalence_inverse_isDenseSubsite :
    (zariskiSliceEquivalence X W).inverse.IsDenseSubsite
      (DiagramOpen.grothendieckTopology (zariskiOverSpace X W)) ((zariskiTopology X).over W) :=
  SimplicialOpen.sliceInverse_isDenseSubsite (zariskiSpace X) W

/-- **Sheaves on the slice of the total Zariski site are sheaves on the total Zariski site of
the over-simplicial-space.** -/
public def zariskiSheafSliceEquivalence (B : Type w) [Category.{v} B] :
    Sheaf ((zariskiTopology X).over W) B ≌
      Sheaf (DiagramOpen.grothendieckTopology (zariskiOverSpace X W)) B :=
  SimplicialOpen.sheafSliceEquivalence (zariskiSpace X) W B

end AlgebraicGeometry.SimplicialScheme

end
