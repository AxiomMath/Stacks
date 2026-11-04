module

public import StacksFrontier.RingTheory.Tor.Balancing.DoubleComplex
public import StacksFrontier.RingTheory.Tor.Balancing.RowComparison
public import StacksFrontier.RingTheory.Tor.Balancing.CanonicalIso
public import StacksFrontier.RingTheory.Tor.Balancing.TorShift
public import StacksFrontier.RingTheory.Tor.Balancing.Horseshoe
public import StacksFrontier.RingTheory.Tor.Balancing.Naturality

/-!
# Double complexes and the balancing of `Tor`

Let `R` be a commutative ring.  A first-quadrant homological double complex
`(A_{i,j}, d, δ)` of `R`-modules consists of modules `A_{i,j}` for `i, j ≥ 0`
together with `R`-linear maps

* `d : A_{i,j} → A_{i-1,j}`, the horizontal differential, lowering the first index;
* `δ : A_{i,j} → A_{i,j-1}`, the vertical differential, lowering the second index;

satisfying `d ∘ d = 0`, `δ ∘ δ = 0` and the commuting relation `d ∘ δ = δ ∘ d`.
Here the differentials are reindexed so that their target always has nonnegative
index: `d i j : A_{i+1,j} → A_{i,j}` and `δ i j : A_{i,j+1} → A_{i,j}`.  This is
equivalent to the informal version, since the maps out of the boundary `A_{0,j}`
and `A_{i,0}` into negative index land in the zero module.

The horizontal cokernels `R(A)_j = Coker (d : A_{1,j} → A_{0,j})` carry an induced
vertical differential `δ̄` and so form a chain complex `R(A)_•`; symmetrically the
vertical cokernels `U(A)_i = Coker (δ : A_{i,1} → A_{i,0})` carry an induced
horizontal differential `d̄` and form `U(A)_•`.  Each row `A_{•,j}` is a resolution
of `R(A)_j` exactly when the rows are exact in positive horizontal degree, i.e.
`ker (d i j) = range (d (i+1) j)`, and symmetrically for the columns.

## Main definitions

* `DoubleCx`: a first-quadrant homological double complex of `R`-modules.
* `DoubleCx.RObj`, `DoubleCx.UObj`: the horizontal and the vertical cokernels.
* `DoubleCx.RHom`, `DoubleCx.UHom`: the homology of the two edge complexes.
* `Hthird`: the homology of the total complex of `A`, the intermediate object
  through which the two edge homologies are compared.
* `canonIso`: the canonical isomorphism `H_i(R(A)_•) ≃ H_i(U(A)_•)`.
* `Tor_iso_Tor'.syzygy M`: the first syzygy `ker (Projective.π M)` of `M`.
* `Tor_iso_Tor'.oneKer M`: the functor `N ↦ ker (K ⊗ N ⟶ P₀ ⊗ N)` through which both
  `Tor_1(M, -)` and `Tor'_1(M, -)` factor.
* `Tor_iso_Tor'.Horseshoe M`: a degreewise split short exact sequence of projective
  resolutions lifting the syzygy sequence `0 → K → P₀ → M → 0` (Weibel 2.2.8).

## Main results

* `statement1`: if every row of `A` is a resolution of `R(A)_j` and every column
  is a resolution of `U(A)_i`, then `H_i(R(A)_•) ≅ H_i(U(A)_•)` for every `i ≥ 0`.
* `statement2`: these isomorphisms can be chosen naturally in `A`, so that the
  naturality square commutes for every morphism of double complexes.
* `torFlip_iso_Tor'`: `(Tor C i).flip ≅ Tor' C i`, obtained by lifting the symmetric
  braiding `M ⊗ - ≅ - ⊗ M` through `NatTrans.leftDerived`.
* `Tor_iso_Tor'`: `Tor C i ≅ Tor' C i`, the balancing of `Tor`: deriving the second variable
  agrees with deriving the first.
* `tor_symm_canonically_iso`: `Tor C i ≅ (Tor C i).flip`.

## References

* [Stacks Project, Tag 00M1](https://stacks.math.columbia.edu/tag/00M1)
* [Stacks Project, Tag 00M3](https://stacks.math.columbia.edu/tag/00M3)

## File structure

This module only re-exports its parts, under `StacksFrontier.RingTheory.Tor.Balancing`:

* `DoubleComplex`: double complexes, the edge complexes and the total complex;
* `RowComparison`: the comparison `cmpR`;
* `CanonicalIso`: `cmpU`, `canonIso`, `statement1` and `statement2`;
* `TorShift`: `Tor` in degrees zero and one, and `torShift`;
* `Horseshoe`: the horseshoe resolution, `Tor'` and `tor'Shift`;
* `Naturality`: naturality, `Tor_iso_Tor'` and `tor_symm_canonically_iso`.
-/
