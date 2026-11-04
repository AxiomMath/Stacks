module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing.SymmetricPowerDiagram
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing.HomogeneousKoszulComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing.KoszulDirectLimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing.HomologyVanishing

/-!
# Vanishing of the low homology of a symmetric power

Let `C` be a small category carrying the chaotic topology and let `B` be a commutative ring, so
that a `B̲`-module on the site is a diagram `F : Cᵒᵖ ⥤ ModuleCat B` (for the chaotic topology
every presheaf is a sheaf, and sheafification is the identity, so the sheaf symmetric power
`Sym^k_{B̲}(F)` is computed sectionwise). Let `U_•` be a cosimplicial object of `C` which is a
point resolution, as in Tag 08Q9. If `F` is flat — every module of sections is flat — and
`H_0(C, F) = 0`, then

`H_l(C, Sym^k_{B̲}(F)) = 0` for `l < k`,

where `H_l(C, -) = L_lπ_!` is the `l`th left derived functor of the colimit over `Cᵒᵖ`, read at
linear coefficients, which is the definition of the homology of a category in Tag 08PF.

## Main definitions

* `Stacks.ChaoticSite.symmetricPowerDiagram`: the sectionwise `k`th symmetric power of a
  diagram of modules over a constant coefficient ring, i.e. `Sym^k_{B̲}(F)`.
* `Stacks.ChaoticSite.homogeneousKoszulComplex`: the homogeneous Koszul complex in total degree
  `k`, with `∧^p M ⊗ Sym^{k-p} M` in degree `p`.
* `Stacks.ChaoticSite.FlatEilenbergZilber`: the Eilenberg–Zilber comparison of Tag 08QD, as a
  predicate on the coefficient ring: for degreewise flat simplicial `B`-modules the Moore
  complex of the degreewise tensor product is quasi-isomorphic to the tensor product of the
  Moore complexes.

## Main results

* `Stacks.ChaoticSite.symmetricKoszul_exact_of_flat`: for a flat module `M`, the Koszul complex
  `∧^• M ⊗ Sym(M)` is exact in every positive degree.
* `Stacks.ChaoticSite.isZero_homology_symmetricPowerDiagram_of_lt`: for any cosimplicial object
  `U_•` of `C`, if the Moore complex of `F(U_•)` has vanishing `H_0`, then the Moore complex of
  `Sym^k_{B̲}(F)(U_•)` has vanishing homology in every degree `l < k`.
* `Stacks.ChaoticSite.isZero_leftDerivedColim_symmetricPowerDiagram_of_lt`: the same vanishing
  for `L_lπ_!` when `U_•` is a point resolution.

## References

* [Stacks Project, Tag 08RD](https://stacks.math.columbia.edu/tag/08RD)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD)

## Files

The development is split into the following parts, in this order.

* `SymmetricPowerVanishing.SymmetricPowerDiagram`: symmetric and exterior powers of module diagrams.
* `SymmetricPowerVanishing.HomogeneousKoszulComplex`: the homogeneous Koszul complex.
* `SymmetricPowerVanishing.KoszulDirectLimit`: exactness of the Koszul complex of a flat module.
* `SymmetricPowerVanishing.HomologyVanishing`: vanishing of the low homology of a symmetric power.
-/
