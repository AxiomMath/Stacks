module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorTotalSpaceAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional

/-!
# The comparison of torsors is an equivalence, with nothing carried

Let `𝒢` be a group algebraic space over an algebraic space `ℬ` over a scheme `S` of a big fppf
site.  **Stacks 04UT** says that the comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors`, which reads a
torsor of algebraic spaces as a torsor of sheaves, is an equivalence of stacks in groupoids over
the big fppf site of `S`.  Every rendering of that tag in this library carried a hypothesis: by
`FppfTorsors.nonempty_isEquivalenceOver_comparison_iff_isAlgebraicSpace_total` the tag is
*equivalent* to the statement that every `𝒢/ℬ`-torsor sheaf has an algebraic space as total space,
and that is the object half of Stacks 04U1, which is Stacks 04S6 part (3).

That predicate is now a theorem —
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection` — so the hypothesis is
discharged here and the tag holds outright.

## Main results

* `AlgebraicGeometry.Space.FppfTorsors.nonempty_isEquivalenceOver_comparison`: **Stacks 04UT**
  with nothing carried, which is the `𝒢/ℬ-Torsors` leg of **Stacks 0CQJ**.

## Implementation notes

The whole content of this file is the instantiation of
`AlgebraicGeometry.Space.FppfTorsors.nonempty_isEquivalenceOver_comparison_of_bootstrap` at
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.  It is a separate module
because the bootstrap theorem lives in
`StacksFrontier/AlgebraicGeometry/Spaces/Representable/Bootstrap/`, which the torsor files do not
import; nothing else is needed, and nothing else is proved here.

The equivalence is asserted as `Nonempty`, as the conditional results it comes from are: the
witness is produced by a choice of quasi-inverse on each fibre, so it is the existence of an
equivalence over the site that is canonical, not the equivalence itself.

## References

* [Stacks Project, Tag 04UT](https://stacks.math.columbia.edu/tag/04UT)
* [Stacks Project, Tag 04U1](https://stacks.math.columbia.edu/tag/04U1)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0CQJ](https://stacks.math.columbia.edu/tag/0CQJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Space.FppfTorsors

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 04UT**, with nothing carried, and with it the `𝒢/ℬ-Torsors` leg of **Stacks
0CQJ**: the comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors` is an equivalence of stacks in
groupoids over the big fppf site of `S`.

The hypothesis every earlier rendering carried is the object half of Stacks 04U1, equivalently
Stacks 04S6 part (3), which is now the theorem
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`. -/
@[stacks 04UT "the equivalence of stacks in groupoids, with nothing carried",
  stacks 0CQJ "the 𝒢/ℬ-Torsors leg: G-Torsors ≌ 𝒢/ℬ-Torsors over the big fppf site"]
theorem nonempty_isEquivalenceOver_comparison (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    Nonempty (Functor.IsEquivalenceOver (projection hB G) (SheafTorsors.projection G.obj)
      (comparison hB G)) :=
  nonempty_isEquivalenceOver_comparison_of_bootstrap hB G
    (isBootstrapAlgebraicSpaceAlongFlatSurjection 𝒞 S hS)

end AlgebraicGeometry.Space.FppfTorsors

end
