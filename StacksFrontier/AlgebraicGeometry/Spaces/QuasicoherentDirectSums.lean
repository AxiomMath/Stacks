module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCartesian

/-!
# The direct-sum clause of Stacks 03M1 at a free module universe

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Clause (1) of
Stacks 03M1 says that a direct sum of quasi-coherent `𝒪_F`-modules is quasi-coherent.

This file proves that clause at a free module universe `m` and for an arbitrary index type,
assuming Descent, Proposition 03DX(2) for the small étale site of `F` at module universe `m`: an
`𝒪_F`-module is quasi-coherent if and only if it is cartesian on affine charts.  This hypothesis
is the explicit argument `h03DX`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_of_imp`: at module
  universe `u`, the implication form of `h03DX` implies its equivalence form.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isColimit_cofan_of_h03DX`: the vertex of a
  colimiting cofan on a family of quasi-coherent `𝒪_F`-modules is quasi-coherent.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_sigma_of_h03DX`: the chosen coproduct `∐ G` of a
  family of quasi-coherent `𝒪_F`-modules is quasi-coherent.

## Implementation notes

The hypothesis `h03DX` is written out at every use rather than named, as are `h03DT`, `h03DW` and
`h03DX` throughout this tree; naming it would create a second spelling of a proposition of
Descent, Chapter 35.

The colimiting cofan, respectively the coproduct instance, is a hypothesis: a coproduct of
sheaves of modules need not exist when the index universe exceeds the module universe, and no
universe bound is written into the statements.

No `@[stacks 03M1]` attribute is attached, since every statement is conditional on `h03DX`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w m u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- At module universe `u`, if every quasi-coherent `𝒪_F`-module is cartesian on affine charts,
then an `𝒪_F`-module is quasi-coherent if and only if it is cartesian on affine charts. -/
theorem isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_of_imp
    (h03DX : ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G) :
    ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G :=
  fun G => ⟨h03DX G, isQuasicoherentOnSite_of_isCartesianOnAffineCharts G⟩

/-- **Clause (1) of Stacks 03M1 at a free module universe.**  The vertex of a colimiting cofan on
a family of quasi-coherent `𝒪_F`-modules is quasi-coherent, granted Descent,
Proposition 03DX(2) for the small étale site of `F` at the module universe in question. -/
theorem isQuasicoherentOnSite_of_isColimit_cofan_of_h03DX
    (h03DX : ∀ G : Modules.{u, m} B S hS F hF,
      G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G)
    {ι : Type w} {G : ι → Modules.{u, m} B S hS F hF} (c : Cofan G) (hc : IsColimit c)
    (hG : ∀ i, (G i).IsQuasicoherentOnSite) :
    c.pt.IsQuasicoherentOnSite :=
  (h03DX _).2 (isCartesianOnAffineCharts_coproduct B S hS F hF c hc
    fun i => (h03DX _).1 (hG i))

/-- **Clause (1) of Stacks 03M1 at a free module universe, for the chosen coproduct.**  A direct
sum of quasi-coherent `𝒪_F`-modules is quasi-coherent, granted Descent, Proposition 03DX(2) at the
module universe in question. -/
theorem isQuasicoherentOnSite_sigma_of_h03DX
    (h03DX : ∀ G : Modules.{u, m} B S hS F hF,
      G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G)
    {ι : Type w} (G : ι → Modules.{u, m} B S hS F hF) [HasCoproduct G]
    (hG : ∀ i, (G i).IsQuasicoherentOnSite) :
    (∐ G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isColimit_cofan_of_h03DX B S hS F hF h03DX _
    (coproductIsCoproduct G) hG

end AlgebraicGeometry.Space

end
