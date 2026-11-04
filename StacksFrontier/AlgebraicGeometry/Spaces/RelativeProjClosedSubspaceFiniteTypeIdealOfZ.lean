module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceFiniteTypeIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceIdealOfZ

/-!
# A closed subspace of a relative Proj of finite presentation is cut out in one degree

This file proves Stacks 085M. Let `X` be a quasi-compact and quasi-separated algebraic space,
`𝒜` a quasi-coherent graded `𝒪_X`-algebra with quasi-compact relative Proj
`π : Proj_X(𝒜) ⟶ X`, and `i : Z ⟶ Proj_X(𝒜)` a closed immersion locally of finite presentation.
Then there are `d > 0` and a quasi-coherent `𝒪_X`-submodule `ℱ ⊆ 𝒜_d` of finite type with
`Z = Proj_X(𝒜/ℱ𝒜)` over `Proj_X(𝒜)`.

The graded ideal `ℐ ⊆ 𝒜` of Stacks 085L that cuts out `Z` is built from the graded ideals of
Stacks 0801 of the base changes of `Z` to the étale scheme points of `X`; its restriction to
every étale scheme point has the sections of that ideal. The statement then follows from
`RelativeProjSituation.exists_finiteType_iso_quotientProjHom_of_gradedIdeal`, which proves it
given such an ideal.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.exists_finiteType_iso_quotientProjHom`: there
  are `d > 0` and a finite type quasi-coherent `ℱ ⊆ 𝒜_d` with `Z ≅ Proj_X(𝒜/ℱ𝒜)` over
  `Proj_X(𝒜)`.

## References

* [Stacks Project, Tag 085M](https://stacks.math.columbia.edu/tag/085M)
* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space.RelativeProjSituation

/-- Let `X` be a quasi-compact and quasi-separated algebraic space, `𝒜` a quasi-coherent graded
`𝒪_X`-algebra whose relative Proj `π : Proj_X(𝒜) ⟶ X` is quasi-compact, and
`i : Z ⟶ Proj_X(𝒜)` a closed immersion locally of finite presentation. Then there are `d > 0`
and a quasi-coherent `𝒪_X`-submodule `ℱ ⊆ 𝒜_d` of finite type such that `Z = Proj_X(𝒜/ℱ𝒜)` as
closed subspaces of `Proj_X(𝒜)`. -/
@[stacks 085M]
theorem exists_finiteType_iso_quotientProjHom (s : RelativeProjSituation.{u, u})
    (hXqc : IsQuasiCompactSpace s.site s.base s.containsBase s.space.1)
    (hXqs : IsAbsolutelyQuasiSeparated s.site s.base s.containsBase
      (BigFppfSite.contains_terminal s.site) s.space.1)
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
    {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)
    (hfp : IsLocallyOfFinitePresentation s.site s.base s.containsBase i.hom) :
    ∃ d : ℕ, 0 < d ∧ ∃ (F : (s.algebra.piece (d : ℤ)).Submodule)
      (hF : F.toSheafOfModules.IsQuasicoherentOnSite), F.toSheafOfModules.IsFiniteType ∧
        ∃ e : Z ≅ (GradedIdeal.ofDegree s F hF).quotientSituation.Proj,
          e.hom ≫ (GradedIdeal.ofDegree s F hF).quotientProjHom = i :=
  exists_finiteType_iso_quotientProjHom_of_gradedIdeal (BigFppfSite.contains_terminal s.site)
    hXqc hXqs hπ i hi hfp (closedSubspaceGradedIdeal hπ i hi)
    (mem_twistKerGradedIdeal_iff_closedSubspaceGradedIdeal hπ i hi)

end AlgebraicGeometry.Space.RelativeProjSituation

end
