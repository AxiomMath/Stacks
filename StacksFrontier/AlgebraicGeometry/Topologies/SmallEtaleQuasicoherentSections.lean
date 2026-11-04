module

public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentCore

/-!
# The pullback-sections presheaf on the small étale site

For a quasi-coherent module `F` on a scheme `S`, the presheaf of Tag 03DS sends a scheme `T`
over `S` to `Γ(T, T.hom⁺ F)`.  Tag 03DU(4) asks for its restriction to the small étale site of
`S` to be a sheaf of abelian groups, which is the sheaf condition underlying the associated
module `F^a` on `S_étale`.

`StacksFrontier/AlgebraicGeometry/Topologies/FpqcQuasicoherentCore.lean` reduces Tag 03DT to one
statement, the sheaf condition for the presheaf of Tag 03DS against an fpqc covering sieve of
the base scheme itself.  This file records that the same statement already gives Tag 03DU(4) on
the small étale site, so nothing beyond that one clause stands between Tag 03DT and the
associated-module sheaf condition.

## Main results

* `AlgebraicGeometry.SmallEtale.isSheaf_quasiCoherentPresheaf_of_base`: granted the sheaf
  condition for the presheaf of Tag 03DS against fpqc covering sieves of the base, its
  restriction along the canonical functor from the small étale site of `S` to the schemes over
  `S` is a sheaf of abelian groups.

## Implementation notes

The hypothesis is taken at the level of *types*, as `CategoryTheory.Presieve.IsSheafFor` of the
composite with `CategoryTheory.forget AddCommGrpCat`, and not as the abelian-group-valued
conclusion of `Stacks.Sites.isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_base`.  That is
forced.  Passing from `CategoryTheory.Presheaf.IsSheaf` for an `AddCommGrpCat.{u}`-valued
presheaf to the sheaf condition of its underlying presheaf of types would use
`CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf` or
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`, both of which require
`CategoryTheory.Limits.PreservesLimitsOfSize.{u, u + 1}` of `CategoryTheory.forget
AddCommGrpCat`; over a site of `Scheme.{u}`-objects that unfolds to the unsatisfiable universe
constraint `u + 1 =?= u`.  This is the same obstruction recorded for the converse direction in
`StacksFrontier/AlgebraicGeometry/Topologies/FpqcQuasicoherentSheaf.lean`, where
`Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget` had to be proved by hand; only the
converse is available, so a consumer of Tag 03DT has to enter at the type level.

Given that, the proof is pure transport: `Stacks.Sites.isSheaf_over_toGrothendieck_iff` turns the
sheaf condition on `CategoryTheory.Over S` for the localized fpqc topology into the family of
`CategoryTheory.Presieve.IsSheafFor` statements that
`Stacks.Sites.isSheafFor_quasiCoherentPresheaf_of_base` supplies, and
`AlgebraicGeometry.SmallEtale.isSheaf_toOver_op_comp` carries the result along the canonical
functor to the small étale site.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

/-- Granted the sheaf condition of Tag 03DT over the base — for every scheme `S'`, every
quasi-coherent module `F'` on it and every fpqc covering sieve of `S'` — the presheaf of
Tag 03DS of a quasi-coherent module on `S` restricts to a sheaf of abelian groups on the small
étale site of `S`.  This is the sheaf condition of Tag 03DU(4) for the small étale site. -/
public theorem isSheaf_quasiCoherentPresheaf_of_base
    (h : ∀ (S' : Scheme.{u}) (F' : S'.Modules) [F'.IsQuasicoherent] (T : Sieve S'),
      T ∈ Scheme.fpqcTopology.{u} S' →
      Presieve.IsSheafFor
        (quasiCoherentPresheafFunctor S' F' ⋙ CategoryTheory.forget AddCommGrpCat)
        ((Sieve.overEquiv (Over.mk (𝟙 S') : Over S')).symm T).arrows)
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (topology B S hS)
      ((toOver B S hS).op ⋙ quasiCoherentPresheafFunctor S F) := by
  refine isSheaf_toOver_op_comp B S hS _ ?_
  rw [Stacks.Sites.isSheaf_over_toGrothendieck_iff Scheme.fpqcPrecoverage.{u} S]
  intro Y R hR
  exact Stacks.Sites.isSheafFor_quasiCoherentPresheaf_of_base F Y h R hR

end AlgebraicGeometry.SmallEtale

end
