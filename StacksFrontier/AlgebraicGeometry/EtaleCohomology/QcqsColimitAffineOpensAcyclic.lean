module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineEtaleModelDenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyVanishing

/-!
# The first geometric hypothesis of Stacks 09YQ, from a presentation on the affine sites

`OpensAcyclicity.subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference` gives
`H^q(X, 𝒢) = 0` for `q > 0` on Mathlib's small étale site of a quasi-compact quasi-separated scheme
`X` from two statements of geometry, the first of which — `haff` — is that for every affine open
`V` of `X` the restriction of `𝒢` to the small étale site of `V` has vanishing global cohomology in
positive degrees.

For the colimit sheaf `colim_i f_i^{-1}F_i` of [Stacks, Tag 09YQ] with every `F_i` injective, that
vanishing is proved on the **raised small affine étale site** of the limit, as
`Stacks.EtaleCohomology.QcqsLimitCohomology.vanishesOnObjects_colimit_of_pointwise_injective` —
condition (1) of [Stacks, Tag 07A1]. This file carries it across to `haff` by the dense subsite
crossing of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/AffineEtaleModelDenseSubsite.lean`.

## Main results

* `subsingleton_H_smallEtaleOpensRestrict_of_affineSitePresentation`
  — **`haff` for an abelian sheaf on Mathlib's small étale site of the limit whose restriction to
  the raised small affine étale site presents `colim_i f_i^{-1}F_i` for a pointwise injective
  system.**

## What this leaves

Exactly one thing, and it is a crossing and not a geometric statement: the hypothesis here is a
colimit presentation *on the raised small affine étale sites*, in the restriction vocabulary of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.IsColimitPresentation`, whereas
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem` carries its presentation on
Mathlib's small étale sites in the *inverse image* vocabulary of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation`. Passing between the two
is the same crossing the degree-zero statement `H0` needs — the adjunction between inverse image
and restriction, the identification of the levels of [Stacks, Tag 0EYL] with base change along the
projections of the cone (`Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso`, and the
universal property already carried across it by `restrictionIsColimitAb_levelBaseChange`), and the
coefficients. Nothing about *affine opens*, about `Stacks.Cohomology.VanishesOnObjects`, or about
the two sites remains to be supplied.

Injectivity is read at the levels of [Stacks, Tag 0EYL], which is where the vanishing statement
reads it; restriction of abelian sheaves from Mathlib's small étale site of `X_i` to such a level
is an equivalence, by
`Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelEtaleRestrictionAb`, and an
equivalence preserves injective objects, so this is not a further hypothesis on the system but the
same one read on the other side of the same crossing.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 07A1](https://stacks.math.columbia.edu/tag/07A1)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem

universe v u

namespace Stacks.EtaleCohomology.QcqsLimitCohomology

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

open Stacks.WeakSites.ColimitSiteCohomology Stacks.Cohomology in
/-- **The first geometric hypothesis of [Stacks, Tag 09YQ], for a system presented on the raised
small affine étale sites.** Let `(X_i)` be an inverse system of schemes over a nonempty directed
index with affine transition morphisms, all of them objects of a big étale site `B`, let `X` be
the vertex of a limit cone, and let `𝒢` be an abelian sheaf on Mathlib's small étale site of `X`.
Suppose that the restriction of `𝒢` to the raised small affine étale site of `X` presents
`colim_j f_j^{-1}F_j` for a system `F` of abelian sheaves on the levels of [Stacks, Tag 0EYL], all
of them injective. Then for every affine open `V` of `X` the restriction of `𝒢` to the small étale
site of `V` has vanishing global cohomology in every positive degree.

This is
`Stacks.EtaleCohomology.QcqsLimitCohomology.vanishesOnObjects_colimit_of_pointwise_injective` —
condition (1) of [Stacks, Tag 07A1] for the colimit sheaf, on the raised small affine étale site
of the limit — carried across the dense subsite inclusion
`Stacks.EtaleCohomology.AffineEtaleModel.toModel` by
`AffineEtaleModel.subsingleton_H_smallEtaleOpensRestrict_of_vanishesOnObjects`.
Nothing is assumed about the affine opens of `X`, and nothing about equalizers in the affine site:
the module docstring of `AffineEtaleModelDenseSubsite.lean` says why that matters. -/
public theorem subsingleton_H_smallEtaleOpensRestrict_of_affineSitePresentation
    (𝒢 : Sheaf (c.pt).smallEtaleTopology AddCommGrpCat.{max u v + 1})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (ι : ∀ j, (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙
      ((AffineEtaleModel.modelRestrict B (c.pt) hX).obj
        ((MayerVietoris.mayerVietorisRestrict (c.pt)).obj 𝒢)).obj)
    (hcolim : IsColimitPresentation.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (AffineEtaleModel.precoverage B (c.pt) hX) F
      ((AffineEtaleModel.modelRestrict B (c.pt) hX).obj
        ((MayerVietoris.mayerVietorisRestrict (c.pt)).obj 𝒢)) ι)
    (hF : ∀ j, Injective (F.obj j))
    (V : (c.pt).Opens) (hV : AlgebraicGeometry.IsAffineOpen V) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H.{max u v + 1}
      ((OpensAcyclicity.smallEtaleOpensRestrict (c.pt) V).obj 𝒢) p) :=
  AffineEtaleModel.subsingleton_H_smallEtaleOpensRestrict_of_vanishesOnObjects B (c.pt) hX 𝒢
    (vanishesOnObjects_colimit_of_pointwise_injective D c B hD hX hc F _ ι hcolim hF) V hV p hp

end Stacks.EtaleCohomology.QcqsLimitCohomology

end
