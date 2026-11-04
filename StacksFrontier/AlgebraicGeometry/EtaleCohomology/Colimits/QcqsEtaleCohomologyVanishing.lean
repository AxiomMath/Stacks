module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimitGlobal
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.VanishingOnObjectsOfColimitOfFiniteSites

/-! # Condition (1) of Stacks 07A1 for the colimit sheaf on the small affine etale site of a limit

Let `I` be a directed set, let `(X_i)` be an inverse system of schemes over `I` whose transition
morphisms are affine, and let `X = lim X_i`. Let `(G_j, ψ_a)` be a system of abelian sheaves on
the small affine etale sites of the `X_i`, **every one of them injective**, and let `𝒢` on the
small affine etale site of `X` present the colimit `colim f_j^{-1}G_j`. Then `𝒢` satisfies
`Stacks.Cohomology.VanishesOnObjects`: its cohomology over every object of the small affine etale
site of `X` vanishes in positive degrees.

This is `Stacks.WeakSites.ColimitSiteCohomology.vanishesOnObjects_of_pointwise_injective`
instantiated at the system of sites of Stacks 0EYL, by the same five inputs that
`Stacks.EtaleCohomology.QcqsLimitCohomology.etaleCohomologyColimit_isColimit` consumes. Nothing
here uses affineness of the levels: the levels are arbitrary schemes of the big etale site, only
the transition morphisms being affine.

## What this leaves

Exactly condition (2) of Stacks 07A1, `Stacks.Cohomology.CechComplexExactPos` for `𝒢`. Those two
conditions give total acyclicity (`Stacks.Cohomology.isTotallyAcyclic_of_conditions`), total
acyclicity gives right acyclicity for sections against a presheaf of sets (part (2) of
Stacks 0731, `Stacks.Cohomology.rightAcyclic_sectionsOverPresheaf_of_isTotallyAcyclic`), and at
the terminal presheaf that is the vanishing of the higher cohomology of `𝒢` over the terminal
*sheaf* — the one input the dimension shift of Stacks 09YQ still lacks for a level that is not an
object of its own small affine etale site. See the module docstring of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/QcqsEtaleCohomologyColimit.lean`.

## References

* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks 07A1](https://stacks.math.columbia.edu/tag/07A1)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.EtaleCohomology.QcqsLimitCohomology

open AlgebraicGeometry Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-! ### The instances the statement of Stacks 07A1 needs at the concrete colimit site

Instance search cannot find sheafification, enough injectives or `Ext` for the colimit site on its
own: `(limitSitePrecoverage D c B hX).toGrothendieck` is a precoverage of a raised full subcategory
of a slice of a full subcategory of schemes, and unfolding it exhausts the `synthInstance`
heartbeat budget before any proof runs. The three facts are therefore registered as instances
whose heads match syntactically. Each is an application of an existing abstract lemma about an
arbitrary small site; none of them is a new statement.
-/

/-- Sheafification of abelian sheaves on the colimit site of Stacks 0EYL. This is
`Stacks.WeakSites.ColimitSiteCohomology.hasSheafifyAb`, which that module carries as a
`local instance`, registered for this site. -/
instance hasSheafify_limitSitePrecoverage :
    HasSheafify (limitSitePrecoverage D c B hX).toGrothendieck (Ab.{max u v + 1}) :=
  Stacks.WeakSites.ColimitSiteCohomology.hasSheafifyAb.{max u v + 1, max u v + 1} _

/-- Abelian sheaves on the colimit site of Stacks 0EYL have enough injectives. This is
`Stacks.WeakSites.ColimitSiteCohomology.enoughInjectivesAb` registered for this site. -/
instance enoughInjectives_limitSitePrecoverage :
    EnoughInjectives (Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Ab.{max u v + 1})) :=
  Stacks.WeakSites.ColimitSiteCohomology.enoughInjectivesAb.{max u v + 1, max u v + 1} _

/-- `Ext`-groups exist for abelian sheaves on the colimit site of Stacks 0EYL. -/
instance hasExt_limitSitePrecoverage :
    HasExt.{max u v + 1}
      (Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Ab.{max u v + 1})) :=
  hasExt_of_enoughInjectives _

open Stacks.WeakSites.ColimitSiteCohomology Stacks.Cohomology in
/-- **Condition (1) of [Stacks, Tag 07A1] for the colimit sheaf, on the small affine etale site of
the limit.** For a system `G` of abelian sheaves on the small affine etale sites of the levels, all
of them injective, and a sheaf `𝒢` on the small affine etale site of `X = lim X_i` presenting
`colim f_j^{-1}G_j`, the cohomology of `𝒢` over every object of that site vanishes in positive
degrees, in the form `Stacks.Cohomology.VanishesOnObjects`.

This is `Stacks.WeakSites.ColimitSiteCohomology.vanishesOnObjects_of_pointwise_injective` applied
to the colimit of sites of Stacks 0EYL through `mem_limitSitePrecoverage_iff` and the three
descent clauses of `Stacks.EtaleCohomology.AffineLimitCohomology`. The module docstring says what
it leaves. -/
theorem vanishesOnObjects_colimit_of_pointwise_injective
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ j, (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ 𝒢.obj)
    (hcolim : IsColimitPresentation.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι)
    (hF : ∀ j, Injective (F.obj j)) :
    VanishesOnObjects.{max u v + 1} (limitSitePrecoverage D c B hX).toGrothendieck 𝒢 :=
  vanishesOnObjects_of_pointwise_injective.{v, v, max u v + 1}
    (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc)
    (toLimitSmall_obj_descends D c B hD hX hc)
    (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc)
    (limitSitePrecoverage D c B hX)
    (mem_limitSitePrecoverage_iff D c B hD hX hc)
    F 𝒢 ι hcolim hF

end Stacks.EtaleCohomology.QcqsLimitCohomology

end
