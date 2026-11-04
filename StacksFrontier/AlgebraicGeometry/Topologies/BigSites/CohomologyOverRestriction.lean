module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CohomologyAfterRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.OverTopologyInstances

/-!
# Cohomology over an object after restriction to a smaller big site

For two nested big sites of schemes of the same topology `τ` (Zariski, étale, smooth, syntomic
or fppf), localized at a scheme `S` of the smaller one, restricting an abelian sheaf from the
larger site does not change its cohomology over an object of the smaller site. This is Stacks
03YY (1), with the `Ext`-groups computing cohomology taken in any universe containing the
morphisms of the sites.

## Main definitions

* `AlgebraicGeometry.cohomologyOverRestrictionIso`: the comparison of the two cohomology
  functors over an object, natural in the abelian sheaf.

## Main results

* `AlgebraicGeometry.hasExt_sheaf_overTopology`: abelian sheaves on a localized big site have
  `Ext`-groups in every universe at least that of the morphisms of the site.

## Implementation notes

Both inputs of `AlgebraicGeometry.cohomologyRestrictionIso` that are not site data are supplied
here. Sheafification of abelian presheaves on a localized big site is the instance
`AlgebraicGeometry.hasSheafify_overTopology_addCommGrp`, which Mathlib's
`CategoryTheory.hasSheafifyEssentiallySmallSite` provides from essential smallness of the
localized site (Stacks 000J). The `Ext`-groups exist because abelian sheaves on an essentially
small site form a Grothendieck abelian category,
`Stacks.Cohomology.BiggerSite.isGrothendieckAbelian_sheaf`, which has enough injectives and
`u`-small hom-types, hence `Ext`-groups in every universe `max u w`.

`CategoryTheory.Abelian.HasExt` is an abbreviation and Mathlib deliberately registers no general
instance of it, so the two `Ext` instances are bound by `letI` in the statement rather than
registered globally; the statement names the universe of the `Ext`-groups as `max u w`, which
ranges over every universe in which they can be small.

## References

* [Stacks Project, Tag 03YY](https://stacks.math.columbia.edu/tag/03YY)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w

namespace AlgebraicGeometry

/-- **Abelian sheaves on a localized big site have `Ext`-groups in every universe containing
the morphisms of the site.** The localized site is essentially small, so its abelian sheaves
form a Grothendieck abelian category; it has enough injectives and `u`-small hom-types, hence
`max u w`-small ones. -/
public theorem hasExt_sheaf_overTopology (τ : CoveringTopology) (B : BigSite.{u} τ)
    (S : Scheme.{u}) (hS : S.size < cutoff τ B) :
    HasExt.{max u w} (Sheaf (overTopology τ B S hS) Ab.{u}) := by
  let : EssentiallySmall.{u} (Over (base B S hS)) := essentiallySmall_overBase B S hS
  let := Stacks.Cohomology.BiggerSite.isGrothendieckAbelian_sheaf (overTopology τ B S hS)
  let : LocallySmall.{max u w} (Sheaf (overTopology τ B S hS) Ab.{u}) :=
    ⟨fun X Y => small_lift.{u + 1, w, u} (X ⟶ Y)⟩
  exact hasExt_of_enoughInjectives _

/-- **Restricting an abelian sheaf from a larger big site to a smaller one preserves cohomology
over every object of the smaller site, naturally in the sheaf.** Let `τ` be one of the Zariski,
étale, smooth, syntomic and fppf topologies, `S` a scheme, and `B ⊆ B'` two big `τ`-sites with
`S` in `B`. For every object `U` of the localized site `(Sch/S)_τ` of `B`, every degree `p` and
every abelian sheaf `ℱ'` on the localized site `(Sch'/S)_τ` of `B'`,
`H^p_τ(U, ℱ'|_{(Sch/S)_τ}) ≅ H^p_τ(U, ℱ')`, naturally in `ℱ'`, with cohomology over an object
the `Ext`-based `CategoryTheory.Sheaf.cohomologyPresheafFunctor` with values in any universe
`max u w`. Sheafification and the `Ext`-groups on both localized sites come from their
essential smallness, `AlgebraicGeometry.hasSheafify_overTopology_addCommGrp` and
`AlgebraicGeometry.hasExt_sheaf_overTopology`. -/
@[stacks 03YY "part (1): for nested big sites `(Sch/S)_τ ⊆ (Sch'/S)_τ` of one of the five
  topologies, the cohomology over an object `U` of the smaller site of the restriction of an
  abelian sheaf on the bigger site is isomorphic to its cohomology over `U` on the bigger site,
  naturally in the sheaf, with sheafification and `Ext`-groups constructed from essential
  smallness of the sites"]
public noncomputable def cohomologyOverRestrictionIso {τ : CoveringTopology}
    (B B' : BigSite.{u} τ) (h : IsContained B B') (S : Scheme.{u})
    (hS : S.size < cutoff τ B) (U : Over (base B S hS)) (p : ℕ) :
    letI := hasExt_sheaf_overTopology.{u, w} τ B S hS
    letI := hasExt_sheaf_overTopology.{u, w} τ B' S (largerContains h hS)
    (inclusionOver h S hS).sheafPushforwardContinuous Ab.{u} (overTopology τ B S hS)
          (overTopology τ B' S (largerContains h hS)) ⋙
        Sheaf.cohomologyPresheafFunctor (overTopology τ B S hS) p ⋙
          (evaluation (Over (base B S hS))ᵒᵖ Ab.{max u w}).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor (overTopology τ B' S (largerContains h hS)) p ⋙
        (evaluation (Over (base B' S (largerContains h hS)))ᵒᵖ Ab.{max u w}).obj
          (op ((inclusionOver h S hS).obj U)) :=
  letI := hasExt_sheaf_overTopology.{u, w} τ B S hS
  letI := hasExt_sheaf_overTopology.{u, w} τ B' S (largerContains h hS)
  cohomologyRestrictionIso.{u, max u w} B B' h S hS U p

end AlgebraicGeometry

end
