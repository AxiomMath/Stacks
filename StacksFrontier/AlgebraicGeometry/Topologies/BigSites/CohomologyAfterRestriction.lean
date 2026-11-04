module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteObjectCohomology

/-!
# Cohomology after restriction to a smaller big site

For two nested big sites of schemes of the same topology, localized at a scheme of the smaller
one, restriction of an abelian sheaf from the larger site does not change its cohomology over an
object of the smaller site.

## Main definitions

* `AlgebraicGeometry.cohomologyRestrictionIso` is the canonical comparison of the two cohomology
  functors over an object, natural in the abelian sheaf.

## Main results

* `AlgebraicGeometry.essentiallySmall_overBase`: a localized big site is essentially small at the
  universe of its morphisms.

## Implementation notes

Cohomology over an object is Mathlib's `Ext`-based
`CategoryTheory.Sheaf.cohomologyPresheafFunctor`, whose `Ext` universe is independent of the
sites; the comparison is therefore an isomorphism of cohomology functors rather than one of
cohomology groups for each sheaf separately.

The statement is `Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso` — Stacks 03YU,
statement 2 — at the localized inclusion, and the work here is to supply its hypotheses: the
inclusion is continuous and cocontinuous and preserves finite limits (Stacks 022K), a localized
big site has finite limits, and it is essentially small at the universe of its morphisms because
the category of schemes below a cardinal is (Stacks 000J). Essential smallness is what makes the
coefficients `Ab.{u}` usable: the objects of a big site live one universe above its morphisms, so
the Kan extensions along the inclusion with coefficients in the lower universe are not given by
the generic instances.

## References

* [Stacks Project, Tag 03YY](https://stacks.math.columbia.edu/tag/03YY)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry

/-- **A localized big site is essentially small at the universe of its morphisms.** It is a slice
of the category of schemes below a cardinal, which is essentially small by Stacks 000J. -/
public lemma essentiallySmall_overBase {τ : CoveringTopology} (B : BigSite.{u} τ)
    (S : Scheme.{u}) (hS : S.size < cutoff τ B) :
    EssentiallySmall.{u} (Over (base B S hS)) := by
  change EssentiallySmall.{u} (CostructuredArrow (𝟭 (siteCategory B)) (base B S hS))
  infer_instance

/-- **Restricting an abelian sheaf from a larger big site to a smaller one preserves cohomology
over every object of the smaller site, naturally in the sheaf.** For nested big `τ`-sites
localized at a scheme `S` of the smaller one, the cohomology over `U` of the restriction of an
abelian sheaf agrees with its cohomology over the image of `U`.

The inclusion of the localized sites is continuous, cocontinuous and preserves finite limits, and
a localized big site is essentially small, so this is
`Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso`. -/
@[stacks 03YY "cohomology_after_restriction"]
public noncomputable def cohomologyRestrictionIso {τ : CoveringTopology}
    (B B' : BigSite.{u} τ) (h : IsContained B B') (S : Scheme.{u})
    (hS : S.size < cutoff τ B)
    [HasSheafify (overTopology τ B S hS) Ab.{u}]
    [HasSheafify (overTopology τ B' S (largerContains h hS)) Ab.{u}]
    [HasExt.{w} (Sheaf (overTopology τ B S hS) Ab.{u})]
    [HasExt.{w} (Sheaf (overTopology τ B' S (largerContains h hS)) Ab.{u})]
    (U : Over (base B S hS)) (p : ℕ) :
    (inclusionOver h S hS).sheafPushforwardContinuous Ab.{u} (overTopology τ B S hS)
          (overTopology τ B' S (largerContains h hS)) ⋙
        Sheaf.cohomologyPresheafFunctor (overTopology τ B S hS) p ⋙
          (evaluation (Over (base B S hS))ᵒᵖ Ab.{w}).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor (overTopology τ B' S (largerContains h hS)) p ⋙
        (evaluation (Over (base B' S (largerContains h hS)))ᵒᵖ Ab.{w}).obj
          (op ((inclusionOver h S hS).obj U)) := by
  let : (inclusionOver h S hS).IsCocontinuous (overTopology τ B S hS)
      (overTopology τ B' S (largerContains h hS)) :=
    inclusionOver_isCocontinuous B B' h S hS
  let : PreservesFiniteLimits (inclusionOver h S hS) :=
    inclusionOver_preservesFiniteLimits B B' h S hS
  let : EssentiallySmall.{u} (Over (base B S hS)) := essentiallySmall_overBase B S hS
  let : EssentiallySmall.{u} (Over (base B' S (largerContains h hS))) :=
    essentiallySmall_overBase B' S (largerContains h hS)
  exact Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso
    (overTopology τ B S hS) (overTopology τ B' S (largerContains h hS))
    (inclusionOver h S hS) U p

end AlgebraicGeometry

end
