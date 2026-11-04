module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.ChangeOfPartialUniverse
public import StacksCore.Tactic.StacksAttribute

/-!
# Change of partial universe for big pro-étale sites, with sheafification supplied

Let `S` be a scheme and let `(Sch/S)_proétale ⊂ (Sch'/S)_proétale` be two big pro-étale sites
of `S` as in Definition 098K, the first contained in the second.  This file states Stacks 0F4T
for them with no side condition on the sites: the cohomology over an object of the smaller site
of the restriction of an abelian sheaf is its cohomology over that object in the bigger site,
and every abelian sheaf on the smaller site is the restriction of one on the bigger site.

## Main results

* `AlgebraicGeometry.ProEtale.hasSheafify_bigProetaleOver_abelian`: abelian presheaves on a
  big pro-étale site over a scheme, with values in the universe of its morphisms, admit
  sheafification.
* `AlgebraicGeometry.ProEtale.hasExt_sheaf_bigProetaleOver`: abelian sheaves on such a site have
  `Ext`-groups in that universe.
* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.cohomologyPresheafRestrictionIso`:
  Stacks 0F4T (1).
* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.essSurj_abelianRestrictionOver`:
  Stacks 0F4T (2), as essential surjectivity of restriction.

## Implementation notes

Both statements are those of
`AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.cohomologyRestrictionIso` and
`AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.exists_extension_abelianSheaf`, which
are proved from Stacks 0F4S, 00XU and 03YU for sites admitting abelian sheafification.  What is
added is that every localized big pro-étale site does admit it: the site is essentially small
at the universe `u` of its morphisms
(`AlgebraicGeometry.ProEtale.essentiallySmall_bigProetaleOver`, from Stacks 000J), so
sheafification is transported from a small model by Mathlib's
`CategoryTheory.hasSheafifyEssentiallySmallSite`.  That is registered as an instance, so the
statements below have no sheafification binder.

Cohomology over an object is Mathlib's `Ext`-based
`CategoryTheory.Sheaf.cohomologyPresheafFunctor`, which is defined for any universe `w` in which
the `Ext`-groups of the two sheaf categories are small; statement (1) is the comparison in every
such universe.  One such universe always exists, `w = u`, by
`AlgebraicGeometry.ProEtale.hasExt_sheaf_bigProetaleOver`: the sheaf category is Grothendieck
abelian, hence has enough injectives.  That is stated as a theorem rather than an instance,
following Mathlib's `CategoryTheory.hasExt_of_enoughInjectives`, since `Ext`-smallness instances in
two universes at once are not distinguished by instance search.

## References

* [Stacks Project, Tag 0F4T](https://stacks.math.columbia.edu/tag/0F4T)
* [Stacks Project, Tag 0F4S](https://stacks.math.columbia.edu/tag/0F4S)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w

namespace AlgebraicGeometry.ProEtale

/-- **Abelian presheaves on a big pro-étale site over a scheme admit sheafification**, with
values in the universe of the site's morphisms.  The site is essentially small at that universe
(`AlgebraicGeometry.ProEtale.essentiallySmall_bigProetaleOver`), so sheafification is
transported from a small model. -/
instance hasSheafify_bigProetaleOver_abelian (B : BigProetaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasSheafify (BigProetaleOver.topology B S hS) Ab.{u} :=
  letI : EssentiallySmall.{u} (BigProetaleOver B S hS) := essentiallySmall_bigProetaleOver B S hS
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- **Abelian sheaves on a big pro-étale site over a scheme have `Ext`-groups in the universe of
the site's morphisms.**  The sheaf category is Grothendieck abelian, the site being essentially
small, so it has enough injectives and its hom-types are small at that universe. -/
theorem hasExt_sheaf_bigProetaleOver (B : BigProetaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasExt.{u} (Sheaf (BigProetaleOver.topology B S hS) Ab.{u}) := by
  let : EssentiallySmall.{u} (BigProetaleOver B S hS) := essentiallySmall_bigProetaleOver B S hS
  let := Stacks.Cohomology.BiggerSite.isGrothendieckAbelian_sheaf (BigProetaleOver.topology B S hS)
  exact hasExt_of_enoughInjectives.{u} _

namespace BigProetaleSite.IsContainedIn

variable {B B' : BigProetaleSite.{u}} (h : B.IsContainedIn B')
  (S : AlgebraicGeometry.Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0F4T (1).** Let `S` be a scheme and let `(Sch/S)_proétale` and
`(Sch'/S)_proétale` be two big pro-étale sites of `S` as in Definition 098K, the first contained
in the second.  For any object `U` of `(Sch/S)_proétale` and any degree `p`,

`H^p(U, ℱ'|_{(Sch/S)_proétale}) = H^p(U, ℱ')`

naturally in the abelian sheaf `ℱ'` on `(Sch'/S)_proétale`, where cohomology over an object is
Mathlib's `Ext`-based `CategoryTheory.Sheaf.cohomologyPresheafFunctor` with values in any
universe `w` where the `Ext`-groups of the two sheaf categories are small (for instance `w = u`,
by `AlgebraicGeometry.ProEtale.hasExt_sheaf_bigProetaleOver`).

Sheafification on both sites is `AlgebraicGeometry.ProEtale.hasSheafify_bigProetaleOver_abelian`,
and the comparison is
`AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.cohomologyRestrictionIso`. -/
@[stacks 0F4T "part (1), the cohomology over an object of the smaller big pro-étale site of the
  restriction of an abelian sheaf on the bigger site agrees with the cohomology of that sheaf
  over the same object in the bigger site, naturally in the sheaf, for every degree"]
noncomputable def cohomologyPresheafRestrictionIso
    [HasExt.{w} (Sheaf (BigProetaleOver.topology B S hS) Ab.{u})]
    [HasExt.{w} (Sheaf (BigProetaleOver.topology B' S (h.contains hS)) Ab.{u})]
    (U : BigProetaleOver B S hS) (p : ℕ) :
    (h.functorOver S hS).sheafPushforwardContinuous Ab.{u}
          (BigProetaleOver.topology B S hS)
          (BigProetaleOver.topology B' S (h.contains hS)) ⋙
        Sheaf.cohomologyPresheafFunctor (BigProetaleOver.topology B S hS) p ⋙
          (evaluation (BigProetaleOver B S hS)ᵒᵖ Ab.{w}).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor (BigProetaleOver.topology B' S (h.contains hS)) p ⋙
        (evaluation (BigProetaleOver B' S (h.contains hS))ᵒᵖ Ab.{w}).obj
          (op ((h.functorOver S hS).obj U)) :=
  h.cohomologyRestrictionIso S hS U p

/-- **Stacks 0F4T (2).** Let `S` be a scheme and let `(Sch/S)_proétale` and
`(Sch'/S)_proétale` be two big pro-étale sites of `S` as in Definition 098K, the first contained
in the second.  Restriction of abelian sheaves from `(Sch'/S)_proétale` to `(Sch/S)_proétale` is
essentially surjective: for any abelian sheaf `ℱ` on `(Sch/S)_proétale` there is an abelian
sheaf `ℱ'` on `(Sch'/S)_proétale` whose restriction to `(Sch/S)_proétale` is isomorphic to `ℱ`.

The witness is the sheaf pullback along the inclusion, which exists by
`AlgebraicGeometry.ProEtale.hasSheafify_bigProetaleOver_abelian`; this is
`AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.exists_extension_abelianSheaf`. -/
@[stacks 0F4T "part (2), restriction of abelian sheaves from the bigger big pro-étale site to
  the smaller one is essentially surjective: every abelian sheaf on the smaller site is
  isomorphic to the restriction of an abelian sheaf on the bigger site"]
instance essSurj_abelianRestrictionOver : (h.abelianRestrictionOver S hS).EssSurj :=
  ⟨fun F => h.exists_extension_abelianSheaf S hS F⟩

end BigProetaleSite.IsContainedIn

end AlgebraicGeometry.ProEtale

end
