module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a higher direct image over the étale neighbourhoods of a geometric point

Let `f : X ⟶ Y` be a morphism of a big étale site, let `F` be an abelian sheaf on the small
étale site of `X` and let `s` be a geometric point of `Y`. Stacks 03Q8 identifies `R^p f_* F`
with the sheafification of the presheaf `V ↦ H^p_ét(X ×_Y V, F)` on the small étale site of `Y`.
Taking stalks at `s` and using that sheafification does not change a stalk, the stalk of
`R^p f_* F` at `s` is the stalk of that cohomology presheaf, that is

`(R^p f_* F)_s = colim_{(V, v)} H^p_ét(X ×_Y V, F)`

over the étale neighbourhoods of `s`. This is the first display in the proof of Stacks 03Q9,
where the source attributes it to Lemma 03Q8.

## Main results

* `Stacks.HigherDirectImage.higherDirectImageStalkCohomologyPresheafIso` — the stalk at `s` of
  the `p`-th higher direct image is the stalk at `s` of the cohomology presheaf, hence the
  colimit of `H^p_ét(X ×_Y V, F)` over the étale neighbourhoods of `s`.
* `Stacks.HigherDirectImage.cohomologyPresheafStalkDiagramObjIso` — the term of that colimit at
  a neighbourhood `V` is the cohomology group `H^p_ét(X ×_Y V, F)`.

## Implementation notes

The stalk is `AlgebraicGeometry.etaleStalk`, the colimit of the restriction of a presheaf to the
category of elements of `AlgebraicGeometry.geometricPointFiber` — the category of étale
neighbourhoods of `s`. That the sheafification unit induces an isomorphism on it is
`AlgebraicGeometry.isIso_etaleStalk_map_toSheafify`, through the identification of the stalk
with the fibre of the point `AlgebraicGeometry.geometricPointSitePoint` of the small étale site.

No hypothesis is placed on `f`, on `Y` or on `s`: the base is arbitrary, and so is the geometric
point. What this does *not* supply, and what Stacks 03Q9 needs on top of it, is the comparison of
this colimit with the cohomology of the base change of `X` to `Spec(𝒪^{sh}_{Y,s})` — Stacks 03Q6,
étale cohomology commuting with the limit of the étale neighbourhoods. The geometry of that limit
is available as `AlgebraicGeometry.strictHenselizationConeIsLimit`; the cohomological statement
is not, and the discussion in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianDirectImageStalk` records exactly
which two steps of it are missing.

*Which framework this is in.* The stalk here is the big-étale-site one, `etaleStalk`, because that
is the framework the Stacks 03Q8 carrier and `etaleStalkSheafificationIso` are stated in. The
comparison map of Stacks 03Q9 itself — `(R f_* K)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)`, Stacks
0GIX, built in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward` as
`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections` — is instead stated with
the stalk `Stacks.EtaleCohomology.smallEtaleStalkAb` of the mainstream small étale site, which is
also the framework its consumers use. So the eventual unrestricted Stacks 03Q9 is most naturally
the assertion that *that* map is an isomorphism, and reaching it from the colimit formula here
needs a comparison of the two stalk notions. Both halves of that comparison are now available:
the direct images are compared by
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`, and the stalks by
`AlgebraicGeometry.sheafEquivCompSmallEtaleStalkAbIso` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkFrameworkBridge`, which identifies
`Stacks.EtaleCohomology.smallEtaleStalkAb`, read through the identification
`AlgebraicGeometry.SmallEtale.sheafEquiv` of the two sheaf categories, with the bounded site's own
`AlgebraicGeometry.etaleStalkFunctorAbelian`. What remains unavailable for the unrestricted tag is
Stacks 03Q6 in a consumable shape, as described above.

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u w

namespace Stacks.HigherDirectImage

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (s : GeometricPoint Y.obj)

variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{w}] [HasProducts.{u} AddCommGrpCat.{w}]
  [HasSheafify (JX B (X := X)) AddCommGrpCat.{w}]
  [HasSheafify (JY B (Y := Y)) AddCommGrpCat.{w}]
  [HasInjectiveResolutions (Sheaf (JX B (X := X)) AddCommGrpCat.{w})]

/-- **Stacks 03Q8 at a geometric point.** The stalk at `s` of the `p`-th higher direct image of
`F` along `f` is the stalk at `s` of the cohomology presheaf `V ↦ H^p_ét(X ×_Y V, F)`, which by
definition of the stalk is the colimit of that presheaf over the étale neighbourhoods of `s`.

This is the objectwise comparison of Stacks 03Q8, `higherDirectImageSheafificationIso`, followed
by the invariance of a stalk under sheafification,
`AlgebraicGeometry.etaleStalkSheafificationIso`. -/
@[stacks 03Q8 "the stalk form: the stalk at a geometric point `s` of `R^p f_* F` is the stalk \
at `s` of the cohomology presheaf `V ↦ H^p(X ×_Y V, F)`, hence the colimit of that presheaf \
over the étale neighbourhoods of `s`. This is the first display in the source's proof of Stacks \
03Q9, which the source attributes to this tag. The base, the morphism `f` and the geometric \
point are arbitrary. It is NOT Stacks 03Q9: that tag identifies the colimit with the cohomology \
of the base change of `X` to `Spec(O^{sh}_{Y,s})`, which is Stacks 03Q6 and is not available in \
a consumable shape", sga "4 VIII 5.1" "partial", sga "4½ Arcata 2.3.3"]
public def higherDirectImageStalkCohomologyPresheafIso
    (F : Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (p : ℕ) :
    etaleStalk B Y.obj Y.property s (((pushforward.{u, w} B f).rightDerived p).obj F).obj ≅
      etaleStalk B Y.obj Y.property s (preimageCohomologyPresheaf.{u, w} B f F p) :=
  HasColimit.isoOfNatIso (Functor.isoWhiskerLeft
    (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op
    ((sheafToPresheaf (JY B (Y := Y)) AddCommGrpCat.{w}).mapIso
      (higherDirectImageSheafificationIso B f F p))) ≪≫
    etaleStalkSheafificationIso B Y.obj Y.property s (preimageCohomologyPresheaf.{u, w} B f F p)

/-- The term at an étale neighbourhood `V` of `s` of the colimit computing the stalk is the
cohomology group `H^p_ét(X ×_Y V, F)`. Together with
`higherDirectImageStalkCohomologyPresheafIso` this is the display
`(R^p f_* F)_s = colim_{(V, v)} H^p_ét(X ×_Y V, F)`. -/
public def cohomologyPresheafStalkDiagramObjIso
    (F : Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (p : ℕ)
    (V : (geometricPointFiber B Y.obj Y.property s).Elementsᵒᵖ) :
    ((Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op ⋙
        preimageCohomologyPresheaf.{u, w} B f F p).obj V ≅
      ((sectionsOnPreimage.{u, w} B f V.unop.1).rightDerived p).obj F :=
  preimageCohomologyPresheafEvaluationIso B f F V.unop.1 p

end Stacks.HigherDirectImage

end
