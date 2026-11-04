module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint

/-!
# The stalk of a higher direct image is the stalk of the cohomology presheaf

Let `B` be a big étale site, let `f : X ⟶ Y` be a morphism of its schemes and let `s` be a
geometric point of `Y`. By [Stacks, Tag 03Q8] the higher direct image `R^p f_* ℱ` is the
sheafification of the presheaf `V ↦ H^p_ét(X ×_Y V, ℱ)`, and a stalk is unchanged by
sheafification, so

`(R^p f_* ℱ)_s = colim_{(V, v)} H^p_ét(X ×_Y V, ℱ)`,

the colimit being over the étale neighbourhoods of `s`. This is the first step of the proof of
[Stacks, Tag 03Q9]; the implementation notes say what that tag still needs on top of it.

## Main results

* `Stacks.HigherDirectImage.higherDirectImageStalkIsoCohomologyPresheafStalk` — the stalk at `s`
  of `R^p f_*` is the stalk at `s` of the cohomology presheaf, naturally in the abelian sheaf.
* `Stacks.HigherDirectImage.higherDirectImageEtaleStalkIsoCohomologyStalk` — the same at a fixed
  sheaf, written with `AlgebraicGeometry.etaleStalk` on both sides.

## Implementation notes

The stalk at a geometric point is the fibre functor of the point
`AlgebraicGeometry.geometricPointSitePoint` of the small étale site, by
`AlgebraicGeometry.etaleStalk_eq_presheafFiber`; invariance of a stalk under sheafification is
then `CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`. The values of
the cohomology presheaf are the cohomology groups of the fibre products, by the existing
`Stacks.HigherDirectImage.preimageCohomologyPresheafEvaluationIso`, and its restriction maps are
the derived restriction maps of sections, by the `restriction` field of
`Stacks.HigherDirectImage.HigherDirectImageComparison`. So the right-hand side is the colimit of
the diagram of cohomology groups of the `X ×_Y V` with their restriction maps.

[Stacks, Tag 03Q9] turns that colimit into the single cohomology group
`H^p_ét(X ×_Y Spec(𝒪^{sh}_{Y,s}), p^{-1}ℱ)`, using that `X ×_Y Spec(𝒪^{sh}_{Y,s})` is the limit
of the `X ×_Y V` — which is
`AlgebraicGeometry.isLimitStrictHenselizationBaseChangeCone` — and Tag 03Q6, that étale
cohomology carries such a limit of schemes to the colimit of the cohomology groups. Tag 03Q6 is
in the library only for an affine `X` over an affine base, and only for a system of abelian
sheaves given on the levels rather than pulled back from one sheaf on `X`; so that last step is
not available here, and nothing below assumes it.

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 04FM](https://stacks.math.columbia.edu/tag/04FM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.HigherDirectImage

universe u w

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (s : GeometricPoint Y.obj) [HasColimitsOfSize.{u, u} AddCommGrpCat.{w}]
  [HasProducts.{u} AddCommGrpCat.{w}]
  [HasSheafify (JX B (X := X)) AddCommGrpCat.{w}]
  [HasSheafify (JY B (Y := Y)) AddCommGrpCat.{w}]
  [HasInjectiveResolutions (Sheaf (JX B (X := X)) AddCommGrpCat.{w})]

/-- **The first step of the proof of [Stacks, Tag 03Q9].** The stalk at a geometric point `s` of
`Y` of the `p`-th higher direct image along `f : X ⟶ Y` is the stalk at `s` of the presheaf
`V ↦ H^p_ét(X ×_Y V, ℱ)`, naturally in the abelian sheaf `ℱ`: the higher direct image is the
sheafification of that presheaf by [Stacks, Tag 03Q8], and sheafification does not change a
stalk. -/
def higherDirectImageStalkIsoCohomologyPresheafStalk (p : ℕ) :
    (pushforward.{u, w} B f).rightDerived p ⋙
        (geometricPointSitePoint B Y.obj Y.property s).sheafFiber ≅
      (preimageSectionsPresheaf.{u, w} B f).rightDerived p ⋙
        (geometricPointSitePoint B Y.obj Y.property s).presheafFiber :=
  Functor.isoWhiskerRight (higherDirectImageComparison B f p).iso _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((geometricPointSitePoint B Y.obj Y.property s).presheafToSheafCompSheafFiberIso
        AddCommGrpCat.{w})

/-- **The first step of the proof of [Stacks, Tag 03Q9]**, at a fixed abelian sheaf and with both
sides written as stalks at the geometric point: the stalk of `R^p f_* ℱ` is the stalk of the
cohomology presheaf `V ↦ H^p_ét(X ×_Y V, ℱ)`, whose value at a neighbourhood is identified with
that cohomology group by
`Stacks.HigherDirectImage.preimageCohomologyPresheafEvaluationIso`. -/
@[sga "4 VIII 5.1" "partial", sga "4½ Arcata 2.3.3"]
def higherDirectImageEtaleStalkIsoCohomologyStalk
    (F : Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (p : ℕ) :
    etaleStalk B Y.obj Y.property s
        (((pushforward.{u, w} B f).rightDerived p).obj F).obj ≅
      etaleStalk B Y.obj Y.property s (preimageCohomologyPresheaf B f F p) :=
  (higherDirectImageStalkIsoCohomologyPresheafStalk B f s p).app F

end Stacks.HigherDirectImage

end
