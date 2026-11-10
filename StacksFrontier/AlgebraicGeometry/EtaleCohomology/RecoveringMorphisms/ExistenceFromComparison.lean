module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposTwoIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Topos.PushforwardRepresentableComparison

/-!
# The existence half of Stacks 04I6, reduced to the comparison of inverse images of representables

Let `X` and `Y` be schemes of a big étale site and let `(g, g^♯)` be a morphism of their small
étale ringed topoi.  The existence half of [Stacks Project, Tag 04I6] asks for a morphism of
schemes `f : X ⟶ Y` with `(g, g^♯)` 2-isomorphic to `(f_small, f_small^♯)`.

This file carries out the last two steps of the source's proof, taking as given the two
geometric inputs that the source produces from the étale equations:

* a comparison `α : g⁻¹h_V ≅ h_{X ×_Y V}`, natural in the étale chart `V` of `Y` — the source's
  `g^{-1}h_V \to h_{X\times_Y V}`, shown there to be an isomorphism by a stalk computation; and
* the agreement of the two structure maps under the isomorphism of direct images that `α`
  produces — the source's closing paragraph.

Given those, the conclusion is Stacks 04I6 in full: a morphism of schemes `f` exists with
`(g, g^♯)` 2-isomorphic to `(f_small, f_small^♯)`, and it is unique, the uniqueness being the
already proved `AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom`.

This file does **not** prove Stacks 04I6 and carries no `@[stacks 04I6]` tag: `α` and the
agreement of the two structure maps are hypotheses here.  Relative to the source's proof what this
file supplies is step (4); the construction of `α` is step (3), and both it and the agreement of
the structure maps are discharged in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineExistence.lean`, where
the tag is proved.

## Main definitions

* `AlgebraicGeometry.pushforwardIsoOfRepresentableComparison` — the isomorphism of direct images
  `g_* ≅ f_{small,*}` which the comparison `α` produces.
* `AlgebraicGeometry.twoIsoOfPushforwardIso` — the 2-isomorphism of ringed topoi
  `(g, g^♯) ≅ (f_small, f_small^♯)` obtained from the isomorphism of direct images by adding the
  agreement of the structure maps.
* `AlgebraicGeometry.twoIsoOfRepresentableComparison` — the same with the isomorphism of direct
  images produced from `α`.

## Main results

* `AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_pushforwardIso` — the `∃!` statement of
  Stacks 04I6, with the isomorphism of direct images supplied.  This is the form the affine-chart
  route consumes, since that route produces `g_* ≅ f_{small,*}` without producing a comparison of
  representables at an arbitrary chart.
* `AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_representableComparison` — the same with
  the comparison `α` supplied.  No affineness is used: affineness enters the source only in
  producing `α`.

## Implementation notes

The direct image of `(f_small, f_small^♯)` is, definitionally, the direct image of the
continuous functor `AlgebraicGeometry.smallEtaleBaseChange B f` of small étale sites
(`AlgebraicGeometry.smallEtaleRingedToposHom_pushforward`), which is what lets the general
`MorphismOfTopoi.pushforwardIsoSheafPushforwardContinuous` be applied here: the functor `u` of
that statement is small étale base change, and `u V` is `X ×_Y V`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04LW](https://stacks.math.columbia.edu/tag/04LW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (f : X ⟶ Y)

/-- The comparison datum of step (3) of the proof of Stacks 04I6: the inverse image along `g` of
the sheaf represented by an étale chart `V` of `Y` is the sheaf represented by the étale chart
`X ×_Y V` of `X`, naturally in `V`. -/
abbrev RepresentableComparison : Type (u + 1) :=
  (SmallEtale.topology B Y.obj Y.property).yoneda ⋙ g.toToposHom.inverseImage ≅
    smallEtaleBaseChange B f ⋙ (SmallEtale.topology B X.obj X.property).yoneda

/-- Small étale base change is continuous for the two topologies spelled as those of the ringed
topoi of the small étale ringed sites, which is how they appear in the direct image of
`(f_small, f_small^♯)`.  The two spellings are the same topology, but instance search does not
see through `AlgebraicGeometry.RingedSite.toRingedTopos`. -/
instance smallEtaleRingedSiteHom_u_isContinuous :
    (smallEtaleRingedSiteHom B f).u.IsContinuous
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).J
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).J :=
  inferInstanceAs ((smallEtaleBaseChange B f).IsContinuous
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property))

/-- **The isomorphism of direct images produced by the comparison of representables.**  If
`g⁻¹h_V ≅ h_{X ×_Y V}` naturally in the étale chart `V`, then `g_* ≅ f_{small,*}`.

This is the Yoneda computation at the end of the proof of Stacks 04I6: the sections of `g_*ℱ`
over `V` are the maps `g⁻¹h_V ⟶ ℱ`, hence the maps `h_{X ×_Y V} ⟶ ℱ`, hence the sections of `ℱ`
over `X ×_Y V`, which are the sections of `f_{small,*}ℱ` over `V`. -/
def pushforwardIsoOfRepresentableComparison (α : RepresentableComparison B g f) :
    g.toToposHom.pushforward ≅ (smallEtaleRingedToposHom B f).toToposHom.pushforward :=
  g.toToposHom.pushforwardIsoSheafPushforwardContinuous α

/-- **The 2-isomorphism of ringed topoi of Stacks 04I6, from an isomorphism of direct images.**
The comparison of representables is used only through the isomorphism `g_* ≅ f_{small,*}` which
it produces, so this is the form in which the source's closing paragraph is consumed: the
hypothesis `hcomm` is that the two structure maps agree under the given isomorphism.

This form is what the affine-chart route needs, where `g_* ≅ f_{small,*}` is obtained from the
comparison of representables at the *affine* étale charts alone and no comparison at an arbitrary
chart is available; see `AlgebraicGeometry.pushforwardIsoOfAffineRepresentableComparison`. -/
def twoIsoOfPushforwardIso
    (e : g.toToposHom.pushforward ≅ (smallEtaleRingedToposHom B f).toToposHom.pushforward)
    (hcomm : RingedToposHom.forgetFSharp g ≫
        e.hom.app
          ((RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).forgetRing.obj
            (RingedSite.toRingedTopos
              (smallEtaleRingedSite B X.obj X.property)).O) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B f)) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B f) where
  e := e
  commutes := hcomm

/-- **The existence half of Stacks 04I6, with the isomorphism of direct images supplied.**  Let
`(g, g^♯)` be a morphism of the small étale ringed topoi of two schemes of a big étale site.  If
some morphism of schemes `f : X ⟶ Y` admits an isomorphism `g_* ≅ f_{small,*}` under which the
two structure maps agree, then `f` is the unique morphism of schemes whose associated morphism of
small étale ringed topoi is 2-isomorphic to `(g, g^♯)`.

Uniqueness is `AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom`, i.e. Stacks 04LW, and
needs no hypothesis.  What the hypotheses buy is existence. -/
theorem existsUnique_schemeHom_twoIso_of_pushforwardIso
    (e : g.toToposHom.pushforward ≅ (smallEtaleRingedToposHom B f).toToposHom.pushforward)
    (hcomm : RingedToposHom.forgetFSharp g ≫
        e.hom.app
          ((RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).forgetRing.obj
            (RingedSite.toRingedTopos
              (smallEtaleRingedSite B X.obj X.property)).O) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B f)) :
    ∃! a : X ⟶ Y,
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
        (smallEtaleRingedToposHom B a)) :=
  ⟨f, ⟨twoIsoOfPushforwardIso B g f e hcomm⟩, fun a ha =>
    eq_of_twoIso_smallEtaleRingedToposHom B g a f ha.some
      (twoIsoOfPushforwardIso B g f e hcomm)⟩

/-- **The 2-isomorphism of ringed topoi of Stacks 04I6.**  The comparison of representables makes
the two direct images isomorphic, and the hypothesis `hcomm` is the source's closing step, that
the two structure maps agree under that isomorphism. -/
def twoIsoOfRepresentableComparison (α : RepresentableComparison B g f)
    (hcomm : RingedToposHom.forgetFSharp g ≫
        (pushforwardIsoOfRepresentableComparison B g f α).hom.app
          ((RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).forgetRing.obj
            (RingedSite.toRingedTopos
              (smallEtaleRingedSite B X.obj X.property)).O) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B f)) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B f) :=
  twoIsoOfPushforwardIso B g f (pushforwardIsoOfRepresentableComparison B g f α) hcomm

/-- **The existence half of Stacks 04I6, with the comparison of representables supplied.**  Let
`(g, g^♯)` be a morphism of the small étale ringed topoi of two schemes of a big étale site.  If
some morphism of schemes `f : X ⟶ Y` admits a comparison `g⁻¹h_V ≅ h_{X ×_Y V}`, natural in the
étale chart `V`, under which the two structure maps agree, then `f` is the unique morphism of
schemes whose associated morphism of small étale ringed topoi is 2-isomorphic to `(g, g^♯)`.

Uniqueness is `AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom`, i.e. Stacks 04LW, and
needs no hypothesis.  What the hypotheses buy is existence.

This is not a proof of Stacks 04I6: `α` and `hcomm` are hypotheses here.  For an affine `Y` and
locally ringed `(g, g^♯)` both are constructed, at the affine charts, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineExistence.lean`, which
is
where the tag is proved. -/
theorem existsUnique_schemeHom_twoIso_of_representableComparison
    (α : RepresentableComparison B g f)
    (hcomm : RingedToposHom.forgetFSharp g ≫
        (pushforwardIsoOfRepresentableComparison B g f α).hom.app
          ((RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).forgetRing.obj
            (RingedSite.toRingedTopos
              (smallEtaleRingedSite B X.obj X.property)).O) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B f)) :
    ∃! a : X ⟶ Y,
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
        (smallEtaleRingedToposHom B a)) :=
  existsUnique_schemeHom_twoIso_of_pushforwardIso B g f
    (pushforwardIsoOfRepresentableComparison B g f α) hcomm

end AlgebraicGeometry

end
