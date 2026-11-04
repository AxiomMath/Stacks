module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineChartNatIsoTransport
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ExistenceFromComparison
public import StacksFrontier.CategoryTheory.Sites.Topos.PushforwardDenseSubsiteComparison

/-!
# Existence of a morphism of schemes from a comparison at the affine étale charts

Let `X` and `Y` be schemes of a big étale site, `(g, g^♯)` a morphism of their small étale ringed
topoi and `f : X ⟶ Y`. A comparison `g⁻¹h_V ≅ h_{X ×_Y V}` natural in the affine étale charts `V`
of `Y` gives an isomorphism of direct images `g_* ≅ f_{small,*}`, the small affine étale site
being a dense subsite of the small étale site ([Stacks Project, Tag 04HR]). If the two structure
maps agree under it, `f` is the unique morphism of schemes whose morphism of small étale ringed
topoi is 2-isomorphic to `(g, g^♯)`.

## Main definitions

* `AlgebraicGeometry.AffineRepresentableComparison` — the comparison datum at the affine étale
  charts of `Y`: `g⁻¹h_V ≅ h_{X ×_Y V}`, naturally in the *affine* chart `V`.
* `AlgebraicGeometry.pushforwardIsoOfAffineRepresentableComparison` — the isomorphism of direct
  images `g_* ≅ f_{small,*}` it produces.
* `AlgebraicGeometry.AffineRepresentableComparison.ofRepresentableComparison` — the restriction
  of a comparison at every chart to the affine charts.

## Main results

* `AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_affineRepresentableComparison` — the `∃!`
  statement of the existence half of Stacks 04I6, with the comparison supplied at the affine
  charts only.
* `AlgebraicGeometry.pushforwardIsoOfAffineRepresentableComparison_ofRepresentableComparison` —
  on a comparison available at every chart, the isomorphism of direct images from its restriction
  to the affine charts is `AlgebraicGeometry.pushforwardIsoOfRepresentableComparison`.

## References

* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
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

/-- **The comparison datum at the affine charts.**  An isomorphism between the inverse image along
`g` of the sheaf represented by an *affine* étale chart `V` of `Y` and the sheaf represented by the
étale chart `X ×_Y V` of `X`, natural in `V`: `AlgebraicGeometry.RepresentableComparison`
restricted along the inclusion of the small affine étale site. -/
abbrev AffineRepresentableComparison : Type (u + 1) :=
  SmallAffineEtale.inclusion B Y.obj Y.property ⋙
      (SmallEtale.topology B Y.obj Y.property).yoneda ⋙ g.toToposHom.inverseImage ≅
    SmallAffineEtale.inclusion B Y.obj Y.property ⋙
      smallEtaleBaseChange B f ⋙ (SmallEtale.topology B X.obj X.property).yoneda

/-- The restriction of a comparison of representables at every étale chart of `Y` to the affine
charts. -/
def AffineRepresentableComparison.ofRepresentableComparison
    (α : RepresentableComparison B g f) : AffineRepresentableComparison B g f :=
  Functor.isoWhiskerLeft (SmallAffineEtale.inclusion B Y.obj Y.property) α

/-- **The isomorphism of direct images produced by the comparison of representables at the affine
charts.**  If `g⁻¹h_V ≅ h_{X ×_Y V}` naturally in the *affine* étale chart `V`, then
`g_* ≅ f_{small,*}`. -/
def pushforwardIsoOfAffineRepresentableComparison (α : AffineRepresentableComparison B g f) :
    g.toToposHom.pushforward ≅ (smallEtaleRingedToposHom B f).toToposHom.pushforward :=
  g.toToposHom.pushforwardIsoSheafPushforwardContinuousOfDenseSubsite
    (SmallAffineEtale.topology B Y.obj Y.property) α

/-- **On a comparison available at every chart, the affine route gives the same isomorphism of
direct images as `AlgebraicGeometry.pushforwardIsoOfRepresentableComparison`.** -/
theorem pushforwardIsoOfAffineRepresentableComparison_ofRepresentableComparison
    (α : RepresentableComparison B g f) :
    pushforwardIsoOfAffineRepresentableComparison B g f
        (AffineRepresentableComparison.ofRepresentableComparison B g f α) =
      pushforwardIsoOfRepresentableComparison B g f α :=
  MorphismOfTopoi.pushforwardIsoSheafPushforwardContinuousOfDenseSubsite_isoWhiskerLeft
    g.toToposHom (SmallAffineEtale.topology B Y.obj Y.property) α

/-- **Existence of the morphism of schemes, with the comparison of representables supplied at the
affine charts only.**  Let `(g, g^♯)` be a morphism of the small étale ringed topoi of two schemes
of a big étale site.  If some morphism of schemes `f : X ⟶ Y` admits a comparison
`g⁻¹h_V ≅ h_{X ×_Y V}`, natural in the *affine* étale chart `V` of `Y`, under which the two
structure maps agree, then `f` is the unique morphism of schemes whose associated morphism of
small étale ringed topoi is 2-isomorphic to `(g, g^♯)`. -/
theorem existsUnique_schemeHom_twoIso_of_affineRepresentableComparison
    (α : AffineRepresentableComparison B g f)
    (hcomm : RingedToposHom.forgetFSharp g ≫
        (pushforwardIsoOfAffineRepresentableComparison B g f α).hom.app
          ((RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).forgetRing.obj
            (RingedSite.toRingedTopos
              (smallEtaleRingedSite B X.obj X.property)).O) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B f)) :
    ∃! a : X ⟶ Y,
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
        (smallEtaleRingedToposHom B a)) :=
  existsUnique_schemeHom_twoIso_of_pushforwardIso B g f
    (pushforwardIsoOfAffineRepresentableComparison B g f α) hcomm

end AlgebraicGeometry

end
