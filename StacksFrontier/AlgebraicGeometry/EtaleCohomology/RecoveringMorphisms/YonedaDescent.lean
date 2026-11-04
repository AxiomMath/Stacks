module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposTwoIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Topos.YonedaDescentPushforward

/-!
# From a comparison of inverse images of affine charts to a comparison of direct images

Let `B` be a big étale site, let `X` and `Y` be schemes of `B`, let

```
  (g, g^♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)
```

be a morphism of ringed topoi and let `a : X ⟶ Y` be a morphism of schemes.  This file performs
step (6) of the proof of [Stacks Project, Tag 04I6]: if the inverse image along `g` of the
representable sheaf `h_V` of an affine chart `V` étale over `Y` is isomorphic to its inverse
image along `a_small`, naturally in `V`, then `g_*` and `a_{small,*}` are isomorphic as functors
`Sh(X_étale) ⥤ Sh(Y_étale)`.

The two inputs are available.  The affine étale charts of `Y` are a dense subsite of its small
étale site, which is [Stacks Project, Tag 04HR]
(`AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous`), so restriction of sheaves
to them is fully faithful; and the small étale topology is subcanonical
(`AlgebraicGeometry.SmallEtale.topology_subcanonical`), so every chart `V` has a representable
sheaf `h_V = AlgebraicGeometry.smallEtaleYoneda.obj V` with no sheafification.  The passage
itself is `MorphismOfTopoi.pushforwardIsoOfInverseImageYonedaIsoOfRestriction`.

## Main results

* `AlgebraicGeometry.smallEtalePushforwardIsoOfInverseImageYonedaIso` — the statement above.

## What this does and does not give for Stacks 04I6

The existence half of Stacks 04I6 asks for a `AlgebraicGeometry.RingedToposHom.TwoIso` between
`(g, g^♯)` and `(a_small, a_small^♯)` for a suitable `a`, i.e. for an isomorphism `e` of the two
direct image functors *together with* the compatibility `g^♯ ≫ e = a_small^♯` of the structure
maps.  This file produces the isomorphism `e` from the comparison on affine charts; it produces
neither the comparison nor the compatibility.

What remains for Stacks 04I6 is therefore, in the numbering of the module documentation of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineCase.lean`:

* step (2) at the level of *sheaves*: the representable `h_V` of an affine `V = Spec C` étale
  over `Y = Spec B` with a standard presentation `C = B[x₁, …, x_n]/(P₁, …, P_n)` as the
  equalizer of two maps `∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y` in `Sheaf(Y_étale)`.  The set-level identification
  and its naturality in the chart are proved
  (`Stacks.EtaleCohomology.homOverEquivSolutions` and
  `Stacks.EtaleCohomology.homOverEquivSolutions_naturality`), and so are the two transfer
  lemmas that turn a sectionwise statement into a limit in a sheaf category
  (`CategoryTheory.Sheaf.isLimitForkOfForallApp`, `CategoryTheory.isLimitFanOfSections`); the
  products `∏ᵢ 𝒪_Y` themselves are not constructed anywhere.
* step (3): the comparison `g⁻¹h_V ⟶ h_{X ×_Y V}` for an abstract `g`, and the identification of
  its stalk with the map of solution sets which [Stacks Project, Tag 04GX]
  (`bijOn_solutions_of_etale`, read on presentations as
  `MvPolynomial.bijective_homOverMap_of_etale`) shows to be bijective.  This is the input `e` of
  the statement below, and it is where the *locally* ringed hypothesis on `(g, g^♯)` is used.
* step (7): the compatibility of the structure maps, which is the `commutes` field of
  `AlgebraicGeometry.RingedToposHom.TwoIso`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}

/-- **Step (6) of the proof of [Stacks Project, Tag 04I6].**  Let `(g, g^♯)` be a morphism of the
small étale ringed topoi of two schemes `X` and `Y` of a big étale site, and let `a : X ⟶ Y` be a
morphism of schemes.  Suppose that for every affine chart `V` étale over `Y` the inverse image
`g⁻¹h_V` of the representable sheaf of `V` is isomorphic to `a_small⁻¹h_V`, naturally in `V`.
Then `g_*` and `a_{small,*}` are isomorphic.

In the source the hypothesis is the composite of its steps (3) and (5): `g⁻¹h_V ≅ h_{X ×_Y V}`,
functorially in `V`, and `a_small⁻¹h_V` is `h_{X ×_Y V}`.  The conclusion is the source's
`f_{small,*} ≅ g_*`, and the argument is the chain
`Γ(V, g_*F) ≅ Mor(h_V, g_*F) ≅ Mor(g⁻¹h_V, F)`, which is
`MorphismOfTopoi.sectionsEquiv`, together with the fact that a sheaf on the small étale site is
determined by its sections over the affine charts, which is [Stacks Project, Tag 04HR].

This is **not** the existence half of Stacks 04I6: that asks for a
`AlgebraicGeometry.RingedToposHom.TwoIso`, which is this isomorphism *together with* the
compatibility of the two structure maps, and it asks for the hypothesis to be *proved* rather
than assumed. See the module documentation. -/
def smallEtalePushforwardIsoOfInverseImageYonedaIso (a : X ⟶ Y)
    (g : RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (e : (SmallAffineEtale.inclusion B Y.obj Y.property ⋙
          smallEtaleYoneda B Y.obj Y.property) ⋙ g.toToposHom.inverseImage ≅
        (SmallAffineEtale.inclusion B Y.obj Y.property ⋙
          smallEtaleYoneda B Y.obj Y.property) ⋙
          (smallEtaleRingedToposHom B a).toToposHom.inverseImage) :
    g.toToposHom.pushforward ≅ (smallEtaleRingedToposHom B a).toToposHom.pushforward :=
  let _hds := (SmallAffineEtale.inclusion_isSpecialCocontinuous B Y.obj Y.property).2
  let := Functor.IsDenseSubsite.isCoverDense
    (SmallAffineEtale.topology B Y.obj Y.property) (SmallEtale.topology B Y.obj Y.property)
    (SmallAffineEtale.inclusion B Y.obj Y.property)
  MorphismOfTopoi.pushforwardIsoOfInverseImageYonedaIsoOfRestriction
    (SmallAffineEtale.inclusion B Y.obj Y.property) e
    (SmallAffineEtale.topology B Y.obj Y.property)

end AlgebraicGeometry

end
