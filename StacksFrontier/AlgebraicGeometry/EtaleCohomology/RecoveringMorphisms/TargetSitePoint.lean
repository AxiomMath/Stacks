module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackAtAPointPair
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.LocallyRingedGeometricStalk
public import StacksFrontier.CategoryTheory.Sites.Point.OfToposPoint
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# The point of the target site attached to a point of the source

Let `(f, f♯) : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi and let `Φ` be a point
of the site `(C, J)`.  Composing the morphism of topoi `Sh(pt) ⟶ Sh(C)` of Stacks 00YA (1) with
`f` gives a point of the *topos* `Sh(D)`, and by Stacks 00YA (2) that point comes from a point
`Ψ` of the *site* `(D, K)`, together with an identification `Ψ⁻¹ ≅ f⁻¹ ⋙ Φ⁻¹` of stalk functors
on sheaves of sets.

That pair `(Ψ, e)` is exactly the datum which
`Stacks.Sheaves.StalkInverseImage.stalkRingEquiv` and
`Stacks.Sheaves.StalkPullback.commRingStalkEquiv` take as a hypothesis, so this file turns those
statements into unconditional ones for a site whose underlying category is essentially small —
the small étale site of a scheme is one.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.targetSitePoint` — the point `Ψ` of the target site.
* `AlgebraicGeometry.RingedToposHom.targetSitePointIso` — the identification `Ψ⁻¹ ≅ f⁻¹ ⋙ Φ⁻¹`.
* `AlgebraicGeometry.RingedToposHom.targetStalkRingEquiv` — the induced isomorphism
  `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of stalk rings.
* `AlgebraicGeometry.RingedToposHom.targetStalkRingMap` — the induced homomorphism
  `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings.

## Main results

* `AlgebraicGeometry.RingedToposHom.isLocalHom_targetStalkRingMap` — for a morphism of
  *locally* ringed topoi the homomorphism `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings is local.
* `AlgebraicGeometry.strictlyHenselianLocalRing_targetStalkRing` — for the small étale ringed
  topoi of two schemes both stalk rings are strictly henselian, so the hypotheses of
  Stacks 04GX are available at `𝒪'_Ψ ⟶ 𝒪_Φ`.
* `AlgebraicGeometry.bijective_homOverMap_targetStalkRingMap` — **Stacks 04GX at the stalks of
  a locally ringed morphism of small étale ringed topoi**: the map of points of a standard étale
  presentation induced by `𝒪'_Ψ ⟶ 𝒪_Φ` is bijective.

## Implementation notes

The reconstruction of a point of the site from a point of the topos,
`CategoryTheory.PointOfTopos.sitePointOfEssentiallySmall`, asks for the underlying category of
the site to be `CategoryTheory.EssentiallySmall` at the universe of the sheaves, not
`CategoryTheory.Small`; the small étale site of a scheme of a big étale site satisfies this.

The locality of `𝒪'_Ψ ⟶ 𝒪_Φ` factors as locality of the isomorphism `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ`, which
is automatic, composed with locality of the stalk at `Φ` of the inverse-image form of the
structure map, which is Stacks 04H9 in the direction (1) ⇒ (3) followed by
`AlgebraicGeometry.RingedTopos.isLocalHom_sheafFiber_of_reflectsUnitsObj`.  The stalk of the
structure map appears in two spellings — `Stacks.Sheaves.StalkPullback.fSharpStalk`, which is
the stalk of the map of presheaves of commutative rings, and
`(Φ.sheafFiber (A := CommRingCat)).map f.fSharpInverseImage`, which is the stalk functor applied
to the morphism of sheaves — and the two are identified by
`Stacks.Sheaves.StalkPullback.fSharpStalk_commRingPresheafFiberIso_ringStalkComparison`.

## References

* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedToposHom

universe w v u v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C]

/-- The point of the topos `Sh(D)` obtained by composing the point of the topos `Sh(C)` that a
point `Φ` of the site `(C, J)` defines (Stacks 00YA (1)) with the morphism of topoi underlying
`f`. -/
def toposPointComp (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) :
    PointOfTopos.{w, v', u'} Y.J :=
  MorphismOfTopoi.comp f.toToposHom Φ.pointOfTopos

omit [LocallySmall.{w} Y.C] in
/-- The inverse image of `AlgebraicGeometry.RingedToposHom.toposPointComp` is the inverse image
along `f` followed by the stalk functor of `Φ`. -/
theorem toposPointComp_inverseImage (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) :
    (f.toposPointComp Φ).inverseImage =
      f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w) :=
  rfl

variable [EssentiallySmall.{w} Y.C] [HasSheafify Y.J (Type w)]

/-- **Stacks 00YA (2) along a morphism of ringed topoi.** The point of the target site `(D, K)`
whose stalk functor is the inverse image along `f` followed by the stalk functor of the point
`Φ` of the source site. -/
@[stacks 00YA "(2), applied to the composite of a point of the source site with a morphism of
  ringed topoi"]
def targetSitePoint (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) : Y.J.Point.{w} :=
  (f.toposPointComp Φ).sitePointOfEssentiallySmall

/-- The stalk functor of `AlgebraicGeometry.RingedToposHom.targetSitePoint` on sheaves of sets
is the inverse image along `f` followed by the stalk functor of `Φ`. -/
def targetSitePointIso (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) :
    (f.targetSitePoint Φ).sheafFiber (A := Type w) ≅
      f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w) :=
  (f.toposPointComp Φ).sheafFiberIsoInverseImageOfEssentiallySmall

/-- **The isomorphism `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of stalk rings**, at the point `Ψ` of the target site
reconstructed from `Φ`. -/
def targetStalkRingEquiv [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) :
    Stacks.ringFiber (f.targetSitePoint Φ) Y.O.obj ≃+*
      Stacks.ringFiber Φ
        (Stacks.Sheaves.StalkPullback.inverseImageStructure f.toRingedToposModulesHom) :=
  Stacks.Sheaves.StalkPullback.commRingStalkEquiv f.toRingedToposModulesHom Φ
    (f.targetSitePoint Φ) (f.targetSitePointIso Φ)

/-- **The homomorphism `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings** read off the structure map of `f`, at the
point `Ψ` of the target site reconstructed from `Φ`. -/
def targetStalkRingMap [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) :
    Stacks.ringFiber (f.targetSitePoint Φ) Y.O.obj →+* Stacks.ringFiber Φ X.O.obj :=
  Stacks.Sheaves.StalkPullback.stalkRingMap f.toRingedToposModulesHom Φ (f.targetSitePoint Φ)
    (f.targetSitePointIso Φ)

section LocallyRinged

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 04H9, (1) ⇒ (3), at the reconstructed point of the target site.** For a morphism of
*locally* ringed topoi the homomorphism `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings is local.

It is the isomorphism `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of stalk rings, which reflects units because it is an
isomorphism, followed by the stalk at `Φ` of the inverse-image form of the structure map, which
reflects units by Stacks 04H9. -/
theorem isLocalHom_targetStalkRingMap (f : RingedToposHom X Y) (hf : f.IsLocallyRinged)
    (Φ : X.J.Point.{w}) : IsLocalHom (f.targetStalkRingMap Φ) := by
  have h : IsLocalHom ((Φ.sheafFiber (A := CommRingCat.{w})).map f.fSharpInverseImage).hom :=
    RingedTopos.isLocalHom_sheafFiber_of_reflectsUnitsObj Φ f.fSharpInverseImage
      (f.reflectsUnitsObj_of_isLocallyRinged hf _)
  refine ⟨fun a ha => ?_⟩
  have h₂ : IsUnit (f.targetStalkRingEquiv Φ a) := h.1 _ ha
  have h₃ := h₂.map (f.targetStalkRingEquiv Φ).symm
  rwa [RingEquiv.symm_apply_apply] at h₃

end LocallyRinged

end AlgebraicGeometry.RingedToposHom

/-! ### The small étale ringed topoi of two schemes -/

namespace AlgebraicGeometry

universe u

variable (B : BigEtaleSite.{u})

/-- Sheafification of sheaves of abelian groups on the small étale site: the site is essentially
small at the universe of the sections. -/
instance hasSheafify_smallEtale_addCommGrpCat (S : Scheme.{u}) (hS : B.Contains S) :
    HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the small étale site the local isomorphisms of sheaves of abelian groups are the locally
bijective maps: again because the site is essentially small. -/
instance wEqualsLocallyBijective_smallEtale_addCommGrpCat (S : Scheme.{u})
    (hS : B.Contains S) :
    (SmallEtale.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- **The stalk of the structure sheaf of a small étale site is strictly henselian**, in the
spelling `Stacks.ringFiber` which the stalk maps of `Stacks.Sheaves.StalkPullback` use.

`AlgebraicGeometry.smallEtaleStalkRing` is the stalk of the structure *sheaf* and
`Stacks.ringFiber` that of the underlying *presheaf*; the two are the same ring, but only after
unfolding `CategoryTheory.GrothendieckTopology.Point.sheafFiber`, which is not reducible, so
instance search does not find the one at the other's spelling. -/
instance strictlyHenselianLocalRing_ringFiber_smallEtale (S : Scheme.{u}) (hS : B.Contains S)
    (p : (SmallEtale.topology B S hS).Point.{u}) :
    StrictlyHenselianLocalRing
      ↥(Stacks.ringFiber p (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)).O.obj) :=
  strictlyHenselianLocalRing_smallEtaleStalkRing B S hS p

variable {X Y : B.Scheme}

/-- **The stalk of the structure sheaf at the reconstructed point of the target small étale site
is strictly henselian.** Every point of the small étale site of a scheme has strictly henselian
structure-sheaf stalk, by Stacks 04HU and Stacks 03PS, and the reconstructed point is one. -/
instance strictlyHenselianLocalRing_targetStalkRing
    (g : RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (p : (SmallEtale.topology B X.obj X.property).Point.{u}) :
    StrictlyHenselianLocalRing
      ↥(smallEtaleStalkRing B Y.obj Y.property (g.targetSitePoint p)) :=
  inferInstance

/-- **Stacks 04GX at the stalks of a locally ringed morphism of small étale ringed topoi.** Let
`(g, g♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of *locally* ringed topoi, let
`p` be a point of the small étale site of `X` and let `Ψ` be the point of the small étale site
of `Y` reconstructed from `p`.  Then the homomorphism `(𝒪_Y)_Ψ ⟶ (𝒪_X)_p` of stalk rings carries
the points of a standard étale presentation over `(𝒪_Y)_Ψ` bijectively onto the points of its
base change.

This is step (3) of the proof of Stacks 04I6 at one stalk: both stalk rings are strictly
henselian and the homomorphism between them is local, so
`MvPolynomial.bijective_homOverMap_of_etale` applies. -/
theorem bijective_homOverMap_targetStalkRingMap
    (g : RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (hg : g.IsLocallyRinged) (p : (SmallEtale.topology B X.obj X.property).Point.{u}) {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n)
      ↥(smallEtaleStalkRing B Y.obj Y.property (g.targetSitePoint p)))
    [Algebra.Etale ↥(smallEtaleStalkRing B Y.obj Y.property (g.targetSitePoint p))
      (MvPolynomial (Fin n)
        ↥(smallEtaleStalkRing B Y.obj Y.property (g.targetSitePoint p)) ⧸
        Ideal.span (Set.range P))] :
    Function.Bijective
      (fun t : MvPolynomial.HomOver P
          (RingHom.id ↥(smallEtaleStalkRing B Y.obj Y.property (g.targetSitePoint p))) =>
        (⟨(g.targetStalkRingMap p).comp t.1,
            (RingHom.comp_assoc _ _ _).trans
              ((congrArg (g.targetStalkRingMap p).comp t.2).trans (RingHom.comp_id _))⟩ :
          MvPolynomial.HomOver P (g.targetStalkRingMap p))) :=
  MvPolynomial.bijective_homOverMap_of_etale P (g.targetStalkRingMap p)
    (g.isLocalHom_targetStalkRingMap hg p)

end AlgebraicGeometry

end
