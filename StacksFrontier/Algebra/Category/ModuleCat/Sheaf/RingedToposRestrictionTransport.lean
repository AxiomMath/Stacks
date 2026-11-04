module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism

/-!
# The restriction comparison of structure sheaves is a transport

A morphism of ringed topoi whose inverse image is restriction along a continuous functor of sites
carries a canonical structure map: the inverse image of a sheaf of commutative rings along
restriction *is* the restriction of that sheaf of commutative rings, by
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, and that comparison is the identity on
sections. This file records the consequence that the square calculus of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposSquare.lean` consumes: on underlying
sheaves of sets the comparison is a `Stacks.IsTransport`, the canonical morphism of an equality of
its source and target.

That is what makes a square of such morphisms commute for free. Two composites of
restriction-presented morphisms of ringed topoi have inverse-image structure maps built out of
these comparisons and out of equalities of restriction functors, hence are transports between the
same two objects, hence are equal by `Stacks.IsTransport.eq`; no 2-cell has to be computed.

## Main results

* `Stacks.Sheaves.ToposPullback.isTransport_forget_restrictionCommRingIso_hom`: the comparison of
  the inverse image of a sheaf of commutative rings with its restriction is a transport on
  underlying sheaves of sets.
* `Stacks.Sheaves.ToposPullback.isTransport_forget_restrictionCommRingIso_trans_eqToIso_hom`: so
  is that comparison followed by an equality of structure sheaves, which is the shape in which
  the structure map of a restriction-presented morphism of ringed topoi arrives.
* `AlgebraicGeometry.RingedToposHom.isTransport_fSharpInverseImageForget_ofInverseImageIso`: the
  inverse-image structure map of a morphism of ringed topoi built by
  `AlgebraicGeometry.RingedToposHom.ofInverseImageIso` is a transport as soon as the isomorphism
  of structure sheaves it was built from is one.
* `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageEqOfIsTransport`: **two morphisms of
  ringed topoi with equal inverse images and transport structure maps are 2-isomorphic**, by the
  adjoint mate of the canonical morphism of that equality. This is the form in which a square of
  restriction-presented morphisms of ringed topoi is shown to 2-commute.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 08QN](https://stacks.math.columbia.edu/tag/08QN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf K CommRingCat.{ww})

omit [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget RingCat.{ww})] in
/-- **The restriction comparison of sheaves of commutative rings is a transport.** The inverse
image of `O` along restriction and the restriction of `O` have the *same* underlying sheaf of
sets — both are `G.op ⋙ O` with the ring operations read off differently — and
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso` is the identity on sections, so forgetting
the operations leaves exactly the canonical morphism of that equality. -/
theorem isTransport_forget_restrictionCommRingIso_hom :
    Stacks.IsTransport ((sheafCompose J (forget CommRingCat.{ww})).map
      (restrictionCommRingIso J K G O).hom) :=
  ⟨rfl, by
    apply Sheaf.hom_ext
    exact NatTrans.ext (funext fun _ ↦ rfl)⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The restriction comparison followed by an equality of structure sheaves is again a transport.
This is the shape in which the structure map of a restriction-presented morphism of ringed topoi
arrives: the comparison identifies the inverse image with a restriction, and an equality
identifies that restriction with the structure sheaf of the source. -/
theorem isTransport_forget_restrictionCommRingIso_trans_eqToIso_hom
    {O' : Sheaf J CommRingCat.{ww}}
    (h : (G.sheafPushforwardContinuous CommRingCat.{ww} J K).obj O = O') :
    Stacks.IsTransport ((sheafCompose J (forget CommRingCat.{ww})).map
      (restrictionCommRingIso J K G O ≪≫ eqToIso h).hom) := by
  rw [Iso.trans_hom, CategoryTheory.Functor.map_comp]
  exact (isTransport_forget_restrictionCommRingIso_hom J K G O).comp
    (Stacks.IsTransport.map _ (Stacks.IsTransport.eqToHom h))

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom

universe w v u v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **A morphism of ringed topoi read off an isomorphism of structure sheaves has a transport for
its structure map as soon as that isomorphism has one.** The inverse-image form of the structure
map of `AlgebraicGeometry.RingedToposHom.ofInverseImageIso f e` *is* `e`, so there is nothing to
compute. -/
theorem isTransport_fSharpInverseImageForget_ofInverseImageIso
    (f : MorphismOfTopoi X.Topos Y.Topos)
    (e : (inverseImageCommRingFunctor f).obj Y.O ≅ X.O)
    (he : Stacks.IsTransport (X.forgetRing.map e.hom)) :
    Stacks.IsTransport (ofInverseImageIso f e).fSharpInverseImageForget := by
  rw [← forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget,
    ofInverseImageIso_fSharpInverseImage]
  exact he

/-- **Two morphisms of ringed topoi with equal inverse images and transport structure maps are
2-isomorphic.** The comparison of the inverse images is the canonical morphism of their equality,
and the 2-isomorphism is its adjoint mate; the compatibility with the structure maps is automatic,
because both sides of it are then transports between the same two objects.

This is the form in which a square of restriction-presented morphisms of ringed topoi is shown to
2-commute: the two ways around it restrict along the same functor of sites, and every structure
map in sight is a transport. -/
noncomputable def TwoIso.ofInverseImageEqOfIsTransport {p q : RingedToposHom X Y}
    (h : q.toToposHom.inverseImage = p.toToposHom.inverseImage)
    (hp : Stacks.IsTransport p.fSharpInverseImageForget)
    (hq : Stacks.IsTransport q.fSharpInverseImageForget) :
    TwoIso p q :=
  TwoIso.ofInverseImageIso (eqToIso h) <| by
    rw [forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget,
      forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget]
    exact Stacks.IsTransport.eq (((Stacks.IsTransport.eqToHom h).app _).comp hp) hq

end AlgebraicGeometry.RingedToposHom

end
