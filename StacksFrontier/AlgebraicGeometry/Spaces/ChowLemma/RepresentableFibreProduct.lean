module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdUnderlying

/-!
# Fibre products of representables over an algebraic space are representable

Let `X` be an algebraic space over `S`. For any two morphisms `a : yoneda.obj U ⟶ X` and
`b : yoneda.obj V ⟶ X` from presheaves represented by objects of the big fppf site, the presheaf
fibre product of `a` and `b` is represented by an object of the site. The same holds for the
fibre product taken in the category `AlgebraicGeometry.AlgebraicSpaces` of algebraic spaces over
`S` and in the spaces-étale site `AlgebraicGeometry.Space.SpacesEtale` of `X`.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.underlyingPullbackIso`: the algebraic space underlying a
  fibre product in the spaces-étale site of `X` is the fibre product of the underlying algebraic
  spaces.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_pullback_yoneda`: the presheaf fibre product of two
  representables over an algebraic space over `S` is representable.
* `AlgebraicGeometry.Space.isRepresentable_pullback`: the same with the two sources only
  assumed representable rather than literally of the form `yoneda.obj U`.
* `AlgebraicGeometry.Space.isRepresentable_pullback_algebraicSpaces`: the presheaf underlying a
  fibre product of algebraic spaces over `S` with representable factors is representable.
* `AlgebraicGeometry.Space.SpacesEtale.isRepresentable_underlying_pullback`: a fibre product of
  site-representable objects of the spaces-étale site of `X` is site-representable.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 0DF3](https://stacks.math.columbia.edu/tag/0DF3)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Representability of a presheaf transports along an isomorphism. -/
theorem isRepresentable_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : F.IsRepresentable) (e : F ≅ G) : G.IsRepresentable := by
  obtain ⟨U, ⟨r⟩⟩ := hF.has_representation
  exact Functor.IsRepresentable.mk' (r.toIso ≪≫ e)

section Presheaf

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A presheaf fibre product that is the vertex of a pullback square with representable vertex is
representable. -/
private theorem isRepresentable_pullback_of_isPullback {W : BigFppfOver B S hS}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ X} {g : G ⟶ X}
    {fst : yoneda.obj W ⟶ F} {snd : yoneda.obj W ⟶ G} (h : IsPullback fst snd f g) :
    (pullback f g).IsRepresentable :=
  Functor.IsRepresentable.mk' ((IsPullback.of_hasPullback f g).isoIsPullback _ _ h).symm

/-- The presheaf fibre product of two representables over an algebraic space over `S` is
representable. -/
theorem isRepresentable_pullback_yoneda (hX : IsAlgebraicSpace B S hS X)
    {U V : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ X) :
    (pullback a b).IsRepresentable :=
  isRepresentable_pullback_of_isPullback B S hS
    ((hX.diagonal_representable.of_diag a).isPullback' b)

/-- The presheaf fibre product of two representable presheaves over an algebraic space over `S`
is representable. -/
theorem isRepresentable_pullback (hX : IsAlgebraicSpace B S hS X)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : F.IsRepresentable) (hG : G.IsRepresentable)
    (f : F ⟶ X) (g : G ⟶ X) : (pullback f g).IsRepresentable := by
  obtain ⟨U, ⟨rU⟩⟩ := hF.has_representation
  obtain ⟨V, ⟨rV⟩⟩ := hG.has_representation
  have ha : yoneda.relativelyRepresentable (rU.toIso.hom ≫ f) :=
    hX.diagonal_representable.of_diag _
  have hsq : IsPullback (ha.fst (rV.toIso.hom ≫ g) ≫ rU.toIso.hom)
      (yoneda.map (ha.snd (rV.toIso.hom ≫ g)) ≫ rV.toIso.hom) f g :=
    (ha.isPullback (rV.toIso.hom ≫ g)).of_iso (Iso.refl _) rU.toIso rV.toIso
      (Iso.refl X) (by simp) (by simp) (by simp) (by simp)
  exact isRepresentable_pullback_of_isPullback B S hS hsq

end Presheaf

/-- The presheaf underlying a fibre product of algebraic spaces over `S` with representable
factors is representable. -/
theorem isRepresentable_pullback_algebraicSpaces {F G H : AlgebraicSpaces B S hS}
    (hF : F.1.IsRepresentable) (hG : G.1.IsRepresentable) (f : F ⟶ H) (g : G ⟶ H) :
    (pullback f g).1.IsRepresentable :=
  isRepresentable_of_iso B S hS
    (isRepresentable_pullback B S hS H.2 hF hG f.hom g.hom)
    (pullbackFiberProductIso B S hS f g).symm

namespace SpacesEtale

variable (X : AlgebraicSpaces B S hS)

/-- The algebraic space underlying a fibre product in the spaces-étale site of `X` is the
fibre product of the underlying algebraic spaces. -/
noncomputable def underlyingPullbackIso {U V W : SpacesEtale B S hS X} (f : U ⟶ W) (g : V ⟶ W) :
    underlying B S hS X (pullback f g) ≅
      pullback ((toSpaces B S hS X).map f) ((toSpaces B S hS X).map g) :=
  PreservesPullback.iso (toSpaces B S hS X) f g

/-- A fibre product of site-representable objects of the spaces-étale site of `X` is
site-representable: if the algebraic spaces underlying `U` and `V` are represented by objects of
the big fppf site, then so is the algebraic space underlying the fibre product `U ×_W V` computed
in the spaces-étale site of `X`. -/
theorem isRepresentable_underlying_pullback {U V W : SpacesEtale B S hS X}
    (hU : (underlying B S hS X U).1.IsRepresentable)
    (hV : (underlying B S hS X V).1.IsRepresentable) (f : U ⟶ W) (g : V ⟶ W) :
    (underlying B S hS X (pullback f g)).1.IsRepresentable :=
  isRepresentable_of_iso B S hS
    (isRepresentable_pullback_algebraicSpaces B S hS hU hV
      ((toSpaces B S hS X).map f) ((toSpaces B S hS X).map g))
    ((ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
      (underlyingPullbackIso B S hS X f g)).symm

end SpacesEtale

end AlgebraicGeometry.Space

end
