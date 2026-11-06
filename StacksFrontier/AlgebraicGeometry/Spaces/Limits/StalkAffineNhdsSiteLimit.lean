module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RingedSite
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SpecStalkSiteMembership
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic

/-!
# `Spec 𝒪_{S, s}` is the limit of the affine open neighbourhoods of `s` in the big fppf site

`StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic` identifies `Spec 𝒪_{S, s}` with the
inverse limit of the affine open neighbourhoods of `s` in the category of *schemes*. This file
transports that identification into the big fppf category over `S`: the affine open
neighbourhoods of `s` are objects of that category by their open immersions, `Spec 𝒪_{S, s}` is
one by `Scheme.fromSpecStalk`, and the canonical maps `Spec 𝒪_{S, s} ⟶ W` make it the limit
there as well.

Nothing here is a hypothesis about the site: a big fppf site contains every open of a scheme it
contains, and it contains `Spec 𝒪_{S, s}` because the stalk has cardinality at most the size of
`S` and the cutoff of a big fppf site is a strong prelimit cardinal
(`AlgebraicGeometry.BigFppfSite.contains_Spec_stalk_of_contains`). In particular the index
category is not required to be small against the cofinality of the cutoff: that bound is what a
*descent* statement along the limit needs, not the limit identification itself.

## Main results

* `AlgebraicGeometry.affineOpenNhdsSiteDiagram`: the affine open neighbourhoods of `s` as a
  diagram in the big fppf category over `S`, whose underlying diagram of schemes is
  `AlgebraicGeometry.affineOpenNhdsDiagram`.
* `AlgebraicGeometry.specStalkSiteCone`: the cone with vertex `Spec 𝒪_{S, s}` over that diagram.
* `AlgebraicGeometry.isLimitSpecStalkSiteCone`: **that cone is a limit in the big fppf category
  over `S`**.
* `AlgebraicGeometry.isLimitMapConeSpecStalkSiteCone`: its cone of underlying schemes is a limit
  of schemes.
* `AlgebraicGeometry.subsingleton_hom_of_mono` and
  `AlgebraicGeometry.subsingleton_hom_siteObject`: an object of the big fppf category over `S`
  whose structure morphism is a monomorphism of schemes receives at most one morphism from each
  object.

## Implementation notes

The limit is proved in the slice by hand rather than by a general creation-of-limits argument.
Both halves are cheap: the underlying scheme functor of the big fppf category over `S` is
faithful, so uniqueness of the lift is the uniqueness at the level of schemes, and the structure
morphism to `S` of the lift is forced because the diagram is nonempty and every object under an
open of `S` has its structure morphism factored through that open. For the same reason the
compatibilities of the cone are free: there is at most one morphism from an object of the site to
an open of `S`, so the naturality of the cone and the factorisation through it hold by
`Subsingleton.elim` instead of by a computation.

## References

* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : S)

/-! ### The diagram of affine open neighbourhoods in the site -/

/-- The affine open neighbourhoods of `s`, as a diagram in the big fppf category over `S`: each
is a scheme over `S` by its open immersion, and an inclusion of neighbourhoods is a morphism
over `S`. -/
noncomputable def affineOpenNhdsSiteDiagram : AffineOpenNhds S s ⥤ BigFppfOver B S hS :=
  (affineOpenNhds S s).ι ⋙ OpenNhds.inclusion s ⋙ BigFppfOver.opensToBig B S hS

/-- The stage of `AlgebraicGeometry.affineOpenNhdsSiteDiagram` at an affine open neighbourhood `W`
is the open `W` of `S`, regarded as an object of the big fppf category over `S`. -/
@[simp]
theorem affineOpenNhdsSiteDiagram_obj (W : AffineOpenNhds S s) :
    (affineOpenNhdsSiteDiagram B S hS s).obj W = BigFppfOver.opensObj B S hS W.obj.1 :=
  rfl

/-- The diagram of affine open neighbourhoods in the site has
`AlgebraicGeometry.affineOpenNhdsDiagram` as its diagram of underlying schemes, objectwise. -/
theorem toScheme_obj_affineOpenNhdsSiteDiagram_obj (W : AffineOpenNhds S s) :
    (BigFppfOver.toScheme B S hS).obj ((affineOpenNhdsSiteDiagram B S hS s).obj W) =
      (affineOpenNhdsDiagram S s).obj W :=
  rfl

/-- The diagram of affine open neighbourhoods in the site has
`AlgebraicGeometry.affineOpenNhdsDiagram` as its diagram of underlying schemes, on morphisms. -/
theorem toScheme_map_affineOpenNhdsSiteDiagram_map {W W' : AffineOpenNhds S s} (f : W ⟶ W') :
    (BigFppfOver.toScheme B S hS).map ((affineOpenNhdsSiteDiagram B S hS s).map f) =
      (affineOpenNhdsDiagram S s).map f :=
  rfl

/-- There is at most one morphism from an object of the big fppf category over `S` to a stage of
the diagram of affine open neighbourhoods, the stage being an open of `S`. -/
theorem subsingleton_hom_affineOpenNhdsSiteDiagram_obj (T : BigFppfOver B S hS)
    (W : AffineOpenNhds S s) :
    Subsingleton (T ⟶ (affineOpenNhdsSiteDiagram B S hS s).obj W) :=
  BigFppfOver.subsingleton_hom_opensObj B S hS T W.obj.1

/-! ### `Spec 𝒪_{S, s}` as an object of the site, and the cone over the diagram -/

/-- `Spec 𝒪_{S, s}` as an object of the big fppf category over `S`, via the canonical morphism
`AlgebraicGeometry.Scheme.fromSpecStalk`. -/
noncomputable def specStalkSiteObj : BigFppfOver B S hS :=
  siteObject B S hS (B.contains_Spec_stalk_of_contains hS s) (S.fromSpecStalk s)

/-- The underlying scheme of `AlgebraicGeometry.specStalkSiteObj` is `Spec 𝒪_{S, s}`. -/
@[simp]
theorem toScheme_obj_specStalkSiteObj :
    (BigFppfOver.toScheme B S hS).obj (specStalkSiteObj B S hS s) =
      Spec (S.presheaf.stalk s) :=
  rfl

/-- The canonical morphism `Spec 𝒪_{S, s} ⟶ W` to an affine open neighbourhood of `s`, as a
morphism of the big fppf category over `S`. -/
noncomputable def specStalkSiteπ (W : AffineOpenNhds S s) :
    specStalkSiteObj B S hS s ⟶ (affineOpenNhdsSiteDiagram B S hS s).obj W :=
  Over.homMk (ObjectProperty.homMk
      (Scheme.Opens.fromSpecStalkOfMem (X := S) W.obj.1 s W.obj.2))
    (by
      apply ObjectProperty.hom_ext
      exact Scheme.Opens.fromSpecStalkOfMem_ι (X := S) W.obj.1 s W.obj.2)

/-- The underlying morphism of schemes of `AlgebraicGeometry.specStalkSiteπ` at `W` is the leg at
`W` of the cone `AlgebraicGeometry.specStalkCone` of schemes. -/
@[simp]
theorem toScheme_map_specStalkSiteπ (W : AffineOpenNhds S s) :
    (BigFppfOver.toScheme B S hS).map (specStalkSiteπ B S hS s W) =
      (specStalkCone S s).π.app W :=
  rfl

/-- The cone exhibiting `Spec 𝒪_{S, s}` over the affine open neighbourhoods of `s` in the big
fppf category over `S`. -/
noncomputable def specStalkSiteCone : Cone (affineOpenNhdsSiteDiagram B S hS s) where
  pt := specStalkSiteObj B S hS s
  π :=
  { app := specStalkSiteπ B S hS s
    naturality := fun _ W' _ =>
      @Subsingleton.elim _
        (subsingleton_hom_affineOpenNhdsSiteDiagram_obj B S hS s _ W') _ _ }

/-- The leg at `W` of `AlgebraicGeometry.specStalkSiteCone` is `AlgebraicGeometry.specStalkSiteπ`
at `W`. -/
@[simp]
theorem specStalkSiteCone_π_app (W : AffineOpenNhds S s) :
    (specStalkSiteCone B S hS s).π.app W = specStalkSiteπ B S hS s W :=
  rfl

/-! ### The limit -/

/-- The cone of underlying schemes of a cone over the diagram of affine open neighbourhoods in
the site. -/
noncomputable def schemeConeOfAffineOpenNhdsSiteCone
    (d : Cone (affineOpenNhdsSiteDiagram B S hS s)) :
    Cone (affineOpenNhdsDiagram S s) :=
  (BigFppfOver.toScheme B S hS).mapCone d

/-- The leg at `W` of the cone of underlying schemes of `d` is the underlying morphism of schemes
of the leg of `d` at `W`. -/
@[simp]
theorem schemeConeOfAffineOpenNhdsSiteCone_π_app (d : Cone (affineOpenNhdsSiteDiagram B S hS s))
    (W : AffineOpenNhds S s) :
    (schemeConeOfAffineOpenNhdsSiteCone B S hS s d).π.app W =
      (BigFppfOver.toScheme B S hS).map (d.π.app W) :=
  rfl

/-- The lift of a cone of the site through `Spec 𝒪_{S, s}`, as a morphism of schemes. -/
noncomputable abbrev specStalkSiteLift (d : Cone (affineOpenNhdsSiteDiagram B S hS s)) :
    (BigFppfOver.toScheme B S hS).obj d.pt ⟶ Spec (S.presheaf.stalk s) :=
  (isLimitSpecStalkCone S s).lift (schemeConeOfAffineOpenNhdsSiteCone B S hS s d)

/-- The lift of a cone of the site through `Spec 𝒪_{S, s}` is a morphism over `S`: composing it
with `Scheme.fromSpecStalk` recovers the structure morphism. -/
theorem specStalkSiteLift_comp_fromSpecStalk
    (d : Cone (affineOpenNhdsSiteDiagram B S hS s)) :
    specStalkSiteLift B S hS s d ≫ S.fromSpecStalk s = B.inclusion.map d.pt.hom := by
  obtain ⟨W₀⟩ := (inferInstance : Nonempty (AffineOpenNhds S s))
  have hfac : specStalkSiteLift B S hS s d ≫
      Scheme.Opens.fromSpecStalkOfMem (X := S) W₀.obj.1 s W₀.obj.2 =
      (BigFppfOver.toScheme B S hS).map (d.π.app W₀) :=
    (isLimitSpecStalkCone S s).fac (schemeConeOfAffineOpenNhdsSiteCone B S hS s d) W₀
  rw [← Scheme.Opens.fromSpecStalkOfMem_ι (X := S) W₀.obj.1 s W₀.obj.2, ← Category.assoc, hfac]
  exact (BigFppfOver.hom_hom_eq B S hS (d.π.app W₀)).symm

/-- **`Spec 𝒪_{S, s}` is the limit of the affine open neighbourhoods of `s` in the big fppf
category over `S`.** This is the identification `Spec 𝒪_{S, s} = lim W` of Stacks 0BPA, read in
the big fppf category over `S` instead of in the category of schemes. -/
noncomputable def isLimitSpecStalkSiteCone : IsLimit (specStalkSiteCone B S hS s) where
  lift d :=
    Over.homMk (ObjectProperty.homMk (specStalkSiteLift B S hS s d))
      (by
        apply ObjectProperty.hom_ext
        exact specStalkSiteLift_comp_fromSpecStalk B S hS s d)
  fac d W :=
    @Subsingleton.elim _ (subsingleton_hom_affineOpenNhdsSiteDiagram_obj B S hS s _ W) _ _
  uniq d m hm := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    refine (isLimitSpecStalkCone S s).uniq (schemeConeOfAffineOpenNhdsSiteCone B S hS s d) _
      fun W => ?_
    have h := congrArg (BigFppfOver.toScheme B S hS).map (hm W)
    rw [Functor.map_comp] at h
    exact h

/-- **The underlying schemes of the cone of `AlgebraicGeometry.specStalkSiteCone` form a limit of
schemes.** -/
noncomputable def isLimitMapConeSpecStalkSiteCone :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone (specStalkSiteCone B S hS s)) :=
  IsLimit.ofIsoLimit (isLimitSpecStalkCone S s)
    (Cone.ext (Iso.refl _) fun _ => (Category.id_comp _).symm)

/-! ### Objects of the site whose structure morphism is a monomorphism -/

/-- The underlying scheme morphism of a morphism of the big fppf category over `S` is compatible
with the structure morphisms. -/
theorem toScheme_map_comp_hom {Z T : BigFppfOver B S hS} (f : Z ⟶ T) :
    (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map T.hom = B.inclusion.map Z.hom :=
  (B.inclusion.map_comp f.left T.hom).symm.trans (congrArg B.inclusion.map (Over.w f))

/-- **An object of the big fppf category over `S` whose structure morphism is a monomorphism of
schemes receives at most one morphism from each object.** -/
theorem subsingleton_hom_of_mono {T : BigFppfOver B S hS}
    (hT : Mono (B.inclusion.map T.hom)) (Z : BigFppfOver B S hS) : Subsingleton (Z ⟶ T) := by
  refine ⟨fun f g => (BigFppfOver.toScheme B S hS).map_injective ?_⟩
  exact (cancel_mono (B.inclusion.map T.hom)).1
    ((toScheme_map_comp_hom B S hS f).trans (toScheme_map_comp_hom B S hS g).symm)

/-- An object of the big fppf category over `S` presented by a monomorphism of schemes receives
at most one morphism from each object. -/
theorem subsingleton_hom_siteObject {T : Scheme.{u}} (hT : B.Contains T) (b : T ⟶ S)
    (hb : Mono b) (Z : BigFppfOver B S hS) : Subsingleton (Z ⟶ siteObject B S hS hT b) :=
  subsingleton_hom_of_mono B S hS (T := siteObject B S hS hT b) hb Z

/-! ### The point-set data of the diagram -/

/-- Every stage of the diagram of affine open neighbourhoods is an open subscheme of `S`. -/
theorem isOpenImmersion_affineOpenNhdsSiteDiagram_obj_hom (W : AffineOpenNhds S s) :
    IsOpenImmersion (B.inclusion.map ((affineOpenNhdsSiteDiagram B S hS s).obj W).hom) :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι (X := S) W.obj.1))

/-- Every stage of the diagram of affine open neighbourhoods contains the point `s`. -/
theorem mem_range_affineOpenNhdsSiteDiagram_obj_hom (W : AffineOpenNhds S s) :
    s ∈ Set.range (B.inclusion.map ((affineOpenNhdsSiteDiagram B S hS s).obj W).hom) := by
  change s ∈ Set.range ⇑(Scheme.Opens.ι (X := S) W.obj.1)
  rw [Scheme.Opens.range_ι]
  exact W.obj.2

/-- Every stage of the diagram of affine open neighbourhoods is affine. -/
instance isAffine_toScheme_affineOpenNhdsSiteDiagram_obj (W : AffineOpenNhds S s) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((affineOpenNhdsSiteDiagram B S hS s).obj W)) :=
  W.property

end AlgebraicGeometry

end
