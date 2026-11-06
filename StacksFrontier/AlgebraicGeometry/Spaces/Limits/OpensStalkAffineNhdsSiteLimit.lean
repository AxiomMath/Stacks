module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SpecStalkSiteMembership
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Spec 𝒪_{S, s} ∩ U` is the limit of the overlaps `W ∩ U` in the big fppf site

`StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic` identifies the preimage of an open
`U ⊆ S` in `Spec 𝒪_{S, s}` with the inverse limit of its preimages in the affine open
neighbourhoods of `s` contained in a fixed one, in the category of *schemes*
(`AlgebraicGeometry.isLimitOpensSpecStalkCone`).  This file transports that identification into
the big fppf category over `S`.

It is the overlap-side companion of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.StalkAffineNhdsSiteLimit`, which does the same for
the neighbourhoods `W` themselves.  The two are separate files because the two systems are not
alike: the stages `W` of the M-side system are *affine*, whereas the overlaps `W ∩ U` are in
general only quasi-compact and quasi-separated (and quasi-compact only when `U` is retrocompact,
which is supplied elsewhere), with affine transition morphisms.  Nothing below needs any of that:
the limit holds for an arbitrary open `U` and an arbitrary point `s`.

## Main results

* `AlgebraicGeometry.BigFppfOver.subsingleton_hom_of_mono_hom`: an object of the big fppf category
  over `S` whose structure morphism is a monomorphism is subterminal.
* `AlgebraicGeometry.opensSpecStalkSiteDiagram`: the overlaps `W ∩ U` as a diagram in the big fppf
  category over `S`, whose underlying diagram of schemes is
  `AlgebraicGeometry.opensSpecStalkDiagram`.
* `AlgebraicGeometry.opensSpecStalkSiteCone`: the cone over it with vertex the site object
  `V = Spec 𝒪_{S, s} ∩ U`.
* `AlgebraicGeometry.isLimitOpensSpecStalkSiteCone`: **that cone is a limit in the big fppf
  category over `S`**.
* `AlgebraicGeometry.isLimitSchemeConeOpensSpecStalkSiteCone`: its cone of underlying schemes is a
  limit of schemes.
* `AlgebraicGeometry.toScheme_obj_opensSpecStalkSiteObj_eq`: the underlying scheme of the vertex is
  `S.fromSpecStalk s ⁻¹ᵁ U`, i.e. it is the `V` of the tag.

## Implementation notes

The index category is `CategoryTheory.Over W₀` for a fixed affine open neighbourhood `W₀` of `s`,
not `AlgebraicGeometry.AffineOpenNhds S s` itself.  That is forced by the scheme-level input: an
overlap `W ∩ U` is the preimage of the trace of `U` on `W₀` along a transition morphism, so the
system is indexed by the neighbourhoods *equipped with* their inclusion into `W₀`, which is the
index of Mathlib's `AlgebraicGeometry.opensDiagram`.  `CategoryTheory.IsCofiltered.over` and
`CategoryTheory.Over.initial_forget` make this harmless: `Over W₀` is cofiltered, and a limit over
`AffineOpenNhds S s` restricts to one over `Over W₀` by
`CategoryTheory.Limits.IsLimit.overPost`.

Two elaboration points govern the shape of everything below.

First, the cone of underlying schemes of a cone of the site is built by hand
(`AlgebraicGeometry.schemeConeOfSiteCone`) rather than as
`(BigFppfOver.toScheme B S hS).mapCone`.  A `Cone ((BigFppfOver.toScheme B S hS).mapCone _)` lives
over the composite functor `opensSpecStalkSiteDiagram ⋙ BigFppfOver.toScheme`, and that composite
does not unify with `AlgebraicGeometry.opensSpecStalkDiagram`, which is a structure literal rather
than a composite of functors.  Building the cone objectwise asks only for the two componentwise
identities `toScheme_obj_opensSpecStalkSiteDiagram_obj` and
`toScheme_map_opensSpecStalkSiteDiagram_map`, both of which hold by `rfl`, and so costs no natural
isomorphism.  The alternative — indexing the stages by the opens `W ⊓ U` of `S` and paying for one
natural isomorphism built from `AlgebraicGeometry.Scheme.Opens.isoOfLE` — was rejected because the
isomorphism is not an identity and every consumer would pay for it again.

Second, the vertex is the *literal* apex of the scheme-level cone, the open
`(specStalkCone S s).π.app W₀ ⁻¹ᵁ (W₀.ι ⁻¹ᵁ U)` of `Spec 𝒪_{S, s}`, rather than the open
`S.fromSpecStalk s ⁻¹ᵁ U` that the tag calls `V`.  The two opens are equal, but by
`AlgebraicGeometry.specStalkCone_π_preimage` and not by `rfl`, and transporting a cone across that
equality is a dependent rewrite whose `eqToHom` debris every consumer would then carry.  The
identification is supplied as the separate theorem
`AlgebraicGeometry.toScheme_obj_opensSpecStalkSiteObj_eq` instead.

For the same reason as on the M-side, the compatibilities of the cone are free: every stage of the
diagram has a monomorphism to `S` as its structure morphism — the open immersion of `W ∩ U` into
`W` followed by that of `W` into `S` — so there is at most one morphism of the site into it, and
naturality and the factorisation hold by `Subsingleton.elim` instead of by a computation.  The
general statement is `AlgebraicGeometry.BigFppfOver.subsingleton_hom_of_mono_hom`, which
subsumes `AlgebraicGeometry.BigFppfOver.subsingleton_hom_opensObj`: the stages here are opens of an
open of `S`, so they are not `AlgebraicGeometry.BigFppfOver.opensObj` of anything.

## References

* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Subterminal objects of the big fppf category over `S` -/

namespace BigFppfOver

/-- **An object of the big fppf category over `S` whose structure morphism is a monomorphism is
subterminal**: there is at most one morphism to it from any object. -/
theorem subsingleton_hom_of_mono_hom (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z T : BigFppfOver B S hS) (hT : Mono T.hom.hom) : Subsingleton (Z ⟶ T) := by
  refine ⟨fun f g => ?_⟩
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  rw [← cancel_mono T.hom.hom, ← hom_hom_comp B S hS f, ← hom_hom_comp B S hS g]

end BigFppfOver

/-! ### The system of overlaps `W ∩ U`, as schemes -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : S)
  (W₀ : AffineOpenNhds S s) (U : S.Opens)

/-- **The diagram of the overlaps `W ∩ U`**, `W` running over the affine open neighbourhoods of
`s` contained in `W₀`: the preimages of the trace of `U` on `W₀` along the transition morphisms of
`AlgebraicGeometry.affineOpenNhdsDiagram`. -/
noncomputable abbrev opensSpecStalkDiagram : Over W₀ ⥤ Scheme.{u} :=
  opensDiagram (affineOpenNhdsDiagram S s) W₀ (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U)

/-- The overlap `W ∩ U` at the stage indexed by `j`, as an open of `W`. -/
noncomputable abbrev opensSpecStalkStageOpen (j : Over W₀) :
    ((affineOpenNhdsDiagram S s).obj j.left).Opens :=
  (affineOpenNhdsDiagram S s).map j.hom ⁻¹ᵁ (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U)

/-- The apex of the scheme-level limit cone, as an open of `Spec 𝒪_{S, s}`.  By
`AlgebraicGeometry.specStalkCone_π_preimage` it is `S.fromSpecStalk s ⁻¹ᵁ U`, the `V` of the
tag, but not by `rfl`. -/
noncomputable abbrev opensSpecStalkApexOpen : (Spec (S.presheaf.stalk s)).Opens :=
  (specStalkCone S s).π.app W₀ ⁻¹ᵁ (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U)

/-- The structure morphism to `S` of a stage `W ∩ U`: its open immersion into `W`, followed by the
open immersion of `W` into `S`. -/
noncomputable def opensSpecStalkStageHom (j : Over W₀) :
    (opensSpecStalkDiagram S s W₀ U).obj j ⟶ S :=
  Scheme.Opens.ι ((affineOpenNhdsDiagram S s).map j.hom ⁻¹ᵁ
      (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U)) ≫
    Scheme.Opens.ι (X := S) j.left.obj.1

/-- The structure morphism to `S` of the apex `V = Spec 𝒪_{S, s} ∩ U`: its open immersion into
`Spec 𝒪_{S, s}`, followed by `AlgebraicGeometry.Scheme.fromSpecStalk`. -/
noncomputable def opensSpecStalkApexHom :
    (opensSpecStalkApexOpen S s W₀ U).toScheme ⟶ S :=
  Scheme.Opens.ι ((specStalkCone S s).π.app W₀ ⁻¹ᵁ
      (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U)) ≫ S.fromSpecStalk s

/-- The structure morphism of a stage is a monomorphism, being a composite of two open
immersions. -/
instance mono_opensSpecStalkStageHom (j : Over W₀) :
    Mono (opensSpecStalkStageHom S s W₀ U j) := by
  have h₁ : Mono (Scheme.Opens.ι ((affineOpenNhdsDiagram S s).map j.hom ⁻¹ᵁ
      (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U))) := inferInstance
  have h₂ : Mono (Scheme.Opens.ι (X := S) j.left.obj.1) := inferInstance
  exact mono_comp' h₁ h₂

/-- For `g : X ⟶ Y` and `h : Y ⟶ Z` with `g ≫ h = k`, the restriction `g.resLE V V' e` followed
by the inclusion of `V` and by `h` equals the inclusion of `V'` followed by `k`. -/
theorem resLE_comp_ι_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (V : Y.Opens) (V' : X.Opens)
    (e : V' ≤ g ⁻¹ᵁ V) (h : Y ⟶ Z) (k : X ⟶ Z) (hk : g ≫ h = k) :
    g.resLE V V' e ≫ Scheme.Opens.ι V ≫ h = Scheme.Opens.ι V' ≫ k := by
  rw [Scheme.Hom.resLE_comp_ι_assoc, hk]

/-- A transition morphism of the system of overlaps is a morphism over `S`. -/
theorem opensSpecStalkDiagram_map_comp_stageHom {j k : Over W₀} (f : j ⟶ k) :
    (opensSpecStalkDiagram S s W₀ U).map f ≫ opensSpecStalkStageHom S s W₀ U k =
      opensSpecStalkStageHom S s W₀ U j := by
  have hι : (affineOpenNhdsDiagram S s).map f.left ≫ Scheme.Opens.ι (X := S) k.left.obj.1 =
      Scheme.Opens.ι (X := S) j.left.obj.1 := by
    rw [affineOpenNhdsDiagram_map]
    exact Scheme.homOfLE_ι S _
  rw [opensSpecStalkStageHom, opensSpecStalkStageHom, opensDiagram_map]
  exact resLE_comp_ι_comp _ _ _ _ _ _ hι

/-- A leg of the scheme-level limit cone is a morphism over `S`. -/
theorem opensCone_π_app_comp_stageHom (j : Over W₀) :
    (opensCone (affineOpenNhdsDiagram S s) (specStalkCone S s) W₀
          (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U)).π.app j ≫
        opensSpecStalkStageHom S s W₀ U j =
      opensSpecStalkApexHom S s W₀ U := by
  have hι : (specStalkCone S s).π.app j.left ≫ Scheme.Opens.ι (X := S) j.left.obj.1 =
      S.fromSpecStalk s := by
    rw [specStalkCone_π_app]
    exact Scheme.Opens.fromSpecStalkOfMem_ι _ s j.left.obj.2
  rw [opensSpecStalkStageHom, opensSpecStalkApexHom, opensCone_π_app]
  exact resLE_comp_ι_comp _ _ _ _ _ _ hι

/-! ### The system of overlaps in the site -/

include hS in
/-- Every stage `W ∩ U` is a scheme of the site: it is an open of an open of `S`. -/
theorem contains_opensSpecStalkDiagram_obj (j : Over W₀) :
    B.Contains ((opensSpecStalkDiagram S s W₀ U).obj j) :=
  B.contains_coe_opens (B.contains_coe_opens hS j.left.obj.1)
    (opensSpecStalkStageOpen S s W₀ U j)

include hS in
/-- The apex `V = Spec 𝒪_{S, s} ∩ U` is a scheme of the site: it is an open of
`Spec 𝒪_{S, s}`, which is itself one by
`AlgebraicGeometry.BigFppfSite.contains_Spec_stalk_of_contains`. -/
theorem contains_opensSpecStalkApexOpen :
    B.Contains ((opensSpecStalkApexOpen S s W₀ U : Scheme.{u})) :=
  B.contains_Spec_stalk_opens hS s (opensSpecStalkApexOpen S s W₀ U)

/-- **The overlaps `W ∩ U` as a diagram in the big fppf category over `S`**: each is a scheme over
`S` by the composite of its two open immersions, and a transition morphism of the system is a
morphism over `S`. -/
noncomputable def opensSpecStalkSiteDiagram : Over W₀ ⥤ BigFppfOver B S hS where
  obj j :=
    siteObject B S hS (contains_opensSpecStalkDiagram_obj B S hS s W₀ U j)
      (opensSpecStalkStageHom S s W₀ U j)
  map {j k} f :=
    Over.homMk
      (ObjectProperty.homMk
        (X := B.obj (contains_opensSpecStalkDiagram_obj B S hS s W₀ U j))
        (Y := B.obj (contains_opensSpecStalkDiagram_obj B S hS s W₀ U k))
        ((opensSpecStalkDiagram S s W₀ U).map f))
      (by
        apply ObjectProperty.hom_ext
        exact opensSpecStalkDiagram_map_comp_stageHom S s W₀ U f)
  map_id j := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (opensSpecStalkDiagram S s W₀ U).map_id j
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (opensSpecStalkDiagram S s W₀ U).map_comp f g

/-- The diagram of overlaps in the site has `AlgebraicGeometry.opensSpecStalkDiagram` as its
diagram of underlying schemes, objectwise. -/
@[simp]
theorem toScheme_obj_opensSpecStalkSiteDiagram_obj (j : Over W₀) :
    (BigFppfOver.toScheme B S hS).obj ((opensSpecStalkSiteDiagram B S hS s W₀ U).obj j) =
      (opensSpecStalkDiagram S s W₀ U).obj j :=
  rfl

/-- The diagram of overlaps in the site has `AlgebraicGeometry.opensSpecStalkDiagram` as its
diagram of underlying schemes, on morphisms. -/
@[simp]
theorem toScheme_map_opensSpecStalkSiteDiagram_map {j k : Over W₀} (f : j ⟶ k) :
    (BigFppfOver.toScheme B S hS).map ((opensSpecStalkSiteDiagram B S hS s W₀ U).map f) =
      (opensSpecStalkDiagram S s W₀ U).map f :=
  rfl

/-- **The transition morphisms of the system of overlaps are affine.**

The stages `W ∩ U` are quasi-affine and not affine, and an open immersion is not an affine
morphism in general.  It holds because the transition `W_j ∩ U ⟶ W_k ∩ U` is a base change of
`W_j ⟶ W_k` along `W_k ∩ U ↪ W_k` — the pullback being `W_j ∩ (W_k ∩ U) = W_j ∩ U` because
`W_j ⊆ W_k` — and `W_j ⟶ W_k` is a morphism of affine schemes. -/
instance isAffineHom_toScheme_map_opensSpecStalkSiteDiagram_map {j k : Over W₀} (f : j ⟶ k) :
    IsAffineHom ((BigFppfOver.toScheme B S hS).map
      ((opensSpecStalkSiteDiagram B S hS s W₀ U).map f)) :=
  inferInstanceAs (IsAffineHom ((opensSpecStalkDiagram S s W₀ U).map f))

/-- There is at most one morphism from an object of the big fppf category over `S` to a stage of
the diagram of overlaps: the stage's structure morphism is a composite of open immersions. -/
theorem subsingleton_hom_opensSpecStalkSiteDiagram_obj (T : BigFppfOver B S hS) (j : Over W₀) :
    Subsingleton (T ⟶ (opensSpecStalkSiteDiagram B S hS s W₀ U).obj j) :=
  BigFppfOver.subsingleton_hom_of_mono_hom B S hS T _
    (inferInstanceAs (Mono (opensSpecStalkStageHom S s W₀ U j)))

/-! ### `V = Spec 𝒪_{S, s} ∩ U` as an object of the site, and the cone over the diagram -/

/-- **`V = Spec 𝒪_{S, s} ∩ U` as an object of the big fppf category over `S`.**  Its underlying
scheme is the literal apex of the scheme-level cone; that this is the open
`S.fromSpecStalk s ⁻¹ᵁ U` of the tag is
`AlgebraicGeometry.toScheme_obj_opensSpecStalkSiteObj_eq`. -/
noncomputable def opensSpecStalkSiteObj : BigFppfOver B S hS :=
  siteObject B S hS (contains_opensSpecStalkApexOpen B S hS s W₀ U)
    (opensSpecStalkApexHom S s W₀ U)

/-- The underlying scheme of `AlgebraicGeometry.opensSpecStalkSiteObj` is the open
`AlgebraicGeometry.opensSpecStalkApexOpen` of `Spec 𝒪_{S, s}`. -/
@[simp]
theorem toScheme_obj_opensSpecStalkSiteObj :
    (BigFppfOver.toScheme B S hS).obj (opensSpecStalkSiteObj B S hS s W₀ U) =
      (opensSpecStalkApexOpen S s W₀ U).toScheme :=
  rfl

/-- **The underlying scheme of the vertex is `Spec 𝒪_{S, s} ∩ U`**, the preimage of `U` along the
canonical morphism `Spec 𝒪_{S, s} ⟶ S`.  This is the `V` of
[Stacks, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91). -/
theorem toScheme_obj_opensSpecStalkSiteObj_eq :
    (BigFppfOver.toScheme B S hS).obj (opensSpecStalkSiteObj B S hS s W₀ U) =
      (S.fromSpecStalk s ⁻¹ᵁ U).toScheme :=
  congrArg Scheme.Opens.toScheme (specStalkCone_π_preimage S s W₀ U)

/-- The canonical morphism `V ⟶ W ∩ U` to a stage of the diagram of overlaps, as a morphism of the
big fppf category over `S`. -/
noncomputable def opensSpecStalkSiteπ (j : Over W₀) :
    opensSpecStalkSiteObj B S hS s W₀ U ⟶ (opensSpecStalkSiteDiagram B S hS s W₀ U).obj j :=
  Over.homMk
    (ObjectProperty.homMk
      (X := B.obj (contains_opensSpecStalkApexOpen B S hS s W₀ U))
      (Y := B.obj (contains_opensSpecStalkDiagram_obj B S hS s W₀ U j))
      ((opensCone (affineOpenNhdsDiagram S s) (specStalkCone S s) W₀
        (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U)).π.app j))
    (by
      apply ObjectProperty.hom_ext
      exact opensCone_π_app_comp_stageHom S s W₀ U j)

/-- The underlying morphism of schemes of `AlgebraicGeometry.opensSpecStalkSiteπ` is the leg at
`j` of the scheme-level cone `AlgebraicGeometry.opensCone`. -/
@[simp]
theorem toScheme_map_opensSpecStalkSiteπ (j : Over W₀) :
    (BigFppfOver.toScheme B S hS).map (opensSpecStalkSiteπ B S hS s W₀ U j) =
      (opensCone (affineOpenNhdsDiagram S s) (specStalkCone S s) W₀
        (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U)).π.app j :=
  rfl

/-- **The cone exhibiting `V = Spec 𝒪_{S, s} ∩ U` over the overlaps `W ∩ U` in the big fppf
category over `S`.** -/
noncomputable def opensSpecStalkSiteCone : Cone (opensSpecStalkSiteDiagram B S hS s W₀ U) where
  pt := opensSpecStalkSiteObj B S hS s W₀ U
  π :=
  { app := opensSpecStalkSiteπ B S hS s W₀ U
    naturality := fun _ k _ =>
      @Subsingleton.elim _
        (subsingleton_hom_opensSpecStalkSiteDiagram_obj B S hS s W₀ U _ k) _ _ }

/-- The leg at `j` of `AlgebraicGeometry.opensSpecStalkSiteCone` is
`AlgebraicGeometry.opensSpecStalkSiteπ`. -/
@[simp]
theorem opensSpecStalkSiteCone_π_app (j : Over W₀) :
    (opensSpecStalkSiteCone B S hS s W₀ U).π.app j = opensSpecStalkSiteπ B S hS s W₀ U j :=
  rfl

/-! ### The limit -/

/-- The cone of underlying schemes of a cone over the diagram of overlaps in the site, as a cone
over `AlgebraicGeometry.opensSpecStalkDiagram`. -/
noncomputable def schemeConeOfSiteCone (d : Cone (opensSpecStalkSiteDiagram B S hS s W₀ U)) :
    Cone (opensSpecStalkDiagram S s W₀ U) where
  pt := (BigFppfOver.toScheme B S hS).obj d.pt
  π :=
  { app := fun j => (BigFppfOver.toScheme B S hS).map (d.π.app j)
    naturality := fun j k f => by
      have h : d.π.app k = d.π.app j ≫ (opensSpecStalkSiteDiagram B S hS s W₀ U).map f := by
        simp
      change 𝟙 _ ≫ (BigFppfOver.toScheme B S hS).map (d.π.app k) =
        (BigFppfOver.toScheme B S hS).map (d.π.app j) ≫ (opensSpecStalkDiagram S s W₀ U).map f
      rw [Category.id_comp, h, Functor.map_comp,
        toScheme_map_opensSpecStalkSiteDiagram_map]
      rfl }

/-- The leg at `j` of `AlgebraicGeometry.schemeConeOfSiteCone d` is the underlying morphism of
schemes of the leg of `d` at `j`. -/
@[simp]
theorem schemeConeOfSiteCone_π_app (d : Cone (opensSpecStalkSiteDiagram B S hS s W₀ U))
    (j : Over W₀) :
    (schemeConeOfSiteCone B S hS s W₀ U d).π.app j =
      (BigFppfOver.toScheme B S hS).map (d.π.app j) :=
  rfl

/-- The lift of a cone of the site through `V = Spec 𝒪_{S, s} ∩ U`, as a morphism of schemes. -/
noncomputable abbrev opensSpecStalkSiteLift
    (d : Cone (opensSpecStalkSiteDiagram B S hS s W₀ U)) :
    (BigFppfOver.toScheme B S hS).obj d.pt ⟶ (opensSpecStalkApexOpen S s W₀ U).toScheme :=
  (isLimitOpensSpecStalkCone S s W₀ U).lift (schemeConeOfSiteCone B S hS s W₀ U d)

/-- The lift of a cone of the site through `V` is a morphism over `S`. -/
theorem opensSpecStalkSiteLift_comp_apexHom
    (d : Cone (opensSpecStalkSiteDiagram B S hS s W₀ U)) :
    opensSpecStalkSiteLift B S hS s W₀ U d ≫ opensSpecStalkApexHom S s W₀ U = d.pt.hom.hom := by
  have hcompat := opensCone_π_app_comp_stageHom S s W₀ U (Over.mk (𝟙 W₀))
  have hfac := (isLimitOpensSpecStalkCone S s W₀ U).fac_assoc
    (schemeConeOfSiteCone B S hS s W₀ U d) (Over.mk (𝟙 W₀))
    (opensSpecStalkStageHom S s W₀ U (Over.mk (𝟙 W₀)))
  have hover := (BigFppfOver.hom_hom_comp B S hS (d.π.app (Over.mk (𝟙 W₀)))).symm
  rw [← hcompat]
  exact hfac.trans hover

/-- **`V = Spec 𝒪_{S, s} ∩ U` is the limit of the overlaps `W ∩ U` in the big fppf category over
`S`.**  This is the identification that
[Stacks, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90) and
[Stacks, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91) use on the overlap side, read in the
big fppf category over `S` instead of in the category of schemes. -/
noncomputable def isLimitOpensSpecStalkSiteCone :
    IsLimit (opensSpecStalkSiteCone B S hS s W₀ U) where
  lift d :=
    Over.homMk (ObjectProperty.homMk (opensSpecStalkSiteLift B S hS s W₀ U d))
      (by
        apply ObjectProperty.hom_ext
        exact opensSpecStalkSiteLift_comp_apexHom B S hS s W₀ U d)
  fac d j :=
    @Subsingleton.elim _
      (subsingleton_hom_opensSpecStalkSiteDiagram_obj B S hS s W₀ U _ j) _ _
  uniq d m hm := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    refine (isLimitOpensSpecStalkCone S s W₀ U).uniq
      (schemeConeOfSiteCone B S hS s W₀ U d) _ fun j => ?_
    have h := congrArg (BigFppfOver.toScheme B S hS).map (hm j)
    rw [Functor.map_comp] at h
    exact h

/-- **The underlying schemes of the cone of `AlgebraicGeometry.opensSpecStalkSiteCone` form a limit
of schemes.** -/
noncomputable def isLimitSchemeConeOpensSpecStalkSiteCone :
    IsLimit (schemeConeOfSiteCone B S hS s W₀ U (opensSpecStalkSiteCone B S hS s W₀ U)) :=
  IsLimit.ofIsoLimit (isLimitOpensSpecStalkCone S s W₀ U)
    (Cone.ext (Iso.refl _) fun _ => (Category.id_comp _).symm)

/-- The diagram of overlaps in the site, composed with the underlying-scheme functor, is
`AlgebraicGeometry.opensSpecStalkDiagram`, by the isomorphism whose components are identities. -/
noncomputable def opensSpecStalkSiteDiagramCompIso :
    opensSpecStalkSiteDiagram B S hS s W₀ U ⋙ BigFppfOver.toScheme B S hS ≅
      opensSpecStalkDiagram S s W₀ U :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun f =>
    (Category.comp_id _).trans
      ((toScheme_map_opensSpecStalkSiteDiagram_map B S hS s W₀ U f).trans
        (Category.id_comp _).symm)

/-- Every component of `AlgebraicGeometry.opensSpecStalkSiteDiagramCompIso` is the identity. -/
@[simp]
theorem opensSpecStalkSiteDiagramCompIso_hom_app (j : Over W₀) :
    (opensSpecStalkSiteDiagramCompIso B S hS s W₀ U).hom.app j = 𝟙 _ :=
  rfl

/-- **The cone of `AlgebraicGeometry.opensSpecStalkSiteCone` is a limit after applying the
underlying-scheme functor**, in the `CategoryTheory.Functor.mapCone` form. -/
@[sga "3 VIB 10.10" "10.10 a), special case", sga "4½ Arcata 2.4.1" "more general"]
noncomputable def isLimitMapConeOpensSpecStalkSiteCone :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone (opensSpecStalkSiteCone B S hS s W₀ U)) :=
  (IsLimit.postcomposeHomEquiv (opensSpecStalkSiteDiagramCompIso B S hS s W₀ U) _)
    (IsLimit.ofIsoLimit (isLimitOpensSpecStalkCone S s W₀ U)
      (Cone.ext (Iso.refl _) fun j =>
        ((Category.id_comp _).trans ((Category.comp_id _).trans
          (toScheme_map_opensSpecStalkSiteπ B S hS s W₀ U j))).symm))

end AlgebraicGeometry

end
