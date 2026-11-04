module

public import StacksFrontier.CategoryTheory.Sites.DenseSubsite.NatIsoTransport
public import StacksFrontier.CategoryTheory.Sites.Topos.PushforwardRepresentableComparison

/-!
# Recognising the direct image of a morphism of topoi from its inverse image on a dense subsite

Let `J` and `K` be subcanonical topologies on categories `C` and `D`, let
`g : Sh(D) ⟶ Sh(C)` be a morphism of topoi, let `u : C ⥤ D` be a continuous functor, and let
`G : C₀ ⥤ C` be a continuous functor from a further site `(C₀, J₀)`.
`MorphismOfTopoi.pushforwardIsoSheafPushforwardContinuous` produces `g_* ≅ u^s` out of an
isomorphism `g⁻¹h_V ≅ h_{u V}` natural in *every* object `V` of `C`.  This file produces the
same conclusion out of an isomorphism given at the objects of the image of `G` only, provided `G`
exhibits `(C₀, J₀)` as a dense subsite of `(C, J)`.

The passage is in two steps, and the first is where the content is:

* with `ρ` the restriction of sheaves along `G`, the comparison on the subsite gives
  `g_* ⋙ ρ ≅ u^s ⋙ ρ`.  This is the computation of
  `MorphismOfTopoi.pushforwardIsoSheafPushforwardContinuous` performed at the objects `G V₀`
  alone: the sections of `g_*F` over `G V₀` are the maps `g⁻¹h_{G V₀} ⟶ F`, hence the maps
  `h_{u (G V₀)} ⟶ F`, hence the sections of `F` over `u (G V₀)`.  Only the component of the
  comparison at `G V₀` and its naturality square at morphisms `G k` are used, which is why
  `MorphismOfTopoi.representableSectionsEquivOfIso` is stated for a single object;
* `g_*` and `u^s` are functors *valued* in sheaves on `(C, J)`, so an isomorphism of their
  restrictions to a dense subsite is an isomorphism of them —
  `CategoryTheory.Functor.IsDenseSubsite.natIsoOfRestriction`.

## This is not a comparison at the non-affine charts in disguise

The second step is cancellation on the **right**, and that is the only direction a dense subsite
provides; see the module documentation of
`StacksFrontier/CategoryTheory/Sites/DenseSubsite/NatIsoTransport.lean`.  In particular the
hypothesis of this file does **not** yield an isomorphism `g⁻¹h_V ≅ h_{u V}` at an object `V`
outside the image of `G`: recovering `J.yoneda ⋙ g.inverseImage ≅ u ⋙ K.yoneda`, a comparison of
functors *indexed* by `C`, from its composite with `G` would be cancellation on the **left**,
which is false.  What is recovered is only the isomorphism of direct images — and that is all the
existence half of [Stacks Project, Tag 04I6] consumes, through
`AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_pushforwardIso`.

## Main definitions

* `MorphismOfTopoi.restrictedPushforwardObjIso` — for one sheaf `F`, the isomorphism of sheaves
  on the subsite `(ρ ∘ g_*) F ≅ (ρ ∘ u^s) F`.
* `MorphismOfTopoi.pushforwardRestrictionIsoSheafPushforwardContinuous` — the isomorphism of
  functors `g_* ⋙ ρ ≅ u^s ⋙ ρ` it assembles into.
* `MorphismOfTopoi.pushforwardIsoSheafPushforwardContinuousOfDenseSubsite` — the resulting
  `g_* ≅ u^s`, for `G` a dense subsite.

## Main results

* `MorphismOfTopoi.map_pushforwardIsoSheafPushforwardContinuousOfDenseSubsite_hom_app` — the
  restriction to the subsite of that isomorphism is the one it was built from.  This is what
  pins the isomorphism down: `ρ` is faithful, so no other morphism restricts to it.

## References

* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v₀ u₀ u₁ u₂

namespace MorphismOfTopoi

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C : Type u₁} [Category.{w} C]
  {D : Type u₂} [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.Subcanonical] [K.Subcanonical]
  (g : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w)))
  {u : C ⥤ D} [u.IsContinuous J K] {G : C₀ ⥤ C}
  (J₀ : GrothendieckTopology C₀) [G.IsContinuous J₀ J]
  (α : G ⋙ J.yoneda ⋙ g.inverseImage ≅ G ⋙ u ⋙ K.yoneda)

/-- **The sections bijections at the objects of the subsite assemble into an isomorphism of
sheaves on the subsite** `ρ(g_*F) ≅ ρ(u^sF)`, where `ρ` is restriction along `G`.

Both sides have, at `V₀`, the sections of the respective sheaf over `G V₀`, so this is
`MorphismOfTopoi.representableSectionsEquivOfIso` at the component of `α` at `V₀`, its
naturality being the naturality square of `α`. -/
def restrictedPushforwardObjIso (F : Sheaf K (Type w)) :
    (G.sheafPushforwardContinuous (Type w) J₀ J).obj (g.pushforward.obj F) ≅
      (G.sheafPushforwardContinuous (Type w) J₀ J).obj
        ((u.sheafPushforwardContinuous (Type w) J K).obj F) :=
  (fullyFaithfulSheafToPresheaf J₀ (Type w)).preimageIso
    (NatIso.ofComponents
      (fun V₀ => Equiv.toIso
        (representableSectionsEquivOfIso g F (V := G.obj V₀.unop) (α.app V₀.unop)))
      (fun {V₀ V₀'} k => by
        ext x
        exact representableSectionsEquivOfIso_naturality g F (G.map k.unop)
          (α.inv.naturality k.unop).symm x))

/-- **A morphism of topoi whose inverse image matches a continuous functor on representables at
the objects of a subsite has that functor's direct image there.**  If `g⁻¹h_{G V₀} ≅ h_{u (G V₀)}`
naturally in the object `V₀` of the subsite, then `g_* ⋙ ρ ≅ u^s ⋙ ρ` for `ρ` the restriction of
sheaves along `G`. -/
def pushforwardRestrictionIsoSheafPushforwardContinuous :
    g.pushforward ⋙ G.sheafPushforwardContinuous (Type w) J₀ J ≅
      u.sheafPushforwardContinuous (Type w) J K ⋙
        G.sheafPushforwardContinuous (Type w) J₀ J :=
  NatIso.ofComponents (restrictedPushforwardObjIso g J₀ α) (fun {F F'} β => by
    ext V₀ x
    exact representableSectionsEquivOfIso_naturality_sheaf g β (α.app V₀.unop) x)

/-- The component of `MorphismOfTopoi.pushforwardRestrictionIsoSheafPushforwardContinuous` at a
sheaf `F` and an object `V₀` of the subsite is `MorphismOfTopoi.representableSectionsEquivOfIso`
applied to the component of `α` at `V₀`. -/
@[simp]
theorem pushforwardRestrictionIsoSheafPushforwardContinuous_hom_app_hom_app
    (F : Sheaf K (Type w)) (V₀ : C₀ᵒᵖ)
    (x : (g.pushforward.obj F).obj.obj (op (G.obj V₀.unop))) :
    ((pushforwardRestrictionIsoSheafPushforwardContinuous g J₀ α).hom.app F).hom.app V₀ x =
      representableSectionsEquivOfIso g F (V := G.obj V₀.unop) (α.app V₀.unop) x :=
  rfl

/-- **The restricted isomorphism of a comparison available at every object is the restriction of
the isomorphism of direct images that comparison produces.** -/
theorem pushforwardRestrictionIsoSheafPushforwardContinuous_isoWhiskerLeft
    (α' : J.yoneda ⋙ g.inverseImage ≅ u ⋙ K.yoneda) (F : Sheaf K (Type w)) :
    (pushforwardRestrictionIsoSheafPushforwardContinuous g J₀
          (Functor.isoWhiskerLeft G α')).hom.app F =
      (G.sheafPushforwardContinuous (Type w) J₀ J).map
        ((pushforwardIsoSheafPushforwardContinuous g α').hom.app F) :=
  rfl

section DenseSubsite

variable [G.IsDenseSubsite J₀ J]

/-- **A morphism of topoi whose inverse image matches a continuous functor on the representables
of a dense subsite has that functor's direct image.**  If `g⁻¹h_{G V₀} ≅ h_{u (G V₀)}` naturally
in the object `V₀` of a dense subsite `G : (C₀, J₀) ⥤ (C, J)`, then `g_* ≅ u^s`.

The comparison is *not* assumed at the objects of `C` outside the image of `G`, and none is
produced: the isomorphism of the direct images is obtained from its restriction to the subsite,
restriction being fully faithful. -/
def pushforwardIsoSheafPushforwardContinuousOfDenseSubsite :
    g.pushforward ≅ u.sheafPushforwardContinuous (Type w) J K :=
  Functor.IsDenseSubsite.natIsoOfRestriction J₀ J G (Type w)
    (pushforwardRestrictionIsoSheafPushforwardContinuous g J₀ α)

/-- **The isomorphism of direct images restricts to the subsite as the isomorphism it was built
from.**  Since restriction along `G` is faithful, this characterizes
`MorphismOfTopoi.pushforwardIsoSheafPushforwardContinuousOfDenseSubsite`. -/
theorem map_pushforwardIsoSheafPushforwardContinuousOfDenseSubsite_hom_app
    (F : Sheaf K (Type w)) :
    (G.sheafPushforwardContinuous (Type w) J₀ J).map
        ((pushforwardIsoSheafPushforwardContinuousOfDenseSubsite g J₀ α).hom.app F) =
      (pushforwardRestrictionIsoSheafPushforwardContinuous g J₀ α).hom.app F :=
  Functor.map_preimage _ _

/-- **On a comparison available at every object, this file's construction agrees with
`MorphismOfTopoi.pushforwardIsoSheafPushforwardContinuous`.**  Restricting to the subsite loses
nothing and recovers the same isomorphism of direct images, by faithfulness of restriction. -/
theorem pushforwardIsoSheafPushforwardContinuousOfDenseSubsite_isoWhiskerLeft
    (α' : J.yoneda ⋙ g.inverseImage ≅ u ⋙ K.yoneda) :
    pushforwardIsoSheafPushforwardContinuousOfDenseSubsite g J₀ (Functor.isoWhiskerLeft G α') =
      pushforwardIsoSheafPushforwardContinuous g α' := by
  refine Iso.ext (NatTrans.ext (funext fun F => ?_))
  refine (G.sheafPushforwardContinuous (Type w) J₀ J).map_injective ?_
  rw [map_pushforwardIsoSheafPushforwardContinuousOfDenseSubsite_hom_app]
  exact pushforwardRestrictionIsoSheafPushforwardContinuous_isoWhiskerLeft g J₀ α' F

end DenseSubsite

end MorphismOfTopoi

end
