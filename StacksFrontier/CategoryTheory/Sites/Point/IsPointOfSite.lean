module

public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksFrontier.CategoryTheory.Elements
public import StacksFrontier.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.CategoryTheory.Sites.Point.OfPreservesFiniteLimits
public import StacksFrontier.CategoryTheory.Sites.Point.StalkExact
public import StacksFrontier.CategoryTheory.Sites.Point.StalkFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Points of a site in the sense of the Stacks project

Let `C` be a site. Stacks defines a *point* of `C` to be a functor `u : C ⥤ Set` such that

1. for every covering `{U_i → U}` the map `∐ u(U_i) → u(U)` is surjective;
2. for every covering `{U_i → U}` and every morphism `V → U` the maps
   `u(U_i ×_U V) → u(U_i) ×_{u(U)} u(V)` are bijective;
3. the stalk functor `Sh(C) ⥤ Set`, `F ↦ F_p = colim_{(U, x)} F(U)`, is left exact.

This is `CategoryTheory.Functor.IsPointOfSite`. Mathlib's notion of a point,
`CategoryTheory.GrothendieckTopology.Point`, instead asks that the category of elements of `u`
be cofiltered and initially small and that `u` be jointly surjective on covering sieves. The two
notions agree: a functor is a point in the sense of Stacks if and only if it is the fiber functor
of a (necessarily unique) point in the sense of Mathlib.

The substantive direction is that a Stacks point gives a Mathlib point, i.e. that `u.Elements` is
cofiltered. By (1) and (2) the presheaves `u^p E : U ↦ Map(u(U), E)` are sheaves, so by Stacks
00Y8 the stalk of a presheaf is the stalk of its sheafification; combined with (3) and the left
exactness of sheafification, the stalk functor on *presheaves* is left exact, and therefore its
category of elements is cofiltered. Since every element of a stalk is represented by a triple
`(Z, z, s)` and the stalk of `h_X` is `u(X)` (Stacks 00Y6), this cofilteredness descends to the
category of elements of `u`.

## Main definitions

* `CategoryTheory.Functor.IsPointOfSite`: Stacks' definition of a point of a site.
* `CategoryTheory.Functor.IsPointOfSite.toPoint`: the Mathlib point with fiber functor `u`.
* `CategoryTheory.Functor.pointOfSiteEquiv`: Stacks points of `C` are Mathlib points of `C`.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.isPointOfSite`: the fiber functor of a Mathlib point
  is a Stacks point.
* `CategoryTheory.Functor.IsPointOfSite.isSheaf_presheafPushforward`: Stacks 00Y8 (1) for a
  Stacks point.
* `CategoryTheory.Functor.IsPointOfSite.isCofiltered_elements`: the category of elements of a
  Stacks point is cofiltered.
* `CategoryTheory.Functor.isPointOfSite_iff_exists_point`: the two notions agree.

## Implementation notes

As elsewhere in this library, a site is a small category `C : Type w` with a Grothendieck
topology `J`, sets are `Type w`, and a covering `{U_i → U}` is a family whose generated sieve is
`J`-covering. Smallness is no restriction: a site in the sense of Stacks has a *set* of
coverings containing `{𝟙_U}` for every object `U`, so its objects form a set. Stacks' axioms for a
site require the fibre products `U_i ×_U V` to exist for every
covering `{U_i → U}` and every `V → U`; since every morphism `f : V → U` is a member of the
covering `{f, 𝟙_U}`, in this language that axiom says exactly that `C` has pullbacks. Condition
(2) of the definition is stated for the fibre products that exist, and the comparison with
Mathlib's points, which uses condition (2), assumes `HasPullbacks C`.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite PresheafPushforwardStalkAdjunction

universe w

variable {C : Type w} [SmallCategory C]

/-- The stalk functor on sheaves of sets at the fiber functor of a point of the site `(C, J)` in
Mathlib's sense is left exact: it is Mathlib's `Point.sheafFiber`, and this is
`Point.sheafFiber_leftExact`. -/
theorem GrothendieckTopology.Point.preservesFiniteLimits_sheafToPresheaf_comp_presheafStalk
    {J : GrothendieckTopology C} (Φ : J.Point.{w}) :
    PreservesFiniteLimits (sheafToPresheaf J (Type w) ⋙ presheafStalk Φ.fiber) :=
  Φ.sheafFiber_leftExact

/-- **Stacks 00Y5.** A *point* of the site `(C, J)` is a functor `u : C ⥤ Set` such that

1. for every covering `{U_i → U}` the map `∐ u(U_i) → u(U)` is surjective;
2. for every covering `{U_i → U}` and every morphism `V → U` the maps
   `u(U_i ×_U V) → u(U_i) ×_{u(U)} u(V)` are bijective;
3. the stalk functor `Sh(C) ⥤ Set`, `F ↦ F_p`, is left exact, where `F_p` is the colimit of the
   sections `F(U)` over the opposite of the category of neighbourhoods `(U, x)`, `x ∈ u(U)`
   (`PresheafPushforwardStalkAdjunction.presheafStalk`, Stacks 04EH).

A covering is a family `{U_i → U}` whose generated sieve is `J`-covering. That this is the same
notion as Mathlib's `GrothendieckTopology.Point` is `Functor.isPointOfSite_iff_exists_point`. -/
@[stacks 00Y5 "Stacks' definition, with conditions (1), (2) and (3) as fields; it is
  identified with Mathlib's `GrothendieckTopology.Point` by
  `Functor.isPointOfSite_iff_exists_point` and `Functor.pointOfSiteEquiv`."]
structure Functor.IsPointOfSite (u : C ⥤ Type w) (J : GrothendieckTopology C) : Prop where
  /-- Condition (1): for a covering `{U_i → U}`, the map `∐ u(U_i) → u(U)` is surjective. -/
  surjective {I : Type w} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U)
    (hf : Sieve.ofArrows Ui f ∈ J U) (x : u.obj U) :
    ∃ (i : I) (y : u.obj (Ui i)), u.map (f i) y = x
  /-- Condition (2): for a covering `{U_i → U}` and a morphism `V → U`, the comparison maps
  `u(U_i ×_U V) → u(U_i) ×_{u(U)} u(V)` are bijective (whenever the fibre product exists, which
  for a site in the sense of Stacks is always the case). -/
  bijective {I : Type w} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U)
    (hf : Sieve.ofArrows Ui f ∈ J U) {V : C} (g : V ⟶ U) (i : I) [HasPullback (f i) g] :
    Function.Bijective (pullbackComparison u (f i) g)
  /-- Condition (3): the stalk functor on sheaves of sets is left exact. -/
  preservesFiniteLimits_stalk :
    PreservesFiniteLimits (sheafToPresheaf J (Type w) ⋙ presheafStalk u)

namespace Functor.IsPointOfSite

variable {u : C ⥤ Type w} {J : GrothendieckTopology C} (h : u.IsPointOfSite J)
include h

/-- Condition (1) of a Stacks point, for covering sieves: every element of `u(U)` comes from
`u(V)` along some arrow `V ⟶ U` of a given covering sieve of `U`. -/
theorem coveringJointlySurjective : u.CoveringJointlySurjective J :=
  Functor.CoveringJointlySurjective.of_ofArrows fun f hf x => h.surjective f hf x

section HasPullbacks

variable [HasPullbacks C]

/-- Condition (2) of a Stacks point, in the form used to glue: if `f : V ⟶ U` is an arrow of a
covering sieve of `U` and `g : W ⟶ U` is any morphism, two elements `y ∈ u(V)` and `z ∈ u(W)`
with the same image in `u(U)` come from one element of `u(V ×_U W)`. -/
theorem exists_pullback {U : C} (S : Sieve U) (hS : S ∈ J U) {V W : C} {f : V ⟶ U} (hf : S f)
    (g : W ⟶ U) (y : u.obj V) (z : u.obj W) (hyz : u.map f y = u.map g z) :
    ∃ t : u.obj (pullback f g),
      u.map (pullback.fst f g) t = y ∧ u.map (pullback.snd f g) t = z := by
  let I := Σ V : C, {f : V ⟶ U // S f}
  have hle : S ≤ Sieve.ofArrows (fun i : I => i.1) (fun i => i.2.1) := fun V f hf =>
    Sieve.ofArrows_mk _ (fun i : I => i.2.1) ⟨V, f, hf⟩
  obtain ⟨t, ht⟩ := (h.bijective (fun i : I => i.2.1) (J.superset_covering hle hS) g
    ⟨V, f, hf⟩).2 ((Types.pullbackIsoPullback (u.map f) (u.map g)).inv ⟨(y, z), hyz⟩)
  refine ⟨t, ?_, ?_⟩
  · have h₁ := ConcreteCategory.congr_hom (pullbackComparison_comp_fst u f g) t
    have h₂ := congrArg (pullback.fst (u.map f) (u.map g)) ht
    rw [Types.pullbackIsoPullback_inv_fst_apply] at h₂
    exact h₁.symm.trans h₂
  · have h₁ := ConcreteCategory.congr_hom (pullbackComparison_comp_snd u f g) t
    have h₂ := congrArg (pullback.snd (u.map f) (u.map g)) ht
    rw [Types.pullbackIsoPullback_inv_snd_apply] at h₂
    exact h₁.symm.trans h₂

/-- **Stacks 00Y8 (1)** for a Stacks point: the presheaf `u^p E : U ↦ Map(u(U), E)` is a sheaf
for every set `E`. -/
theorem isSheaf_presheafPushforward (E : Type w) :
    Presheaf.IsSheaf J ((presheafPushforward u).obj E) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U S hS x hx
  have key : ∀ {W₁ W₂ : C} (g₁ : W₁ ⟶ U) (g₂ : W₂ ⟶ U) (h₁ : S g₁) (h₂ : S g₂)
      (z₁ : u.obj W₁) (z₂ : u.obj W₂), u.map g₁ z₁ = u.map g₂ z₂ →
        x g₁ h₁ z₁ = x g₂ h₂ z₂ := by
    intro W₁ W₂ g₁ g₂ h₁ h₂ z₁ z₂ hz
    obtain ⟨t, ht₁, ht₂⟩ := h.exists_pullback S hS h₁ g₂ z₁ z₂ hz
    have hc := congrFun (hx (pullback.fst g₁ g₂) (pullback.snd g₁ g₂) h₁ h₂
      pullback.condition) t
    rw [presheafPushforward_obj_map_apply, presheafPushforward_obj_map_apply] at hc
    simpa only [Quiver.Hom.unop_op, ht₁, ht₂] using hc
  choose V f hf y hy using h.coveringJointlySurjective S hS
  refine ⟨fun a => x (f a) (hf a) (y a), ?_, ?_⟩
  · intro W g hg
    funext b
    rw [presheafPushforward_obj_map_apply]
    exact key _ _ _ _ _ _ ((hy _).trans rfl)
  · intro t ht
    funext a
    have := congrFun (ht (f a) (hf a)) (y a)
    rw [presheafPushforward_obj_map_apply] at this
    exact (congrArg t (hy a)).symm.trans this

/-- **Stacks 00Y8 (3)** for a Stacks point: the map `F_p → (F^#)_p` from the stalk of a presheaf
of sets to the stalk of its sheafification is an isomorphism. -/
theorem isIso_presheafStalk_map_toSheafify (F : Cᵒᵖ ⥤ Type w) :
    IsIso ((presheafStalk u).map (toSheafify J F)) := by
  have hb := fun E : Type w => main_theorem00Y8 J (presheafStalk u) (presheafPushforward u)
    (PresheafPushforwardStalkAdjunction.adjunction u) h.isSheaf_presheafPushforward F E
  obtain ⟨r, hr⟩ := (hb _).2 (𝟙 _)
  replace hr : (presheafStalk u).map (toSheafify J F) ≫ r = 𝟙 _ := hr
  refine ⟨r, hr, (hb _).1 ?_⟩
  change (presheafStalk u).map (toSheafify J F) ≫ r ≫ (presheafStalk u).map (toSheafify J F) =
    (presheafStalk u).map (toSheafify J F) ≫ 𝟙 _
  rw [← Category.assoc, hr, Category.id_comp, Category.comp_id]

/-- For a Stacks point the stalk functor on *presheaves* of sets is left exact: it is the
composite of sheafification, which is left exact, with the stalk functor on sheaves, which is
left exact by condition (3). -/
theorem preservesFiniteLimits_presheafStalk : PreservesFiniteLimits (presheafStalk u) := by
  have : ∀ F, IsIso ((Functor.whiskerRight (sheafificationAdjunction J (Type w)).unit
      (presheafStalk u)).app F) := fun F => by
    rw [Functor.whiskerRight_app, sheafificationAdjunction_unit_app]
    exact h.isIso_presheafStalk_map_toSheafify F
  have : IsIso (Functor.whiskerRight (sheafificationAdjunction J (Type w)).unit
      (presheafStalk u)) := NatIso.isIso_of_isIso_app _
  have := h.preservesFiniteLimits_stalk
  exact preservesFiniteLimits_of_natIso
    ((Functor.leftUnitor _).symm ≪≫ asIso (Functor.whiskerRight
      (sheafificationAdjunction J (Type w)).unit (presheafStalk u)) ≪≫
        Functor.associator _ _ _).symm

/-- The category of elements (the category of neighbourhoods) of a Stacks point is cofiltered.

The category of elements of the left exact functor `presheafStalk u` is cofiltered. An element of
a stalk `F_p` is a class `[(Z, z, s)]`, and the map `F_p → (h_X)_p = u(X)` induced by
`φ : F ⟶ h_X` sends it to `u(φ(s))(z)`; so a cone in the category of elements of the stalk
functor over neighbourhoods of `u` yields one in the category of elements of `u`. -/
theorem isCofiltered_elements : IsCofiltered u.Elements := by
  have := h.preservesFiniteLimits_presheafStalk
  have hcof : IsCofiltered (presheafStalk u).Elements := (presheafStalk u).isCofiltered_elements
  have key : ∀ (P : Cᵒᵖ ⥤ Type w) (t : (presheafStalk u).obj P),
      ∃ (Z : C) (z : u.obj Z) (s : P.obj (op Z)), stalkMk u P Z z s = t := by
    intro P t
    obtain ⟨⟨j⟩, s, rfl⟩ := Types.jointly_surjective' (F := (Functor.Elements.π u).op ⋙ P) t
    exact ⟨j.1, j.2, s, rfl⟩
  have hmap : ∀ {P : Cᵒᵖ ⥤ Type w} {X : C} (φ : P ⟶ yoneda.obj X) (Z : C) (z : u.obj Z)
      (s : P.obj (op Z)),
      thetaInv u X ((presheafStalk u).map φ (stalkMk u P Z z s)) = u.map (φ.app (op Z) s) z := by
    intro P X φ Z z s
    unfold stalkMk
    rw [presheafStalk_map_ι_apply]
    unfold thetaInv
    rw [colimit.ι_desc_apply]
    rfl
  have hel : ∀ {P : Cᵒᵖ ⥤ Type w} {X : C} (φ : P ⟶ yoneda.obj X) (x : u.obj X)
      (t : (presheafStalk u).obj P), (presheafStalk u).map φ t = theta u X x →
      ∃ (Z : C) (z : u.obj Z) (s : P.obj (op Z)), stalkMk u P Z z s = t ∧
        u.map (φ.app (op Z) s) z = x := by
    intro P X φ x t ht
    obtain ⟨Z, z, s, rfl⟩ := key P t
    refine ⟨Z, z, s, rfl, ?_⟩
    have := congrArg (thetaInv u X) ht
    rwa [hmap, thetaInv_theta] at this
  refine { cone_objs := ?_, cone_maps := ?_, nonempty := ?_ }
  · rintro @⟨Xa, xa⟩ @⟨Xb, xb⟩
    obtain ⟨W, φ, ψ, -⟩ := IsCofilteredOrEmpty.cone_objs
      ((presheafStalk u).elementsMk (yoneda.obj Xa) (theta u Xa xa))
      ((presheafStalk u).elementsMk (yoneda.obj Xb) (theta u Xb xb))
    obtain ⟨Z, z, s, hs, ha⟩ := hel φ.1 xa W.2 φ.2
    have hb : u.map (ψ.1.app (op Z) s) z = xb := by
      have := congrArg (thetaInv u Xb) ψ.2
      rw [← hmap ψ.1 Z z s, hs]
      exact this.trans (thetaInv_theta u Xb xb)
    exact ⟨u.elementsMk Z z, ⟨φ.1.app (op Z) s, ha⟩, ⟨ψ.1.app (op Z) s, hb⟩, trivial⟩
  · rintro @⟨Xa, xa⟩ @⟨Xb, xb⟩ α β
    let α' : (presheafStalk u).elementsMk (yoneda.obj Xa) (theta u Xa xa) ⟶
        (presheafStalk u).elementsMk (yoneda.obj Xb) (theta u Xb xb) :=
      ⟨yoneda.map α.1, by
        change (presheafStalk u).map (yoneda.map α.1) (theta u Xa xa) = theta u Xb xb
        rw [← Phi_naturality u α.1 xa, α.2]⟩
    let β' : (presheafStalk u).elementsMk (yoneda.obj Xa) (theta u Xa xa) ⟶
        (presheafStalk u).elementsMk (yoneda.obj Xb) (theta u Xb xb) :=
      ⟨yoneda.map β.1, by
        change (presheafStalk u).map (yoneda.map β.1) (theta u Xa xa) = theta u Xb xb
        rw [← Phi_naturality u β.1 xa, β.2]⟩
    obtain ⟨W, k, hk⟩ := IsCofilteredOrEmpty.cone_maps α' β'
    obtain ⟨Z, z, s, -, ha⟩ := hel k.1 xa W.2 k.2
    refine ⟨u.elementsMk Z z, ⟨k.1.app (op Z) s, ha⟩, ?_⟩
    apply Functor.Elements.hom_ext
    change k.1.app (op Z) s ≫ α.1 = k.1.app (op Z) s ≫ β.1
    have hk' := congrArg (fun m => m.hom.app (op Z) s) hk
    simpa [α', β'] using hk'
  · obtain ⟨W⟩ := hcof.nonempty
    obtain ⟨Z, z, -, -⟩ := key W.1 W.2
    exact ⟨u.elementsMk Z z⟩

/-- The point of the site `(C, J)` in Mathlib's sense whose fiber functor is a given Stacks
point `u`. -/
noncomputable def toPoint : J.Point.{w} where
  fiber := u
  isCofiltered := h.isCofiltered_elements
  initiallySmall := CategoryOfElements.initiallySmall_elements_of_essentiallySmall u
  jointly_surjective R hR x := h.coveringJointlySurjective R hR x

@[simp]
theorem toPoint_fiber : h.toPoint.fiber = u :=
  rfl

end HasPullbacks

end Functor.IsPointOfSite

/-- The fiber functor of a point of the site `(C, J)` in Mathlib's sense is a point in the sense
of Stacks: the three conditions are `Point.fiber_jointly_surjective_of_ofArrows`,
`Point.fiber_pullbackComparison_bijective` and `Point.sheafFiber_leftExact`. -/
theorem GrothendieckTopology.Point.isPointOfSite {J : GrothendieckTopology C}
    (Φ : J.Point.{w}) : Φ.fiber.IsPointOfSite J where
  surjective f hf x := Φ.fiber_jointly_surjective_of_ofArrows f hf x
  bijective := fun {_ _ _} f _ {_} g i _ => Φ.fiber_pullbackComparison_bijective (f i) g
  preservesFiniteLimits_stalk := Φ.preservesFiniteLimits_sheafToPresheaf_comp_presheafStalk

/-- **Stacks 00Y5, comparison with Mathlib.** A functor `u : C ⥤ Set` is a point of the site
`(C, J)` in the sense of Stacks if and only if it is the fiber functor of a point of `(C, J)` in
the sense of Mathlib. -/
theorem Functor.isPointOfSite_iff_exists_point [HasPullbacks C] {J : GrothendieckTopology C}
    (u : C ⥤ Type w) :
    u.IsPointOfSite J ↔ ∃ Φ : J.Point.{w}, Φ.fiber = u :=
  ⟨fun h => ⟨h.toPoint, rfl⟩, by rintro ⟨Φ, rfl⟩; exact Φ.isPointOfSite⟩

/-- Points of the site `(C, J)` in the sense of Stacks are the same thing as points in the sense
of Mathlib: the bijection sends a Stacks point `u` to the Mathlib point with fiber functor `u`. -/
noncomputable def Functor.pointOfSiteEquiv [HasPullbacks C] (J : GrothendieckTopology C) :
    {u : C ⥤ Type w // u.IsPointOfSite J} ≃ J.Point.{w} where
  toFun u := u.2.toPoint
  invFun Φ := ⟨Φ.fiber, Φ.isPointOfSite⟩
  left_inv _ := rfl
  right_inv _ := GrothendieckTopology.Point.eq_of_fiber_eq rfl

end CategoryTheory
