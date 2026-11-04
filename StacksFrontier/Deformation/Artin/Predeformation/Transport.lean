module

public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.CofiberedPresentation.SmoothPresentation
public import StacksFrontier.Deformation.Artin.Predeformation.ThinVertical

/-!
# Transport of predeformation categories along a functor over the site

Let `Φ : 𝒳 ⟶ 𝒴` be a functor between categories fibred in groupoids over the big fppf site of
`S`, commuting strictly with the projections, let `x₀` be an object of `𝒳` over `Spec k` and let
`φ : y₀ ⟶ Φ(x₀)` be a vertical isomorphism in `𝒴`. Sending a deformation `x₀ ⟶ x` of `x₀` to the
deformation `y₀ ⟶ Φ(x₀) ⟶ Φ(x)` of `y₀` is a functor `𝓕_{𝒳,k,x₀} ⟶ 𝓕_{𝒴,k,y₀}` over `𝒞_Λ`.

This file proves that this functor is an equivalence over `𝒞_Λ` as soon as `Φ` is faithful, lifts
the arrows between images of deformations which are compatible with the arrows out of `x₀`, and
lifts every deformation of `y₀` up to a vertical isomorphism. In particular an equivalence
`𝒳 ≃ 𝒴` over the site induces an equivalence of predeformation categories at `x₀` and at any
object vertically isomorphic to the image of `x₀`.

## Main definitions

* `Deformation.Artin.transportPredeformationFunctor`: the functor `(x₀ ⟶ x) ↦ (y₀ ⟶ Φ(x))`.

## Main results

* `Deformation.Artin.transportPredeformationEquivalence`: the general criterion.
* `Deformation.Artin.predeformationEquivalenceOfEquivalenceOver`: an equivalence over the site
  induces an equivalence of predeformation categories.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u u₁ v₁ u₂ v₂

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
variable (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS) (Φ : X ⥤ Y)
  (hΦ : Φ ⋙ pY = pX) (x₀ : X)
  (hx₀ : (pX ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) (y₀ : Y)
  (hy₀ : (pY ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (φ : y₀ ⟶ Φ.obj x₀)

include hΦ in
/-- If `Φ ⋙ pY = pX`, then `Φ(x)` and `x` lie over the same scheme over `S`. -/
theorem transport_obj_eq (x : X) :
    (pY ⋙ Over.post B.inclusion).obj (Φ.obj x) = (pX ⋙ Over.post B.inclusion).obj x := by
  subst hΦ; rfl

/-- The deformation `y₀ ⟶ Φ(x₀) ⟶ Φ(x)` of `y₀` attached to a deformation `x₀ ⟶ x` of `x₀`. -/
abbrev transportDeformationObject
    (hφ : (pY ⋙ Over.post B.inclusion).map φ =
      eqToHom (hy₀.trans ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀).symm))
    (d : DeformationObject iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀) :
    DeformationObject iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀ where
  algebra := d.algebra
  point := Φ.obj d.point
  arrow := φ ≫ Φ.map d.arrow
  base := (transport_obj_eq B hS pX pY Φ hΦ d.point).trans d.base
  arrow_base := by
    subst hΦ
    rw [← d.arrow_base, Functor.map_comp, hφ, Over.comp_left, Over.eqToHom_left]
    simp only [Category.assoc, eqToHom_trans_assoc]
    rfl

/-- The morphism of deformations `y₀ ⟶ Φ(x)` induced by a morphism of deformations of `x₀`. -/
abbrev transportedDeformationMorphism
    (hφ : (pY ⋙ Over.post B.inclusion).map φ =
      eqToHom (hy₀.trans ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀).symm))
    {a b : DeformationObject iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀}
    (m : DeformationMorphism iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀ a b) :
    DeformationMorphism iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀
      (transportDeformationObject B hS iΛ pX pY Φ hΦ x₀ hx₀ y₀ hy₀ φ hφ a)
      (transportDeformationObject B hS iΛ pX pY Φ hΦ x₀ hx₀ y₀ hy₀ φ hφ b) where
  ringHom := m.ringHom
  arrow := Φ.map m.arrow
  triangle := by
    change (φ ≫ Φ.map b.arrow) ≫ Φ.map m.arrow = φ ≫ Φ.map a.arrow
    rw [Category.assoc, ← Φ.map_comp, m.triangle]
  arrow_base := by
    subst hΦ
    exact m.arrow_base

/-- **The transported functor of predeformation categories**: `(x₀ ⟶ x) ↦ (y₀ ⟶ Φ(x₀) ⟶ Φ(x))`. -/
noncomputable def transportPredeformationFunctor
    (hφ : (pY ⋙ Over.post B.inclusion).map φ =
      eqToHom (hy₀.trans ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀).symm)) :
    letI := (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).category
    letI := (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀).category
    (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).carrier ⥤
      (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀).carrier :=
  letI := (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).category
  letI := (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀).category
  { obj := fun d => (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀).objects.symm
      (transportDeformationObject B hS iΛ pX pY Φ hΦ x₀ hx₀ y₀ hy₀ φ hφ
        ((predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).objects d))
    map := fun {a b} f =>
      ((predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀).morphisms _ _).symm
        (transportedDeformationMorphism B hS iΛ pX pY Φ hΦ x₀ hx₀ y₀ hy₀ φ hφ
          ((predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).morphisms a b f))
    map_id := fun _ => DeformationMorphism.ext_of_components _ _ _ _ rfl (Φ.map_id _)
    map_comp := fun _ _ => DeformationMorphism.ext_of_components _ _ _ _ rfl (Φ.map_comp _ _) }

/-- The transported functor commutes strictly with the projections to `𝒞_Λ`. -/
theorem transportPredeformationFunctor_comp_projection
    (hφ : (pY ⋙ Over.post B.inclusion).map φ =
      eqToHom (hy₀.trans ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀).symm)) :
    letI := (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).category
    letI := (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀).category
    transportPredeformationFunctor B hS iΛ pX pY Φ hΦ x₀ hx₀ y₀ hy₀ φ hφ ⋙
        (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀).projection =
      (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).projection := by
  let := (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).category
  let := (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀).category
  exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => by simp; rfl)

/-- **Criterion for the transported functor to be an equivalence over `𝒞_Λ`.** Let `𝒳`, `𝒴` be
fibred in groupoids, let `Φ` be faithful, let `φ : y₀ ⟶ Φ(x₀)` be a vertical isomorphism, and
suppose
* (arrows) every arrow `β : Φ(x_b) ⟶ Φ(x_a)` between images of deformations of `x₀` compatible
  with the arrows out of `Φ(x₀)` is the image of an arrow of `𝒳`;
* (objects) every deformation `y₀ ⟶ y` of `y₀` over `A` is, up to a vertical isomorphism
  `y ≅ Φ(x)` compatible with the arrows out of `y₀`, the transport of a deformation of `x₀`
  over `A`.
Then `(x₀ ⟶ x) ↦ (y₀ ⟶ Φ(x))` is an equivalence `𝓕_{𝒳,k,x₀} ≃ 𝓕_{𝒴,k,y₀}` over `𝒞_Λ`. -/
noncomputable def transportPredeformationEquivalence
    (hpX : pX.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids)
    (hφ : (pY ⋙ Over.post B.inclusion).map φ =
      eqToHom (hy₀.trans ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀).symm))
    [IsIso φ] [Φ.Faithful]
    (hfull : ∀ (a b : DeformationObject iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀)
      (β : Φ.obj b.point ⟶ Φ.obj a.point), Φ.map b.arrow ≫ β = Φ.map a.arrow →
        ∃ α : b.point ⟶ a.point, Φ.map α = β)
    (hess : ∀ c : DeformationObject iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀,
      ∃ (d : DeformationObject iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀)
        (ψ : c.point ⟶ Φ.obj d.point) (_ : d.algebra = c.algebra)
        (H : (pY ⋙ Over.post B.inclusion).obj c.point =
          (pY ⋙ Over.post B.inclusion).obj (Φ.obj d.point)),
        c.arrow ≫ ψ = φ ≫ Φ.map d.arrow ∧
          (pY ⋙ Over.post B.inclusion).map ψ = eqToHom H) :
    letI := (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).category
    letI := (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀).category
    StacksRepresentableCFG.EquivalenceOver
      (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).projection
      (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀).projection := by
  let Cx := predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀
  let Cy := predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀
  letI := Cx.category
  letI := Cy.category
  let Ψ := transportPredeformationFunctor B hS iΛ pX pY Φ hΦ x₀ hx₀ y₀ hy₀ φ hφ
  have hcofX : IsCofiberedInGroupoids Cx.projection :=
    (predeformationCategory_isPredeformationCategory B hS iΛ pX x₀ hx₀ hpX).cofibered
  have hcofY : IsCofiberedInGroupoids Cy.projection :=
    (predeformationCategory_isPredeformationCategory B hS iΛ pY y₀ hy₀ hpY).cofibered
  haveI : Ψ.Faithful := ⟨fun {a b} f g h => by
    apply (Cx.morphisms a b).injective
    apply DeformationMorphism.ext_of_components
    · exact congrArg (fun m : DeformationMorphism iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀ _ _ =>
        m.ringHom) (congrArg (Cy.morphisms _ _) h)
    · apply Φ.map_injective
      exact congrArg (fun m : DeformationMorphism iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀ _ _ =>
        m.arrow) (congrArg (Cy.morphisms _ _) h)⟩
  haveI : Ψ.Full := ⟨fun {a b} h => by
    generalize hm : (Cy.morphisms _ _ h : DeformationMorphism iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀
      (transportDeformationObject B hS iΛ pX pY Φ hΦ x₀ hx₀ y₀ hy₀ φ hφ (Cx.objects a))
      (transportDeformationObject B hS iΛ pX pY Φ hΦ x₀ hx₀ y₀ hy₀ φ hφ (Cx.objects b))) = m
    obtain ⟨r, β, tri, ab⟩ := m
    have htri : Φ.map (Cx.objects b).arrow ≫ β = Φ.map (Cx.objects a).arrow :=
      (cancel_epi φ).mp ((Category.assoc _ _ _).symm.trans tri)
    obtain ⟨α, rfl⟩ := hfull (Cx.objects a) (Cx.objects b) β htri
    let n : DeformationMorphism iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀ (Cx.objects a)
        (Cx.objects b) :=
      { ringHom := r
        arrow := α
        triangle := Φ.map_injective ((Φ.map_comp _ _).trans htri)
        arrow_base := by
          subst hΦ
          exact ab }
    refine ⟨(Cx.morphisms a b).symm n, ?_⟩
    exact (Cy.morphisms _ _).injective
      ((DeformationMorphism.ext_of_components _ _ _ _ rfl rfl).trans hm.symm)⟩
  haveI : Ψ.EssSurj := ⟨fun c => by
    obtain ⟨d, ψ, hA, H, htri, hbase⟩ := hess (Cy.objects c)
    let n : DeformationMorphism iΛ (pY ⋙ Over.post B.inclusion) y₀ hy₀
        (transportDeformationObject B hS iΛ pX pY Φ hΦ x₀ hx₀ y₀ hy₀ φ hφ d) (Cy.objects c) :=
      { ringHom := eqToHom hA
        arrow := ψ
        triangle := htri
        arrow_base := by
          rw [specMap_ofHom_eqToHom hA (by rw [hA])]
          simp only [hbase, Over.eqToHom_left, eqToHom_trans] }
    let mm : Ψ.obj (Cx.objects.symm d) ⟶ c := (Cy.morphisms _ _).symm n
    have : IsIso (Cy.projection.map mm) := by
      change IsIso (eqToHom hA); infer_instance
    have : IsIso mm := isIso_of_isCofiberedInGroupoids_of_map_isIso hcofY mm
    exact ⟨Cx.objects.symm d, ⟨asIso mm⟩⟩⟩
  exact Deformation.equivalenceOverOfCofibered hcofX Ψ
    (transportPredeformationFunctor_comp_projection B hS iΛ pX pY Φ hΦ x₀ hx₀ y₀ hy₀ φ hφ)

/-- **An equivalence over the site induces an equivalence of predeformation categories.** If
`e : 𝒳 ≃ 𝒴` is an equivalence over the big fppf site of `S` between categories fibred in
groupoids and `x₀` lies over `Spec k`, then `(x₀ ⟶ x) ↦ (e(x₀) ⟶ e(x))` is an equivalence
`𝓕_{𝒳,k,x₀} ≃ 𝓕_{𝒴,k,e(x₀)}` over `𝒞_Λ`. -/
noncomputable def predeformationEquivalenceOfEquivalenceOver
    (hpX : pX.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver pX pY) :
    letI := (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).category
    letI := (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) (e.hom.functor.obj x₀)
      ((transport_obj_eq B hS pX pY _ e.hom.w x₀).trans hx₀)).category
    StacksRepresentableCFG.EquivalenceOver
      (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).projection
      (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) (e.hom.functor.obj x₀)
        ((transport_obj_eq B hS pX pY _ e.hom.w x₀).trans hx₀)).projection := by
  haveI : e.hom.functor.IsEquivalence := e.isEquivalence_hom_functor
  refine transportPredeformationEquivalence B hS iΛ pX pY e.hom.functor e.hom.w x₀ hx₀
    (e.hom.functor.obj x₀) ((transport_obj_eq B hS pX pY _ e.hom.w x₀).trans hx₀) (𝟙 _)
    hpX hpY (by rw [CategoryTheory.Functor.map_id, eqToHom_refl])
    (fun a b β _ => ⟨e.hom.functor.preimage β, e.hom.functor.map_preimage β⟩)
    (fun c => ?_)
  let ψ := e.counitIso.inv.app c.point
  have hψ := e.isHomLift_counitIso_inv_app c.point
  have hinv : (pX ⋙ Over.post B.inclusion).obj (e.inv.functor.obj c.point) =
      (pY ⋙ Over.post B.inclusion).obj c.point :=
    congrArg (Over.post B.inclusion).obj (Functor.congr_obj e.inv.w c.point)
  have hH : (pY ⋙ Over.post B.inclusion).obj c.point =
      (pY ⋙ Over.post B.inclusion).obj (e.hom.functor.obj (e.inv.functor.obj c.point)) :=
    hinv.symm.trans (transport_obj_eq B hS pX pY _ e.hom.w _).symm
  have hψmap : (pY ⋙ Over.post B.inclusion).map ψ = eqToHom hH := by
    have h : pY.map ψ = _ := IsHomLift.fac' pY (𝟙 (pY.obj c.point)) ψ
    rw [Functor.comp_map, h, Category.id_comp, eqToHom_trans, eqToHom_map]
  let α : x₀ ⟶ e.inv.functor.obj c.point := e.hom.functor.preimage (c.arrow ≫ ψ)
  have hα : (pX ⋙ Over.post B.inclusion).map α =
      eqToHom (transport_obj_eq B hS pX pY _ e.hom.w x₀).symm ≫
        (pY ⋙ Over.post B.inclusion).map c.arrow ≫ eqToHom hH ≫
          eqToHom (transport_obj_eq B hS pX pY _ e.hom.w _) := by
    have h := Functor.congr_hom (congrArg (· ⋙ Over.post B.inclusion) e.hom.w).symm α
    rw [h]
    change eqToHom _ ≫ (pY ⋙ Over.post B.inclusion).map (e.hom.functor.map α) ≫ eqToHom _ = _
    rw [Functor.map_preimage, Functor.map_comp, hψmap]
    simp only [Category.assoc]
  refine ⟨⟨c.algebra, e.inv.functor.obj c.point, α, hinv.trans c.base, ?_⟩, ψ, rfl, hH, ?_, hψmap⟩
  · rw [hα, ← c.arrow_base]
    simp only [Over.comp_left, Over.eqToHom_left, Category.assoc, eqToHom_trans,
      eqToHom_trans_assoc]
  · simp only [Category.id_comp, α, Functor.map_preimage]

end Deformation.Artin

end
