module

public import StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleScheme
public import StacksFrontier.Deformation.Artin.Infinitesimal.OverLiftClasses
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentBaseChangeDescent

/-!
# Lift classes along a formally étale morphism of schemes

Let `g : X₁ ⟶ X₀` be a morphism of schemes over `S` in the big fppf site whose underlying
morphism of schemes is formally étale (Stacks 02HG), and regard `X₁`, `X₀` as categories fibred
in groupoids through their slices. Composition with `g` is a `1`-morphism `Over.map g`. For a
point `x : Spec A ⟶ X₁` and an `A`-module `M`, the lift classes of `x` over `Spec A[M]` are the
arrows `Spec A[M] ⟶ X₁` restricting to `x` (`Deformation.Artin.overLiftClassEquiv`), and the
induced map to the lift classes of `g ∘ x` is composition with `g`. Since `Spec A ⟶ Spec A[M]`
is a first-order thickening of affine schemes, the unique infinitesimal lifting property of `g`
makes this map bijective: existence of the filler is surjectivity, its uniqueness injectivity.

This is the bijection `T_w(W) ≅ T_x(X)` along an étale chart `W ⟶ X` used in the proof of
Stacks 0DNT, for a chart which is a scheme (in particular for an open immersion, where it
reduces the tangent spaces of a scheme to those of its affine opens).

## Main results

* `Deformation.Artin.overLiftClassEquiv_liftClassOfOneMorphism_overMap`: the map on lift
  classes induced by `Over.map g` is composition with `g`.
* `Deformation.Artin.bijective_liftClassOfOneMorphism_overMap`: it is bijective when `g` is
  formally étale.
* `Deformation.Artin.bijective_tangentMapOfOneMorphism_overMap`: the same for any tangent
  functors.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
  {X₁ X₀ : BigFppfOver B S hS} (g : X₁ ⟶ X₀) {x : Over X₁}
  (hx : (Over.forget X₁).obj x = algebraOver A B S hS toS hA)

/-- Composition with `g` commutes with forgetting to the site. -/
public theorem overMap_comp_forget : Over.map g ⋙ Over.forget X₀ = Over.forget X₁ := rfl

/-- **The map on lift classes induced by composition with `g` is composition with `g`.** -/
public theorem overLiftClassEquiv_liftClassOfOneMorphism_overMap (M : SiteModule A B)
    (c : squareZeroLiftClasses A B S hS toS hA (Over.forget X₁) x hx M) :
    (overLiftClassEquiv X₀ (oneMorphism_obj_eq A B S hS toS hA _ _ (Over.map g)
        (overMap_comp_forget g) x hx) (squareZeroArrow A B S hS toS hA M)
        (liftClassOfOneMorphism A B S hS toS hA (Over.forget X₁) (Over.forget X₀) (Over.map g)
          (overMap_comp_forget g) x hx M c)).1 =
      (overLiftClassEquiv X₁ hx (squareZeroArrow A B S hS toS hA M) c).1 ≫ g := by
  induction c using Quotient.ind with
  | _ t =>
    rw [liftClassOfOneMorphism_mk, overLiftClassEquiv_mk, overLiftClassEquiv_mk]
    rfl

variable {g}

/-- **Along a formally étale morphism of schemes, composition is bijective on lift classes.** -/
public theorem bijective_liftClassOfOneMorphism_overMap
    (hg : AlgebraicGeometry.FormallyEtale ((BigFppfOver.toScheme B S hS).map g))
    (M : SiteModule A B) :
    Function.Bijective (liftClassOfOneMorphism A B S hS toS hA (Over.forget X₁) (Over.forget X₀)
      (Over.map g) (overMap_comp_forget g) x hx M) := by
  set T := BigFppfOver.toScheme B S hS
  set aa := squareZeroArrow A B S hS toS hA M
  have hthk := isFirstOrderThickening_squareZeroArrow A toS hA M (hS := hS)
  have : IsAffine (T.obj (algebraOver A B S hS toS hA)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  have : IsAffine (T.obj (squareZeroOver A B S hS toS M)) :=
    inferInstanceAs (IsAffine (Spec _))
  -- uniqueness of fillers in the site
  have huniq : ∀ h₁ h₂ : squareZeroOver A B S hS toS M ⟶ X₁, aa ≫ h₁ = aa ≫ h₂ →
      h₁ ≫ g = h₂ ≫ g → h₁ = h₂ := by
    intro h₁ h₂ ha hb
    have hsq : T.map (aa ≫ h₁) ≫ T.map g = T.map aa ≫ T.map (h₁ ≫ g) := by
      rw [← T.map_comp, ← T.map_comp, Category.assoc]
    obtain ⟨k, -, hk⟩ := hg (T.map aa) hthk (T.map (h₁ ≫ g)) (T.map (aa ≫ h₁)) hsq
    have e₁' := hk (T.map h₁) ⟨(T.map_comp _ _).symm, (T.map_comp _ _).symm⟩
    have e₂' := hk (T.map h₂) ⟨by rw [← T.map_comp, ha], by rw [← T.map_comp, hb]⟩
    exact T.map_injective (e₁'.trans e₂'.symm)
  refine ⟨fun c₁ c₂ hc => ?_, fun c => ?_⟩
  · apply (overLiftClassEquiv X₁ hx aa).injective
    apply Subtype.ext
    apply huniq
    · rw [((overLiftClassEquiv X₁ hx aa) c₁).2, ((overLiftClassEquiv X₁ hx aa) c₂).2]
    · rw [← overLiftClassEquiv_liftClassOfOneMorphism_overMap A toS hA g hx M c₁,
        ← overLiftClassEquiv_liftClassOfOneMorphism_overMap A toS hA g hx M c₂, hc]
  · set k := ((overLiftClassEquiv X₀ (oneMorphism_obj_eq A B S hS toS hA _ _ (Over.map g)
      (overMap_comp_forget g) x hx) aa) c).1
    have hk : aa ≫ k = eqToHom _ ≫ ((Over.map g).obj x).hom :=
      ((overLiftClassEquiv X₀ (oneMorphism_obj_eq A B S hS toS hA _ _ (Over.map g)
        (overMap_comp_forget g) x hx) aa) c).2
    set x₀ : algebraOver A B S hS toS hA ⟶ X₁ := eqToHom hx.symm ≫ x.hom
    have hk' : aa ≫ k = x₀ ≫ g := by
      rw [hk]
      simp [x₀]
    have hsq : T.map x₀ ≫ T.map g = T.map aa ≫ T.map k := by
      rw [← T.map_comp, ← T.map_comp, hk']
    obtain ⟨h₀, ⟨hh₀, hh₁⟩, -⟩ := hg (T.map aa) hthk (T.map k) (T.map x₀) hsq
    let hS' : (squareZeroOver A B S hS toS M).left ⟶ X₁.left := B.inclusion.preimage h₀
    have hS'map : B.inclusion.map hS' = h₀ := B.inclusion.map_preimage h₀
    have hw : hS' ≫ X₁.hom = (squareZeroOver A B S hS toS M).hom := by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, hS'map, ← Over.w g, Functor.map_comp, ← Category.assoc]
      change h₀ ≫ T.map g ≫ _ = _
      rw [← Category.assoc, hh₁]
      change B.inclusion.map (k.left ≫ X₀.hom) = _
      rw [Over.w k]
    let h : squareZeroOver A B S hS toS M ⟶ X₁ := Over.homMk hS' hw
    have hTh : T.map h = h₀ := hS'map
    have hah : aa ≫ h = x₀ := by
      apply T.map_injective
      rw [T.map_comp, hTh, hh₀]
    have hhg : h ≫ g = k := by
      apply T.map_injective
      rw [T.map_comp, hTh, hh₁]
    refine ⟨(overLiftClassEquiv X₁ hx aa).symm ⟨h, hah⟩,
      (overLiftClassEquiv X₀ (oneMorphism_obj_eq A B S hS toS hA _ _ (Over.map g)
        (overMap_comp_forget g) x hx) aa).injective (Subtype.ext ?_)⟩
    rw [overLiftClassEquiv_liftClassOfOneMorphism_overMap A toS hA g hx M]
    convert hhg using 2
    exact congrArg Subtype.val (Equiv.apply_symm_apply (overLiftClassEquiv X₁ hx aa) ⟨h, hah⟩)

/-- **Along a formally étale morphism of schemes the tangent map is bijective**, for any tangent
functors of `x` and of its image. -/
public theorem bijective_tangentMapOfOneMorphism_overMap
    (hg : AlgebraicGeometry.FormallyEtale ((BigFppfOver.toScheme B S hS).map g))
    (F : TangentFunctorData A B S hS toS hA (Over.forget X₁) x hx)
    (F' : TangentFunctorData A B S hS toS hA (Over.forget X₀) ((Over.map g).obj x)
      (oneMorphism_obj_eq A B S hS toS hA _ _ (Over.map g) (overMap_comp_forget g) x hx))
    (M : SiteModule A B) :
    Function.Bijective (tangentMapOfOneMorphism A B S hS toS hA (Over.forget X₁)
      (Over.forget X₀) (Over.map g) (overMap_comp_forget g) x hx F F' M) := by
  have h := bijective_liftClassOfOneMorphism_overMap A toS hA hx hg M
  have he : (tangentMapOfOneMorphism A B S hS toS hA (Over.forget X₁)
      (Over.forget X₀) (Over.map g) (overMap_comp_forget g) x hx F F' M) =
      (F'.liftEquiv M).symm ∘ (liftClassOfOneMorphism A B S hS toS hA (Over.forget X₁)
        (Over.forget X₀) (Over.map g) (overMap_comp_forget g) x hx M) ∘ (F.liftEquiv M) := by
    funext z
    apply (F'.liftEquiv M).injective
    rw [liftEquiv_tangentMapOfOneMorphism]
    simp
  rw [he]
  exact (F'.liftEquiv M).symm.bijective.comp (h.comp (F.liftEquiv M).bijective)

end Deformation.Artin

end
