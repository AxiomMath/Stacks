module

public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.Deformation.Artin.Predeformation.Transport

/-!
# Finite-dimensional tangent spaces transport along an equivalence over the site

Let `Φ : 𝒳 ⥤ 𝒴` commute strictly with the structure functors to the big fppf site of `S`, be full
and faithful, and let every object of `𝒴` be vertically isomorphic to an object in the image of
`Φ` — for instance a functor of an equivalence over the site. For an object `x₀` of `𝒳` over
`Spec k`, the predeformation categories `𝓕_{𝒳,k,x₀}` and `𝓕_{𝒴,k,Φ(x₀)}` are equivalent over
`𝒞_Λ` (`Deformation.Artin.transportPredeformationEquivalence`), so their tangent spaces are
finite dimensional together.

## Main results

* `Deformation.Artin.finiteDimensional_tangentModuleAt_iff_of_fullyFaithful`.
* `Deformation.Artin.finiteDimensional_tangentModuleAt_congr`: the tangent module only depends on
  the projection, transported along an equality of projections.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u u₁ v₁ u₂ v₂

namespace Deformation.Artin

/-- The tangent module of a deformation category depends only on its projection: an equality of
projections identifies the finite-dimensionality of the two tangent modules. -/
theorem finiteDimensional_tangentModuleAt_congr {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] {C : Type u₁} [Category.{v₁} C]
    {p p' : C ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k} (h : p = p')
    (hp : IsDeformationCategory.{u, u, u} (BasedCategory.ofFunctor p).p)
    (hp' : IsDeformationCategory.{u, u, u} (BasedCategory.ofFunctor p').p)
    (M : FGModuleCat.{u} k) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor p) hp M) ↔
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor p') hp' M) := by
  subst h
  rfl

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
variable (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS) (Φ : X ⥤ Y)
  (hΦ : Φ ⋙ pY = pX)

/-- **The predeformation categories at `x₀` and `Φ(x₀)` are equivalent** when `Φ` is full,
faithful and essentially surjective by vertical isomorphisms. -/
noncomputable def predeformationEquivalenceOfFullyFaithful
    (hpX : pX.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids) [Φ.Full] [Φ.Faithful]
    (hess : ∀ y : Y, ∃ (x : X) (e : y ≅ Φ.obj x), pY.IsHomLift (𝟙 (pY.obj y)) e.hom)
    (x₀ : X) (hx₀ : (pX ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI := (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).category
    letI := (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) (Φ.obj x₀)
      ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀)).category
    StacksRepresentableCFG.EquivalenceOver
      (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).projection
      (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) (Φ.obj x₀)
        ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀)).projection := by
  refine transportPredeformationEquivalence B hS iΛ pX pY Φ hΦ x₀ hx₀ (Φ.obj x₀)
    ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀) (𝟙 _) hpX hpY
    (by rw [CategoryTheory.Functor.map_id]; exact (eqToHom_refl _ _).symm)
    (fun a b β _ => ⟨Φ.preimage β, Φ.map_preimage β⟩) ?_
  intro c
  obtain ⟨x, e, he⟩ := hess c.point
  have hpt : pY.obj (Φ.obj x) = pY.obj c.point :=
    IsHomLift.codomain_eq pY (𝟙 (pY.obj c.point)) e.hom
  have hH : (pY ⋙ Over.post B.inclusion).obj c.point =
      (pY ⋙ Over.post B.inclusion).obj (Φ.obj x) :=
    (congrArg (Over.post B.inclusion).obj hpt).symm
  have hmap : (pY ⋙ Over.post B.inclusion).map e.hom = eqToHom hH := by
    rw [Functor.comp_map, IsHomLift.fac' pY (𝟙 (pY.obj c.point)) e.hom, Category.id_comp,
      eqToHom_trans, eqToHom_map]
  subst hΦ
  let d : DeformationObject iΛ ((Φ ⋙ pY) ⋙ Over.post B.inclusion) x₀ hx₀ :=
    { algebra := c.algebra
      point := x
      arrow := Φ.preimage (c.arrow ≫ e.hom)
      base := hH.symm.trans c.base
      arrow_base := by
        have hab := c.arrow_base
        change eqToHom _ ≫ ((pY ⋙ Over.post B.inclusion).map
          (Φ.map (Φ.preimage (c.arrow ≫ e.hom)))).left ≫ eqToHom _ = _
        rw [Φ.map_preimage, Functor.map_comp, hmap, Over.comp_left, Over.eqToHom_left]
        rw [← hab]
        simp only [Category.assoc, eqToHom_trans] }
  refine ⟨d, e.hom, rfl, hH, ?_, hmap⟩
  simp [d]

variable [Φ.Full] [Φ.Faithful]

/-- **Finite-dimensionality of the tangent spaces is invariant under a fully faithful functor
over the site which is essentially surjective by vertical isomorphisms**: the tangent module of
`𝓕_{𝒳,k,x₀}` is finite dimensional exactly when that of `𝓕_{𝒴,k,Φ(x₀)}` is. -/
theorem finiteDimensional_tangentModuleAt_iff_of_fullyFaithful
    (hpX : pX.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids)
    (hess : ∀ y : Y, ∃ (x : X) (e : y ≅ Φ.obj x), pY.IsHomLift (𝟙 (pY.obj y)) e.hom)
    (x₀ : X) (hx₀ : (pX ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hDX : IsDeformationCategory.{u, u, u}
      (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (hDY : IsDeformationCategory.{u, u, u}
      (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) (Φ.obj x₀)
        ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀)).projection)
    (M : FGModuleCat.{u} k) :
    letI := (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).category
    letI := (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) (Φ.obj x₀)
      ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀)).category
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).projection) hDX M) ↔
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) (Φ.obj x₀)
          ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀)).projection) hDY M) := by
  let := (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).category
  let := (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) (Φ.obj x₀)
    ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀)).category
  let e := predeformationEquivalenceOfFullyFaithful B hS iΛ pX pY Φ hΦ hpX hpY hess x₀ hx₀
  let φ₁ : BasedCategory.ofFunctor
        (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) (Φ.obj x₀)
          ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀)).projection ⥤ᵇ
      BasedCategory.ofFunctor
        (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).projection :=
    ⟨e.inv.functor, e.inv.w⟩
  let φ₂ : BasedCategory.ofFunctor
        (predeformationCategory iΛ (pX ⋙ Over.post B.inclusion) x₀ hx₀).projection ⥤ᵇ
      BasedCategory.ofFunctor
        (predeformationCategory iΛ (pY ⋙ Over.post B.inclusion) (Φ.obj x₀)
          ((transport_obj_eq B hS pX pY Φ hΦ x₀).trans hx₀)).projection :=
    ⟨e.hom.functor, e.hom.w⟩
  have : φ₁.toFunctor.IsEquivalence := e.toEquivalence.isEquivalence_inverse
  have : φ₂.toFunctor.IsEquivalence := e.toEquivalence.isEquivalence_functor
  exact ⟨fun h => finiteDimensional_tangentModuleAt_of_fullyFaithful hDY hDX φ₁ M h,
    fun h => finiteDimensional_tangentModuleAt_of_fullyFaithful hDX hDY φ₂ M h⟩

end Deformation.Artin

end
