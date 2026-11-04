module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleAdicMonomorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStabilityRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# Cancelling rig-étaleness along an adic monomorphism

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian formal algebraic spaces over
`S`. If `g ∘ f` is rig-étale and `g` is an adic monomorphism, then `f` is rig-étale.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isAdicMorphism_of_mono'`: if `g ∘ f` is
  rig-étale and `g` is an adic monomorphism, then `f` is rig-étale.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GH4.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian formal
algebraic spaces over `S`. If `g ∘ f` is rig-étale and `g` is an adic monomorphism, then `f` is
rig-étale. -/
theorem isRigEtale_of_comp_of_isAdicMorphism_of_mono' (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (hcond : TopologicalRing.PropertyIsLocalNoetherian'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        Rig.RigEtaleCondition φ))
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ))
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS (f ≫ g) g)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hfg : IsRigEtale B S hS (f ≫ g))
    (hgadic : IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS g) (hgmono : Mono g) :
    IsRigEtale B S hS f := by
  have hpb : IsPullback (𝟙 X) f (f ≫ g) g := isPullback_id_of_mono B S hS f g hgmono
  have key : IsRigEtale B S hS (pullback.snd (f ≫ g) g) :=
    isRigEtale_pullback_snd_of_isAdicMorphism' B S hS hcond h31 (f ≫ g) g hcover hX hZ hY
      hfg hgadic
  have hmain := isRigEtale_iso_hom_comp B S hS hpb.isoPullback (pullback.snd (f ≫ g) g) key
  rwa [hpb.isoPullback_hom_snd] at hmain

end AlgebraicGeometry.FormalSpace
