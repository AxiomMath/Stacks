module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.RingTheory.Rig.RigEtaleLocalityRefined
public import StacksFrontier.RingTheory.Rig.RigSmoothStableUnderComposition
public import StacksFrontier.RingTheory.Rig.RigSmoothStabilityRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# Stability properties of rig-étale morphisms of formal algebraic spaces: the refined forms

Rig-étale morphisms of locally Noetherian formal algebraic spaces are stable under composition
and under base change by adic morphisms, and satisfy cancellation.

## Main definitions

* `TransfersCancellationOnAffineEtaleDiagrams'`: Cancellation for a local property of arrows of
  `WAdm^{Noeth}` transfers to morphisms of formal algebraic spaces.

## Main results

* `isRigEtale_comp'`: The composite of two rig-étale morphisms is rig-étale.
* `isRigEtale_of_comp'`: If a composite and its second factor are rig-étale, so is the first
  factor.
* `isRigEtale_pullback_snd_of_isAdicMorphism'`: The base change of a rig-étale morphism by an
  adic morphism is rig-étale.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-- The transfer to formal algebraic spaces drawn in **Stacks 0GBP**: whenever a local property
`P` of arrows of `WAdm^{Noeth}` has the cancellation property, condition (1) of Stacks 0ANG
passes from a composite with `P` and a second factor with `P` to the first factor. -/
abbrev TransfersCancellationOnAffineEtaleDiagrams' (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
    TopologicalRing.PropertyIsLocalNoetherian'.{u} P →
    TopologicalRing.HasNoetherianCancellationProperty.{u} P →
    ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
      HasPropertyOnEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g) →
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P g →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f

/-- **Stacks 0GD2.** The composite of two rig-étale morphisms of locally Noetherian formal
algebraic spaces over `S` is rig-étale: if `f : X ⟶ Y` and `g : Y ⟶ Z` are rig-étale, then so
is `g ∘ f`. -/
theorem isRigEtale_comp' (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hcond : TopologicalRing.PropertyIsLocalNoetherian'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        Rig.RigEtaleCondition φ))
    (htransfer : TransfersCompositionOnAffineEtaleDiagrams B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (_hX : IsLocallyNoetherian B S hS X) (_hY : IsLocallyNoetherian B S hS Y)
    (_hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsRigEtale B S hS f) (hg : IsRigEtale B S hS g) :
    IsRigEtale B S hS (f ≫ g) :=
  (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (f ≫ g)).mpr
    (htransfer _
      (Rig.rigEtale_isStableUnderCompositionNoetherian
        (Rig.rigEtale_isLocalNoetherian' hcond).toPropertyIsLocal)
      f g ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf)
      ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS g).mp hg))

/-- **Stacks 0GD3.** Rig-étaleness of morphisms of locally Noetherian formal algebraic spaces
over `S` cancels on the right: if `g ∘ f` and `g` are rig-étale, for `f : X ⟶ Y` and
`g : Y ⟶ Z`, then `f` is rig-étale. -/
theorem isRigEtale_of_comp' (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hcond : TopologicalRing.PropertyIsLocalNoetherian'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        Rig.RigEtaleCondition φ))
    (htransfer : TransfersCancellationOnAffineEtaleDiagrams' B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (_hX : IsLocallyNoetherian B S hS X) (_hY : IsLocallyNoetherian B S hS Y)
    (_hZ : IsLocallyNoetherian B S hS Z)
    (hfg : IsRigEtale B S hS (f ≫ g)) (hg : IsRigEtale B S hS g) :
    IsRigEtale B S hS f :=
  (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mpr
    (htransfer _ (Rig.rigEtale_isLocalNoetherian' hcond)
      Rig.rigEtale_hasNoetherianCancellationProperty f g
      ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (f ≫ g)).mp hfg)
      ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS g).mp hg))

/-- **Stacks 0GD1.** The base change of a rig-étale morphism of locally Noetherian formal
algebraic spaces over `S` by an adic morphism is rig-étale: if `f : X ⟶ Y` is rig-étale and
`g : Z ⟶ Y` is adic, then `X ×_Y Z ⟶ Z` is rig-étale. -/
theorem isRigEtale_pullback_snd_of_isAdicMorphism' (B : BigFppfSite.{u}) (S : Scheme.{u})
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
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
    (_hX : IsLocallyNoetherian B S hS X) (_hY : IsLocallyNoetherian B S hS Y)
    (_hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsRigEtale B S hS f)
    (hg : IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS g) :
    IsRigEtale B S hS (pullback.snd f g) :=
  (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (pullback.snd f g)).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_pullback_snd' B S hS _ _
      (TopologicalRing.rigEtale_isStableUnderBaseChangeByAdic'
        (Rig.rigEtale_isLocalNoetherian' hcond))
      h31 f g hcover
      ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf) hg)

end AlgebraicGeometry.FormalSpace

end
