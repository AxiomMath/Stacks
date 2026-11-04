module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherianRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Proper
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStabilityRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveBaseChange
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# Formal modifications are stable under adic base change: the refined forms

The strengthened and newly added declarations of the 2026-10 chapter-87 round that belong with
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChange`. A declaration of that
module whose statement the round strengthened keeps its original statement there; its strengthened
form lives here under a primed name.

## Main results

* `isFormalModification_pullback_snd'` (Stacks 0GDN): if `f : X ⟶ Y` is a formal modification
  and `g : Z ⟶ Y` is an adic morphism, locally of finite type, with `Z` locally Noetherian, then
  `X ×_Y Z ⟶ Z` is a formal modification (given the carried hypotheses of its statement).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### The diagonal of a base change, categorically -/

section Categorical

variable {C : Type*} [Category* C] [HasPullbacks C]

end Categorical

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Properness and local finite typeness -/

/-! ### Stacks 0AQ8 as a carried hypothesis -/

/-! ### Stacks 0GDN -/

/-- **Stacks 0GDN.** Let `f : X ⟶ Y` be a formal modification of locally Noetherian formal
algebraic spaces over `S` and let `g : Z ⟶ Y` be an adic morphism, `Z` locally Noetherian.
Then the base change `X ×_Y Z ⟶ Z` of `f` along `g` is a formal modification. -/
theorem isFormalModification_pullback_snd'
    (hcond : TopologicalRing.PropertyIsLocalNoetherian'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        Rig.RigEtaleCondition φ))
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ))
    (hcover : ∀ {X₀ Y₀ Z₀ : FppfSheaf B S hS} (f₀ : X₀ ⟶ Y₀) (g₀ : Z₀ ⟶ Y₀),
      HasBaseChangeCoverOverPullbackSnd B S hS f₀ g₀)
    (h0AQ8 : FibreProductIsLocallyNoetherian B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hg : IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS g)
    (hgft : IsLocallyOfFiniteType B S hS g)
    (hdiag : IsLocallyOfFiniteType B S hS (pullback.diagonal f))
    (hf : IsFormalModification B S hS f) :
    IsFormalModification B S hS (pullback.snd f g) := by
  have sq : IsPullback (pullback.snd f g) (pullback.fst f g) g f :=
    (IsPullback.of_hasPullback f g).flip
  have hfft : IsLocallyOfFiniteType B S hS f :=
    IsProper.isLocallyOfFiniteType B S hS hf.isProper
  have hmft : IsLocallyOfFiniteType B S hS
      (pullback.map (pullback.snd f g) (pullback.snd f g) f f (pullback.fst f g)
        (pullback.fst f g) g sq.w sq.w) :=
    IsLocallyOfFiniteType.of_isPullback B S hS (isPullback_selfPullbackMap sq) hgft
  exact
    { isLocallyNoetherian_source := h0AQ8 sq hZ hfft
      isLocallyNoetherian_target := hZ
      isProper := IsProper.of_isPullback B S hS sq hf.isProper
      isRigEtale := isRigEtale_pullback_snd_of_isAdicMorphism' B S hS hcond h31 f g
        (hcover f g) hf.isLocallyNoetherian_source hf.isLocallyNoetherian_target hZ
        hf.isRigEtale hg
      isRigSurjective :=
        (IsRigSurjective.of_isPullback B S hS sq hfft hgft hf.isRigSurjective).2
      isRigSurjective_diagonal :=
        (IsRigSurjective.of_isPullback B S hS (isPullback_diagonal_selfPullbackMap sq) hdiag
          hmft hf.isRigSurjective_diagonal).2 }

end AlgebraicGeometry.FormalSpace

end
