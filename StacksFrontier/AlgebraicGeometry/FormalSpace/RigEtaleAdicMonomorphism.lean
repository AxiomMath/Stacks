module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability

/-!
# Cancelling rig-étaleness along an adic monomorphism

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of fppf sheaves over `S`. When `g` is a monomorphism the square with sides `𝟙 X` and
`f` over `f ≫ g` and `g` is cartesian, so `f` is the base change of `g ∘ f` along `g`. This is
the step by which **Stacks 0GH4** — if `g ∘ f` is rig-étale and `g` is an adic monomorphism of
locally Noetherian formal algebraic spaces, then `f` is rig-étale — is deduced from the base
change result Stacks 0GD1; the statement itself is
`isRigEtale_of_comp_of_isAdicMorphism_of_mono_of_isLocallyNoetherian` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleBaseChangeCharts`.

## Main results

* `AlgebraicGeometry.FormalSpace.isPullback_id_of_mono`: a composite `f ≫ g` with `g` a
  monomorphism exhibits the source of `f` as the fibre product of `f ≫ g` and `g`.
* `AlgebraicGeometry.FormalSpace.isRigEtale_iso_hom_comp`: rig-étaleness is invariant under
  precomposition with an isomorphism of the source.
* `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isAdicMorphism_of_mono`: the same
  cancellation, on the inputs of `isRigEtale_pullback_snd_of_isAdicMorphism`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A composite `f ≫ g` whose second factor is a monomorphism exhibits the source of `f` as
the fibre product of `f ≫ g` and `g`: the square with sides `𝟙 X` and `f` over `f ≫ g` and
`g` is cartesian. In other words `f` is the base change of `f ≫ g` along `g`. -/
theorem isPullback_id_of_mono {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : Mono g) : IsPullback (𝟙 X) f (f ≫ g) g :=
  have : Mono g := hg
  IsPullback.of_horiz_isIso_mono ⟨Category.id_comp _⟩

/-- Rig-étaleness of a morphism of fppf sheaves is invariant under precomposition with an
isomorphism of the source: the affine étale diagrams over `e.hom ≫ p` are the affine étale
diagrams over `p`, read through `e`. -/
theorem isRigEtale_iso_hom_comp {X X' Y : FppfSheaf B S hS} (e : X ≅ X') (p : X' ⟶ Y)
    (hp : IsRigEtale B S hS p) : IsRigEtale B S hS (e.hom ≫ p) := by
  intro U V hU hV a b t ha hb haet hbet hcomm
  obtain ⟨ha', ha'et⟩ := IsRepresentableEtale.comp B S hS (a := a) (b := e.hom)
    ⟨ha, haet⟩ (isRepresentableEtale_of_isIso B S hS e.hom)
  exact hp U V hU hV (a ≫ e.hom) b t ha' hb ha'et hbet
    (by rw [Category.assoc]; exact hcomm)

/-- Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian formal algebraic spaces
over `S` with `g ∘ f` rig-étale and `g` a monomorphism whose chart maps are adic, given the
inputs `hcond`, `hiso`, `h31` and `hcover` of
`AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isAdicMorphism`. Then `f` is
rig-étale.

The hypothesis `hcond` can never be supplied (see
`StacksFrontier.RingTheory.Rig.RigEtaleConditionCounterexample`); Stacks 0GH4 itself, with exactly
the source's hypotheses, is
`AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isAdicMorphism_of_mono_of_isLocallyNoetherian`.
-/
theorem isRigEtale_of_comp_of_isAdicMorphism_of_mono (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (hcond : TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        Rig.RigEtaleCondition φ))
    (hiso : PropertyIsInvariantUnderTargetIso.{u}
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ))
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
    isRigEtale_pullback_snd_of_isAdicMorphism B S hS hcond hiso h31 (f ≫ g) g hcover hX hZ hY
      hfg hgadic
  have hmain := isRigEtale_iso_hom_comp B S hS hpb.isoPullback (pullback.snd (f ≫ g) g) key
  rwa [hpb.isoPullback_hom_snd] at hmain

end AlgebraicGeometry.FormalSpace
