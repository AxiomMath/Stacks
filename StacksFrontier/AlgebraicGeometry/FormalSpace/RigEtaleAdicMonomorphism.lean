module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability

/-!
# Cancelling rig-étaleness along an adic monomorphism

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. When `g` is a monomorphism
the square with sides `𝟙 X` and `f` over `f ≫ g` and `g` is cartesian, so `f` is the base
change of `g ∘ f` along `g`. Consequently, if `g ∘ f` is rig-étale (Stacks 0AQM) and `g` is an
adic monomorphism, then `f` is rig-étale: this is **Stacks 0GH4**, a complement to the right
cancellation of Stacks 0GD3, where the second factor is asked to be rig-étale instead.

## Main results

* `AlgebraicGeometry.FormalSpace.isPullback_id_of_mono`: a composite `f ≫ g` with `g` a
  monomorphism exhibits the source of `f` as the fibre product of `f ≫ g` and `g`.
* `AlgebraicGeometry.FormalSpace.isRigEtale_iso_hom_comp`: rig-étaleness is invariant under
  precomposition with an isomorphism of the source.
* `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isAdicMorphism_of_mono`: **Stacks
  0GH4**.

## Implementation notes

The base change along the adic morphism `g` is taken by the stability result of Stacks 0GD1,
which the library carries for the chosen fibre product in the shape
`AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isAdicMorphism`. Its four open
inputs — the locality `hcond` of the cohomology-annihilation half of rig-étaleness, and the
three parts `hcover`, `h31`, `hiso` of Remark 0GBG that the library leaves open — are
therefore carried verbatim into the statement below, with `hcover` asked of the fibre product
of `g ∘ f` and `g` that the proof actually forms.

Passing from the second projection of that fibre product to `f` itself is the invariance of
rig-étaleness under an isomorphism of the source, which reduces to the stability of
representable étale morphisms under composition with an isomorphism and is proved here.
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

/-- **Stacks 0GH4.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian formal
algebraic spaces over `S`. If `g ∘ f` is rig-étale and `g` is an adic monomorphism, then `f` is
rig-étale: as `g` is a monomorphism, `f` is the base change of `g ∘ f` along `g`, and the base
change of a rig-étale morphism along an adic morphism is rig-étale. -/
@[stacks 0GH4 "granting the locality of the cohomology-annihilation half of rig-étaleness, \
which is the hypothesis hcond and the only input of Stacks 0AQL, together with the three \
inputs of Remark 0GBG that the library leaves open and that Stacks 0GD1, the sole cited \
input of this tag, is itself carried with: the covering by fibre products of charts of \
Stacks 0GBD and 0AN0 (hcover), the implication (3) ⟹ (1) of Stacks 0ANG (h31), and the \
invariance of rig-étaleness under isomorphism of targets implied by Stacks 0ANI (hiso)"]
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
