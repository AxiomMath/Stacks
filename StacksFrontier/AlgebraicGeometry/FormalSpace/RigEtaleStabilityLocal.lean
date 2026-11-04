module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationArtinConditions
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleAdicMonomorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleTargetIso
public import StacksFrontier.RingTheory.Rig.RigEtaleIsLocal

/-!
# Stability of rig-étale morphisms of formal algebraic spaces, from the locality of 0AQL

The statements of `StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability` and of the
files built on it obtain the locality of rig-étaleness (Stacks 0AQL) from the hypothesis
`hcond`, the locality of the annihilation half `Rig.RigEtaleCondition`; that hypothesis is
never satisfied (`Rig.not_propertyIsLocalNoetherian_rigEtaleCondition`). The statements here
are the same results with `hcond` removed: the locality of rig-étaleness is
`Rig.rigEtale_propertyIsLocalNoetherian`, which is unconditional, and the invariance of
rig-étaleness under isomorphism of targets (the hypothesis `hiso` of the base change
statements) is `AlgebraicGeometry.FormalSpace.propertyIsInvariantUnderTargetIso_isRigEtaleArrow`.

The formal-space predicate `AlgebraicGeometry.FormalSpace.IsRigEtale` of Stacks 0AQM is itself
sound: on each chart it asks for `RingHom.IsRigEtale`, which carries both the finite-type half
and the annihilation half of Stacks 0GCV, and
`AlgebraicGeometry.FormalSpace.isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram` identifies
it with condition (1) of Stacks 0ANG for `RingHom.IsRigEtaleArrow`.

The remaining inputs are those of the generic transfers of Stacks 0GBG, 0GBK and 0GBP (the
implication (3) ⟹ (1) of Stacks 0ANG and the covering of Stacks 0GBD for base change, the
transfers themselves for composition and cancellation), which do not mention rig-étaleness;
the statements are therefore not registered under their tags.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigEtale_comp_of_transfer`: Stacks 0GD2.
* `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_transfer`: Stacks 0GD3.
* `AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_cover`: Stacks 0GD1.
* `AlgebraicGeometry.FormalSpace.isRigEtale_diagonal_of_transfer`: the first half of Ad (ii) of
  Stacks 0GDL.
* `AlgebraicGeometry.FormalSpace.isFormalModification_pullback_snd_of_cover`: Stacks 0GDN.
* `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_mono_of_cover`: Stacks 0GH4.

## References

* [Stacks Project, Tag 0AQL](https://stacks.math.columbia.edu/tag/0AQL)
* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0GD2](https://stacks.math.columbia.edu/tag/0GD2)
* [Stacks Project, Tag 0GD3](https://stacks.math.columbia.edu/tag/0GD3)
* [Stacks Project, Tag 0GDN](https://stacks.math.columbia.edu/tag/0GDN)
* [Stacks Project, Tag 0GH4](https://stacks.math.columbia.edu/tag/0GH4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Stacks 0GD2 without `hcond`: the composite of two rig-étale morphisms of locally
Noetherian formal algebraic spaces over `S` is rig-étale, on the transfer of Remark 0GBK. -/
theorem isRigEtale_comp_of_transfer
    (htransfer : TransfersCompositionOnAffineEtaleDiagrams B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (_hX : IsLocallyNoetherian B S hS X) (_hY : IsLocallyNoetherian B S hS Y)
    (_hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsRigEtale B S hS f) (hg : IsRigEtale B S hS g) :
    IsRigEtale B S hS (f ≫ g) :=
  (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (f ≫ g)).mpr
    (htransfer _
      (Rig.rigEtale_isStableUnderCompositionNoetherian Rig.rigEtale_propertyIsLocalNoetherian)
      f g ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf)
      ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS g).mp hg))

/-- Stacks 0GD3 without `hcond`: if `g ∘ f` and `g` are rig-étale morphisms of locally
Noetherian formal algebraic spaces over `S`, then `f` is rig-étale, on the transfer of
Remark 0GBP. -/
theorem isRigEtale_of_comp_of_transfer
    (htransfer : TransfersCancellationOnAffineEtaleDiagrams B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (_hX : IsLocallyNoetherian B S hS X) (_hY : IsLocallyNoetherian B S hS Y)
    (_hZ : IsLocallyNoetherian B S hS Z)
    (hfg : IsRigEtale B S hS (f ≫ g)) (hg : IsRigEtale B S hS g) :
    IsRigEtale B S hS f :=
  (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mpr
    (htransfer _ Rig.rigEtale_propertyIsLocalNoetherian
      Rig.rigEtale_hasNoetherianCancellationProperty f g
      ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (f ≫ g)).mp hfg)
      ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS g).mp hg))

/-- Stacks 0GD1 without `hcond` and `hiso`: the base change of a rig-étale morphism of locally
Noetherian formal algebraic spaces by an adic morphism is rig-étale, on the implication
(3) ⟹ (1) of Stacks 0ANG (`h31`) and the covering of Stacks 0GBD (`hcover`). -/
theorem isRigEtale_pullback_snd_of_cover
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
    (hasPropertyOnEveryAffineEtaleDiagram_pullback_snd B S hS _ _
      (TopologicalRing.rigEtale_isStableUnderBaseChangeByAdic
        Rig.rigEtale_propertyIsLocalNoetherian)
      propertyIsInvariantUnderTargetIso_isRigEtaleArrow h31 f g hcover
      ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf) hg)

/-- The first half of Ad (ii) of Stacks 0GDL without `hcond`: the relative diagonal of a
rig-étale morphism of locally Noetherian formal algebraic spaces, representable by algebraic
spaces and locally of finite type, is rig-étale, on the transfer of Remark 0GBP, Stacks 0AQ8
(`h0AQ8`) and the representable base change of Stacks 0GD1 (`h0GD1`). -/
theorem isRigEtale_diagonal_of_transfer
    (htransfer : TransfersCancellationOnAffineEtaleDiagrams B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hft : IsLocallyOfFiniteType B S hS f)
    (h0AQ8 : FibreProductIsLocallyNoetherian B S hS)
    (h0GD1 : RigEtaleIsStableUnderRepresentableBaseChange B S hS)
    (hf : IsRigEtale B S hS f) :
    IsRigEtale B S hS (pullback.diagonal f) := by
  have sq : IsPullback (pullback.fst f f) (pullback.snd f f) f f := IsPullback.of_hasPullback f f
  have hXX : IsLocallyNoetherian B S hS (pullback f f) := h0AQ8 sq hX hft
  have hid : IsRigEtale B S hS (𝟙 X) :=
    isRigEtale_of_comp_of_transfer B S hS htransfer (𝟙 X) f hX hX hY
      (by rwa [Category.id_comp]) hf
  have hfst : IsRigEtale B S hS (pullback.fst f f) := h0GD1 sq hrep hX hY hX hf
  refine isRigEtale_of_comp_of_transfer B S hS htransfer (pullback.diagonal f)
    (pullback.fst f f) hX hXX hX ?_ hfst
  rw [pullback.diagonal_fst]
  exact hid

/-- Stacks 0GDN without `hcond` and `hiso`: the base change of a formal modification of
locally Noetherian formal algebraic spaces along an adic morphism is a formal modification, on
the inputs `h31` and `hcover` of Stacks 0GD1 and Stacks 0AQ8 (`h0AQ8`). -/
theorem isFormalModification_pullback_snd_of_cover
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ))
    (h0AQ8 : FibreProductIsLocallyNoetherian B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
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
      isRigEtale := isRigEtale_pullback_snd_of_cover B S hS h31 f g hcover
        hf.isLocallyNoetherian_source hf.isLocallyNoetherian_target hZ hf.isRigEtale hg
      isRigSurjective :=
        (IsRigSurjective.of_isPullback B S hS sq hfft hgft hf.isRigSurjective).2
      isRigSurjective_diagonal :=
        (IsRigSurjective.of_isPullback B S hS (isPullback_diagonal_selfPullbackMap sq) hdiag
          hmft hf.isRigSurjective_diagonal).2 }

/-- Stacks 0GH4 without `hcond` and `hiso`: if `g ∘ f` is rig-étale and `g` is an adic
monomorphism of locally Noetherian formal algebraic spaces, then `f` is rig-étale, on the
inputs `h31` and `hcover` of Stacks 0GD1. -/
theorem isRigEtale_of_comp_of_mono_of_cover
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
    isRigEtale_pullback_snd_of_cover B S hS h31 (f ≫ g) g hcover hX hZ hY hfg hgadic
  have hmain := isRigEtale_iso_hom_comp B S hS hpb.isoPullback (pullback.snd (f ≫ g) g) key
  rwa [hpb.isoPullback_hom_snd] at hmain

end AlgebraicGeometry.FormalSpace

end
