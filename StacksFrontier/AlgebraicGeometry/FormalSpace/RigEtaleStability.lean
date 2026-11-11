module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.RingTheory.Rig.RigEtaleLocality
public import StacksFrontier.RingTheory.Rig.RigSmoothStableUnderComposition

/-!
# Stability properties of rig-étale morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. Rig-étaleness (Stacks 0AQM) of morphisms
of locally Noetherian formal algebraic spaces over `S`, conditionally, cancels on the right
(Stacks 0GD3, proved unconditionally in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleCompositionCharts`) and is stable under base
change by an adic morphism (Stacks 0GD1, proved unconditionally in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleBaseChangeCharts`).

## Main definitions

* `AlgebraicGeometry.FormalSpace.TransfersCancellationOnAffineEtaleDiagrams`: the transfer to
  formal algebraic spaces drawn in **Stacks 0GBP**.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram`:
  conditions (1) and (2) of Stacks 0GCZ.
* `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp`: right cancellation of rig-étaleness
  through the transfer of Stacks 0GBP; Stacks 0GD3 itself is
  `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isLocallyNoetherian`.
* `AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isAdicMorphism`: a conditional
  variant of Stacks 0GD1; Stacks 0GD1 is
  `AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isLocallyNoetherian`.

## Implementation notes

Each of the two statements is the composite of a ring-level stability result for arrows of
`WAdm^{Noeth}` with the geometric transfer of the corresponding remark of Stacks 0GBG, 0GBP,
the passage between the predicate of Stacks 0AQM and the generic machinery of Stacks
0ANG being conditions (1) and (2) of Stacks 0GCZ.

At the ring level the two inputs are Stacks 0GCY
(`Rig.rigEtale_hasNoetherianCancellationProperty`) and Stacks 0GCW
(`TopologicalRing.rigEtale_completedTensorProduct_of_isAdic`). One of the bundles that the
transfers consume also carries the locality of rig-étaleness, which is Stacks 0AQL. The
statements below obtain it through `Rig.rigEtale_isLocalNoetherian` from the locality of the
cohomology-annihilation half `Rig.RigEtaleCondition`, the hypothesis `hcond`; that hypothesis
is refuted by `Rig.not_propertyIsLocalNoetherian_rigEtaleCondition`, so both statements are
vacuous as they stand. Stacks 0AQL itself is proved without it, as
`Rig.rigEtale_propertyIsLocalNoetherian`. The
cancellation predicate `TopologicalRing.HasNoetherianCancellationProperty` has no locality
field, so locality is asked of the transfer of Stacks 0GBP separately, as in the statement of
Remark 0GBP.

The transfer of Remark 0GBP is the hypothesis `TransfersCancellationOnAffineEtaleDiagrams` of
`isRigEtale_of_comp`, quantified over *all* properties admitting the relevant bundle; it is a
statement about the generic machinery of the remark and not a restatement of the conclusion
below. The library proves the transfer for locally Noetherian formal algebraic spaces as
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_comp_of_isLocallyNoetherian`,
and proves Stacks 0GD3 directly on charts, with the source's hypotheses exactly, as
`AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isLocallyNoetherian` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleCompositionCharts`. The transfer of
Remark 0GBG is carried by
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_pullback_snd`, so the
conditional variant of Stacks 0GD1 below assumes only its three inputs: the covering of
`X ×_Y Z` by fibre products of charts coming from Stacks 0GBD and 0AN0, the implication
(3) ⟹ (1) of Stacks 0ANG, and the invariance of rig-étaleness under isomorphism of targets
implied by the locality of Stacks 0ANI. Stacks 0GD1 is proved with none of these inputs, and
with the source's hypotheses exactly, as
`AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isLocallyNoetherian` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleBaseChangeCharts`, which works with the
charts of Stacks 0GBD directly and condition (4) of Stacks 0GCZ.

The locally Noetherian hypotheses of Stacks 0AKY on the spaces involved are supplied by each
statement, since the predicate of Stacks 0AQM does not build them in; they are carried in the
statements rather than used in the proofs, where the class of rings over which the chart
condition quantifies already provides adicness and Noetherianity of every chart ring.

## References

* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0GD2](https://stacks.math.columbia.edu/tag/0GD2)
* [Stacks Project, Tag 0GD3](https://stacks.math.columbia.edu/tag/0GD3)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
* [Stacks Project, Tag 0AQL](https://stacks.math.columbia.edu/tag/0AQL)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GCW](https://stacks.math.columbia.edu/tag/0GCW)
* [Stacks Project, Tag 0GCX](https://stacks.math.columbia.edu/tag/0GCX)
* [Stacks Project, Tag 0GCY](https://stacks.math.columbia.edu/tag/0GCY)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GBP](https://stacks.math.columbia.edu/tag/0GBP)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **Stacks 0GCZ, conditions (1) and (2).** A morphism of formal algebraic spaces over `S` is
rig-étale exactly when rig-étaleness as a property of arrows of `WAdm^{Noeth}` holds on every
affine étale diagram over it: the two conditions are the same, which is what Definition 0AQM
says. -/
theorem isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsRigEtale B S hS f ↔
      HasPropertyOnEveryAffineEtaleDiagram B S hS
        (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
        (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
          [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
          RingHom.IsRigEtaleArrow φ) f := by
  constructor
  · intro h U V a b t hU hV ⟨ha, haet⟩ ⟨hb, hbet⟩ hcomm A R _ _ _ _ _ _ _ _
      ⟨hAadic, hAnoeth⟩ ⟨hRadic, hRnoeth⟩ hA D E eU eV g hg _ _ _ _
    exact ⟨g.continuous,
      h U V hU hV a b t ha hb haet hbet hcomm A R hAadic hRadic hA D E eU eV g hg⟩
  · intro h U V hU hV a b t ha hb haet hbet hcomm A R _ _ _ _ _ _ _ _ _ _
      hAadic hRadic hA D E eU eV g hg
    have hP := h U V a b t hU hV ⟨ha, haet⟩ ⟨hb, hbet⟩ hcomm A R
      ⟨hAadic, inferInstance⟩ ⟨hRadic, inferInstance⟩ hA D E eU eV g hg
    exact hP.2

/-- The transfer to formal algebraic spaces drawn in **Stacks 0GBP**: whenever a local property
`P` of arrows of `WAdm^{Noeth}` has the cancellation property, condition (1) of Stacks 0ANG
passes from a composite with `P` and a second factor with `P` to the first factor. -/
abbrev TransfersCancellationOnAffineEtaleDiagrams (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
    TopologicalRing.PropertyIsLocalNoetherian.{u} P →
    TopologicalRing.HasNoetherianCancellationProperty.{u} P →
    ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
      HasPropertyOnEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g) →
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P g →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f

/-- Rig-étaleness of morphisms of locally Noetherian formal algebraic spaces over `S` cancels
on the right, derived from the ring-level cancellation of Stacks 0GCY through a transfer
`htransfer` of Remark 0GBP and a locality statement `hcond` for `Rig.RigEtaleCondition`: if
`g ∘ f` and `g` are rig-étale, for `f : X ⟶ Y` and `g : Y ⟶ Z`, then `f` is rig-étale. Stacks
0GD3 itself is `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isLocallyNoetherian`, which
takes exactly the hypotheses of the source. The hypothesis `hcond` here can never be supplied:
`Rig.not_propertyIsLocalNoetherian_rigEtaleCondition` refutes it. -/
theorem isRigEtale_of_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hcond : TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        Rig.RigEtaleCondition φ))
    (htransfer : TransfersCancellationOnAffineEtaleDiagrams B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (_hX : IsLocallyNoetherian B S hS X) (_hY : IsLocallyNoetherian B S hS Y)
    (_hZ : IsLocallyNoetherian B S hS Z)
    (hfg : IsRigEtale B S hS (f ≫ g)) (hg : IsRigEtale B S hS g) :
    IsRigEtale B S hS f :=
  (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mpr
    (htransfer _ (Rig.rigEtale_isLocalNoetherian hcond)
      Rig.rigEtale_hasNoetherianCancellationProperty f g
      ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (f ≫ g)).mp hfg)
      ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS g).mp hg))

/-- A conditional variant of Stacks 0GD1, assembled from the generic transfer of Remark 0GBG:
if `f : X ⟶ Y` is rig-étale and `g : Z ⟶ Y` satisfies the chart condition
`IsAdicOnEveryAffineEtaleDiagramNoetherian`, then `X ×_Y Z ⟶ Z` is rig-étale, given the inputs
`hcond`, `hiso`, `h31` and `hcover`.

Stacks 0GD1 itself is
`AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isLocallyNoetherian`, which takes
exactly the hypotheses of the source. The hypothesis `hcond` here can never be supplied:
`Rig.not_propertyIsLocalNoetherian_rigEtaleCondition` refutes it. -/
theorem isRigEtale_pullback_snd_of_isAdicMorphism (B : BigFppfSite.{u}) (S : Scheme.{u})
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
        (Rig.rigEtale_isLocalNoetherian hcond))
      hiso h31 f g hcover
      ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf) hg)

end AlgebraicGeometry.FormalSpace

end
