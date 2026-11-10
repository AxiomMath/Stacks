module

public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorHenselianSpecMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralCodimensionZeroHypotheses

/-!
# Hypotheses (a), (b) and (c) of Stacks 0ENA for `Spec(𝒪^h_{X, ξ})`

Let `X` be a decent, locally Noetherian, integral algebraic space over `S` and let `Z ⊆ X` be a
prime divisor with generic point `ξ`.  The germ API of
`AlgebraicGeometry.Space.PrimeDivisor.genericMeromorphicGerm` carries the henselian local ring
there as an abstract henselization `R` in `Type u` of the Zariski local ring of
`AlgebraicGeometry.Space.PrimeDivisor.genericChart`, and reads the meromorphic sections of
`ℒ_ξ = c_ξ^*ℒ` on the algebraic space `Spec(R)` that `R` represents.

This file proves hypotheses (a), (b) and (c) of Stacks 0ENA for `Spec(R)` from the standing
hypotheses of Chapter 72's divisor theory on `X`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.isReduced_genericHenselization`,
  `.isNoetherianRing_genericHenselization` and
  `.ringKrullDim_genericHenselization_eq_one`: the abstract henselization `R` the germ API
  carries is reduced, Noetherian and of Krull dimension one.  The corresponding statements for
  `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRing`, a `CommRingCat.{u + 1}`,
  are a different constant and do not apply to `R`.
* `AlgebraicGeometry.Space.PrimeDivisor.forall_localRingDimension_genericHenselianSpace_eq_zero`,
  `.hasLocallyFiniteIrreducibleComponents_genericHenselianSpace` and
  `.hasMonomorphicCodimensionZeroPoints_genericHenselianSpace`: hypotheses (a), (b) and (c) of
  Stacks 0ENA for `Spec(R)`.
* `PrimeDivisor.nonempty_codimensionZeroPresentation_genericHenselianSpace`: the presentation
  of the schematic locus of `Spec(R)` at its codimension-zero points that Stacks 0ENA produces
  from them.

## Implementation notes

The three ring-theoretic properties of `R` are those of the Zariski local ring of the generic
chart, transported along
`StacksDraft.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_of_isHenselization`, which is
universe-polymorphic in the henselization and so applies to `R : Type u`.  The stalk itself is
reduced and Noetherian because the chart is an étale scheme over a reduced, locally Noetherian
algebraic space (`AlgebraicGeometry.Space.PrimeDivisor.isReduced_chart` and
`.isLocallyNoetherian_chart`), and of Krull dimension one by Stacks 0ED1 and the
codimension-one hypothesis on the prime divisor.

`Spec(R)` is a *representable* algebraic space, so hypotheses (a) and (b) come from the scheme
`Spec(R)` through `AlgebraicGeometry.Space.hasEtaleLocalProperty_of_representable` — which
needs no étale locality of the property — and hypothesis (c) from
`AlgebraicGeometry.Space.isDecentSpace_yoneda`, a representable space being decent with no
hypotheses at all.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ED1](https://stacks.math.columbia.edu/tag/0ED1)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X)

/-! ### The Zariski local ring of the generic chart -/

include hInt in
/-- The Zariski local ring of the generic chart of a prime divisor at its distinguished point is
reduced, the chart being an étale scheme over an integral, hence reduced, algebraic space. -/
theorem PrimeDivisor.isReduced_genericChartStalk :
    _root_.IsReduced ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point) :=
  have : IsReduced (Z.genericChart B S hS hX hdec).scheme.left.1 :=
    Z.isReduced_chart B S hS hX hInt (Z.genericChart B S hS hX hdec)
  isReduced_stalk_of_isReduced (Z.genericChart B S hS hX hdec).scheme.left.1
    (Z.genericChart B S hS hX hdec).point

include hN in
/-- The Zariski local ring of the generic chart of a prime divisor at its distinguished point is
Noetherian, the chart being an étale scheme over a locally Noetherian algebraic space. -/
theorem PrimeDivisor.isNoetherianRing_genericChartStalk :
    IsNoetherianRing ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point) :=
  have : IsLocallyNoetherian (Z.genericChart B S hS hX hdec).scheme.left.1 :=
    Z.isLocallyNoetherian_chart B S hS hX hN (Z.genericChart B S hS hX hdec)
  inferInstance

include hX hdec in
/-- **Stacks 0ED1 at the generic point of a prime divisor.**  The Zariski local ring of the
generic chart at its distinguished point has Krull dimension one: the point lies above the
generic point `ξ` of the prime divisor, so that Krull dimension is the dimension of the local
ring of `X` at `ξ`, which is the codimension of `Z`. -/
theorem PrimeDivisor.ringKrullDim_genericChartStalk_eq_one :
    ringKrullDim ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point) = 1 := by
  have hUetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (Z.genericChart B S hS hX hdec).toSpace :=
    (isEtale_iff_presheaf_of_yoneda B S hS (Z.genericChart B S hS hX hdec).toSpace).1
      (Z.genericChart B S hS hX hdec).etale_toSpace
  have hChart : ChartPoint B S hS (Z.genericChart B S hS hX hdec).scheme
      (Z.genericChart B S hS hX hdec).toSpace (Z.genericChart B S hS hX hdec).point
      (Z.genericPoint B S hS X) :=
    ⟨⟨(Z.genericChart B S hS hX hdec).scheme.left.1.residueField
          (Z.genericChart B S hS hX hdec).point,
        (Z.genericChart B S hS hX hdec).residueField_contained,
        (Z.genericChart B S hS hX hdec).scheme.left.1.fromSpecResidueField
            (Z.genericChart B S hS hX hdec).point ≫
          (Z.genericChart B S hS hX hdec).scheme.hom.1,
        residueFieldMap B S hS (Z.genericChart B S hS hX hdec).scheme
          (Z.genericChart B S hS hX hdec).point
          (Z.genericChart B S hS hX hdec).residueField_contained⟩,
      (Z.genericChart B S hS hX hdec).scheme.left.1.fromSpecResidueField_apply
        (Z.genericChart B S hS hX hdec).point _,
      (Z.genericChart B S hS hX hdec).map_point⟩
  have hdimChart : (localRingDimension B S hS (Z.genericPoint B S hS X) : WithBot ℕ∞) =
      ringKrullDim ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point) :=
    localRingDimension_eq_of_chartPoint B S hS hX (Z.genericChart B S hS hX hdec).scheme
      (Z.genericChart B S hS hX hdec).toSpace hUetale (Z.genericChart B S hS hX hdec).point
      (Z.genericPoint B S hS X) hChart
  have hdim1 : localRingDimension B S hS (Z.genericPoint B S hS X) = 1 :=
    (codimension_eq_localRingDimension B S hS hX hdec
        (IrreducibleCloseds.closureSingleton (Z.genericPoint B S hS X))
        (Z.genericPoint B S hS X)
        (IrreducibleCloseds.coe_closureSingleton (Z.genericPoint B S hS X)).symm).symm.trans
      (Z.codimension_genericPoint B S hS X)
  rw [← hdimChart, hdim1]
  norm_cast

/-! ### The abstract henselization the germ API carries -/

section Generic

variable (R : Type u) [CommRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  (hR : B.Contains (Spec (.of R)))

section Henselization

variable [IsLocalRing R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R]

include hX hdec hInt hN Z in
/-- **The abstract henselization `𝒪^h_{X, ξ}` the germ API carries is reduced, of Krull
dimension one, and Noetherian.**

These are the three ring-theoretic properties of Stacks 0ENK, for the henselization `R` in
`Type u` of the Zariski local ring of the generic chart rather than for
`AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRing`, which is a different constant
one universe up.  The Zariski local ring has them, and they are invariant under henselization in
any universe. -/
theorem PrimeDivisor.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_genericHenselization :
    _root_.IsReduced R ∧ ringKrullDim R = 1 ∧ IsNoetherianRing R :=
  have : _root_.IsReduced ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point) :=
    Z.isReduced_genericChartStalk B S hS hX hdec hInt
  have : IsNoetherianRing ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point) :=
    Z.isNoetherianRing_genericChartStalk B S hS hX hdec hN
  StacksDraft.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_of_isHenselization
    (R := (Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (H := R) (Z.ringKrullDim_genericChartStalk_eq_one B S hS hX hdec)

include hX hdec hInt hN Z in
/-- The abstract henselization `𝒪^h_{X, ξ}` the germ API carries is reduced. -/
theorem PrimeDivisor.isReduced_genericHenselization : _root_.IsReduced R :=
  (Z.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_genericHenselization
    B S hS hX hdec hInt hN R).1

include hX hdec hInt hN Z in
/-- The abstract henselization `𝒪^h_{X, ξ}` the germ API carries has Krull dimension one. -/
theorem PrimeDivisor.ringKrullDim_genericHenselization_eq_one : ringKrullDim R = 1 :=
  (Z.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_genericHenselization
    B S hS hX hdec hInt hN R).2.1

include hX hdec hInt hN Z in
/-- The abstract henselization `𝒪^h_{X, ξ}` the germ API carries is Noetherian. -/
theorem PrimeDivisor.isNoetherianRing_genericHenselization : IsNoetherianRing R :=
  (Z.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_genericHenselization
    B S hS hX hdec hInt hN R).2.2

end Henselization

/-! ### Hypotheses (a), (b) and (c) of Stacks 0ENA for `Spec(𝒪^h_{X, ξ})` -/

include hX hdec Z in
/-- `Spec(𝒪^h_{X, ξ})` is a reduced algebraic space: it is represented by the spectrum of the
reduced ring `𝒪^h_{X, ξ}`. -/
theorem PrimeDivisor.hasEtaleLocalProperty_isReduced_genericHenselianSpace
    (hred : _root_.IsReduced R) :
    HasEtaleLocalProperty B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).1
      (fun Y : Scheme.{u} => IsReduced Y) :=
  have : _root_.IsReduced R := hred
  hasEtaleLocalProperty_of_representable B S hS _ _
    ((Z.genericChart B S hS hX hdec).henselianObj R hR) (Iso.refl _)
    (inferInstanceAs (IsReduced (Spec (.of R))))

include hX hdec Z in
/-- **Hypothesis (a) of Stacks 0ENA for `Spec(𝒪^h_{X, ξ})`.**  Every weakly associated point of
`Spec(𝒪^h_{X, ξ})` has codimension `0`, the ring `𝒪^h_{X, ξ}` being reduced. -/
theorem PrimeDivisor.forall_localRingDimension_genericHenselianSpace_eq_zero
    (hred : _root_.IsReduced R) :
    ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (Z.genericHenselianSpace B S hS hX hdec R hR),
      localRingDimension B S hS z = 0 :=
  forall_localRingDimension_eq_zero_of_isReduced B S hS
    (Z.genericHenselianSpace B S hS hX hdec R hR)
    (Z.hasEtaleLocalProperty_isReduced_genericHenselianSpace B S hS hX hdec R hR hred)

include hX hdec Z in
/-- `Spec(𝒪^h_{X, ξ})` is a locally Noetherian algebraic space: it is represented by the
spectrum of the Noetherian ring `𝒪^h_{X, ξ}`. -/
theorem PrimeDivisor.hasEtaleLocalProperty_isLocallyNoetherian_genericHenselianSpace
    (hnoeth : IsNoetherianRing R) :
    HasEtaleLocalProperty B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).1
      (fun Y : Scheme.{u} => IsLocallyNoetherian Y) :=
  have : IsNoetherianRing R := hnoeth
  hasEtaleLocalProperty_of_representable B S hS _ _
    ((Z.genericChart B S hS hX hdec).henselianObj R hR) (Iso.refl _)
    (inferInstanceAs (IsLocallyNoetherian (Spec (.of R))))

include hX hdec Z in
/-- **Hypothesis (b) of Stacks 0ENA for `Spec(𝒪^h_{X, ξ})`.**  The irreducible components of
`Spec(𝒪^h_{X, ξ})` are locally finite, the ring `𝒪^h_{X, ξ}` being Noetherian. -/
theorem PrimeDivisor.hasLocallyFiniteIrreducibleComponents_genericHenselianSpace
    (hnoeth : IsNoetherianRing R) :
    HasLocallyFiniteIrreducibleComponents B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).1 :=
  hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS _
    (Z.genericHenselianSpace B S hS hX hdec R hR).2
    (Z.hasEtaleLocalProperty_isLocallyNoetherian_genericHenselianSpace
      B S hS hX hdec R hR hnoeth)

/-- `Spec(𝒪^h_{X, ξ})` is a decent algebraic space, being representable. -/
theorem PrimeDivisor.isDecentSpace_genericHenselianSpace :
    IsDecentSpace B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).1 :=
  isDecentSpace_yoneda B S hS ((Z.genericChart B S hS hX hdec).henselianObj R hR)

/-- **Hypothesis (c) of Stacks 0ENA for `Spec(𝒪^h_{X, ξ})`.**  Every codimension-zero point of
`Spec(𝒪^h_{X, ξ})` is represented by a monomorphism from the spectrum of a field, the space
being representable and hence decent. -/
theorem PrimeDivisor.hasMonomorphicCodimensionZeroPoints_genericHenselianSpace :
    HasMonomorphicCodimensionZeroPoints B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).1 :=
  hasMonomorphicCodimensionZeroPoints_of_isDecentSpace B S hS
    (Z.isDecentSpace_genericHenselianSpace B S hS hX hdec R hR)

include hX hdec Z in
/-- **Stacks 0ENA for `Spec(𝒪^h_{X, ξ})`.**  The schematic locus of `Spec(𝒪^h_{X, ξ})` has a
presentation at its codimension-zero points, so the local rings `𝒪_{Spec(𝒪^h_{X, ξ}), η}` and
the morphisms `j_η` there are defined. -/
theorem PrimeDivisor.nonempty_codimensionZeroPresentation_genericHenselianSpace
    (hnoeth : IsNoetherianRing R) :
    Nonempty (CodimensionZeroPresentation B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).1) :=
  exists_codimensionZeroPresentation B S hS
    (Z.genericHenselianSpace B S hS hX hdec R hR).2
    (Z.hasLocallyFiniteIrreducibleComponents_genericHenselianSpace B S hS hX hdec R hR hnoeth)
    (Z.hasMonomorphicCodimensionZeroPoints_genericHenselianSpace B S hS hX hdec R hR)

end Generic

end AlgebraicGeometry.Space

end
