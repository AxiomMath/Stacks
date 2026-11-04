module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.RingTheory.Rig.FlatIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeLocality

/-!
# Rig-flatness is stable under base change by a morphism locally of finite type

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GGZ** says that if
`f` is rig-flat (Stacks 0GGX) and `g` is locally of finite type (Stacks 0AM4, part (1)), then
the second projection `X ×_Y Z ⟶ Z` is rig-flat.

## Main definitions

* `AlgebraicGeometry.FormalSpace.RigFlatBaseChangeByAdicFiniteType`: the base-change assertion
  of **Stacks 0GGR**, in the shape the `baseChange` field of
  `TopologicalRing.IsStableUnderBaseChangeBy` asks for.

## Main results

* `TopologicalRing.propertyIsLocalNoetherian_of_adicStar`: a property local on the weakly
  admissible adic\* rings of Stacks 0ANH is local on the Noetherian adic rings of Stacks 0ANI.
* `TopologicalRing.adicAndFiniteType_propertyIsLocalNoetherian`: **Stacks 0GBW** read in the
  Noetherian subcategory.
* `AlgebraicGeometry.FormalSpace.rigFlat_isStableUnderBaseChangeByAdicFiniteType`: Stacks 0GGR
  packaged as the stability bundle of Stacks 0GBG.

## Implementation notes

Stacks 0GGZ is the composite of two facts, exactly as its rig-smooth counterpart Stacks 0GCR
is in `StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange`. At the level of
topological rings, rig-flatness is stable under base change by homomorphisms which are adic and
topologically of finite type, in the sense of Remark 0GBG; this is Stacks 0GGR. Remark 0GBG then
draws from such a stability bundle the geometric transfer: condition (1) of Stacks 0ANG passes
from `f` and `g` to the second projection of their fibre product.

Three inputs of that chain are not in the library and are carried as hypotheses. None of them
mentions the fibre product of `f` and `g`, so none is a restatement of the conclusion.

* The base-change assertion of Stacks 0GGR is `RigFlatBaseChangeByAdicFiniteType`. The library
  carries only the last step of 0GGR, for `C` a restricted power series ring and for flatness
  at a single rig-closed point, as
  `Rig.flat_atPrime_completedTensorProduct_restrictedPowerSeries` in
  `StacksFrontier.RingTheory.Rig.ClosedPoint.CompletedTensorProductFlat`; that is not enough to
  discharge the field. The two locality fields of the bundle, on the other hand, are proved:
  locality of rig-flatness is Stacks 0GGU (`Rig.rigFlat_isLocalNoetherian`) and locality of
  "adic and topologically of finite type" is Stacks 0GBW
  (`TopologicalRing.adicAndFiniteType_propertyIsLocal`), the latter stated for the weakly
  admissible adic\* rings of Stacks 0ANH and transported here to the Noetherian adic rings of
  Stacks 0ANI, a Noetherian adic ring having a finitely generated ideal of definition.
* The geometric transfer of Remark 0GBG is
  `TransfersBaseChangeOnAffineEtaleDiagrams`, reused from the rig-smooth development; it is
  quantified over *all* pairs of properties admitting a stability bundle and is therefore a
  statement about the generic machinery of the remark.
* The chart reading of "locally of finite type" is the hypothesis `h0AQ2`: a morphism of
  locally Noetherian formal algebraic spaces which is locally of finite type gives, on every
  affine étale diagram over it, a continuous homomorphism which is adic and topologically of
  finite type. This is the discussion of Formal Spaces, Section 0AQ2 that the proof of Stacks
  0GGZ invokes — adicness of the chart maps is the equivalence of Lemma 0ANK used there, and
  topological finite type of the chart maps is Stacks 0ANL followed by Stacks 0ANT. The library
  has neither Lemma 0ANK nor the implication of Stacks 0ANL that produces the chart square, and
  of Stacks 0ANT only the half recorded in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType`.

Rig-flatness of `f` and local finite type of `g` are taken in their own library spellings,
`AlgebraicGeometry.FormalSpace.IsRigFlat` of Stacks 0GGX and
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType` of Stacks 0AM4; the locally Noetherian
hypotheses on `X`, `Y`, `Z` are `AlgebraicGeometry.FormalSpace.IsLocallyNoetherian` of Stacks
0AKY. The hypothesis on `X` is not used in the proof — the class of rings over which the chart
condition of Stacks 0GGX quantifies already provides adicness and Noetherianity of every chart
ring — and the ones on `Y` and `Z` are consumed only by `h0AQ2`, exactly as for Stacks 0GD1 in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability`.

## References

* [Stacks Project, Tag 0GGZ](https://stacks.math.columbia.edu/tag/0GGZ)
* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0GGU](https://stacks.math.columbia.edu/tag/0GGU)
* [Stacks Project, Tag 0GGX](https://stacks.math.columbia.edu/tag/0GGX)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0AQ2](https://stacks.math.columbia.edu/tag/0AQ2)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

/-- A Noetherian adic topological ring lies in the subcategory of Stacks 0ANH: it has a
finitely generated ideal of definition. This is the local form of a fact that
`StacksFrontier.RingTheory.Rig.FlatIsLocal` records as `Rig.exists_fg_isAdic_of_isAdicRing`. -/
private theorem exists_fg_isAdic_of_isAdic_and_isNoetherian {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (hR : TopologicalRing.IsAdic R ∧ IsNoetherianRing R) :
    ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I :=
  let : IsNoetherianRing R := hR.2
  Rig.exists_fg_isAdic_of_isAdicRing hR.1

/-- A property of morphisms which is local on the weakly admissible adic\* rings of **Stacks
0ANH** is local on the Noetherian adic rings of **Stacks 0ANI**: the three locality axioms
restrict all the rings involved to the ambient subcategory, and a Noetherian adic ring has a
finitely generated ideal of definition. -/
theorem propertyIsLocalNoetherian_of_adicStar
    {P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop}
    (hP : TopologicalRing.AdicStarPropertyIsLocal.{u} P) :
    TopologicalRing.PropertyIsLocalNoetherian.{u} P := by
  refine ⟨?_, ?_, ?_⟩
  · intro A R A' R' _ _ _ _ _ _ _ _ _ _ D hA hR hA' hR' hmap
    exact hP.localizationPreserves D (exists_fg_isAdic_of_isAdic_and_isNoetherian hA)
      (exists_fg_isAdic_of_isAdic_and_isNoetherian hR)
      (exists_fg_isAdic_of_isAdic_and_isNoetherian hA')
      (exists_fg_isAdic_of_isAdic_and_isNoetherian hR') hmap
  · intro A R A' R' _ _ _ _ _ _ _ _ _ _ D hA hR hA' hR' hff hmap
    exact hP.faithfullyFlatDescent D (exists_fg_isAdic_of_isAdic_and_isNoetherian hA)
      (exists_fg_isAdic_of_isAdic_and_isNoetherian hR)
      (exists_fg_isAdic_of_isAdic_and_isNoetherian hA')
      (exists_fg_isAdic_of_isAdic_and_isNoetherian hR') hff hmap
  · intro R _ _ _ _ hR hRcount ι _ A _ _ _ _ hA hAcount φ hφ hRmem hAmem hprop
    exact hP.finiteProduct hR hRcount A hA hAcount φ hφ
      (exists_fg_isAdic_of_isAdic_and_isNoetherian hRmem)
      (fun i ↦ exists_fg_isAdic_of_isAdic_and_isNoetherian (hAmem i)) hprop

/-- **Stacks 0GBW** read in the Noetherian subcategory of Stacks 0ANI: being adic and
topologically of finite type is a local property of morphisms of Noetherian adic topological
rings. -/
theorem adicAndFiniteType_propertyIsLocalNoetherian :
    TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) :=
  propertyIsLocalNoetherian_of_adicStar TopologicalRing.adicAndFiniteType_propertyIsLocal

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

section BaseChangeHypothesis

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The base-change assertion of **Stacks 0GGR**: if `R₀ → R₁` is rig-flat and `R₀ → R₂` is
adic and topologically of finite type, all three rings being Noetherian and adic, then the
completed tensor product `R₁ ⊗̂_{R₀} R₂` is Noetherian and adic again and `R₂ → R₁ ⊗̂_{R₀} R₂`
is rig-flat.

This is written in the shape the `baseChange` field of
`TopologicalRing.IsStableUnderBaseChangeBy` asks for, which is the shape in which Remark 0GBG
consumes it. -/
abbrev RigFlatBaseChangeByAdicFiniteType : Prop :=
  ∀ {R₀ R₁ R₂ : Type u} [CommRing R₀] [TopologicalSpace R₀] [IsTopologicalRing R₀]
      [IsLinearTopology R₀ R₀] [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [IsLinearTopology R₁ R₁] [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
      [IsLinearTopology R₂ R₂] [Algebra R₀ R₁] [Algebra R₀ R₂] [IsNoetherianRing R₀]
      [IsNoetherianRing R₁] [IsNoetherianRing R₂],
    TopologicalRing.IsAdic R₀ → TopologicalRing.IsAdic R₁ → TopologicalRing.IsAdic R₂ →
    Continuous (algebraMap R₀ R₁) → Continuous (algebraMap R₀ R₂) →
    Rig.RingHom.IsRigFlat (algebraMap R₀ R₁) →
    (RingHom.IsAdic (algebraMap R₀ R₂) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (algebraMap R₀ R₂)) →
    (TopologicalRing.IsAdic
        (TopologicalRing.CompletedTensorProduct (R := R₀) (M := R₁) (N := R₂)) ∧
      IsNoetherianRing
        (TopologicalRing.CompletedTensorProduct (R := R₀) (M := R₁) (N := R₂)) ∧
      Rig.RingHom.IsRigFlat (algebraMap R₂
        (TopologicalRing.CompletedTensorProduct (R := R₀) (M := R₁) (N := R₂))))

/-- Stacks 0GGR packaged as the bundle `TopologicalRing.IsStableUnderBaseChangeBy`, which
carries the locality of both properties as further fields. Both localities are proved: that of
rig-flatness is Stacks 0GGU and that of "adic and topologically of finite type" is Stacks 0GBW.
The base-change condition itself — all that Remark 0GBG defines and all that Stacks 0GGR
asserts — is the hypothesis `hbc`, since the library carries only the last step of Stacks 0GGR.

This statement is deliberately untagged, exactly as its rig-smooth counterpart
`TopologicalRing.rigSmooth_isStableUnderBaseChangeByAdic` is: it carries a hypothesis that
Stacks 0GGR itself does not, so a tag over it would stand over a hypothesis rather than over a
theorem. -/
theorem rigFlat_isStableUnderBaseChangeByAdicFiniteType
    (hbc : RigFlatBaseChangeByAdicFiniteType.{u}) :
    TopologicalRing.IsStableUnderBaseChangeBy.{u}
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        Rig.RingHom.IsRigFlat φ)
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) where
  isLocalP := Rig.rigFlat_isLocalNoetherian
  isLocalQ := TopologicalRing.adicAndFiniteType_propertyIsLocalNoetherian
  baseChange h₀ h₁ h₂ hc₁ hc₂ hP hQ := hbc h₀ h₁ h₂ hc₁ hc₂ hP hQ

end BaseChangeHypothesis

/-- The chart reading of "locally of finite type" drawn from the discussion of Formal Spaces,
**Section 0AQ2**: a morphism of locally Noetherian formal algebraic spaces over `S` which is
locally of finite type satisfies condition (1) of Stacks 0ANG for the property "adic and
topologically of finite type" of arrows of `WAdm^{Noeth}`. -/
abbrev LocalFiniteTypeReadsOnAffineEtaleDiagrams (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ {X Y : FppfSheaf B S hS} (h : X ⟶ Y), IsLocallyNoetherian B S hS X →
    IsLocallyNoetherian B S hS Y → IsLocallyOfFiniteType B S hS h →
      HasPropertyOnEveryAffineEtaleDiagram B S hS
        (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
        (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
          [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
          RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) h

end AlgebraicGeometry.FormalSpace

end
