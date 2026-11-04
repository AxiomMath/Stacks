module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicStarBaseChangeSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicStarChartCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffineCharts

/-!
# Base change of a local property of morphisms of locally adic\* formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. **Remark 87.21.8 (Stacks 0GBE)** defines
what it means for a local property `P` of morphisms of `WAdm^{adic*}` (Remark 0ANH) to be
*stable under base change* — `TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar`, whose
well definedness, that `A ⊗̂_B C` is again an object of `WAdm^{adic*}`, is
`TopologicalRing.isAdicStar_completedTensorProduct` (Lemma 87.4.12, Stacks 0GB4) — and asserts
that in exactly the same way as Lemma 87.21.7 (Stacks 0GBD) one obtains its variant for
morphisms between locally adic\* formal algebraic spaces over `S`. This file states that
variant.

## Main results

* `TopologicalRing.adicStarPropertyIsStableUnderBaseChange_iff`: the two readings of the first
  half of the remark, at the classes `∃ I : Ideal R, I.FG ∧ _root_.IsAdic I` and
  `TopologicalRing.IsAdicStar`, agree.
* `TopologicalRing.adicStarPropertyIsStableUnderComposition_iff`: the same for the notion of
  stability under composition of Stacks 0GBJ.
* `AlgebraicGeometry.FormalSpace.pullback_snd_hasProperty_of_isLocallyAdicStar`: if
  `f : X ⟶ Y` and `g : Z ⟶ Y` are morphisms of locally adic\* formal algebraic spaces and `f`
  satisfies the equivalent conditions of Stacks 0ANG for `P`, then so does
  `pr₂ : X ×_Y Z ⟶ Z`.

## Implementation notes

Situation 0CBA, whose axioms Remark 0ANH reads at `WAdm^{adic*}`, opens with "let `P` be a
property of morphisms of `WAdm^count`, invariant under isomorphism of source and target in this
category"; that invariance is part of the source's hypothesis on `P` and is carried as `hsrc`
and `htgt`. The hypothesis on `f` is condition (1) of Stacks 0ANG, the one the proof of Stacks
0GBD starts from; the conclusion is all three conditions for `pr₂`.

The proof is the source's. The covering of `X ×_Y Z` by the fibre products of charts
`Uⱼᵢ ×_{Vⱼ} Wⱼₖ` is built in
`StacksFrontier/AlgebraicGeometry/FormalSpace/AdicStarBaseChangeSpaces.lean`, with adic\* charts
throughout; its chart maps to `Wⱼₖ` have `P` by stability under base change, the chart ring of
a fibre product of charts being the completed tensor product by clause (3) of Stacks 0AN3. That
gives conditions (2) and (3) for `pr₂`, and condition (1) follows by the implication (3) ⟹ (1)
of Stacks 0ANG, `hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal`, at the
class `WAdm^{adic*}`.

## References

* [Stacks Project, Tag 0GBE](https://stacks.math.columbia.edu/tag/0GBE)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The two readings of stability under base change on `WAdm^{adic*}` agree.**
`TopologicalRing.AdicStarPropertyIsStableUnderBaseChange` reads the first half of Stacks 0GBE
at the class `∃ I : Ideal R, I.FG ∧ _root_.IsAdic I`, and
`TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar` at the class
`TopologicalRing.IsAdicStar`. The two classes coincide on weakly admissible rings, and every ring
either notion tests is weakly admissible: the locality clauses agree by
`TopologicalRing.adicStarPropertyIsLocal_iff_propertyIsLocalAdicStar`, and each of the three
rings of the base-change clause is assumed weakly admissible alongside its class membership, so
that `TopologicalRing.isAdicStar_of_isWeaklyAdmissible` and
`Rig.idealOfDefinition_isAdic_of_isAdicRing` pass between the two memberships. -/
theorem adicStarPropertyIsStableUnderBaseChange_iff
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) :
    AdicStarPropertyIsStableUnderBaseChange.{u} P ↔
      PropertyIsStableUnderBaseChangeAdicStar.{u} P := by
  refine ⟨isStableUnderBaseChangeAdicStar_of_adicStarProperty, fun hP ↦
    ⟨(adicStarPropertyIsLocal_iff_propertyIsLocalAdicStar P).2 hP.isLocal, ?_⟩⟩
  intro B A C _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBw hB hAw hA hCw hC hcA hcC hp
  exact hP.baseChange hBw (isAdicStar_of_isWeaklyAdmissible hBw hB) hAw
    (isAdicStar_of_isWeaklyAdmissible hAw hA) hCw (isAdicStar_of_isWeaklyAdmissible hCw hC)
    hcA hcC hp

end

/-- **The two readings of stability under composition on `WAdm^{adic*}` agree**, for the reason
recorded at `TopologicalRing.adicStarPropertyIsStableUnderBaseChange_iff`: the locality clauses
agree by `TopologicalRing.adicStarPropertyIsLocal_iff_propertyIsLocalAdicStar`, and the three
rings of the composition clause are assumed weakly admissible. -/
theorem adicStarPropertyIsStableUnderComposition_iff
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) :
    AdicStarPropertyIsStableUnderComposition.{u} P ↔
      PropertyIsStableUnderCompositionAdicStar.{u} P := by
  refine ⟨isStableUnderCompositionAdicStar_of_adicStarProperty, fun hP ↦
    ⟨(adicStarPropertyIsLocal_iff_propertyIsLocalAdicStar P).2 hP.isLocal, ?_⟩⟩
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC hAadic hBadic hCadic f g hf hg hPf hPg
  exact hP.comp hA hB hC (isAdicStar_of_isWeaklyAdmissible hA.1 hAadic)
    (isAdicStar_of_isWeaklyAdmissible hB.1 hBadic) (isAdicStar_of_isWeaklyAdmissible hC.1 hCadic)
    f g hf hg hPf hPg

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GBE, second half: the variant of Lemma 0GBD for locally adic\* formal algebraic
spaces.** Let `P` be a local property of morphisms of `WAdm^{adic*}` (Remark 0ANH), invariant
under isomorphism of source and target as Situation 0CBA stipulates, and stable under base
change in the sense of the first half of Remark 0GBE. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally adic\* formal algebraic spaces over `S`. If `f` satisfies the equivalent
conditions of Stacks 0ANG for `P` — here condition (1), that `P` holds on every affine étale
diagram over `f` — then `X ×_Y Z` is again locally adic\* (Stacks 0GBB (4)), so that the
conditions of Stacks 0ANG make sense for `pr₂ : X ×_Y Z ⟶ Z`, and `pr₂` satisfies all three of
them. -/
@[stacks 0GBE "the second half, the variant of Lemma 0GBD for morphisms between locally adic* \
formal algebraic spaces: for a local property P of morphisms of WAdm^{adic*} (Remark 0ANH, with \
the invariance under isomorphism of source and target that Situation 0CBA stipulates) which is \
stable under base change in the sense of the first half, \
TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar, and morphisms f : X -> Y, g : Z -> Y of \
locally adic* formal algebraic spaces, if f satisfies condition (1) of the equivalent conditions \
of Stacks 0ANG then X x_Y Z is locally adic* and pr2 : X x_Y Z -> Z satisfies all three"]
theorem pullback_snd_hasProperty_of_isLocallyAdicStar
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar.{u} P)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} TopologicalRing.IsAdicStar P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (hZ : IsLocallyAdicStar B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    IsLocallyAdicStar B S hS (pullback f g) ∧
      HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P
        (pullback.snd f g) ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P (pullback.snd f g) ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P (pullback.snd f g) := by
  have hEt : RepresentableEtaleOverAffineIsFormal B S hS :=
    representableEtaleOverAffineIsFormal B S hS
  exact ⟨isLocallyAdicStar_pullback_of_representableEtaleOverAffine B S hS hEt f g hX hY hZ,
    hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal B S hS
        TopologicalRing.IsAdicStar P classIsWeaklyAdmissible_isAdicStar
        classHasCountableNhdsZero_isAdicStar classIsStableUnderEtaleCompletion_isAdicStar
        classIsStableUnderFinitePi_isAdicStar hsrc htgt hP.isLocal (pullback.snd f g)
        (hasEtaleRefinementOfSourceCover_of_etale B S hS hEt (pullback.snd f g))
        (hasPropertyAfterSourceCoverOfClass_pullback_snd_of_isLocallyAdicStar B S hS hEt P hP htgt
          f g hX hY hZ hf),
      hasPropertyAfterTargetCover_pullback_snd_of_isLocallyAdicStar B S hS hEt P hP htgt f g hX hY
        hZ.1 hf,
      hasPropertyAfterSourceCover_pullback_snd_of_isLocallyAdicStar B S hS hEt P hP htgt f g hX hY
        hZ.1 hf⟩

end AlgebraicGeometry.FormalSpace

end
