module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicStarChartCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyUpToIsoInvariance
public import StacksFrontier.Topology.Algebra.AdicTopology.EquivTransport

/-!
# Stacks 0ANH: local properties of morphisms of `WAdm^{adic*}` and the variant of Stacks 0ANG

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0ANH** makes two assertions.

1. A property `P` of morphisms of `WAdm^{adic*}`, the adic topological rings possessing a
   finitely generated ideal of definition, is *local* if axioms (1), (2), (3) of Situation 0CBA
   hold for morphisms of `WAdm^{adic*}`. This is
   `TopologicalRing.PropertyIsLocalAdicStarUpToIso`. As in the source, the completed corners
   `(A')^∧ = lim A'/IA'` and `(B')^∧ = lim B'/JB'` of the diagrams of axioms (1) and (2) are any
   limits, that is, any rings isomorphic to the inverse limits.
   `TopologicalRing.propertyIsLocalAdicStarUpToIso_iff` restates the definition in the source's
   words, with the class `WAdm^{adic*}` asked only of the lower corners `A` and `B`.
2. For such a `P`, the three conditions of Stacks 0ANG are equivalent for a morphism of locally
   adic\* formal algebraic spaces over `S`. This is
   `AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_propertyIsLocalAdicStarUpToIso`.

The second assertion takes no hypothesis on `P` beyond locality. The proof of Stacks 0ANG uses
that `P` is invariant under isomorphism of source and target, and here that invariance is derived
from axiom (1) of Situation 0CBA, an isomorphism being étale, as the Stacks Project derives it.
The derivation is, in the namespace `AlgebraicGeometry.FormalSpace`,
`propertyIsInvariantUnderSourceIso_of_propertyIsLocalAdicStarUpToIso` and its target
counterpart. A variant reading of Situation 0CBA also requires `P` to be
invariant under isomorphism of source and target, which the online statement does not. That
invariance is a consequence of the notion of locality here, not a further hypothesis, so the
results hold under either reading.

## Main results

* `TopologicalRing.propertyIsLocalAdicStarUpToIso_iff`: the first half of Stacks 0ANH in the
  source's words.
* `AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_propertyIsLocalAdicStarUpToIso`: the second
  half of Stacks 0ANH, the variant of Stacks 0ANG for morphisms between locally adic\* formal
  algebraic spaces.

## References

* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

/-- Membership in `WAdm^{adic*}` transports along an isomorphism of topological rings. -/
theorem isAdicStar_of_ringEquiv {X Y : Type u} [CommRing X] [TopologicalSpace X]
    [IsTopologicalRing X] [IsLinearTopology X X] [CommRing Y] [TopologicalSpace Y]
    [IsTopologicalRing Y] [IsLinearTopology Y Y] (e : X ≃+* Y) (he : Continuous e)
    (hes : Continuous e.symm) (h : IsAdicStar X) : IsAdicStar Y :=
  ⟨isAdic_of_ringEquiv e he hes h.1, exists_fg_isIdealOfDefinition_of_ringEquiv e he hes h.2⟩

/-- **The first half of Stacks 0ANH, in the source's words.** A property `P` of morphisms of
`WAdm^{adic*}` is a local property, `TopologicalRing.PropertyIsLocalAdicStarUpToIso P`, exactly
when the three axioms of Situation 0CBA hold for morphisms of `WAdm^{adic*}`:

1. for every diagram of Situation 0CBA with `A` and `B` in `WAdm^{adic*}`, and any rings `Â`,
   `B̂` isomorphic to the limits `lim A'/IA'`, `lim B'/JB'`, `P(φ) ⟹ P(φ')`;
2. for every such diagram with `A → A'` faithfully flat, `P(φ') ⟹ P(φ)`;
3. if `P(B → Aᵢ)` for finitely many `Aᵢ` of `WAdm^{adic*}`, then `P(B → ∏ᵢ Aᵢ)`.

The definition asks in addition that `Â` and `B̂` be in `WAdm^{adic*}`, and that the rings
of the third axiom be weakly admissible and countably indexed. Neither is an extra condition. The
completions are in `WAdm^{adic*}` by Stacks 0ANB (4),
`AlgebraicGeometry.FormalSpace.classIsStableUnderEtaleCompletion_isAdicStar`, and so are `Â`
and `B̂`, which are isomorphic to them. Every ring of `WAdm^{adic*}` is weakly admissible and
countably indexed. -/
@[stacks 0ANH "the first half, the definition of a local property of morphisms of \
WAdm^{adic*}, in the source's words: axioms (1), (2), (3) of Situation 0CBA quantified over the \
diagrams and finite families of WAdm^{adic*}, the completed corners being any limits"]
theorem propertyIsLocalAdicStarUpToIso_iff
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) :
    PropertyIsLocalAdicStarUpToIso.{u} P ↔
      (∀ {A B A' B' Ahat Bhat : Type u}
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
        [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
        [CommRing A'] [CommRing B']
        [CommRing Ahat] [TopologicalSpace Ahat] [IsTopologicalRing Ahat]
        [IsLinearTopology Ahat Ahat]
        [CommRing Bhat] [TopologicalSpace Bhat] [IsTopologicalRing Bhat]
        [IsLinearTopology Bhat Bhat]
        (D : LocalizationDiagram A B A' B')
        (eA : CompletionOver D.toA' ≃+* Ahat) (eB : CompletionOver D.toB' ≃+* Bhat),
        Continuous eA → Continuous eA.symm → Continuous eB → Continuous eB.symm →
        IsAdicStar A → IsAdicStar B → P D.map →
          P ((eA.toRingHom.comp D.completedMap).comp eB.symm.toRingHom)) ∧
      (∀ {A B A' B' Ahat Bhat : Type u}
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
        [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
        [CommRing A'] [CommRing B']
        [CommRing Ahat] [TopologicalSpace Ahat] [IsTopologicalRing Ahat]
        [IsLinearTopology Ahat Ahat]
        [CommRing Bhat] [TopologicalSpace Bhat] [IsTopologicalRing Bhat]
        [IsLinearTopology Bhat Bhat]
        (D : LocalizationDiagram A B A' B')
        (eA : CompletionOver D.toA' ≃+* Ahat) (eB : CompletionOver D.toB' ≃+* Bhat),
        Continuous eA → Continuous eA.symm → Continuous eB → Continuous eB.symm →
        IsAdicStar A → IsAdicStar B → D.toA'.FaithfullyFlat →
          P ((eA.toRingHom.comp D.completedMap).comp eB.symm.toRingHom) → P D.map) ∧
      (∀ {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [IsLinearTopology B B] {ι : Type u} [Fintype ι] (A : ι → Type u)
        [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
        [∀ i, IsTopologicalRing (A i)] [∀ i, IsLinearTopology (A i) (A i)]
        (f : ∀ i, B →+* A i), (∀ i, Continuous (f i)) → IsAdicStar B →
        (∀ i, IsAdicStar (A i)) → (∀ i, P (f i)) → P (RingHom.pi f)) := by
  have hcompl : AlgebraicGeometry.FormalSpace.ClassIsStableUnderEtaleCompletion.{u} IsAdicStar :=
    AlgebraicGeometry.FormalSpace.classIsStableUnderEtaleCompletion_isAdicStar
  constructor
  · intro hP
    refine ⟨fun D eA eB heA heAs heB heBs hA hB ↦ hP.localizationPreserves D eA eB heA heAs heB
        heBs hA hB ?_ ?_,
      fun D eA eB heA heAs heB heBs hA hB ↦ hP.faithfullyFlatDescent D eA eB heA heAs heB
        heBs hA hB ?_ ?_,
      fun A _ _ _ _ f hf hB hA ↦ hP.finiteProduct (Rig.weaklyAdmissible_of_isAdicRing hB.1)
        (Rig.countablyGenerated_nhds_of_isAdicRing hB.1) A
        (fun i ↦ Rig.weaklyAdmissible_of_isAdicRing (hA i).1)
        (fun i ↦ Rig.countablyGenerated_nhds_of_isAdicRing (hA i).1) f hf hB hA⟩ <;>
    first
    | exact isAdicStar_of_ringEquiv eA heA heAs (hcompl D.toA' hA D.weaklyAdmissibleA D.etaleA)
    | exact isAdicStar_of_ringEquiv eB heB heBs (hcompl D.toB' hB D.weaklyAdmissibleB D.etaleB)
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun D eA eB heA heAs heB heBs hA hB _ _ ↦ h1 D eA eB heA heAs heB heBs hA hB,
      fun D eA eB heA heAs heB heBs hA hB _ _ ↦ h2 D eA eB heA heAs heB heBs hA hB,
      fun _ _ _ _ A _ _ _ _ _ _ f hf hB hA hfP ↦ h3 A f hf hB hA hfP⟩

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- **The second half of Stacks 0ANH: the variant of Stacks 0ANG for morphisms between locally
adic\* formal algebraic spaces.** Let `f : X ⟶ Y` be a morphism of locally adic\* formal
algebraic spaces over `S` and let `P` be a local property of morphisms of `WAdm^{adic*}`
(`TopologicalRing.PropertyIsLocalAdicStarUpToIso P`). The following are equivalent:

1. for every commutative diagram with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a
   morphism of `WAdm^{adic*}` with property `P`;
2. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ` corresponds to a
   morphism of `WAdm^{adic*}` with property `P`;
3. there are a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` with `Yᵢ` an affine formal algebraic space, `Yᵢ ⟶ Y` representable by
   algebraic spaces and étale, and `Xᵢ ⟶ Yᵢ` corresponding to a morphism of `WAdm^{adic*}` with
   property `P`.

There is no hypothesis on `P` beyond locality. Its invariance under isomorphism of source and
target, which the proof of Stacks 0ANG uses, is derived from axiom (1) of Situation 0CBA by
`propertyIsInvariantUnderSourceIso_of_propertyIsLocalAdicStarUpToIso` and
`propertyIsInvariantUnderTargetIsoOn_of_propertyIsLocalAdicStarUpToIso`. The equivalence is
then `AlgebraicGeometry.FormalSpace.hasProperty_tfae_isAdicStar`. -/
@[stacks 0ANH "the second half: the variant of Stacks 0ANG for morphisms between locally adic* \
formal algebraic spaces over S, at any local property of morphisms of WAdm^{adic*}"]
theorem hasProperty_tfae_of_propertyIsLocalAdicStarUpToIso
    (hP : TopologicalRing.PropertyIsLocalAdicStarUpToIso.{u} P)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y) :
    List.TFAE
      [ HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f,
        HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P f,
        HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P f ] :=
  hasProperty_tfae_isAdicStar B S hS P hP.toPropertyIsLocal
    (propertyIsInvariantUnderSourceIso_of_propertyIsLocalAdicStarUpToIso P hP)
    (propertyIsInvariantUnderTargetIsoOn_of_propertyIsLocalAdicStarUpToIso P hP) f hX hY

end AlgebraicGeometry.FormalSpace

end
