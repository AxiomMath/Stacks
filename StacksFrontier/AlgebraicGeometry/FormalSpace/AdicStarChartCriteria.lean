module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicStarBaseChangeSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproductTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineEtaleChartTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertySourceCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffineCharts
public import StacksFrontier.RingTheory.Ideal.Pi
public import StacksFrontier.RingTheory.Rig.RigSmoothLocality
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeLocality
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties

/-!
# The variant of Stacks 0ANG for locally adic\* formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. The second half of **Stacks 0ANH** asserts
that, for a local property `P` of morphisms of `WAdm^{adic*}` — the adic topological rings
possessing a finitely generated ideal of definition, `TopologicalRing.IsAdicStar` — one obtains
in exactly the same way as in Stacks 0ANG a variant of Stacks 0ANG for morphisms between locally
adic\* formal algebraic spaces over `S`: the three conditions of Stacks 0ANG, read at the class
`WAdm^{adic*}`, are equivalent.

## The class of rings

The first half of Stacks 0ANH, the notion of a local property of morphisms of `WAdm^{adic*}`,
is `TopologicalRing.PropertyIsLocalAdicStar`, which is `TopologicalRing.PropertyIsLocal` at the
class `TopologicalRing.IsAdicStar`. This file proves the four facts about that class which
the proof of Stacks 0ANG uses:

* `AlgebraicGeometry.FormalSpace.classIsWeaklyAdmissible_isAdicStar`: an adic\* ring is weakly
  admissible;
* `AlgebraicGeometry.FormalSpace.classHasCountableNhdsZero_isAdicStar`: an adic\* ring has a
  countable fundamental system of neighbourhoods of zero;
* `AlgebraicGeometry.FormalSpace.classIsStableUnderEtaleCompletion_isAdicStar`: **Stacks 0ANB
  (4)**, the completion of an étale algebra over an adic\* ring is adic\*;
* `AlgebraicGeometry.FormalSpace.classIsStableUnderFinitePi_isAdicStar`: a finite product of
  adic\* rings is adic\*, which is what makes axiom (3) of Situation 0CBA meaningful for
  `WAdm^{adic*}`.

## Main results

* `TopologicalRing.propertyIsLocalAdicStar_iff`: the first half of Stacks 0ANH in the source's
  words.
* `TopologicalRing.adicStarPropertyIsLocal_iff_propertyIsLocalAdicStar`: the two spellings of
  the class `WAdm^{adic*}` in `TopologicalRing.AdicStarPropertyIsLocal` and
  `TopologicalRing.PropertyIsLocalAdicStar` give the same notion of a local property.
* `AlgebraicGeometry.FormalSpace.hasProperty_tfae_isAdicStar`: the second half of Stacks 0ANH,
  the variant of Stacks 0ANG for morphisms between locally adic\* formal algebraic spaces.

## Invariance under isomorphism

Situation 0CBA, whose axioms Stacks 0ANH reads at `WAdm^{adic*}`, opens with "let `P` be a
property of morphisms of `WAdm^count`, invariant under isomorphism of source and target in this
category". That invariance is part of the source's hypothesis on `P`, not a consequence of the
three axioms in this library's formulation, where the completion of a complete ring is only
isomorphic to it. It is carried here as `hsrc` and `htgt`, through
`AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderSourceIso` and
`AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderTargetIsoOn` at the class
`TopologicalRing.IsAdicStar`.

## References

* [Stacks Project, Tag 0ANB](https://stacks.math.columbia.edu/tag/0ANB)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### The class `WAdm^{adic*}` -/

/-- The rings of `WAdm^{adic*}` are weakly admissible. -/
theorem classIsWeaklyAdmissible_isAdicStar :
    ClassIsWeaklyAdmissible.{u} TopologicalRing.IsAdicStar :=
  fun _ _ _ _ _ h ↦ Rig.weaklyAdmissible_of_isAdicRing h.1

/-- The rings of `WAdm^{adic*}` have a countable fundamental system of neighbourhoods of zero,
the powers of an ideal of definition. -/
theorem classHasCountableNhdsZero_isAdicStar :
    ClassHasCountableNhdsZero.{u} TopologicalRing.IsAdicStar :=
  fun _ _ _ _ _ h ↦ Rig.countablyGenerated_nhds_of_isAdicRing h.1

/-- **Stacks 0ANB (4).** The completion of an étale algebra over a ring of `WAdm^{adic*}` along
the weak ideals of definition of that ring is again in `WAdm^{adic*}`: it is complete and
separated, being weakly admissible, and its topology is defined by a finitely generated ideal,
by `TopologicalRing.completionOver_exists_fg_isAdic`, which is then an ideal of definition. -/
theorem classIsStableUnderEtaleCompletion_isAdicStar :
    ClassIsStableUnderEtaleCompletion.{u} TopologicalRing.IsAdicStar := by
  intro R R' _ _ _ _ _ ι hR hRw _
  obtain ⟨I, hIdef, hIfg⟩ := hR.2
  obtain ⟨J, hJfg, hJ⟩ := TopologicalRing.completionOver_exists_fg_isAdic ι hRw
    ⟨I, hIfg, Rig.idealOfDefinition_isAdic_of_isAdicRing hR.1 I hIdef⟩
  have hw := TopologicalRing.completionOver_isWeaklyAdmissible ι hRw
  exact ⟨⟨⟨J, Rig.isIdealOfDefinition_of_isAdic hJ, hJ⟩, hw.2.2, hw.2.1⟩,
    J, Rig.isIdealOfDefinition_of_isAdic hJ, hJfg⟩

/-- A finite product of rings of `WAdm^{adic*}` is in `WAdm^{adic*}`, for the product topology:
it is adic by `Rig.isAdic_pi`, and the product of finitely generated ideals of definition of
the factors is a finitely generated ideal of definition of the product. -/
theorem classIsStableUnderFinitePi_isAdicStar :
    ClassIsStableUnderFinitePi.{u} TopologicalRing.IsAdicStar := by
  intro K _ A _ _ _ _ h
  classical
  choose I hIdef hIfg using fun k ↦ (h k).2
  exact ⟨Rig.isAdic_pi A fun k ↦ (h k).1, Ideal.pi I,
    TopologicalRing.isIdealOfDefinition_pi_ideal A I hIdef, Ideal.fg_pi _ hIfg⟩

end AlgebraicGeometry.FormalSpace

namespace TopologicalRing

/-- **The first half of Stacks 0ANH, in the source's words.** A property `P` of morphisms of
`WAdm^{adic*}` is a local property, `TopologicalRing.PropertyIsLocalAdicStar P`, exactly when the
three axioms of Situation 0CBA hold for morphisms of `WAdm^{adic*}`:

1. for every diagram of Situation 0CBA with `A` and `B` in `WAdm^{adic*}`, `P(φ) ⟹ P(φ')`;
2. for every such diagram with `A → A'` faithfully flat, `P(φ') ⟹ P(φ)`;
3. if `P(B → Aᵢ)` for finitely many `Aᵢ` of `WAdm^{adic*}`, then `P(B → ∏ᵢ Aᵢ)`.

`TopologicalRing.PropertyIsLocal` asks in addition that the two completions `(A')^∧` and
`(B')^∧` of a diagram be in `WAdm^{adic*}`, and that the rings of axiom (3) be weakly admissible
with a countable fundamental system of neighbourhoods of zero. Neither is an extra condition:
the completions are in `WAdm^{adic*}` by Stacks 0ANB (4),
`AlgebraicGeometry.FormalSpace.classIsStableUnderEtaleCompletion_isAdicStar`, and every ring of
`WAdm^{adic*}` is weakly admissible and countably indexed. This equivalence records that
`TopologicalRing.PropertyIsLocalAdicStar` is the source's notion. -/
@[stacks 0ANH "the first half, the definition of a local property of morphisms of \
WAdm^{adic*}, with the three axioms of Situation 0CBA quantified over the diagrams and finite \
families of WAdm^{adic*} exactly as in the source"]
theorem propertyIsLocalAdicStar_iff
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) :
    PropertyIsLocalAdicStar.{u} P ↔
      (∀ {A B A' B' : Type u}
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
        [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
        [CommRing A'] [CommRing B'] (D : LocalizationDiagram A B A' B'),
        IsAdicStar A → IsAdicStar B → P D.map → P D.completedMap) ∧
      (∀ {A B A' B' : Type u}
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
        [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
        [CommRing A'] [CommRing B'] (D : LocalizationDiagram A B A' B'),
        IsAdicStar A → IsAdicStar B → D.toA'.FaithfullyFlat → P D.completedMap → P D.map) ∧
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
    refine ⟨fun D hA hB ↦ hP.localizationPreserves D hA hB
        (hcompl D.toA' hA D.weaklyAdmissibleA D.etaleA)
        (hcompl D.toB' hB D.weaklyAdmissibleB D.etaleB),
      fun D hA hB ↦ hP.faithfullyFlatDescent D hA hB
        (hcompl D.toA' hA D.weaklyAdmissibleA D.etaleA)
        (hcompl D.toB' hB D.weaklyAdmissibleB D.etaleB),
      fun A _ _ _ _ f hf hB hA ↦ hP.finiteProduct (Rig.weaklyAdmissible_of_isAdicRing hB.1)
        (Rig.countablyGenerated_nhds_of_isAdicRing hB.1) A
        (fun i ↦ Rig.weaklyAdmissible_of_isAdicRing (hA i).1)
        (fun i ↦ Rig.countablyGenerated_nhds_of_isAdicRing (hA i).1) f hf hB hA⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun D hA hB _ _ ↦ h1 D hA hB, fun D hA hB _ _ ↦ h2 D hA hB,
      fun _ _ _ _ A _ _ _ _ _ _ f hf hB hA hfP ↦ h3 A f hf hB hA hfP⟩

/-- On a weakly admissible topological ring, a topology defined by the powers of a finitely
generated ideal makes the ring an object of `WAdm^{adic*}`: the ideal is an ideal of
definition, and weak admissibility supplies completeness and separatedness. -/
theorem isAdicStar_of_isWeaklyAdmissible {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (hR : IsWeaklyAdmissible R)
    (h : ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I) : IsAdicStar R := by
  obtain ⟨I, hIfg, hI⟩ := h
  exact ⟨⟨⟨I, Rig.isIdealOfDefinition_of_isAdic hI, hI⟩, hR.2.2, hR.2.1⟩,
    I, Rig.isIdealOfDefinition_of_isAdic hI, hIfg⟩

/-- **The two readings of a local property of morphisms of `WAdm^{adic*}` agree.**
`TopologicalRing.AdicStarPropertyIsLocal` tests the locality axioms at the class
`∃ I : Ideal R, I.FG ∧ _root_.IsAdic I`, and `TopologicalRing.PropertyIsLocalAdicStar` at the
class `TopologicalRing.IsAdicStar`. The two classes differ only on rings which are not weakly
admissible, and every ring the axioms test is weakly admissible: the corners `A`, `B` of a
`TopologicalRing.LocalizationDiagram` by its fields, its two completions by
`TopologicalRing.completionOver_isWeaklyAdmissible`, and the rings of the finite-product axiom
by its hypotheses. On a weakly admissible ring the two classes coincide, by
`TopologicalRing.isAdicStar_of_isWeaklyAdmissible` in one direction and
`Rig.idealOfDefinition_isAdic_of_isAdicRing` in the other. -/
theorem adicStarPropertyIsLocal_iff_propertyIsLocalAdicStar
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) :
    AdicStarPropertyIsLocal.{u} P ↔ PropertyIsLocalAdicStar.{u} P := by
  refine ⟨propertyIsLocalAdicStar_of_adicStarPropertyIsLocal, fun hP ↦ ⟨?_, ?_, ?_⟩⟩
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hMap
    exact hP.localizationPreserves D (isAdicStar_of_isWeaklyAdmissible D.weaklyAdmissibleA hA)
      (isAdicStar_of_isWeaklyAdmissible D.weaklyAdmissibleB hB)
      (isAdicStar_of_isWeaklyAdmissible
        (completionOver_isWeaklyAdmissible D.toA' D.weaklyAdmissibleA) hA')
      (isAdicStar_of_isWeaklyAdmissible
        (completionOver_isWeaklyAdmissible D.toB' D.weaklyAdmissibleB) hB') hMap
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hFF hCompleted
    exact hP.faithfullyFlatDescent D (isAdicStar_of_isWeaklyAdmissible D.weaklyAdmissibleA hA)
      (isAdicStar_of_isWeaklyAdmissible D.weaklyAdmissibleB hB)
      (isAdicStar_of_isWeaklyAdmissible
        (completionOver_isWeaklyAdmissible D.toA' D.weaklyAdmissibleA) hA')
      (isAdicStar_of_isWeaklyAdmissible
        (completionOver_isWeaklyAdmissible D.toB' D.weaklyAdmissibleB) hB') hFF hCompleted
  · intro B _ _ _ _ hB hBcount ι _ A _ _ _ _ hAweak hAcount f hf hBstar hAstar hfP
    exact hP.finiteProduct hB hBcount A hAweak hAcount f hf
      (isAdicStar_of_isWeaklyAdmissible hB hBstar)
      (fun i ↦ isAdicStar_of_isWeaklyAdmissible (hAweak i) (hAstar i)) hfP

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

/-! ### The variant of Stacks 0ANG -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- The three conditions of the variant of **Stacks 0ANG** for morphisms of locally adic\*
formal algebraic spaces and a local property of morphisms of `WAdm^{adic*}`, at one statement
about formal algebraic spaces which does not mention `P`: the étale case of Stacks 0AJH, as
`hEt`.

The implication (1) ⟹ (2) takes the fibre products of condition (2) from `hEt`; (2) ⟹ (3)
holds for any class and property; and (3) ⟹ (1) is
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal`
at the class `WAdm^{adic*}`, whose covering refinement comes from `hEt` and whose charts are
adic\* by the implication (2) ⟹ (1) of Stacks 0AKX for the adic\* property,
`hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem`. -/
theorem hasProperty_tfae_isAdicStar_of_inputs
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    (hP : TopologicalRing.PropertyIsLocalAdicStar.{u} P)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} TopologicalRing.IsAdicStar P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y) :
    List.TFAE
      [ HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f,
        HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P f,
        HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P f ] := by
  have hadic : ∀ {Z : FppfSheaf B S hS}, IsLocallyAdicStar B S hS Z →
      HasAffineEtaleChartProperty B S hS Z (IsAdicStar B S hS) := fun hZ ↦
    (hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem B S hS _ hZ.1 _
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).2 hZ.2
  tfae_have 1 → 2 := fun h ↦
    hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS _ P f hY.1
      (isFormalAlgebraicSpace_pullback_chart_of_etale B S hS hEt hX.1 hY.1) h
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS _ P f h
  tfae_have 3 → 1 := fun h ↦
    hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal B S hS _ P
      classIsWeaklyAdmissible_isAdicStar classHasCountableNhdsZero_isAdicStar
      classIsStableUnderEtaleCompletion_isAdicStar classIsStableUnderFinitePi_isAdicStar
      hsrc htgt hP f (hasEtaleRefinementOfSourceCover_of_etale B S hS hEt f)
      (hasPropertyAfterSourceCoverOfClass_of_afterSourceCover B S hS _ P f
        (fun U a hU ha ↦ isChartOfClass_of_isAdicStar B S hS (hadic hX U a hU ha))
        (fun V b hV hb ↦ isChartOfClass_of_isAdicStar B S hS (hadic hY V b hV hb)) h)
  tfae_finish

/-- **The second half of Stacks 0ANH: the variant of Stacks 0ANG for morphisms between locally
adic\* formal algebraic spaces.** Let `f : X ⟶ Y` be a morphism of locally adic\* formal
algebraic spaces over `S` and let `P` be a local property of morphisms of `WAdm^{adic*}`
(`TopologicalRing.PropertyIsLocalAdicStar P`), invariant under isomorphism of source and target
as Situation 0CBA stipulates. The following are equivalent:

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

This is `AlgebraicGeometry.FormalSpace.hasProperty_tfae_isAdicStar_of_inputs` with the étale
case of Stacks 0AJH supplied by
`AlgebraicGeometry.FormalSpace.representableEtaleOverAffineIsFormal`. -/
@[stacks 0ANH "the second half: the variant of Stacks 0ANG for morphisms between locally adic* \
formal algebraic spaces over S, at a local property of morphisms of WAdm^{adic*} invariant under \
isomorphism of source and target (the standing hypothesis of Situation 0CBA)"]
theorem hasProperty_tfae_isAdicStar
    (hP : TopologicalRing.PropertyIsLocalAdicStar.{u} P)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} TopologicalRing.IsAdicStar P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y) :
    List.TFAE
      [ HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f,
        HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P f,
        HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P f ] :=
  hasProperty_tfae_isAdicStar_of_inputs B S hS P (representableEtaleOverAffineIsFormal B S hS)
    hP hsrc htgt f hX hY

end AlgebraicGeometry.FormalSpace

end
