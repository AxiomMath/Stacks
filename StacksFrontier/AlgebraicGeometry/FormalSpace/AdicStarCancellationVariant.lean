module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicStarChartCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.IsomorphismInvariantSourceTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCancellation
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicStarCancellation

/-!
# Cancellation of a local property of morphisms of locally adic\* formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. **Remark 87.21.17 (Stacks 0GBN)** defines
what it means for a local property `P` of morphisms of `WAdm^{adic*}` (Remark 0ANH) to have the
*cancellation property* — for arrows `B → A` and `C → B` of `WAdm^{adic*}`,
`P(C → A) ∧ P(C → B) ⟹ P(B → A)`, which is `TopologicalRing.HasAdicStarCancellationProperty` —
and asserts that in exactly the same way one obtains the variant for morphisms between locally
adic\* formal algebraic spaces over `S`. The statement so obtained is the one of Lemma 0GBM
(the cancellation lemma, whose proof is the covering argument of Lemma 0GBI): if
`f : X ⟶ Y` and `g : Y ⟶ Z` are morphisms of locally adic\* formal algebraic spaces such that
`g ∘ f` and `g` satisfy the equivalent conditions of Stacks 0ANG (in its adic\* variant, the
second half of Stacks 0ANH), then so does `f`. This file states and proves that variant.

The remark as printed says "a variant of Lemma 0GBI"; 0GBI is the composition lemma, whose
adic\* variant is Remark 0GBJ, and the lemma about the cancellation property is 0GBM. The slip
is an erratum to the Stacks Project.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_comp_of_isLocallyAdicStar`
  — **Stacks 0GBN**, the second half.

## Implementation notes

The proof is the source's. The covering of Stacks 0GBM,
`AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_of_comp_of_atlas`, is built for an
arbitrary class of rings and atlas property; here it is instantiated at the class
`WAdm^{adic*}` (`TopologicalRing.IsAdicStar`) and at adic\* atlases. Its charts stay adic\*
along representable étale maps by clause (4) of Stacks 0AKQ and are presented by rings of
`WAdm^{adic*}` (`AlgebraicGeometry.FormalSpace.exists_spfPresentation_of_isAdicStar`), so the
cancellation property applies on each `Uᵢ ⟶ Vᵢ ⟶ Wᵢ` through Stacks 0AN0. That gives condition
(3) of Stacks 0ANG for `f`; conditions (1) and (2) follow from the variant of Stacks 0ANG for
locally adic\* formal algebraic spaces,
`AlgebraicGeometry.FormalSpace.hasProperty_tfae_isAdicStar`.

Situation 0CBA, whose axioms Remark 0ANH reads at `WAdm^{adic*}`, opens with "let `P` be a
property of morphisms of `WAdm^{count}`, invariant under isomorphism of source and target in
this category"; a local property is such a property satisfying the three axioms. Read at
`WAdm^{adic*}`, that whole notion is
`TopologicalRing.PropertyIsLocal' P TopologicalRing.IsAdicStar`:
its field `isomorphismInvariant` is the opening clause, and its other three fields are the
axioms, so that forgetting the first field gives `TopologicalRing.PropertyIsLocalAdicStar P`.
The one-sided invariances which `AlgebraicGeometry.FormalSpace.hasProperty_tfae_isAdicStar`
consumes are derived from the opening clause in
`StacksFrontier/AlgebraicGeometry/FormalSpace/IsomorphismInvariantSourceTarget.lean`.

## References

* [Stacks Project, Tag 0GBN](https://stacks.math.columbia.edu/tag/0GBN)
* [Stacks Project, Tag 0GBM](https://stacks.math.columbia.edu/tag/0GBM)
* [Stacks Project, Tag 0GBI](https://stacks.math.columbia.edu/tag/0GBI)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AKQ](https://stacks.math.columbia.edu/tag/0AKQ)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- **Stacks 0GBN, second half: the cancellation variant for locally adic\* formal algebraic
spaces.** Let `P` be a local property of morphisms of `WAdm^{adic*}` in the sense of Remark
0ANH, `hP`: a property of arrows of `WAdm^{adic*}` invariant under isomorphism of source and
target in that category and satisfying the three axioms of Situation 0CBA there. Suppose `P`
has the cancellation property of the first half of the remark, `hcancel`: for `B → A` and
`C → B` in `WAdm^{adic*}`, `P(C → A) ∧ P(C → B) ⟹ P(B → A)`. Let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of locally adic\* formal algebraic
spaces over `S`. If `g ∘ f` and `g` satisfy the equivalent conditions of
Stacks 0ANG for `P` at `WAdm^{adic*}` — here condition (1), which is equivalent to the other two
by the second half of Stacks 0ANH — then so does `f`; the conclusion lists all three.

The proof is that of Stacks 0GBM: on the covering `Uᵢ ⟶ Vᵢ ⟶ Wᵢ` of
`AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_of_comp_of_atlas`, built on adic\*
atlases of `X`, `Y`, `Z`, the maps `Vᵢ ⟶ Wᵢ` and `Uᵢ ⟶ Wᵢ` correspond to arrows `C → B` and
`C → A` of `WAdm^{adic*}` with `P`, so `Uᵢ ⟶ Vᵢ`, corresponding to `B → A`, has `P`. -/
@[stacks 0GBN "the second half: the variant of Lemma 0GBM (the remark's Lemma 0GBI is a slip \
for 0GBM, an erratum to the Stacks Project) for morphisms \
f : X -> Y, g : Y -> Z between locally adic* formal algebraic spaces over S, for a local \
property P of WAdm^{adic*} (Remark 0ANH: invariant under isomorphism of source and target and \
satisfying the three axioms of Situation 0CBA) having the cancellation property \
TopologicalRing.HasAdicStarCancellationProperty: if g o f and g satisfy the equivalent \
conditions of Stacks 0ANG then so does f"]
theorem hasPropertyOnEveryAffineEtaleDiagram_of_comp_of_isLocallyAdicStar
    (hP : TopologicalRing.PropertyIsLocal'.{u} P TopologicalRing.IsAdicStar)
    (hcancel : TopologicalRing.HasAdicStarCancellationProperty.{u} P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (hZ : IsLocallyAdicStar B S hS Z)
    (hfg : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P (f ≫ g))
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P f ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P f := by
  have hfgI : ∀ {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], TopologicalRing.IsAdicStar R →
        ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I :=
    fun h ↦ by
      obtain ⟨I, hIdef, hIfg⟩ := h.2
      exact ⟨I, hIfg, Rig.idealOfDefinition_isAdic_of_isAdicRing h.1 I hIdef⟩
  have h3 : HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P f :=
    hasPropertyAfterSourceCover_of_comp_of_atlas B S hS _ P classIsWeaklyAdmissible_isAdicStar
      (fun hA hM hR φ ψ hφ hψ hPψ hPφψ ↦ hcancel φ ψ
        (classIsWeaklyAdmissible_isAdicStar _ hR) (hfgI hR)
        (classIsWeaklyAdmissible_isAdicStar _ hM) (hfgI hM)
        (classIsWeaklyAdmissible_isAdicStar _ hA) (hfgI hA) hφ hψ ⟨hPφψ, hPψ⟩)
      (IsAdicStar B S hS)
      (fun e hV' hV he hVQ ↦ isAdicStar_of_isRepresentable' B S hS e hV' hV he.1 hVQ)
      (fun V _ hV ↦ exists_spfPresentation_of_isAdicStar B S hS V hV)
      f g hX.2 hY.1 hY.2 hZ.1 hZ.2 hfg hg
  have htfae := hasProperty_tfae_isAdicStar B S hS P hP.toPropertyIsLocal
    (propertyIsInvariantUnderSourceIso_of_isomorphismInvariant hP.isomorphismInvariant)
    (propertyIsInvariantUnderTargetIsoOn_of_isomorphismInvariant hP.isomorphismInvariant) f hX hY
  have h1 := (htfae.out 1 3).2 h3
  exact ⟨h1, (htfae.out 1 2).1 h1, h3⟩

end AlgebraicGeometry.FormalSpace

end
