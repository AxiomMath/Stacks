module

public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.PolynomialSurjection
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.SegreClosedImmersion

/-!
# A relative homogeneous spectrum is H-projective over an affine open with degree-one generators

Let `A` be a quasi-coherent graded `𝒪_S`-algebra, `P` its relative homogeneous spectrum and
`V ⊆ S` an affine open. The chart of `P` over `V` is `Proj Γ(V, A)`, the absolute homogeneous
spectrum of the graded ring of sections, and it is the inverse image of `V`. If that graded ring
is generated as a `Γ(S, V)`-algebra by `n + 1` of its degree-one elements, then

* `R[T₀, …, Tₙ] ⟶ Γ(V, A)`, `Tⱼ ↦ xⱼ`, is a graded homomorphism surjective in every degree, so
  by [Stacks, Tag 01N0] the induced morphism `Proj Γ(V, A) ⟶ Proj R[T₀, …, Tₙ]` is defined
  everywhere and is a closed immersion;
* `Proj R[T₀, …, Tₙ] ≅ ℙⁿ_{Spec R}` over `Spec R`, and `V ≅ Spec R`, so the chart is a closed
  subscheme of `ℙⁿ_V` **over `V`**, the degree-zero half of the comparison being the structure
  map of `A`;
* consequently a closed immersion `i : Y ⟶ P` over `S` base changes, along the chart, to a
  closed immersion of `Y ×_S V` into the chart, and `Y ×_S V ⟶ V` is H-projective.

This is the local half of the implication (1) ⟹ (2) of [Stacks, Tag 01WB], with the generators
left as a hypothesis; `StacksFrontier.AlgebraicGeometry.LocallyProjectiveHProjective.Sym` discharges
the hypothesis for the symmetric algebra of a finite-type quasi-coherent module.

## Main definitions

* `Stacks.LocallyProjectiveHProjective.chartToProjPoly`: the morphism
  `Proj Γ(V, A) ⟶ Proj Γ(S, V)[T₀, …, Tₙ]` induced by the generators.
* `Stacks.LocallyProjectiveHProjective.chartToProjectiveSpace`: that morphism followed by the
  two identifications, so a morphism `Proj Γ(V, A) ⟶ ℙⁿ_V`.

## Main results

* `Stacks.LocallyProjectiveHProjective.isClosedImmersion_chartToProjPoly` and
  `isClosedImmersion_chartToProjectiveSpace`: both morphisms are closed immersions.
* `Stacks.LocallyProjectiveHProjective.chartToProjectiveSpace_over`: the second is a morphism
  over `V`.
* `Stacks.LocallyProjectiveHProjective.isProjectiveMorphism_pullback_snd`: **the conclusion** —
  the base change over `V` of a closed immersion into `P` over `S` is H-projective.

## Implementation notes

**The algebra structure on the section ring is a hypothesis, not the canonical one.** Every
statement below takes `[Algebra Γ(S, V) (A.sectionRing V)]` together with
`hC : algebraMap … = A.strHom V`, rather than fixing the instance to
`(A.strHom V).toAlgebra`: `Stacks.AlgebraicGeometry.RelativeProjChain.polyGradedHom` is stated
for an arbitrary algebra structure landing in degree zero, and a `letI` cannot appear in the
statement of the generation hypothesis `Algebra.adjoin Γ(S, V) (Set.range x) = ⊤`. The
degree-zero comparison is where `hC` is spent, and nothing else uses it.

**`ℙⁿ_V` is reached in two steps and both are available.**
`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare` identifies the polynomial model of
projective space over a ring with the base-change model, over that ring, and
`Stacks.FiniteMorphismProjective.baseTransport` moves the base-change model along the
isomorphism `V ≅ Spec Γ(S, V)`. Neither needs Tag 01O3, the base change of a relative
homogeneous spectrum, which `Stacks.RelativeProj.Situation.relativeProjBaseChangeIso` carries
only for a graded algebra identified with a pullback: nothing below base changes `P`
itself, the chart being a *field* of
`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData` already known to be the inverse image
of its affine open.

**The base change of the closed immersion is obtained by pasting, not by a comparison of
pullbacks.** `Y ×_S V` is `Y ×_P (P ×_S V)` because `f = i ≫ P.toBase`, which is
`CategoryTheory.IsPullback.of_right` applied to the chart square and to the defining square of
`Y ×_S V`; closed immersions are stable under base change, so the lift is one.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01WB](https://stacks.math.columbia.edu/tag/01WB)

## Not done here

**No tag is claimed.** Every statement carries the generation hypothesis, which is not a
hypothesis of any Stacks statement; Tag 01N0 is already carried by
`Stacks.AlgebraicGeometry.RelativeProjChain.isClosedImmersion_projToProjectiveSpaceGradeZero`
and nothing here is a second assertion of it.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjChain

universe u

namespace Stacks.LocallyProjectiveHProjective

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The chart as a closed subscheme of projective space -/

section Chart

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) {V : S.Opens} {n : ℕ}
  [Algebra ↥Γ(S, V) (A.sectionRing V)]

/-- The degree-zero part of the evaluation homomorphism is the structure map. -/
theorem zeroHom_polyGradedHom_comp
    (halg : ∀ r : ↥Γ(S, V), algebraMap ↥Γ(S, V) (A.sectionRing V) r ∈ A.grading V 0)
    (x : Fin (n + 1) → A.sectionRing V) (hx : ∀ j, x j ∈ A.grading V 1)
    (hC : ∀ r : ↥Γ(S, V), algebraMap ↥Γ(S, V) (A.sectionRing V) r = A.strHom V r) :
    (zeroHom (polyGrading ↥Γ(S, V) n) (A.grading V)
          (polyGradedHom (A.grading V) halg x hx)).comp
        ((GradedRing.projZeroRingHom' (polyGrading ↥Γ(S, V) n)).comp
          (algebraMap ↥Γ(S, V) (MvPolynomial (Fin (n + 1)) ↥Γ(S, V)))) =
      (GradedRing.projZeroRingHom' (A.grading V)).comp (A.strHom V) := by
  refine RingHom.ext fun r => Subtype.ext ?_
  have hCr : (algebraMap ↥Γ(S, V) (MvPolynomial (Fin (n + 1)) ↥Γ(S, V))) r =
      MvPolynomial.C r := by simp [MvPolynomial.algebraMap_eq]
  have hmem : (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) ↥Γ(S, V)) ∈
      polyGrading ↥Γ(S, V) n 0 :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C _ _)
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, coe_zeroHom_apply, hCr,
    projZeroRingHom'_coe_of_mem _ hmem,
    projZeroRingHom'_coe_of_mem _ (A.strHom_mem V r)]
  show MvPolynomial.aeval x (MvPolynomial.C r) = _
  rw [MvPolynomial.aeval_C]
  exact hC r

variable (hV : IsAffineOpen V)
  (halg : ∀ r : ↥Γ(S, V), algebraMap ↥Γ(S, V) (A.sectionRing V) r ∈ A.grading V 0)
  (x : Fin (n + 1) → A.sectionRing V) (hx : ∀ j, x j ∈ A.grading V 1)
  (hgen : Algebra.adjoin ↥Γ(S, V) (Set.range x) = ⊤)

include hgen in
/-- The evaluation homomorphism is everywhere defined. -/
theorem mapDomain_polyGradedHom_eq_top :
    mapDomain (polyGrading ↥Γ(S, V) n) (A.grading V)
      (polyGradedHom (A.grading V) halg x hx) = ⊤ :=
  mapDomain_eq_top_of_eventually_surjective _ _ _
    (eventually_surjective_polyGradedHom (A.grading V) halg x hx hgen)

include hgen in
/-- The morphism of projective spectra induced by the evaluation homomorphism, on the whole of
the chart. -/
def chartToProjPoly :
    AlgebraicGeometry.Proj (A.grading V) ⟶
      AlgebraicGeometry.Proj (polyGrading ↥Γ(S, V) n) :=
  mapHomOfTop (polyGrading ↥Γ(S, V) n) (A.grading V)
    (polyGradedHom (A.grading V) halg x hx)
    (mapDomain_polyGradedHom_eq_top A halg x hx hgen)

include hgen in
instance isClosedImmersion_chartToProjPoly :
    IsClosedImmersion (chartToProjPoly A halg x hx hgen) :=
  Stacks.AlgebraicGeometry.SegreClosedImmersion.isClosedImmersion_mapHomOfTop
    (polyGrading ↥Γ(S, V) n) (A.grading V) (polyGradedHom (A.grading V) halg x hx)
    (mapDomain_polyGradedHom_eq_top A halg x hx hgen)
    (eventually_surjective_polyGradedHom (A.grading V) halg x hx hgen)

include hgen in
/-- **The induced morphism is a morphism over the spectrum of the functions on the affine
open**: it carries the structure morphism of the polynomial model to the structure morphism of
the chart. -/
@[reassoc]
theorem chartToProjPoly_projToSpecCoeff (hV : IsAffineOpen V)
    (hC : ∀ r : ↥Γ(S, V), algebraMap ↥Γ(S, V) (A.sectionRing V) r = A.strHom V r) :
    chartToProjPoly A halg x hx hgen ≫ projToSpecCoeff ↥Γ(S, V) n =
      Proj.toSpecZero (A.grading V) ≫
        Spec.map (A.toGradedAlgebra.strZero (⟨V, hV⟩ : S.AffineZariskiSite)) := by
  rw [projToSpecCoeff, chartToProjPoly, ← Category.assoc, mapHomOfTop_toSpecZero,
    Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    zeroHom_polyGradedHom_comp A halg x hx hC]
  rfl

include hV hgen in
/-- **The chart over an affine open is a closed subscheme of `ℙⁿ` over that open**, given
`n + 1` degree-one generators of its graded ring of sections. -/
def chartToProjectiveSpace :
    AlgebraicGeometry.Proj (A.grading V) ⟶ projectiveSpaceOver n V.toScheme :=
  chartToProjPoly A halg x hx hgen ≫ projCompare ↥Γ(S, V) n ≫
    Stacks.FiniteMorphismProjective.baseTransport n hV.isoSpec.symm

include hgen in
instance isClosedImmersion_chartToProjectiveSpace (hV : IsAffineOpen V) :
    IsClosedImmersion (chartToProjectiveSpace A hV halg x hx hgen) := by
  have h := isClosedImmersion_chartToProjPoly A halg x hx hgen
  rw [chartToProjectiveSpace]
  infer_instance

include hgen in
/-- **The closed immersion of the chart into `ℙⁿ` is a morphism over the affine open.** -/
theorem chartToProjectiveSpace_over (hV : IsAffineOpen V)
    (hC : ∀ r : ↥Γ(S, V), algebraMap ↥Γ(S, V) (A.sectionRing V) r = A.strHom V r) :
    chartToProjectiveSpace A hV halg x hx hgen ≫
        (projectiveSpaceOver n V.toScheme ↘ V.toScheme) =
      projInclusionToOpen A V hV := by
  rw [Stacks.HProjective.over_projectiveSpaceOver, chartToProjectiveSpace]
  simp only [Category.assoc, Stacks.FiniteMorphismProjective.baseTransport_fst, Iso.symm_hom]
  rw [reassoc_of% projCompare_fst,
    chartToProjPoly_projToSpecCoeff_assoc A halg x hx hgen hV hC]
  rfl

/-! ### The generation hypothesis from generation in degree one -/

section Generation

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} {V : S.Opens} {n : ℕ}

/-- **Generation in degree one plus a finite degree-one generating family gives the hypothesis of
`Stacks.LocallyProjectiveHProjective.isProjectiveMorphism_pullback_snd`.** If the ring of
sections is generated by its degree-one part over its degree-zero part, if the degree-zero part
is the image of the structure map, and if finitely many degree-one elements generate the
degree-one part as a module over the functions on the open, then those elements generate the
whole ring as an algebra over the functions on the open. -/
theorem adjoin_eq_top_of_grading_one [Algebra ↥Γ(S, V) (A.sectionRing V)]
    (hgen0 : Algebra.adjoin ↥(A.grading V 0) (A.grading V 1 : Set (A.sectionRing V)) = ⊤)
    (hzero : ∀ z ∈ A.grading V 0, ∃ r : ↥Γ(S, V), algebraMap ↥Γ(S, V) (A.sectionRing V) r = z)
    (x : Fin (n + 1) → A.sectionRing V)
    (hone : ∀ z ∈ A.grading V 1, z ∈ Algebra.adjoin ↥Γ(S, V) (Set.range x)) :
    Algebra.adjoin ↥Γ(S, V) (Set.range x) = ⊤ := by
  set B := Algebra.adjoin ↥Γ(S, V) (Set.range x) with hB
  have h0 : ∀ z ∈ A.grading V 0, z ∈ B := by
    intro z hz
    obtain ⟨r, hr⟩ := hzero z hz
    exact hr ▸ B.algebraMap_mem r
  let B' : Subalgebra ↥(A.grading V 0) (A.sectionRing V) :=
    { B.toSubsemiring with algebraMap_mem' := fun r => h0 r.1 r.2 }
  have hle : Algebra.adjoin ↥(A.grading V 0) (A.grading V 1 : Set (A.sectionRing V)) ≤ B' :=
    Algebra.adjoin_le fun z hz => hone z hz
  rw [hgen0] at hle
  refine top_unique fun z _ => ?_
  exact hle (Algebra.mem_top (R := ↥(A.grading V 0)) (x := z))

end Generation

variable {Y : Scheme.{u}} {f : Y ⟶ S}

include halg hx hgen in
/-- **The base change of a closed immersion into a relative homogeneous spectrum over an affine
open of the base is H-projective**, given `n + 1` degree-one generators of the graded ring of
sections over that open.

The chart over the affine open is the inverse image of that open, so the base change of the
closed immersion along the chart is a closed immersion of `Y ×_S V` into the chart; the chart is
a closed subscheme of `ℙⁿ_V` over `V`; and the composite is a closed immersion over `V`. -/
theorem isProjectiveMorphism_pullback_snd (P : RelativeProjData A) (i : Y ⟶ P.scheme)
    (hi : IsClosedImmersion i) (hif : i ≫ P.toBase = f) (hV : IsAffineOpen V)
    (hC : ∀ r : ↥Γ(S, V), algebraMap ↥Γ(S, V) (A.sectionRing V) r = A.strHom V r) :
    IsProjectiveMorphism (pullback.snd f V.ι) := by
  have hch := P.chart_isPullback V hV
  have hw : (pullback.fst f V.ι ≫ i) ≫ P.toBase = pullback.snd f V.ι ≫ V.ι := by
    rw [Category.assoc, hif]
    exact pullback.condition
  obtain ⟨l, h1, h2⟩ : ∃ l, l ≫ P.chart V hV = pullback.fst f V.ι ≫ i ∧
      l ≫ projInclusionToOpen A V hV = pullback.snd f V.ι :=
    ⟨hch.lift _ _ hw, hch.lift_fst _ _ _, hch.lift_snd _ _ _⟩
  have hs : IsPullback (l ≫ projInclusionToOpen A V hV) (pullback.fst f V.ι) V.ι
      (i ≫ P.toBase) := by
    rw [h2, hif]
    exact (IsPullback.of_hasPullback f V.ι).flip
  have hci : IsClosedImmersion l :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (IsPullback.of_right hs h1 hch.flip).flip hi
  have hcc := isClosedImmersion_chartToProjectiveSpace A halg x hx hgen hV
  refine ⟨n, l ≫ chartToProjectiveSpace A hV halg x hx hgen, inferInstance, ?_⟩
  rw [Category.assoc, chartToProjectiveSpace_over A halg x hx hgen hV hC, h2]

end Chart

/-! ### The conclusion, with the canonical algebra structure -/

section Bundled

variable {S : Scheme.{u}}

/-- **A closed immersion into a relative homogeneous spectrum over the base is H-projective over
an affine open of the base whose graded ring of sections is generated in degree one by finitely
many elements.**

This is `Stacks.LocallyProjectiveHProjective.isProjectiveMorphism_pullback_snd` with the algebra
structure on the ring of sections fixed to the structure map of `A` and with the generation
hypothesis replaced by the three facts it is assembled from: generation of the ring of sections
by its degree-one part over its degree-zero part, surjectivity of the structure map onto the
degree-zero part, and a finite family of degree-one elements generating the degree-one part as a
module over the functions on the open. -/
theorem isProjectiveMorphism_pullback_snd_of_degreeOne (A : SheafGradedAlgebra S)
    (P : RelativeProjData A) {Y : Scheme.{u}} {f : Y ⟶ S} (i : Y ⟶ P.scheme)
    (hi : IsClosedImmersion i) (hif : i ≫ P.toBase = f) {V : S.Opens} (hV : IsAffineOpen V)
    (hgen0 : Algebra.adjoin ↥(A.grading V 0) (A.grading V 1 : Set (A.sectionRing V)) = ⊤)
    (hzero : ∀ z ∈ A.grading V 0, ∃ r : ↥Γ(S, V), A.strHom V r = z)
    {n : ℕ} (y : Fin (n + 1) → A.sectionRing V) (hy : ∀ j, y j ∈ A.grading V 1)
    (hspan : ∀ z ∈ A.grading V 1,
      ∃ c : Fin (n + 1) → ↥Γ(S, V), z = ∑ j, A.strHom V (c j) * y j) :
    IsProjectiveMorphism (pullback.snd f V.ι) := by
  let : Algebra ↥Γ(S, V) (A.sectionRing V) := (A.strHom V).toAlgebra
  have hC : ∀ r : ↥Γ(S, V), algebraMap ↥Γ(S, V) (A.sectionRing V) r = A.strHom V r := fun r => by
    rw [RingHom.algebraMap_toAlgebra]
  have halg : ∀ r : ↥Γ(S, V), algebraMap ↥Γ(S, V) (A.sectionRing V) r ∈ A.grading V 0 := fun r =>
    (hC r) ▸ A.strHom_mem V r
  have hone : ∀ z ∈ A.grading V 1, z ∈ Algebra.adjoin ↥Γ(S, V) (Set.range y) := by
    intro z hz
    obtain ⟨c, rfl⟩ := hspan z hz
    refine sum_mem fun j _ => ?_
    exact mul_mem ((hC (c j)) ▸ Subalgebra.algebraMap_mem _ (c j))
      (Algebra.subset_adjoin ⟨j, rfl⟩)
  have hgen : Algebra.adjoin ↥Γ(S, V) (Set.range y) = ⊤ :=
    adjoin_eq_top_of_grading_one hgen0
      (fun z hz => ((hzero z hz).imp fun r hr => (hC r).trans hr)) y hone
  exact isProjectiveMorphism_pullback_snd A halg y hy hgen P i hi hif hV hC

end Bundled

end Stacks.LocallyProjectiveHProjective

end
