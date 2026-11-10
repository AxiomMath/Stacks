module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Graph
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative projective line is integral

Let `S` be an integral scheme. This file proves that the relative projective line `ℙ¹_S` of
`Stacks.Chow.relativeProjectiveLine` is again integral, together with the two statements it is
assembled from: that the affine line `𝔸¹_S` of
`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOver` is integral, and that the two
affine charts of `ℙ¹_S` cover it and overlap.

The affine line of this development is `S ×_{Spec ℤ} Spec ℤ[T]`, where Mathlib's affine space
`AlgebraicGeometry.AffineSpace` is `S ×_{Spec ℤ} Spec ℤ[n]` for an index type `n`. For a
one-element `n` the two bases are isomorphic, so the two schemes are, and Mathlib's instance for
the affine space of an integral base transports: that is
`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOverIsoAffineSpace` and
`Stacks.Chow.isIntegral_affineLineOver`. The isomorphism is over `S` and matches the two
projections, so the whole affine-space API — the identification of `𝔸¹_{Spec R}` with `Spec R[T]`
among it — becomes available for
`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOver`.

For `ℙ¹_S` itself, reducedness is local and so follows from the cover by the two charts
(`Stacks.Chow.chartCover`). Irreducibility does not: two disjoint irreducible opens cover a
reducible space. What is needed is that the two charts meet, and they do because the point
`T = 1` of `ℙ¹_ℤ` lies on both of them. That point is `Stacks.Chow.integralOneSection`,
constructed from evaluation at `1` of Laurent polynomials, which factors the inclusion of the
punctured line; and the inclusion of the punctured line into the first chart equals its
inclusion into the second up to inversion of the coordinate, by
`AlgebraicGeometry.isPullback_projectiveLineCharts`. Base-changing the point to `S` gives the
section `Stacks.Chow.lineOneSection` of `ℙ¹_S ⟶ S` whose image lies in both charts, so the
overlap is nonempty as soon as `S` is. A dense irreducible open then forces the whole space to
be irreducible.

## Main definitions

* `Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOverIsoAffineSpace` — `𝔸¹_S` is
  Mathlib's affine space on a one-element index type over `S`.
* `Stacks.Chow.integralOneSection` — the point `T = 1` of `ℙ¹_ℤ`, which lies on both charts.
* `Stacks.Chow.lineOneSection` — the corresponding section of `ℙ¹_S ⟶ S`.
* `Stacks.Chow.chartCover` — the two affine charts as an open cover of `ℙ¹_S`.

## Main results

* `Stacks.Chow.isIntegral_affineLineOver` — `𝔸¹_S` is integral when `S` is.
* `Stacks.Chow.range_affineYChart` — the image of the second affine chart is the preimage of the
  second chart of `ℙ¹_ℤ`, the companion of `Stacks.Chow.range_affineChart`.
* `Stacks.Chow.range_affineChart_union_range_affineYChart` — the two affine charts cover `ℙ¹_S`.
* `Stacks.Chow.range_affineChart_eq_compl_support_lineInfinityDivisor` — the first affine chart
  is the complement of `D_∞`.
* `Stacks.Chow.nonempty_inter_range_affineYChart_range_affineChart` — the two affine charts of
  `ℙ¹_S` meet when `S` is nonempty.
* `Stacks.Chow.isIntegral_relativeProjectiveLine` — **`ℙ¹_S` is integral when `S` is.**
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_relativeProjectiveLine'` — the
  reduction of the degree-of-a-principal-divisor statement for a proper curve to the projective
  line, with the integrality of `ℙ¹_S` no longer a hypothesis.

## Implementation notes

### What this leaves open, and why no tag is placed

`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_relativeProjectiveLine` of
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Graph` carries four hypotheses
that Tag 02RU does not state: integrality of `ℙ¹_S`, the value `1` of its delta-dimension, the
statement itself for `ℙ¹_S`, and dominance of the second projection out of the graph closure.
This file discharges the first of the four; the remaining three are untouched, so the primed
form here is still a reduction and not the tag, and no declaration in this file bears a Stacks
attribute. See the implementation notes of that file for what each of the other three needs.

### The index type of the affine space

`AlgebraicGeometry.AffineSpace` takes its index type in `Type u`, the same universe as the
schemes, so the one-element type used here is `PUnit.{u + 1}`. The base change used to define
the affine line of this development is along `CategoryTheory.Limits.terminal.from`, exactly as
in Mathlib, so the isomorphism needs nothing beyond the isomorphism of the two polynomial rings
and the uniqueness of morphisms to a terminal object.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The affine line is Mathlib's affine space on one variable -/

/-- The spectra of the one-variable and of the one-element-indexed multivariate polynomial ring
over the integers are isomorphic. -/
def specPolynomialIsoSpecMvPolynomial :
    Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ))) ≅
      Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))) :=
  Scheme.Spec.mapIso
    ((MvPolynomial.uniqueAlgEquiv (ULift.{u} ℤ) PUnit.{u + 1}).toRingEquiv.toCommRingCatIso).op

/-- The comparison morphism from the affine line to the affine space on one variable. -/
def toAffineSpace (S : Scheme.{u}) : affineLineOver S ⟶
    pullback (terminal.from S)
      (terminal.from (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))))) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ specPolynomialIsoSpecMvPolynomial.hom) (terminal.hom_ext _ _)

/-- The comparison morphism from the affine space on one variable to the affine line. -/
def fromAffineSpace (S : Scheme.{u}) :
    pullback (terminal.from S)
        (terminal.from (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))))) ⟶
      affineLineOver S :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ specPolynomialIsoSpecMvPolynomial.inv) (terminal.hom_ext _ _)

/-- The comparison morphism to the affine space commutes with the first projections. -/
theorem toAffineSpace_fst (S : Scheme.{u}) :
    toAffineSpace S ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

/-- The comparison morphism to the affine space intertwines the second projections with the
isomorphism of the polynomial spectra. -/
theorem toAffineSpace_snd (S : Scheme.{u}) :
    toAffineSpace S ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ specPolynomialIsoSpecMvPolynomial.hom := pullback.lift_snd _ _ _

/-- The comparison morphism from the affine space commutes with the first projections. -/
theorem fromAffineSpace_fst (S : Scheme.{u}) :
    fromAffineSpace S ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

/-- The comparison morphism from the affine space intertwines the second projections with the
inverse isomorphism of the polynomial spectra. -/
theorem fromAffineSpace_snd (S : Scheme.{u}) :
    fromAffineSpace S ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ specPolynomialIsoSpecMvPolynomial.inv := pullback.lift_snd _ _ _

/-- The affine line `𝔸¹_S` of this development is Mathlib's affine space `𝔸(n; S)` on a
one-element index type `n`, both being the base change of the spectrum of a polynomial ring on
one variable over the integers along the terminal morphism of `S`. The isomorphism commutes with
the two projections of the defining pullbacks, in particular with the structure morphism
to `S`. -/
def affineLineOverIsoAffineSpace (S : Scheme.{u}) :
    affineLineOver S ≅
      pullback (terminal.from S)
        (terminal.from (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))))) where
  hom := toAffineSpace S
  inv := fromAffineSpace S
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, fromAffineSpace_fst, toAffineSpace_fst, Category.id_comp]
    · rw [Category.assoc, fromAffineSpace_snd, ← Category.assoc, toAffineSpace_snd,
        Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, toAffineSpace_fst, fromAffineSpace_fst, Category.id_comp]
    · rw [Category.assoc, toAffineSpace_snd, ← Category.assoc, fromAffineSpace_snd,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The affine line over an integral scheme is integral. -/
instance isIntegral_affineLineOver (S : Scheme.{u}) [IsIntegral S] :
    IsIntegral (affineLineOver S) :=
  @IsIntegral.of_isIso _ _ (inferInstanceAs (IsIntegral 𝔸(PUnit.{u + 1}; S)))
    (affineLineOverIsoAffineSpace S).inv inferInstance

/-! ### The two affine charts cover the relative projective line -/

/-- The image of the second affine chart of `ℙ¹_S` is the preimage of the second chart of
`ℙ¹_ℤ`, the companion of `Stacks.Chow.range_affineChart`. -/
theorem range_affineYChart (S : Scheme.{u}) :
    Set.range (affineYChart S) =
      pullback.snd (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ))) ⁻¹'
        Set.range (projectiveLineYChart (ULift.{u} ℤ)) := by
  have h := isPullback_affineYChart S
  rw [show affineYChart S = h.isoPullback.hom ≫
      pullback.fst (pullback.snd (terminal.from S)
        (terminal.from (projectiveLine (ULift.{u} ℤ))))
        (projectiveLineYChart (ULift.{u} ℤ)) from h.isoPullback_hom_fst.symm,
    range_comp_scheme, (surjective_of_isIso h.isoPullback.hom).range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]

/-- The two charts of the two-chart gluing cover `ℙ¹_ℤ`. -/
theorem range_projectiveLineXChart_union_range_projectiveLineYChart
    (k : Type u) [CommRing k] :
    Set.range (projectiveLineXChart k) ∪ Set.range (projectiveLineYChart k) = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
  obtain ⟨i, y, hy⟩ := Scheme.GlueData.ι_jointly_surjective (projectiveLineGluingData k) x
  obtain ⟨b⟩ := i
  cases b
  · exact Set.mem_union_left _ ⟨y, hy⟩
  · exact Set.mem_union_right _ ⟨y, hy⟩

/-- The two affine charts cover `ℙ¹_S`, each being the preimage of a chart of `ℙ¹_ℤ`. -/
theorem range_affineChart_union_range_affineYChart (S : Scheme.{u}) :
    Set.range (affineChart S) ∪ Set.range (affineYChart S) = Set.univ := by
  rw [range_affineChart, range_affineYChart, ← Set.preimage_union,
    range_projectiveLineXChart_union_range_projectiveLineYChart, Set.preimage_univ]

/-- The first affine chart of `ℙ¹_S` is the complement of the infinity divisor `D_∞`. -/
theorem range_affineChart_eq_compl_support_lineInfinityDivisor (S : Scheme.{u}) :
    Set.range (affineChart S) =
      ((lineInfinityDivisor S).support : Set (relativeProjectiveLine S))ᶜ := by
  rw [coe_support_lineInfinityDivisor, range_lineConstantSection, range_affineChart,
    ← Set.preimage_compl]
  congr 1
  ext P
  refine ⟨fun hP hinf => Set.disjoint_left.mp
    disjoint_range_integralInfinitySection_projectiveLineXChart hinf hP, fun hP => ?_⟩
  by_contra hX
  obtain ⟨y, rfl⟩ : P ∈ Set.range (projectiveLineYChart (ULift.{u} ℤ)) :=
    (Set.eq_univ_iff_forall.mp
      (range_projectiveLineXChart_union_range_projectiveLineYChart (ULift.{u} ℤ)) P).resolve_left
      hX
  have hXy : (Polynomial.X : Polynomial (ULift.{u} ℤ)) ∈
      (y : PrimeSpectrum (Polynomial (ULift.{u} ℤ))).asIdeal := by
    by_contra h
    exact hX (mem_range_ι_of_X_notMem (ULift.{u} ℤ) _ _
      (fun h => projectiveLineXIndex_ne_projectiveLineYIndex (ULift.{u} ℤ) h.symm) y h)
  refine hP ?_
  rw [range_integralInfinitySection, range_specMap_evalRingHom_zero]
  refine ⟨y, ?_, rfl⟩
  change ((RingHom.ker (Polynomial.evalRingHom (0 : ULift.{u} ℤ)) :
      Ideal (Polynomial (ULift.{u} ℤ))) : Set (Polynomial (ULift.{u} ℤ))) ⊆ _
  rw [Polynomial.ker_evalRingHom, map_zero, sub_zero]
  exact (Ideal.span_singleton_le_iff_mem _).2 hXy

/-- The two affine charts as an open cover of `ℙ¹_S`. -/
def chartCover (S : Scheme.{u}) : (relativeProjectiveLine S).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun _ ↦ affineLineOver S)
    (fun b ↦ bif b then affineYChart S else affineChart S)
    (fun x ↦ by
      rcases Set.eq_univ_iff_forall.mp (range_affineChart_union_range_affineYChart S) x with
        ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨false, y, hy⟩
      · exact ⟨true, y, hy⟩)
    (fun b ↦ by
      cases b
      · exact isOpenImmersion_affineChart S
      · exact isOpenImmersion_affineYChart S)

/-! ### The two affine charts meet -/

/-- Evaluation of a Laurent polynomial over the integers at `1`. It is a retraction of the
constants, so its spectrum is a point of the punctured line. -/
def laurentEvalOne :
    CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)) ⟶ CommRingCat.of (ULift.{u} ℤ) :=
  CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id (ULift.{u} ℤ)) 1)

/-- The point `T = 1` of `ℙ¹_ℤ`. Unlike `Stacks.Chow.integralZeroSection` and
`Stacks.Chow.integralInfinitySection`, which are the origins of the two charts, this point lies
on the punctured line and hence on both charts. -/
def integralOneSection : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ) :=
  specULiftZIsTerminal.from (⊤_ Scheme.{u}) ≫ Spec.map laurentEvalOne ≫
    projectiveLinePuncturedChart (ULift.{u} ℤ) ≫ projectiveLineXChart (ULift.{u} ℤ)

/-- The point `T = 1` lies on the first chart of `ℙ¹_ℤ`, being defined through it. -/
theorem range_integralOneSection_subset_range_projectiveLineXChart :
    Set.range (integralOneSection.{u}) ⊆
      Set.range (projectiveLineXChart (ULift.{u} ℤ)) := by
  rw [integralOneSection]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩

/-- The point `T = 1` lies on the second chart of `ℙ¹_ℤ` as well: it factors through the
punctured line, whose inclusion into the first chart is its inclusion into the second composed
with inversion of the coordinate. -/
theorem range_integralOneSection_subset_range_projectiveLineYChart :
    Set.range (integralOneSection.{u}) ⊆
      Set.range (projectiveLineYChart (ULift.{u} ℤ)) := by
  rw [integralOneSection]
  rintro _ ⟨x, rfl⟩
  refine ⟨((Spec.map laurentEvalOne ≫
    Spec.map (CommRingCat.ofHom
      (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom)) : _ ⟶ _)
      (specULiftZIsTerminal.from (⊤_ Scheme.{u}) x), ?_⟩
  have hfactor : specULiftZIsTerminal.from (⊤_ Scheme.{u}) ≫ Spec.map laurentEvalOne ≫
      projectiveLinePuncturedChart (ULift.{u} ℤ) ≫ projectiveLineXChart (ULift.{u} ℤ) =
    specULiftZIsTerminal.from (⊤_ Scheme.{u}) ≫ Spec.map laurentEvalOne ≫
      Spec.map (CommRingCat.ofHom
        (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom) ≫
      projectiveLineYChart (ULift.{u} ℤ) := by
    rw [(isPullback_projectiveLineCharts (ULift.{u} ℤ)).w]
  exact congrArg
    (fun f : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ) => f.base x) hfactor.symm

/-- The section of `ℙ¹_S ⟶ S` through the point `T = 1`. -/
abbrev lineOneSection (S : Scheme.{u}) : S ⟶ relativeProjectiveLine S :=
  lineConstantSection S integralOneSection

/-- The image of the `1`-section lies on both affine charts of `ℙ¹_S`. -/
theorem range_lineOneSection_subset (S : Scheme.{u}) :
    Set.range (lineOneSection S) ⊆
      Set.range (affineYChart S) ∩ Set.range (affineChart S) := by
  rw [range_affineChart, range_affineYChart, lineOneSection, range_lineConstantSection]
  exact Set.subset_inter
    (Set.preimage_mono range_integralOneSection_subset_range_projectiveLineYChart)
    (Set.preimage_mono range_integralOneSection_subset_range_projectiveLineXChart)

/-- The two affine charts of `ℙ¹_S` meet, as soon as `S` is nonempty: the `1`-section lands in
both of them. -/
theorem nonempty_inter_range_affineYChart_range_affineChart (S : Scheme.{u}) [Nonempty S] :
    (Set.range (affineYChart S) ∩ Set.range (affineChart S)).Nonempty :=
  ⟨_, range_lineOneSection_subset S ⟨‹Nonempty S›.some, rfl⟩⟩

/-! ### The relative projective line over an integral base is integral -/

/-- `ℙ¹_S` is irreducible when `S` is integral. The first chart is irreducible, being a
homeomorphic image of `𝔸¹_S`; it is open; and it meets the second chart, which together with
irreducibility of the second chart makes the second chart lie in the closure of the first. The
two charts cover, so the first chart is dense, and a space with a dense irreducible subset is
irreducible. -/
theorem irreducibleSpace_relativeProjectiveLine (S : Scheme.{u}) [IsIntegral S] :
    IrreducibleSpace (relativeProjectiveLine S) := by
  have hirr : ∀ f : affineLineOver S ⟶ relativeProjectiveLine S, IsIrreducible (Set.range f) :=
    fun f ↦ by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ (affineLineOver S)).image _
        f.continuous.continuousOn
  have hU := hirr (affineChart S)
  have hV := hirr (affineYChart S)
  have hUopen : IsOpen (Set.range (affineChart S)) := IsOpenImmersion.isOpen_range _
  have hsub : Set.range (affineYChart S) ⊆ closure (Set.range (affineChart S)) := fun y hy ↦
    closure_mono Set.inter_subset_right
      (subset_closure_inter_of_isPreirreducible_of_isOpen hV.2 hUopen
        (nonempty_inter_range_affineYChart_range_affineChart S) hy)
  have huniv : closure (Set.range (affineChart S)) = Set.univ :=
    Set.eq_univ_of_univ_subset (by
      rw [← range_affineChart_union_range_affineYChart S]
      exact Set.union_subset subset_closure hsub)
  rw [irreducibleSpace_def, Set.top_eq_univ, ← huniv]
  exact hU.closure

/-- `ℙ¹_S` is reduced when `S` is integral: reducedness is local, and the two affine charts
cover `ℙ¹_S` by copies of the integral, hence reduced, `𝔸¹_S`. -/
theorem isReduced_relativeProjectiveLine (S : Scheme.{u}) [IsIntegral S] :
    IsReduced (relativeProjectiveLine S) := by
  have hred : ∀ i : (chartCover S).I₀, IsReduced ((chartCover S).X i) := fun _ ↦
    inferInstanceAs (IsReduced (affineLineOver S))
  exact IsReduced.of_openCover _ (chartCover S)

/-- **The relative projective line over an integral scheme is integral.** This is the first of
the four hypotheses that
`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_relativeProjectiveLine` adds to
Tag 02RU. -/
@[ega "II 7.4.14" "more general"]
instance isIntegral_relativeProjectiveLine (S : Scheme.{u}) [IsIntegral S] :
    IsIntegral (relativeProjectiveLine S) := by
  have hirr := irreducibleSpace_relativeProjectiveLine S
  have hred := isReduced_relativeProjectiveLine S
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-! ### The reduction to the projective line, with integrality discharged -/

/-- **The degree of a principal divisor on a proper curve, reduced to the projective line**, with
the integrality of `ℙ¹_S` no longer assumed. The base of the Chow situation is the spectrum of a
field, hence integral, so `Stacks.Chow.isIntegral_relativeProjectiveLine` supplies it.

Three hypotheses that Tag 02RU does not state remain: the value `1` of the delta-dimension of
`ℙ¹_S`, the statement itself for `ℙ¹_S`, and dominance of the second projection out of the graph
closure of every unit section representing `f`. So this is still a reduction and not the tag,
and bears no attribute; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Graph`.

The instance `[IsIntegral C.S]` is not a further hypothesis in substance: it follows from `hS`,
a field being a domain. It is listed because `AlgebraicGeometry.Scheme.functionField` asks for
an irreducible space, so without it the function field of `ℙ¹_S` cannot be written in the
statement of `hP` at all. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_relativeProjectiveLine'
    (k : Type u) [Field k] (C : ChowSituation.{u}) [IsIntegral C.S]
    (hS : C.S = AlgebraicGeometry.Spec (.of k))
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X : Scheme.{u}} (c : X ⟶ C.S) [IsProper c] [IsIntegral X]
    (hdim : schemeDeltaDimension C c = (1 : EInt))
    (hPdim : schemeDeltaDimension C (relativeProjectiveLine C.S ↘ C.S) = (1 : EInt))
    (hP : ∀ h : (relativeProjectiveLine C.S).functionField, h ≠ 0 →
      principalDivisorDegree (relativeProjectiveLine C.S ↘ C.S) h = 0)
    (f : (rationalFunctions X)ˣ)
    (hdom : ∀ (U : X.Opens) (hU : Dense (U : Set X)) (g : (Γ(X, U))ˣ),
      ofSection X ⟨U, hU⟩ ↑g = (f : rationalFunctions X) →
        IsDominant (graphLineProjection c U ↑g)) :
    properPushforward C c (𝟙 C.S) c (by simp) 0
      (principalDivisorCycle C c hdim ((rationalFunctionsEquivFunctionField X).1 ↑f)) = 0 :=
  properPushforward_principalDivisorCycle_eq_zero_of_relativeProjectiveLine k C hS hδ c hdim
    (isIntegral_relativeProjectiveLine C.S) hPdim hP f hdom

end Stacks.Chow

end
