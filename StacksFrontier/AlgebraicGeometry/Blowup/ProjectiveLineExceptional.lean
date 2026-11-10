module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorPullback
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorReesPresentation
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.ComparisonNatural
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorReesKernel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exceptional divisor of the blowup of a regular local surface is a projective line

Let `(A, 𝔪, κ)` be a regular local ring of dimension two, let `X ⟶ Spec A` be the blowup of
`Spec A` in `𝔪`, and let `r : X ⟶ 𝐏¹_{Spec A}` be the closed immersion of
`Stacks.Blowup.exists_isClosedImmersion_blowUpSpec_maximalIdeal`. This file proves that the
exceptional divisor `E = X ×_{Spec A} Spec κ` is, through `r`, the projective line `𝐏¹_κ`: part (1)
of Stacks tag 0AGQ.

## Main results

* `Stacks.AlmostBlowUp.isIso_blowUpSpecToModification`: **for a regular sequence `f₁, f₂` the
  blowup of `Spec A` in `(f₁,f₂)` *is* the two-generator modification**
  `Proj (A[T₀,T₁]/(f₂T₀-f₁T₁))`, not merely a closed subscheme of it.
* `Stacks.Blowup.exists_isClosedImmersion_isPullback_projectiveLine_blowUpSpec_maximalIdeal`:
  for a regular local ring `A` of dimension two, the closed immersion `r` of the blowup into
  `𝐏¹_{Spec A}` restricts to an isomorphism of the exceptional divisor with `𝐏¹_κ`.

## Implementation notes

The source states that `r|_E : E ⟶ 𝐏¹_κ` is an isomorphism. The exceptional divisor `E` is the
inverse image of the centre, that is the fibre `X ×_{Spec A} Spec κ`, and `𝐏¹_κ` is the fibre
`𝐏¹_{Spec A} ×_{Spec A} Spec κ`; so the assertion is that `𝐏¹_κ`, mapped to `X` by a morphism over
`Spec κ ⟶ Spec A` whose composite with `r` is the standard closed immersion `𝐏¹_κ ⟶ 𝐏¹_{Spec A}`,
*is* that fibre. That is what is stated: a morphism `s : 𝐏¹_κ ⟶ X` making the square

```
𝐏¹_κ  ⟶ˢ  X
 |          |
 v          v
Spec κ ⟶ Spec A
```

cartesian — so that `s` induces an isomorphism `𝐏¹_κ ≅ E` — together with the identity
`s ≫ r = 𝐏¹_κ ⟶ 𝐏¹_{Spec A}`, which says that the isomorphism is the one induced by `r`. No
separate name for `E` or for `r|_E` is needed, and none is introduced.

`𝐏¹_κ` is written out as `Proj κ[T₀,T₁]`.

The proof is the source's, with the two-generator square of Tag 0EVH carrying the base change.

* `Stacks.AlmostBlowUp.ker_centerReesPresentation_eq_relationIdeal` says that for a regular
  sequence the relation `f₂T₀-f₁T₁` is the whole kernel of the polynomial presentation of the Rees
  algebra, so `Stacks.AlmostBlowUp.reesQuotPresentation` is bijective. Its inverse is graded — a
  homogeneous element of the Rees algebra of degree `d` is the value of a homogeneous polynomial of
  degree `d`, by `Stacks.Blowup.surjective_gradedAddHom_reesPresentation` — so `Proj` of it is an
  isomorphism `X ≅ Proj (A[T₀,T₁]/(f₂T₀-f₁T₁))`, and the cartesian square of Tag 0EVH becomes a
  cartesian square with `X` in the corner.
* The upper-left corner of that square is `Proj ((A/(f₁,f₂))[T₀,T₁])`. For `(f₁,f₂) = 𝔪` the
  coefficient ring `A/(f₁,f₂)` is the residue field, but only up to the identification
  `Ideal.quotEquivOfEq`, since `𝔪` is `(f₁,f₂)` propositionally and not syntactically. That
  identification is transported to `Proj` by `Stacks.ProjectiveCohomology.polyGradedMap` and its
  functoriality `Stacks.ProjectiveCohomology.polyGradedMap_comp`, which is the functoriality of
  `Proj R[T₀,T₁]` in `R`.
* The two generators of `𝔪` are a regular sequence by Tag 00NQ,
  `IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay`.

## References

* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Blowup

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlmostBlowUp

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-! ### The modification ring is the Rees algebra, as graded rings -/

/-- **The presentation of the Rees algebra by the modification ring is onto each graded piece.** A
homogeneous element of degree `d` of `⨁ₙ (f₁,f₂)ⁿ` is the value of a homogeneous polynomial of
degree `d`, whose class in `A[T₀,T₁]/(f₂T₀-f₁T₁)` is homogeneous of degree `d`. No regularity is
needed: this is degreewise surjectivity of the polynomial presentation,
`Stacks.Blowup.surjective_gradedAddHom_reesPresentation`. -/
theorem exists_mem_modificationGrading_reesQuotPresentation_eq (d : ℕ)
    {y : reesAlgebra (centerIdeal A f₁ f₂)} (hy : y ∈ reesGrading (centerIdeal A f₁ f₂) d) :
    ∃ z ∈ modificationGrading A f₁ f₂ d, reesQuotPresentation A f₁ f₂ z = y := by
  obtain ⟨p, hp⟩ := surjective_gradedAddHom_reesPresentation (centerIdeal A f₁ f₂)
    (centerGens A f₁ f₂) (centerGens_mem A f₁ f₂) (centerIdeal_eq_span_range A f₁ f₂) d ⟨y, hy⟩
  refine ⟨Ideal.Quotient.mk (relationIdeal A f₁ f₂)
      (p : MvPolynomial (Fin 2) A),
    AddSubgroup.mem_map_of_mem _ (Iff.mpr (Submodule.mem_toAddSubgroup _) p.2), ?_⟩
  rw [reesQuotPresentation_mk]
  exact congrArg Subtype.val hp

/-- **For a regular sequence of length two the modification ring *is* the Rees algebra of the
centre**, as rings: `A[T₀,T₁]/(f₂T₀-f₁T₁) ≃+* ⨁ₙ (f₁,f₂)ⁿ`. This is
`Stacks.AlmostBlowUp.bijective_reesQuotPresentation` bundled. -/
def reesQuotEquiv (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    modificationRing A f₁ f₂ ≃+* reesAlgebra (centerIdeal A f₁ f₂) :=
  RingEquiv.ofBijective (reesQuotPresentation A f₁ f₂).toRingHom
    (bijective_reesQuotPresentation A f₁ f₂ hreg)

/-- `Stacks.AlmostBlowUp.reesQuotEquiv` is given by `Stacks.AlmostBlowUp.reesQuotPresentation`. -/
@[simp]
theorem reesQuotEquiv_apply (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂])
    (z : modificationRing A f₁ f₂) :
    reesQuotEquiv A f₁ f₂ hreg z = reesQuotPresentation A f₁ f₂ z := rfl

/-- **The inverse of the presentation of the Rees algebra by the modification ring, as a
homomorphism of graded rings.** The inverse exists because the presentation is bijective for a
regular sequence; it is graded because the presentation is onto each graded piece, so the preimage
of a homogeneous element of degree `d` is the homogeneous element of degree `d` that maps to it. -/
def reesQuotPresentationInv (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    reesGrading (centerIdeal A f₁ f₂) →+*ᵍ modificationGrading A f₁ f₂ where
  __ := (reesQuotEquiv A f₁ f₂ hreg).symm.toRingHom
  map_mem := by
    intro d y hy
    obtain ⟨z, hz, hzy⟩ := exists_mem_modificationGrading_reesQuotPresentation_eq A f₁ f₂ d hy
    have hsymm : (reesQuotEquiv A f₁ f₂ hreg).symm y = z := by
      rw [← hzy]
      exact (reesQuotEquiv A f₁ f₂ hreg).symm_apply_apply z
    exact hsymm ▸ hz

/-- `Stacks.AlmostBlowUp.reesQuotPresentationInv` is the inverse of
`Stacks.AlmostBlowUp.reesQuotEquiv`. -/
@[simp]
theorem reesQuotPresentationInv_apply (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂])
    (y : reesAlgebra (centerIdeal A f₁ f₂)) :
    reesQuotPresentationInv A f₁ f₂ hreg y = (reesQuotEquiv A f₁ f₂ hreg).symm y := rfl

/-- `Stacks.AlmostBlowUp.reesQuotPresentationInv` is a left inverse of
`Stacks.AlmostBlowUp.reesQuotPresentation`, as graded ring homomorphisms. -/
theorem reesQuotPresentationInv_comp (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    (reesQuotPresentationInv A f₁ f₂ hreg).comp (reesQuotPresentation A f₁ f₂) =
      GradedRingHom.id (modificationGrading A f₁ f₂) :=
  GradedRingHom.ext fun z => (reesQuotEquiv A f₁ f₂ hreg).symm_apply_apply z

/-- `Stacks.AlmostBlowUp.reesQuotPresentationInv` is a right inverse of
`Stacks.AlmostBlowUp.reesQuotPresentation`, as graded ring homomorphisms. -/
theorem reesQuotPresentation_comp_inv (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    (reesQuotPresentation A f₁ f₂).comp (reesQuotPresentationInv A f₁ f₂ hreg) =
      GradedRingHom.id (reesGrading (centerIdeal A f₁ f₂)) :=
  GradedRingHom.ext fun y => (reesQuotEquiv A f₁ f₂ hreg).apply_symm_apply y

/-- `Stacks.AlmostBlowUp.reesQuotPresentationInv` is surjective. -/
theorem surjective_reesQuotPresentationInv
    (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    Function.Surjective (reesQuotPresentationInv A f₁ f₂ hreg) :=
  (reesQuotEquiv A f₁ f₂ hreg).symm.surjective

/-- The irrelevant ideal of the modification ring is contained in the image of the irrelevant ideal
of the Rees algebra under `Stacks.AlmostBlowUp.reesQuotPresentationInv`. -/
theorem irrelevant_le_map_reesQuotPresentationInv
    (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    HomogeneousIdeal.irrelevant (modificationGrading A f₁ f₂) ≤
      (HomogeneousIdeal.irrelevant (reesGrading (centerIdeal A f₁ f₂))).map
        (reesQuotPresentationInv A f₁ f₂ hreg) :=
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  Proj.irrelevant_le_map_of_surjective _ (surjective_reesQuotPresentationInv A f₁ f₂ hreg)

/-! ### The blowup is the two-generator modification -/

/-- **The two-generator modification maps back to the blowup, for a regular sequence**: `Proj` of
`Stacks.AlmostBlowUp.reesQuotPresentationInv`. This is the inverse of
`Stacks.AlmostBlowUp.blowUpSpecToModification`. -/
def modificationToBlowUpSpec (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    AlgebraicGeometry.Proj (modificationGrading A f₁ f₂) ⟶ blowUpSpec (centerIdeal A f₁ f₂) :=
  letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
  Proj.map (reesQuotPresentationInv A f₁ f₂ hreg)
    (irrelevant_le_map_reesQuotPresentationInv A f₁ f₂ hreg)

/-- `Proj` of two graded ring homomorphisms whose composite is the identity composes to the
identity. -/
private theorem proj_map_comp_proj_map_eq_id {A B σ τ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ}
    {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (h : f.comp g = GradedRingHom.id ℬ) :
    Proj.map f hf ≫ Proj.map g hg =
      CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Proj ℬ) := by
  rw [← Proj.map_comp]
  exact (Proj.map_congr h _ (by simp)).trans Proj.map_id

/-- `Stacks.AlmostBlowUp.modificationToBlowUpSpec` is a left inverse of
`Stacks.AlmostBlowUp.blowUpSpecToModification`. -/
theorem blowUpSpecToModification_comp_modificationToBlowUpSpec
    (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    blowUpSpecToModification A f₁ f₂ ≫ modificationToBlowUpSpec A f₁ f₂ hreg =
      CategoryTheory.CategoryStruct.id (blowUpSpec (centerIdeal A f₁ f₂)) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  exact proj_map_comp_proj_map_eq_id _ _ _ _ (reesQuotPresentation_comp_inv A f₁ f₂ hreg)

/-- `Stacks.AlmostBlowUp.modificationToBlowUpSpec` is a right inverse of
`Stacks.AlmostBlowUp.blowUpSpecToModification`. -/
theorem modificationToBlowUpSpec_comp_blowUpSpecToModification
    (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    modificationToBlowUpSpec A f₁ f₂ hreg ≫ blowUpSpecToModification A f₁ f₂ =
      CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  exact proj_map_comp_proj_map_eq_id _ _ _ _ (reesQuotPresentationInv_comp A f₁ f₂ hreg)

/-- **For a regular sequence of length two the blowup of `Spec A` in `(f₁,f₂)` *is* the
two-generator modification** `Proj (A[T₀,T₁]/(f₂T₀-f₁T₁))`, not merely a closed subscheme of it.
The closed immersion `Stacks.AlmostBlowUp.blowUpSpecToModification` is `Proj` of the presentation
of the Rees algebra by the modification ring, and that presentation is a graded isomorphism as soon
as `f₁, f₂` is a regular sequence. -/
@[sga "6 VII 3.5" "special case"]
theorem isIso_blowUpSpecToModification (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsIso (blowUpSpecToModification A f₁ f₂) :=
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  ⟨modificationToBlowUpSpec A f₁ f₂ hreg,
    blowUpSpecToModification_comp_modificationToBlowUpSpec A f₁ f₂ hreg,
    modificationToBlowUpSpec_comp_blowUpSpecToModification A f₁ f₂ hreg⟩

/-- The blowup of `Spec A` in a two-generated centre, identified with the two-generator
modification: `Stacks.AlmostBlowUp.isIso_blowUpSpecToModification` as an isomorphism. -/
def blowUpSpecIsoModification (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    blowUpSpec (centerIdeal A f₁ f₂) ≅ AlgebraicGeometry.Proj (modificationGrading A f₁ f₂) :=
  letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
  { hom := blowUpSpecToModification A f₁ f₂
    inv := modificationToBlowUpSpec A f₁ f₂ hreg
    hom_inv_id := blowUpSpecToModification_comp_modificationToBlowUpSpec A f₁ f₂ hreg
    inv_hom_id := modificationToBlowUpSpec_comp_blowUpSpecToModification A f₁ f₂ hreg }

/-! ### The exceptional line inside the projective line over the base -/

/-- **The exceptional projective line maps into `𝐏¹_{Spec A}` by reduction of coefficients.** Read
on graded rings: the quotient map `A[T₀,T₁] ⟶ A[T₀,T₁]/(f₂T₀-f₁T₁)` obtained by inverting the
presentation of the Rees algebra, followed by the reduction of coefficients, *is* the reduction of
coefficients `A[T₀,T₁] ⟶ (A/(f₁,f₂))[T₀,T₁]`. -/
theorem exceptionalGradedHom_comp_inv_comp_centerReesPresentation
    (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    (exceptionalGradedHom A f₁ f₂).comp
        ((reesQuotPresentationInv A f₁ f₂ hreg).comp (centerReesPresentation A f₁ f₂)) =
      Stacks.ProjectiveCohomology.polyGradedMap (Fin 2)
        (Ideal.Quotient.mk (centerIdeal A f₁ f₂)) := by
  refine GradedRingHom.ext fun p => ?_
  have h1 : reesQuotPresentationInv A f₁ f₂ hreg (centerReesPresentation A f₁ f₂ p) =
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) p := by
    rw [reesQuotPresentationInv_apply, show centerReesPresentation A f₁ f₂ p =
        reesQuotPresentation A f₁ f₂ (Ideal.Quotient.mk (relationIdeal A f₁ f₂) p) from
      (reesQuotPresentation_mk A f₁ f₂ p).symm, ← reesQuotEquiv_apply A f₁ f₂ hreg,
      RingEquiv.symm_apply_apply]
  rw [GradedRingHom.comp_apply, GradedRingHom.comp_apply, h1, exceptionalGradedHom_mk]
  rfl

/-- **The exceptional projective line is the fibre of `𝐏¹_{Spec A}`, inside the blowup.** The
composite `𝐏¹_{A/(f₁,f₂)} ⟶ X' ≅ X ⟶ 𝐏¹_{Spec A}` of the closed immersion of the exceptional line
into the modification, the identification of the modification with the blowup, and the closed
immersion of the blowup into the projective line over the base, is the standard morphism
`𝐏¹_{A/(f₁,f₂)} ⟶ 𝐏¹_{Spec A}` induced by reduction of coefficients. -/
theorem exceptionalToModification_comp_inv_comp_blowUpSpecToProjSpace
    (hreg : RingTheory.Sequence.IsWeaklyRegular A [f₁, f₂]) :
    exceptionalToModification A f₁ f₂ ≫ modificationToBlowUpSpec A f₁ f₂ hreg ≫
        blowUpSpecToProjSpace (centerIdeal A f₁ f₂) (centerGens A f₁ f₂)
          (centerGens_mem A f₁ f₂) (centerIdeal_eq_span_range A f₁ f₂) =
      Proj.map (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2)
          (Ideal.Quotient.mk (centerIdeal A f₁ f₂)))
        (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
          (Ideal.Quotient.mk (centerIdeal A f₁ f₂))) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have key : Proj.map (exceptionalGradedHom A f₁ f₂) (irrelevant_le_map A f₁ f₂) ≫
      Proj.map (reesQuotPresentationInv A f₁ f₂ hreg)
          (irrelevant_le_map_reesQuotPresentationInv A f₁ f₂ hreg) ≫
        Proj.map (centerReesPresentation A f₁ f₂)
          (Proj.irrelevant_le_map_of_surjective _ (surjective_reesPresentation
            (centerIdeal A f₁ f₂) (centerGens A f₁ f₂) (centerGens_mem A f₁ f₂)
            (centerIdeal_eq_span_range A f₁ f₂))) =
      Proj.map (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2)
          (Ideal.Quotient.mk (centerIdeal A f₁ f₂)))
        (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
          (Ideal.Quotient.mk (centerIdeal A f₁ f₂))) := by
    rw [← Proj.map_comp, ← Proj.map_comp]
    exact Proj.map_congr (exceptionalGradedHom_comp_inv_comp_centerReesPresentation A f₁ f₂ hreg)
      _ _
  exact key

end Stacks.AlmostBlowUp

namespace Stacks.Blowup

open Stacks.AlmostBlowUp

/-! ### Two generators of the maximal ideal are a regular sequence -/

/-- **Two generators of the maximal ideal of a regular local ring of dimension two form a regular
sequence.** A family of two elements spanning `𝔪` has the minimal length
`(𝔪).spanFinrank = dim A = 2`, so Tag 00NQ applies to it. -/
@[stacks 00NQ "for a two-dimensional regular local ring and a two-element generating family of \
the maximal ideal"]
theorem isWeaklyRegular_of_span_range_eq_maximalIdeal (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) (x : Fin 2 → A)
    (hspan : IsLocalRing.maximalIdeal A = Ideal.span (Set.range x)) :
    RingTheory.Sequence.IsWeaklyRegular A [x 0, x 1] := by
  have hfr : (IsLocalRing.maximalIdeal A).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hdim] at h
    exact_mod_cast h
  have hset : {r : A | r ∈ [x 0, x 1]} = Set.range x := by
    ext a
    refine ⟨fun ha => ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  have hlist : Ideal.ofList [x 0, x 1] = IsLocalRing.maximalIdeal A := by
    rw [hspan]
    exact congrArg Ideal.span hset
  exact ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
    A).1 [x 0, x 1] hlist (by simp [hfr])).1.toIsWeaklyRegular

/-! ### Tag 0AGQ part (1) -/

/-- Let `(A, 𝔪, κ)` be a regular local ring of dimension two and let `X ⟶ Spec A` be the blowup of
`Spec A` in `𝔪`. There is a closed immersion `r : X ⟶ 𝐏¹_{Spec A}` over `Spec A` whose restriction
to the exceptional divisor is an isomorphism `E ≅ 𝐏¹_κ`.

The exceptional divisor is the fibre `E = X ×_{Spec A} Spec κ`, so the last clause is stated as:
there is a morphism `s : 𝐏¹_κ ⟶ X` over `Spec κ ⟶ Spec A` making `𝐏¹_κ` that fibre — the cartesian
square — whose composite with `r` is the standard closed immersion `𝐏¹_κ ⟶ 𝐏¹_{Spec A}` given by
reduction of coefficients. The cartesian square says that `s` induces an isomorphism `𝐏¹_κ ≅ E`,
and the identity says that this isomorphism is the one induced by `r`, that is `(r|_E)⁻¹`.

Here `𝐏¹_κ` is `Proj κ[T₀,T₁]`, and `r` is the closed immersion of
`Stacks.Blowup.exists_isClosedImmersion_blowUpSpec_maximalIdeal`. -/
@[stacks 0AGQ "part (1)"]
theorem exists_isClosedImmersion_isPullback_projectiveLine_blowUpSpec_maximalIdeal
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    ∃ r : blowUpSpec (IsLocalRing.maximalIdeal A) ⟶
        AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) A),
      IsClosedImmersion r ∧
        r ≫ projSpaceToSpec A 2 = toSpec (IsLocalRing.maximalIdeal A) ∧
        ∃ s : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2)
              (IsLocalRing.ResidueField A)) ⟶
            blowUpSpec (IsLocalRing.maximalIdeal A),
          IsPullback s (projSpaceToSpec (IsLocalRing.ResidueField A) 2)
              (toSpec (IsLocalRing.maximalIdeal A))
              (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ∧
            s ≫ r = Proj.map
                (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (IsLocalRing.residue A))
                (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
                  (IsLocalRing.residue A)) := by
  classical
  obtain ⟨x, hspan⟩ := exists_range_eq_maximalIdeal A hdim
  have hreg := isWeaklyRegular_of_span_range_eq_maximalIdeal A hdim x hspan
  have hJ : centerIdeal A (x 0) (x 1) = IsLocalRing.maximalIdeal A := by
    rw [hspan]
    refine congrArg Ideal.span (Set.ext fun a => ⟨?_, ?_⟩)
    · rintro (rfl | ha)
      · exact ⟨0, rfl⟩
      · rw [Set.mem_singleton_iff] at ha
        exact ⟨1, ha.symm⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  let ε : centerRing A (x 0) (x 1) ≃+* IsLocalRing.ResidueField A := Ideal.quotEquivOfEq hJ
  have hεmk : ε.toRingHom.comp (Ideal.Quotient.mk (centerIdeal A (x 0) (x 1))) =
      IsLocalRing.residue A := RingHom.ext fun a => Ideal.quotEquivOfEq_mk hJ a
  have hεsymm : ε.toRingHom.comp ε.symm.toRingHom =
      RingHom.id (IsLocalRing.ResidueField A) := RingHom.ext fun c => ε.apply_symm_apply c
  have hεsymm' : ε.symm.toRingHom.comp ε.toRingHom =
      RingHom.id (centerRing A (x 0) (x 1)) := RingHom.ext fun c => ε.symm_apply_apply c
  rw [← hJ]
  let := (twoGeneratorSquare A (x 0) (x 1)).modificationGraded
  let e₁ : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2)
        (IsLocalRing.ResidueField A)) ≅
      AlgebraicGeometry.Proj (exceptionalGrading A (x 0) (x 1)) :=
    { hom := Proj.map (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) ε.toRingHom)
        (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2) ε.toRingHom)
      inv := Proj.map (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) ε.symm.toRingHom)
        (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2) ε.symm.toRingHom)
      hom_inv_id := proj_map_comp_proj_map_eq_id _ _ _ _
        (((Stacks.ProjectiveCohomology.polyGradedMap_comp _ _ _ (Fin 2) ε.symm.toRingHom
              ε.toRingHom).trans
            (congrArg (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2)) hεsymm)).trans
          (Stacks.ProjectiveCohomology.polyGradedMap_id (Fin 2)))
      inv_hom_id := proj_map_comp_proj_map_eq_id _ _ _ _
        (((Stacks.ProjectiveCohomology.polyGradedMap_comp _ _ _ (Fin 2) ε.toRingHom
              ε.symm.toRingHom).trans
            (congrArg (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2)) hεsymm')).trans
          (Stacks.ProjectiveCohomology.polyGradedMap_id (Fin 2))) }
  let e₃ : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ≅
      Spec (CommRingCat.of (centerRing A (x 0) (x 1))) :=
    { hom := Spec.map (CommRingCat.ofHom ε.toRingHom)
      inv := Spec.map (CommRingCat.ofHom ε.symm.toRingHom)
      hom_inv_id := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hεsymm, CommRingCat.ofHom_id, Spec.map_id]
      inv_hom_id := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hεsymm', CommRingCat.ofHom_id,
          Spec.map_id] }
  refine ⟨blowUpSpecToProjSpace (centerIdeal A (x 0) (x 1)) (centerGens A (x 0) (x 1))
      (centerGens_mem A (x 0) (x 1)) (centerIdeal_eq_span_range A (x 0) (x 1)), inferInstance,
    blowUpSpecToProjSpace_comp_projSpaceToSpec _ _ _ _,
    e₁.hom ≫ exceptionalToModification A (x 0) (x 1) ≫
      (blowUpSpecIsoModification A (x 0) (x 1) hreg).inv, ?_, ?_⟩
  · refine (twoGenerator_isPullback A (x 0) (x 1)).of_iso' e₁
      (blowUpSpecIsoModification A (x 0) (x 1) hreg) e₃ (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · have hzero : (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2)
            ε.toRingHom).gradedZeroRingHom.comp (centerRingHom A (x 0) (x 1)) =
          (AlgebraicGeometry.ProjectiveSpace.gradeZeroEquiv (Fin 2)
            (IsLocalRing.ResidueField A)).toRingHom.comp ε.toRingHom := by
        refine RingHom.ext fun c => Subtype.ext ?_
        have hlhs : ((Stacks.ProjectiveCohomology.polyGradedMap (Fin 2)
              ε.toRingHom).gradedZeroRingHom (centerRingHom A (x 0) (x 1) c) :
            MvPolynomial (Fin 2) (IsLocalRing.ResidueField A)) =
            MvPolynomial.map ε.toRingHom (MvPolynomial.C c) := rfl
        have hrhs : ∀ c' : IsLocalRing.ResidueField A,
            (((AlgebraicGeometry.ProjectiveSpace.gradeZeroEquiv (Fin 2)
                  (IsLocalRing.ResidueField A)).toRingHom c' :
                MvPolynomial.homogeneousSubmodule (Fin 2) (IsLocalRing.ResidueField A) 0) :
              MvPolynomial (Fin 2) (IsLocalRing.ResidueField A)) = MvPolynomial.C c' := by
          intro c'
          change ((algebraMap (IsLocalRing.ResidueField A)
            (MvPolynomial.homogeneousSubmodule (Fin 2) (IsLocalRing.ResidueField A) 0) c' :
              MvPolynomial.homogeneousSubmodule (Fin 2) (IsLocalRing.ResidueField A) 0) :
            MvPolynomial (Fin 2) (IsLocalRing.ResidueField A)) = MvPolynomial.C c'
          simp
        rw [RingHom.comp_apply, RingHom.comp_apply, hlhs, hrhs, MvPolynomial.map_C]
      have key : Proj.map (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) ε.toRingHom)
            (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2) ε.toRingHom) ≫
            (Proj.toSpecZero (exceptionalGrading A (x 0) (x 1)) ≫
              Spec.map (CommRingCat.ofHom (centerRingHom A (x 0) (x 1)))) =
          (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2)
              (IsLocalRing.ResidueField A)) ≫
            Spec.map (CommRingCat.ofHom (AlgebraicGeometry.ProjectiveSpace.gradeZeroEquiv (Fin 2)
              (IsLocalRing.ResidueField A)).toRingHom)) ≫
            Spec.map (CommRingCat.ofHom ε.toRingHom) := by
        rw [← Category.assoc, Proj.map_toSpecZero, Category.assoc, Category.assoc,
          ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
          hzero]
      exact key
    · have key : blowUpSpecToModification A (x 0) (x 1) ≫ modificationToBase A (x 0) (x 1) =
          toSpec (centerIdeal A (x 0) (x 1)) ≫ (Iso.refl (Spec (CommRingCat.of A))).hom := by
        rw [Iso.refl_hom, Category.comp_id]
        exact blowUpSpecToModification_comp_modificationToBase A (x 0) (x 1)
      exact key
    · have key : Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ centerToBase A (x 0) (x 1) =
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
            (Iso.refl (Spec (CommRingCat.of A))).hom := by
        rw [Iso.refl_hom, Category.comp_id, centerToBase, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, hεmk]
      exact key
  · rw [Category.assoc, Category.assoc,
      show (blowUpSpecIsoModification A (x 0) (x 1) hreg).inv =
        modificationToBlowUpSpec A (x 0) (x 1) hreg from rfl,
      exceptionalToModification_comp_inv_comp_blowUpSpecToProjSpace A (x 0) (x 1) hreg]
    have key : Proj.map (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) ε.toRingHom)
          (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2) ε.toRingHom) ≫
          Proj.map (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2)
              (Ideal.Quotient.mk (centerIdeal A (x 0) (x 1))))
            (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
              (Ideal.Quotient.mk (centerIdeal A (x 0) (x 1)))) =
        Proj.map (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (IsLocalRing.residue A))
          (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
            (IsLocalRing.residue A)) := by
      rw [← Proj.map_comp]
      exact Proj.map_congr
        ((Stacks.ProjectiveCohomology.polyGradedMap_comp _ _ _ (Fin 2)
            (Ideal.Quotient.mk (centerIdeal A (x 0) (x 1))) ε.toRingHom).trans
          (congrArg (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2)) hεmk)) _ _
    exact key

end Stacks.Blowup

end
