module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreExceptionalCompletionRing

/-!
# The exceptional divisor of the blowup at infinity of a regular immersion

Let `i : Z ⟶ X` be a regular closed immersion, `b : W ⟶ 𝐏¹_X` the blowup of `𝐏¹_X` in the centre
`∞(Z)` and `E ⊆ W` its exceptional divisor. Write `𝒩` for the normal bundle of `i`
(`Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`) and `𝒞 = 𝒩^∨` for its dual, the
conormal sheaf. This file constructs an isomorphism over `Z`

  `E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)`

between `E` and the projective completion of the normal bundle, under which the normal cone
`C_ZX ⊆ E` of Stacks 0FBH corresponds to the vector bundle `N = 𝐕(𝒞) ⊆ 𝐏(𝒞 ⊕ 𝒪_Z)`.

Over an affine open `U = Spec A` of `X` with `I` the ideal of `Z ∩ U`, the part of `E` over `U`
is `Proj (A/I ⊗_{A[s]} A[s][(I, s) t])`, and for a regular immersion
`A/I ⊗_{A[s]} A[s][(I, s) t] = Gr_{(I, s)}(A[s]) = Gr_I(A)[T] = Sym_{A/I}(I/I² ⊕ A/I)`, which is
the graded ring of the chart of `𝐏(𝒞 ⊕ 𝒪_Z)` over `Z ∩ U`. These identifications are compatible
with restriction to smaller affine opens, so they glue (Stacks 01LH).

## Main definitions

* `Stacks.Chow.exceptionalDivisorIsoProjectiveCompletion`: **`E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)`**, over `Z`.

## Main results

* `Stacks.Chow.exceptionalDivisorIsoProjectiveCompletion_hom_projection`: the isomorphism lies
  over `Z`.

## References

* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AssociatedGraded Stacks.AlgebraicGeometry.ReflexiveModules
open scoped Stacks.ProjectiveCompletion

universe u

namespace Stacks.Chow

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-! ### The gluing datum of `E` over the affine opens of `X` -/

section GluingData

/-- The structure morphisms of the charts of `E` to the affine opens of `X` are compatible with
restriction. -/
theorem exceptionalProjChartToOpen_naturality {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    exceptionalProjChartRestrict i h ≫ exceptionalProjChartToOpen i U =
      exceptionalProjChartToOpen i V ≫ X.homOfLE h := by
  rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
    (isPullback_exceptionalProjChart i U).w, (isPullback_exceptionalProjChart i V).w,
    ← Category.assoc, exceptionalProjChartRestrict_exceptionalProjChart]

/-- **The gluing datum of `E` over the affine opens of `X`** (Stacks 01LH): over `U`, the
projective spectrum of `B_U = Γ(Z ∩ U) ⊗_{Γ(V)} Γ(V)[𝒥 t]`. -/
abbrev exceptionalBasisGluingData : Scheme.BasisGluingData X X.affineOpens where
  obj U := AlgebraicGeometry.Proj (centreChartGrading i U)
  proj U := exceptionalProjChartToOpen i U
  res h := exceptionalProjChartRestrict i h
  isPullback_res {V U} h := by
    refine IsPullback.of_right (h₁₂ := exceptionalProjChart i U) (h₂₂ := U.1.ι)
      (v₁₃ := exceptionalDivisorToCentre i ≫ i) ?_ (exceptionalProjChartToOpen_naturality i h)
      (isPullback_exceptionalProjChart i U).flip
    rw [exceptionalProjChartRestrict_exceptionalProjChart i h, Scheme.homOfLE_ι]
    exact (isPullback_exceptionalProjChart i V).flip
  res_trans {W V U} hWV hVU := by
    rw [← cancel_mono (exceptionalProjChart i U), Category.assoc,
      exceptionalProjChartRestrict_exceptionalProjChart,
      exceptionalProjChartRestrict_exceptionalProjChart,
      exceptionalProjChartRestrict_exceptionalProjChart]

/-- `E` as a solution of its gluing problem. -/
abbrev exceptionalGluing : (exceptionalBasisGluingData i).Gluing where
  base := (exceptionalIdealAtInfinity i.ker).subscheme
  toBase := exceptionalDivisorToCentre i ≫ i
  chart := exceptionalProjChart i
  isPullback_chart := isPullback_exceptionalProjChart i
  res_comp_chart h := exceptionalProjChartRestrict_exceptionalProjChart i h

end GluingData


/-! ### `𝐏(𝒞 ⊕ 𝒪_Z)` as a solution of the gluing problem of `E` -/

section Completion

/-- Two composites of `Proj.map` agree when the composites of the graded maps do. -/
theorem _root_.AlgebraicGeometry.Proj.map_comp_map_eq {A B C D σ τ υ ω : Type u} [CommRing A]
    [CommRing B] [CommRing C] [CommRing D] [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B]
    [AddSubgroupClass τ B] [SetLike υ C] [AddSubgroupClass υ C] [SetLike ω D]
    [AddSubgroupClass ω D] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → υ} {𝒟 : ℕ → ω} [GradedRing 𝒜]
    [GradedRing ℬ] [GradedRing 𝒞] [GradedRing 𝒟] (f₁ : 𝒜 →+*ᵍ ℬ) (g₁ : ℬ →+*ᵍ 𝒟)
    (f₂ : 𝒜 →+*ᵍ 𝒞) (g₂ : 𝒞 →+*ᵍ 𝒟)
    (hf₁ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f₁)
    (hg₁ : HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant ℬ).map g₁)
    (hf₂ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒜).map f₂)
    (hg₂ : HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant 𝒞).map g₂)
    (h : g₁.comp f₁ = g₂.comp f₂) :
    Proj.map g₁ hg₁ ≫ Proj.map f₁ hf₁ = Proj.map g₂ hg₂ ≫ Proj.map f₂ hf₂ := by
  rw [← Proj.map_comp, ← Proj.map_comp]
  exact Proj.map_congr h _ _

variable [IsLocallyNoetherian Z]
  (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)

/-- The chart of `𝐏(𝒞 ⊕ 𝒪_Z)` over `Z ∩ U`, with source the chart `Proj B_U` of `E`. -/
def completionGluingChart (U : X.affineOpens) :
    AlgebraicGeometry.Proj (centreChartGrading i U) ⟶
      Stacks.ProjectiveCompletion.projectiveCompletion
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) :=
  exceptionalChartProjInv i U hi ≫
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (completionAlgebra (dualSheaf
      (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))).chart (i ⁻¹ᵁ U.1)
        (isAffineOpen_centrePreimage i U)

/-- `Proj B_U ≅ Proj Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))` followed by the structure morphism to `Z ∩ U` is the
structure morphism of `Proj B_U`. -/
theorem exceptionalChartProjInv_projInclusionToOpen (U : X.affineOpens) :
    exceptionalChartProjInv i U hi ≫ Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
        (completionAlgebra (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))
        (i ⁻¹ᵁ U.1) (isAffineOpen_centrePreimage i U) =
      centreChartToSpec i U ≫ (isAffineOpen_centrePreimage i U).isoSpec.inv := by
  show exceptionalChartProjInv i U hi ≫ (Proj.toSpecZero ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1)) ≫
      Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1))).comp
          ((completionAlgebra (dualSheaf
            (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).strHom (i ⁻¹ᵁ U.1)))) ≫
    (isAffineOpen_centrePreimage i U).isoSpec.inv) = _
  rw [← Category.assoc, ← Category.assoc, Category.assoc (exceptionalChartProjInv i U hi),
    exceptionalChartProjInv_toSpecZero]

/-- `Proj B_U ≅ Proj Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))` lies over `U`. -/
theorem exceptionalChartProjInv_toOpen (U : X.affineOpens) :
    exceptionalChartProjInv i U hi ≫ Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
        (completionAlgebra (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))
        (i ⁻¹ᵁ U.1) (isAffineOpen_centrePreimage i U) ≫ (i ∣_ U.1) =
      exceptionalProjChartToOpen i U := by
  rw [← Category.assoc, exceptionalChartProjInv_projInclusionToOpen, Category.assoc]
  rfl

/-- **The chart of `𝐏(𝒞 ⊕ 𝒪_Z)` over `Z ∩ U` is the part of `𝐏(𝒞 ⊕ 𝒪_Z)` over `U`**, with source
the chart `Proj B_U` of `E`. -/
theorem isPullback_completionGluingChart (U : X.affineOpens) :
    IsPullback (exceptionalProjChartToOpen i U) (completionGluingChart i hi U) U.1.ι
      (Stacks.ProjectiveCompletion.projectiveCompletionProj
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) ≫ i) := by
  have h1 := ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj (completionAlgebra (dualSheaf
      (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))).chart_isPullback (i ⁻¹ᵁ U.1)
        (isAffineOpen_centrePreimage i U)).flip.paste_horiz (isPullback_morphismRestrict i U.1)
  refine IsPullback.of_iso h1 (asIso (exceptionalChartProjInv i U hi)).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) ?_
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
    exact exceptionalChartProjInv_toOpen i hi U
  · simp only [Iso.refl_hom, Iso.symm_hom, asIso_inv, completionGluingChart]
    exact (Category.comp_id _).trans (IsIso.inv_hom_id_assoc _ _).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl

/-- The identifications `Proj B_U ≅ Proj Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))` are compatible with
restriction. -/
theorem exceptionalProjChartRestrict_exceptionalChartProjInv {U V : X.affineOpens}
    (h : V.1 ≤ U.1) :
    exceptionalProjChartRestrict i h ≫ exceptionalChartProjInv i U hi =
      exceptionalChartProjInv i V hi ≫
        Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap (completionAlgebra (dualSheaf
          (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)) (i ⁻¹ᵁ V.1) (i ⁻¹ᵁ U.1)
          (i.preimage_mono h) (isAffineOpen_centrePreimage i V)
          (isAffineOpen_centrePreimage i U) := by
  have hres : HomogeneousIdeal.irrelevant ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ V.1)) ≤
      (HomogeneousIdeal.irrelevant ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1))).map
        ((completionAlgebra (dualSheaf
          (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).res
            (i.preimage_mono h)) :=
    Stacks.AlgebraicGeometry.RelativeProjGeneral.irrelevant_le_map_res_of_le_opens
      (completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).toGradedAlgebra
      (U := ⟨i ⁻¹ᵁ V.1, isAffineOpen_centrePreimage i V⟩)
      (V := ⟨i ⁻¹ᵁ U.1, isAffineOpen_centrePreimage i U⟩) (i.preimage_mono h)
  have hdom := Stacks.AlgebraicGeometry.RelativeProj.projInclusionDomain_eq_top
    (completionAlgebra (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))
    (i ⁻¹ᵁ V.1) (i ⁻¹ᵁ U.1) (i.preimage_mono h) (isAffineOpen_centrePreimage i V)
    (isAffineOpen_centrePreimage i U)
  have hmap : Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap (completionAlgebra (dualSheaf
      (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)) (i ⁻¹ᵁ V.1) (i ⁻¹ᵁ U.1)
      (i.preimage_mono h) (isAffineOpen_centrePreimage i V)
      (isAffineOpen_centrePreimage i U) =
      Proj.map ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).res
          (i.preimage_mono h)) hres :=
    Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map _ _ _ hres hdom
  rw [hmap]
  exact AlgebraicGeometry.Proj.map_comp_map_eq _ _ _ _ _ _ _ _
    (centreChartRestrict_comp_exceptionalChartGradedHom i U hi h)

/-- The charts of `𝐏(𝒞 ⊕ 𝒪_Z)` with sources the charts of `E` are compatible with restriction. -/
theorem exceptionalProjChartRestrict_completionGluingChart {U V : X.affineOpens}
    (h : V.1 ≤ U.1) :
    exceptionalProjChartRestrict i h ≫ completionGluingChart i hi U =
      completionGluingChart i hi V := by
  have e1 := exceptionalProjChartRestrict_exceptionalChartProjInv i hi h
  have e2 := (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (completionAlgebra (dualSheaf
    (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))).chart_transition (i ⁻¹ᵁ V.1)
      (i ⁻¹ᵁ U.1) (i.preimage_mono h) (isAffineOpen_centrePreimage i V)
      (isAffineOpen_centrePreimage i U)
  have e3 : exceptionalProjChartRestrict i h ≫ exceptionalChartProjInv i U hi ≫
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))).chart (i ⁻¹ᵁ U.1)
          (isAffineOpen_centrePreimage i U) =
      exceptionalChartProjInv i V hi ≫
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (completionAlgebra (dualSheaf
          (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))).chart (i ⁻¹ᵁ V.1)
            (isAffineOpen_centrePreimage i V) := by
    rw [reassoc_of% e1, e2]
  exact e3

/-- `𝐏(𝒞 ⊕ 𝒪_Z)` as a solution of the gluing problem of `E`. -/
abbrev completionGluing : (exceptionalBasisGluingData i).Gluing where
  base := Stacks.ProjectiveCompletion.projectiveCompletion
    (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
  toBase := Stacks.ProjectiveCompletion.projectiveCompletionProj
    (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) ≫ i
  chart := completionGluingChart i hi
  isPullback_chart := isPullback_completionGluingChart i hi
  res_comp_chart h := exceptionalProjChartRestrict_completionGluingChart i hi h

/-- **The exceptional divisor of the blowup at infinity of a regular immersion is the projective
completion of the normal bundle**: `E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)`, with `𝒞 = 𝒩^∨` the dual of the normal
bundle `𝒩` of `i`. -/
def exceptionalDivisorIsoProjectiveCompletion :
    (exceptionalIdealAtInfinity i.ker).subscheme ≅
      Stacks.ProjectiveCompletion.projectiveCompletion
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) :=
  (exceptionalGluing i).isoOfGluing X.isBasis_affineOpens (completionGluing i hi)

/-- On the chart `Proj B_U` of `E`, the isomorphism `E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` is the chart of
`𝐏(𝒞 ⊕ 𝒪_Z)` over `Z ∩ U`. -/
@[reassoc (attr := simp)]
theorem exceptionalProjChart_exceptionalDivisorIsoProjectiveCompletion_hom (U : X.affineOpens) :
    exceptionalProjChart i U ≫ (exceptionalDivisorIsoProjectiveCompletion i hi).hom =
      completionGluingChart i hi U :=
  (exceptionalGluing i).chart_comp_desc X.isBasis_affineOpens (completionGluing i hi) U

/-- **The isomorphism `E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` lies over `Z`.** -/
@[reassoc (attr := simp)]
theorem exceptionalDivisorIsoProjectiveCompletion_hom_projection :
    (exceptionalDivisorIsoProjectiveCompletion i hi).hom ≫
        Stacks.ProjectiveCompletion.projectiveCompletionProj
          (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) =
      exceptionalDivisorToCentre i := by
  rw [← cancel_mono i, Category.assoc]
  exact (exceptionalGluing i).desc_comp_toBase X.isBasis_affineOpens (completionGluing i hi)

end Completion

end Stacks.Chow

end
