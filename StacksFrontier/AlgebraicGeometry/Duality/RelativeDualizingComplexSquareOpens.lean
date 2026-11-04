module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexOpenRestriction

/-!
# The diagonal open of an open subscheme, as an open of `W`

Let `W ⊆ X ×_S X` be a diagonal open of `f : X ⟶ S`, with closed immersion `Δ : X ⟶ W`, and let
`U ⊆ X` be open. The open `W_U = W ∩ (U ×_S U) = pr₁⁻¹(U) ∩ pr₂⁻¹(U)` of `W` is a diagonal open of
`U ⟶ X ⟶ S`: the relative diagonal of `U` factors through it as the base change
`Δ_U : U ⟶ W_U` of `Δ`, because `Δ⁻¹(W_U) = U`. Unlike the restriction
`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrict`, whose underlying scheme is a fibre product,
`W_U` is literally an open of `W`, so that `W_V ⊆ W_U` for `V ⊆ U` is an inclusion of opens of `W`
and `W_U ∩ W_V = W_{U ∩ V}`. This is the form in which the proof of Stacks 0E2X uses the opens
`U ×_S U` of `W`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.squareOpens`: the open `W ∩ (U ×_S U)` of `W`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.opensRestrict`: it, as a diagonal open of `U ⟶ S`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isPullback_opensRestrictDiag`: `Δ_U` is the base
  change of `Δ` along `W_U ⊆ W`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isPullback_opensRestrictDiag_homOfLE`: for `V ⊆ U`,
  `Δ_V` is the base change of `Δ_U` along `W_V ⊆ W_U`.

## References

* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

/-- The second projection restricted to `W`, that is `pr₂|_W : W ⟶ X`. -/
abbrev projSnd : D.W ⟶ X := D.ι ≫ pullback.snd f f

/-- The diagonal `Δ : X ⟶ W` is a section of the first projection: `Δ ≫ pr₁|_W = 𝟙 X`. -/
@[reassoc (attr := simp)]
theorem diag_proj_eq_id : D.diag ≫ D.proj = 𝟙 X := by
  rw [proj, ← Category.assoc, D.fac, pullback.diagonal_fst]

/-- The diagonal `Δ : X ⟶ W` is a section of the second projection: `Δ ≫ pr₂|_W = 𝟙 X`. -/
@[reassoc (attr := simp)]
theorem diag_projSnd_eq_id : D.diag ≫ D.projSnd = 𝟙 X := by
  rw [projSnd, ← Category.assoc, D.fac, pullback.diagonal_snd]

/-- **The open `W ∩ (U ×_S U)` of `W`**: `pr₁⁻¹(U) ∩ pr₂⁻¹(U)`. -/
def squareOpens (U : X.Opens) : D.W.Opens :=
  D.proj ⁻¹ᵁ U ⊓ D.projSnd ⁻¹ᵁ U

/-- `W ∩ (U ×_S U) ⊆ pr₁⁻¹(U)`. -/
theorem squareOpens_le_proj (U : X.Opens) : D.squareOpens U ≤ D.proj ⁻¹ᵁ U :=
  inf_le_left

/-- `W ∩ (U ×_S U) ⊆ pr₂⁻¹(U)`. -/
theorem squareOpens_le_projSnd (U : X.Opens) : D.squareOpens U ≤ D.projSnd ⁻¹ᵁ U :=
  inf_le_right

variable {D} in
/-- For `V ⊆ U`, `W ∩ (V ×_S V) ⊆ W ∩ (U ×_S U)`. -/
theorem squareOpens_mono {U V : X.Opens} (h : V ≤ U) : D.squareOpens V ≤ D.squareOpens U :=
  inf_le_inf (D.proj.preimage_mono h) (D.projSnd.preimage_mono h)

/-- `W ∩ ((U ∩ V) ×_S (U ∩ V)) = (W ∩ (U ×_S U)) ∩ (W ∩ (V ×_S V))`. -/
theorem squareOpens_inf (U V : X.Opens) :
    D.squareOpens (U ⊓ V) = D.squareOpens U ⊓ D.squareOpens V := by
  simp only [squareOpens, Scheme.Hom.preimage_inf]
  ac_rfl

/-- `Δ⁻¹(W ∩ (U ×_S U)) = U`. -/
theorem diag_preimage_squareOpens (U : X.Opens) : D.diag ⁻¹ᵁ D.squareOpens U = U := by
  rw [squareOpens, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage, diag_proj_eq_id, diag_projSnd_eq_id, Scheme.Hom.id_preimage,
    inf_idem]

/-- A point `x` of `X` lies in `U` if and only if `Δ(x)` lies in `W ∩ (U ×_S U)`. -/
theorem diag_mem_squareOpens_iff {U : X.Opens} (x : X) :
    D.diag.base x ∈ D.squareOpens U ↔ x ∈ U := by
  conv_rhs => rw [← D.diag_preimage_squareOpens U]
  rfl

variable {D} in
/-- If `W ∩ (V ×_S V) ⊆ W ∩ (U ×_S U)`, then `V ⊆ U`. -/
theorem le_of_squareOpens_le {U V : X.Opens} (h : D.squareOpens V ≤ D.squareOpens U) : V ≤ U :=
  fun x hx => (D.diag_mem_squareOpens_iff x).1 (h ((D.diag_mem_squareOpens_iff x).2 hx))

variable (U : X.Opens)

/-- `W ∩ (U ×_S U) ⟶ U ×_S U`. -/
def opensRestrictIota : (D.squareOpens U).toScheme ⟶ pullback (U.ι ≫ f) (U.ι ≫ f) :=
  pullback.lift (D.proj.resLE U (D.squareOpens U) (D.squareOpens_le_proj U))
    (D.projSnd.resLE U (D.squareOpens U) (D.squareOpens_le_projSnd U)) (by
      rw [Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.resLE_comp_ι_assoc, Category.assoc,
        Category.assoc, pullback.condition])

/-- The first coordinate of `W ∩ (U ×_S U) ⟶ U ×_S U` is the restriction of `pr₁|_W`. -/
@[reassoc (attr := simp)]
theorem opensRestrictIota_fst :
    D.opensRestrictIota U ≫ pullback.fst (U.ι ≫ f) (U.ι ≫ f) =
      D.proj.resLE U (D.squareOpens U) (D.squareOpens_le_proj U) :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `W ∩ (U ×_S U) ⟶ U ×_S U` is the restriction of `pr₂|_W`. -/
@[reassoc (attr := simp)]
theorem opensRestrictIota_snd :
    D.opensRestrictIota U ≫ pullback.snd (U.ι ≫ f) (U.ι ≫ f) =
      D.projSnd.resLE U (D.squareOpens U) (D.squareOpens_le_projSnd U) :=
  pullback.lift_snd _ _ _

/-- The square formed by `W ∩ (U ×_S U) ⟶ U ×_S U`, `U ×_S U ⟶ X ×_S X`, and the inclusions
`W ∩ (U ×_S U) ⊆ W ⊆ X ×_S X` commutes. -/
theorem opensRestrictIota_pullbackOpensMap :
    D.opensRestrictIota U ≫ pullbackOpensMap U.ι = (D.squareOpens U).ι ≫ D.ι := by
  apply pullback.hom_ext <;> simp

/-- `W ∩ (U ×_S U) ⟶ U ×_S U` is an open immersion. -/
instance isOpenImmersion_opensRestrictIota : IsOpenImmersion (D.opensRestrictIota U) := by
  have := D.isOpenImmersion
  have : IsOpenImmersion (D.opensRestrictIota U ≫ pullbackOpensMap U.ι) := by
    rw [opensRestrictIota_pullbackOpensMap]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullbackOpensMap U.ι)

/-- `Δ_U : U ⟶ W ∩ (U ×_S U)`, the restriction of `Δ`. -/
def opensRestrictDiag : U.toScheme ⟶ (D.squareOpens U).toScheme :=
  D.diag.resLE (D.squareOpens U) U (D.diag_preimage_squareOpens U).ge

/-- `Δ_U` followed by the inclusion `W ∩ (U ×_S U) ⊆ W` is `U ⊆ X` followed by `Δ`. -/
@[reassoc (attr := simp)]
theorem opensRestrictDiag_ι : D.opensRestrictDiag U ≫ (D.squareOpens U).ι = U.ι ≫ D.diag :=
  Scheme.Hom.resLE_comp_ι _ _

/-- **`Δ_U` is the base change of `Δ` along `W ∩ (U ×_S U) ⊆ W`.** -/
theorem isPullback_opensRestrictDiag :
    IsPullback (D.opensRestrictDiag U) U.ι (D.squareOpens U).ι D.diag :=
  IsOpenImmersion.isPullback _ _ _ _ (D.opensRestrictDiag_ι U).symm (by
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, diag_preimage_squareOpens])

/-- `Δ_U : U ⟶ W ∩ (U ×_S U)` is a closed immersion. -/
instance isClosedImmersion_opensRestrictDiag : IsClosedImmersion (D.opensRestrictDiag U) := by
  have := D.isClosedImmersion
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (D.isPullback_opensRestrictDiag U).flip ‹_›

/-- `Δ_U` followed by `W ∩ (U ×_S U) ⟶ U ×_S U` is the relative diagonal of `U ⟶ S`. -/
theorem opensRestrictDiag_fac :
    D.opensRestrictDiag U ≫ D.opensRestrictIota U = pullback.diagonal (U.ι ≫ f) := by
  apply pullback.hom_ext <;> simp [← cancel_mono U.ι]

/-- **The diagonal open `W ∩ (U ×_S U)` of `U ⟶ X ⟶ S`**, an open of `W`. -/
abbrev opensRestrict : DiagonalOpen (U.ι ≫ f) where
  W := (D.squareOpens U).toScheme
  ι := D.opensRestrictIota U
  isOpenImmersion := inferInstance
  diag := D.opensRestrictDiag U
  isClosedImmersion := inferInstance
  fac := D.opensRestrictDiag_fac U

/-- The first projection of the diagonal open `W ∩ (U ×_S U)` of `U ⟶ S` is the restriction of
`pr₁|_W`. -/
theorem opensRestrict_proj :
    (D.opensRestrict U).proj = D.proj.resLE U (D.squareOpens U) (D.squareOpens_le_proj U) :=
  D.opensRestrictIota_fst U

/-- The first projection of `W ∩ (U ×_S U)` lies over that of `W`. -/
@[reassoc]
theorem opensRestrict_proj_ι : (D.opensRestrict U).proj ≫ U.ι = (D.squareOpens U).ι ≫ D.proj := by
  rw [opensRestrict_proj, Scheme.Hom.resLE_comp_ι]

/-- For `V ⊆ U`, the first projections of `W_V ⊆ W_U` lie over `V ⊆ U`. -/
@[reassoc]
theorem homOfLE_opensRestrict_proj {U V : X.Opens} (h : V ≤ U) :
    D.W.homOfLE (squareOpens_mono h) ≫ (D.opensRestrict U).proj =
      (D.opensRestrict V).proj ≫ X.homOfLE h := by
  rw [← cancel_mono U.ι, Category.assoc, opensRestrict_proj_ι, Scheme.homOfLE_ι_assoc,
    Category.assoc, Scheme.homOfLE_ι, opensRestrict_proj_ι]

/-- **For `V ⊆ U`, `Δ_V` is the base change of `Δ_U` along `W_V ⊆ W_U`.** -/
theorem isPullback_opensRestrictDiag_homOfLE {U V : X.Opens} (h : V ≤ U) :
    IsPullback (D.opensRestrict V).diag (X.homOfLE h) (D.W.homOfLE (squareOpens_mono h))
      (D.opensRestrict U).diag := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [← cancel_mono (D.squareOpens U).ι, Category.assoc, Category.assoc,
      Scheme.homOfLE_ι]
    show X.homOfLE h ≫ D.opensRestrictDiag U ≫ _ = D.opensRestrictDiag V ≫ _
    rw [opensRestrictDiag_ι, opensRestrictDiag_ι, Scheme.homOfLE_ι_assoc]
  · rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage]
    show (D.opensRestrictDiag U ≫ (D.squareOpens U).ι) ⁻¹ᵁ D.squareOpens V = _
    rw [opensRestrictDiag_ι, Scheme.Hom.comp_preimage, diag_preimage_squareOpens]

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
