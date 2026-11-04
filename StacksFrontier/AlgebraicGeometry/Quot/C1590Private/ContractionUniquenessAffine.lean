module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ContractionUniquenessNoetherian
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.NoetherianModelContraction

/-!
# Uniqueness of contractions near a point of an affine base

Let `S` be an affine scheme and `t : Spec K ⟶ S` a field-valued point over `s ∈ S`, let `X`, `Y₁`,
`Y₂` be proper flat schemes of finite presentation over `S` and let `cᵢ : X ⟶ Yᵢ` be morphisms over
`S`. Suppose the fibres `Y₁,ₜ`, `Y₂,ₜ` over `Spec K` are identified compatibly with `c₁,ₜ`, `c₂,ₜ`,
that the fibres of `c₁,ₜ` have dimension at most one, and that `𝒪_{Y₁,ₜ} ≅ c₁,ₜ,*𝒪_{Xₜ}` and
`R¹c₁,ₜ,*𝒪_{Xₜ} = 0`. Then there are an open neighbourhood `U` of `s` and an isomorphism
`Y₁|_U ≅ Y₂|_U` over `U` compatible with `c₁` and `c₂`.

This is [Stacks, Tag 0E89] for schemes over an affine base, proved as the source proves it: the
configuration has a Noetherian model over some `S₀`
(`AlgebraicGeometry.C1590Private.exists_noetherianModel_pair`), the fibre data move to the image of
`t` in `S₀` and then to the residue field of its image point
(`AlgebraicGeometry.C1590Private.fibreData_residueField_of_fieldPoint`), the locally Noetherian
case (`AlgebraicGeometry.C1590Private.exists_open_iso_of_residueFibre_of_isLocallyNoetherian`)
applies over `S₀`, and its conclusion pulls back to `S`.

## Main results

* `AlgebraicGeometry.C1590Private.exists_open_iso_of_fieldFibre_of_isAffine`: the statement above.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

/-- **Uniqueness of contractions near a point of an affine base** ([Stacks, Tag 0E89] for schemes
over an affine base). Let `S` be affine, `t : Spec K ⟶ S` a field-valued point over `s`, let `X`,
`Y₁`, `Y₂` be proper flat schemes of finite presentation over `S` and `cᵢ : X ⟶ Yᵢ` morphisms over
`S`. Let `φ : Y₁,ₜ ≅ Y₂,ₜ` be an isomorphism of the fibres over `Spec K` with `c₁,ₜ ≫ φ = c₂,ₜ`. If
the fibres of `c₁,ₜ` have dimension at most one, `𝒪_{Y₁,ₜ} ≅ c₁,ₜ,*𝒪_{Xₜ}` and
`R¹c₁,ₜ,*𝒪_{Xₜ} = 0`, there are an open `U ∋ s` and an isomorphism `ψ : Y₁|_U ≅ Y₂|_U` over `U`
compatible with `c₁` and `c₂`. -/
theorem exists_open_iso_of_fieldFibre_of_isAffine {S : Scheme.{u}} [IsAffine S] {K : Type u}
    [Field K] (t : Spec (.of K) ⟶ S) (s : S) (hs : t (IsLocalRing.closedPoint K) = s)
    {X Y₁ Y₂ : Scheme.{u}} (fX : X ⟶ S) (fY₁ : Y₁ ⟶ S) (fY₂ : Y₂ ⟶ S)
    [IsProper fX] [Flat fX] [LocallyOfFinitePresentation fX] [IsProper fY₁] [Flat fY₁]
    [LocallyOfFinitePresentation fY₁] [IsProper fY₂] [Flat fY₂] [LocallyOfFinitePresentation fY₂]
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    (φ : pullback fY₁ t ≅ pullback fY₂ t) (hφ : φ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hφc : fibreHom t fX fY₁ c₁ hc₁ ≫ φ.hom = fibreHom t fX fY₂ c₂ hc₂)
    (hdim : ∀ y, topologicalKrullDim ((fibreHom t fX fY₁ c₁ hc₁).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit (fibreHom t fX fY₁ c₁ hc₁)))
    (hR : IsZero (((Scheme.Modules.pushforward (fibreHom t fX fY₁ c₁ hc₁)).rightDerived 1).obj
      (SheafOfModules.unit (pullback fX t).ringCatSheaf))) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ ψ : (fY₁ ⁻¹ᵁ U).toScheme ≅ (fY₂ ⁻¹ᵁ U).toScheme,
      ψ.hom ≫ (fY₂ ⁻¹ᵁ U).ι ≫ fY₂ = (fY₁ ⁻¹ᵁ U).ι ≫ fY₁ ∧
      ∀ a : (fX ⁻¹ᵁ U).toScheme ⟶ (fY₁ ⁻¹ᵁ U).toScheme,
        a ≫ (fY₁ ⁻¹ᵁ U).ι = (fX ⁻¹ᵁ U).ι ≫ c₁ →
          a ≫ ψ.hom ≫ (fY₂ ⁻¹ᵁ U).ι = (fX ⁻¹ᵁ U).ι ≫ c₂ := by
  obtain ⟨S₀, π, hS₀, -, X₀, Y₁₀, Y₂₀, fX₀, fY₁₀, fY₂₀, gX, gY₁, gY₂, c₁₀, c₂₀,
    ⟨hX₁, hX₂, hX₃⟩, ⟨hY₁₁, hY₁₂, hY₁₃⟩, ⟨hY₂₁, hY₂₂, hY₂₃⟩, sqX, sqY₁, sqY₂, hc₁₀, hc₂₀, hcc₁,
    hcc₂⟩ := exists_noetherianModel_pair fX fY₁ fY₂ c₁ hc₁ c₂ hc₂
  have : IsProper c₁ := by subst hc₁; exact IsProper.of_comp c₁ fY₁
  -- the fibre data at `t ≫ π`
  set t₀ := t ≫ π
  have hst : t ≫ π = 𝟙 _ ≫ t₀ := (Category.id_comp _).symm
  have hsq₁ : IsPullback gX c₁ c₁₀ gY₁ :=
    IsPullback.of_bot (by rw [hc₁, hc₁₀]; exact sqX) hcc₁.symm sqY₁
  have hsq₂ : IsPullback gX c₂ c₂₀ gY₂ :=
    IsPullback.of_bot (by rw [hc₂, hc₂₀]; exact sqX) hcc₂.symm sqY₂
  have H₁ := isPullback_fibreHom hst fX₀ fY₁₀ fX fY₁ gX gY₁ sqX.w.symm sqY₁.w.symm c₁₀ hc₁₀ c₁
    hc₁ hcc₁ hsq₁
  have H₂ := isPullback_fibreHom hst fX₀ fY₂₀ fX fY₂ gX gY₂ sqX.w.symm sqY₂.w.symm c₂₀ hc₂₀ c₂
    hc₂ hcc₂ hsq₂
  set mX := fibreMap hst fX₀ fX gX sqX.w.symm
  set m₁ := fibreMap hst fY₁₀ fY₁ gY₁ sqY₁.w.symm
  set m₂ := fibreMap hst fY₂₀ fY₂ gY₂ sqY₂.w.symm
  have : IsIso mX := (isPullback_fibreMap hst fX₀ fX gX sqX.w.symm sqX).isIso_fst_of_isIso
  have : IsIso m₁ := (isPullback_fibreMap hst fY₁₀ fY₁ gY₁ sqY₁.w.symm sqY₁).isIso_fst_of_isIso
  have : IsIso m₂ := (isPullback_fibreMap hst fY₂₀ fY₂ gY₂ sqY₂.w.symm sqY₂).isIso_fst_of_isIso
  have : IsProper (fibreHom t₀ fX₀ fY₁₀ c₁₀ hc₁₀) :=
    MorphismProperty.of_isPullback (isPullback_fibreHom_fst t₀ fX₀ fY₁₀ c₁₀ hc₁₀)
      (by subst hc₁₀; exact IsProper.of_comp c₁₀ fY₁₀)
  have hdim₀ : ∀ y, topologicalKrullDim ((fibreHom t₀ fX₀ fY₁₀ c₁₀ hc₁₀).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞) := by
    intro y
    obtain ⟨y', rfl⟩ := m₁.surjective y
    exact Stacks.AlgebraicGeometry.TopDegreeBaseChange.topologicalKrullDim_fiber_le_of_isPullback'
      H₁ 1 y' (hdim y')
  obtain ⟨h0₀, hR₀⟩ := fibreConditions_of_isPullback_of_surjective H₁ hdim₀ h0 hR
  let φ₀ : pullback fY₁₀ t₀ ≅ pullback fY₂₀ t₀ := (asIso m₁).symm ≪≫ φ ≪≫ asIso m₂
  have hm₁ : m₁ ≫ pullback.snd fY₁₀ t₀ = pullback.snd fY₁ t := by
    rw [fibreMap_snd, Category.comp_id]
  have hm₂ : m₂ ≫ pullback.snd fY₂₀ t₀ = pullback.snd fY₂ t := by
    rw [fibreMap_snd, Category.comp_id]
  have hφ₀ : φ₀.hom ≫ pullback.snd fY₂₀ t₀ = pullback.snd fY₁₀ t₀ := by
    simp only [φ₀, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc, hm₂, hφ,
      IsIso.inv_comp_eq, hm₁]
  have hφc₀ : fibreHom t₀ fX₀ fY₁₀ c₁₀ hc₁₀ ≫ φ₀.hom = fibreHom t₀ fX₀ fY₂₀ c₂₀ hc₂₀ := by
    rw [← cancel_epi mX]
    simp only [φ₀, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, ← Category.assoc]
    rw [H₁.w]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [reassoc_of% hφc, H₂.w]
  -- the locally Noetherian case over `S₀`
  have hs₀ : t₀ (IsLocalRing.closedPoint K) = π s := congrArg (fun z => π z) hs
  obtain ⟨φ', hφ', hφc', hdim', h0', hR'⟩ := fibreData_residueField_of_fieldPoint t₀ (π s) hs₀
    fX₀ fY₁₀ fY₂₀ c₁₀ hc₁₀ c₂₀ hc₂₀ φ₀ hφ₀ hφc₀ hdim₀ h0₀ hR₀
  obtain ⟨U₀, hsU₀, ψ₀, hψ₀, hcψ₀⟩ := exists_open_iso_of_residueFibre_of_isLocallyNoetherian (π s)
    fX₀ fY₁₀ fY₂₀ c₁₀ hc₁₀ c₂₀ hc₂₀ φ' hφ' hφc' hdim' h0' hR'
  -- pulling the isomorphism back along `π`
  set U := π ⁻¹ᵁ U₀
  have hmem : ∀ {Z Z₀ : Scheme.{u}} (fZ : Z ⟶ S) (fZ₀ : Z₀ ⟶ S₀) (gZ : Z ⟶ Z₀)
      (_ : gZ ≫ fZ₀ = fZ ≫ π) (z : (fZ ⁻¹ᵁ U).toScheme), fZ₀ (((fZ ⁻¹ᵁ U).ι ≫ gZ) z) ∈ U₀ :=
    fun fZ fZ₀ gZ hg z => by
      rw [← Scheme.Hom.comp_apply, Category.assoc, hg, ← Category.assoc, Scheme.Hom.comp_apply]
      exact z.2
  set r₁ := toPreimage fY₁₀ U₀ ((fY₁ ⁻¹ᵁ U).ι ≫ gY₁) (hmem fY₁ fY₁₀ gY₁ sqY₁.w)
  set r₂ := toPreimage fY₂₀ U₀ ((fY₂ ⁻¹ᵁ U).ι ≫ gY₂) (hmem fY₂ fY₂₀ gY₂ sqY₂.w)
  set rX := toPreimage fX₀ U₀ ((fX ⁻¹ᵁ U).ι ≫ gX) (hmem fX fX₀ gX sqX.w)
  have hψ₀' : ψ₀.inv ≫ (fY₁₀ ⁻¹ᵁ U₀).ι ≫ fY₁₀ = (fY₂₀ ⁻¹ᵁ U₀).ι ≫ fY₂₀ := by
    rw [← hψ₀, ψ₀.inv_hom_id_assoc]
  set n₁ := sqY₂.lift (r₁ ≫ ψ₀.hom ≫ (fY₂₀ ⁻¹ᵁ U₀).ι) ((fY₁ ⁻¹ᵁ U).ι ≫ fY₁) (by
    rw [Category.assoc, Category.assoc, hψ₀, toPreimage_ι_assoc, Category.assoc, sqY₁.w,
      Category.assoc])
  set n₂ := sqY₁.lift (r₂ ≫ ψ₀.inv ≫ (fY₁₀ ⁻¹ᵁ U₀).ι) ((fY₂ ⁻¹ᵁ U).ι ≫ fY₂) (by
    rw [Category.assoc, Category.assoc, hψ₀', toPreimage_ι_assoc, Category.assoc, sqY₂.w,
      Category.assoc])
  set Ψ₁ := toPreimage fY₂ U n₁ (mem_of_comp_eq fY₂ U n₁ (sqY₂.lift_snd _ _ _))
  set Ψ₂ := toPreimage fY₁ U n₂ (mem_of_comp_eq fY₁ U n₂ (sqY₁.lift_snd _ _ _))
  have hΨ₁r : Ψ₁ ≫ r₂ = r₁ ≫ ψ₀.hom := by
    rw [← cancel_mono (fY₂₀ ⁻¹ᵁ U₀).ι, Category.assoc, toPreimage_ι, toPreimage_ι_assoc,
      sqY₂.lift_fst, Category.assoc]
  have hΨ₂r : Ψ₂ ≫ r₁ = r₂ ≫ ψ₀.inv := by
    rw [← cancel_mono (fY₁₀ ⁻¹ᵁ U₀).ι, Category.assoc, toPreimage_ι, toPreimage_ι_assoc,
      sqY₁.lift_fst, Category.assoc]
  refine ⟨U, hsU₀, ⟨Ψ₁, Ψ₂, ?_, ?_⟩, ?_, ?_⟩
  · rw [← cancel_mono (fY₁ ⁻¹ᵁ U).ι, Category.assoc, Category.id_comp]
    apply sqY₁.hom_ext
    · rw [Category.assoc, Category.assoc, toPreimage_ι_assoc, sqY₁.lift_fst, ← Category.assoc Ψ₁,
        hΨ₁r, Category.assoc, Iso.hom_inv_id_assoc, toPreimage_ι]
    · rw [Category.assoc, Category.assoc, toPreimage_ι_assoc, sqY₁.lift_snd, toPreimage_ι_assoc,
        sqY₂.lift_snd]
  · rw [← cancel_mono (fY₂ ⁻¹ᵁ U).ι, Category.assoc, Category.id_comp]
    apply sqY₂.hom_ext
    · rw [Category.assoc, Category.assoc, toPreimage_ι_assoc, sqY₂.lift_fst, ← Category.assoc Ψ₂,
        hΨ₂r, Category.assoc, Iso.inv_hom_id_assoc, toPreimage_ι]
    · rw [Category.assoc, Category.assoc, toPreimage_ι_assoc, sqY₂.lift_snd, toPreimage_ι_assoc,
        sqY₁.lift_snd]
  · rw [toPreimage_ι_assoc, sqY₂.lift_snd]
  · intro a ha
    set r' := toPreimage fY₁₀ U₀ ((fX₀ ⁻¹ᵁ U₀).ι ≫ c₁₀) (fun x => by
      rw [← Scheme.Hom.comp_apply, Category.assoc, hc₁₀]
      exact x.2)
    have har : a ≫ r₁ = rX ≫ r' := by
      rw [← cancel_mono (fY₁₀ ⁻¹ᵁ U₀).ι, Category.assoc, toPreimage_ι, reassoc_of% ha,
        Category.assoc, toPreimage_ι, toPreimage_ι_assoc, Category.assoc, hcc₁]
    have hψ := hcψ₀ r' (toPreimage_ι _ _ _ _)
    rw [toPreimage_ι]
    apply sqY₂.hom_ext
    · rw [Category.assoc, sqY₂.lift_fst, reassoc_of% har, hψ, toPreimage_ι_assoc, Category.assoc,
        Category.assoc, hcc₂]
    · rw [Category.assoc, sqY₂.lift_snd, reassoc_of% ha, hc₁, Category.assoc, hc₂]

end AlgebraicGeometry.C1590Private

end
