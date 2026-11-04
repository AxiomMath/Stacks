module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorSection

/-!
# The Gysin classes of the two constant sections of `X ×_A X`

Let `f : X ⟶ Spec A` be proper and smooth of relative dimension `n` with a section `σ`, and
`W = X ×_A X` with projections `p₁`, `p₂`. Besides the diagonal `Δ`, the proof of
[Stacks, Tag 0G8J] meets the two closed immersions

`j = (σ ∘ f, id) : X ⟶ W` (a section of `p₂`, with image `p₁⁻¹(σ(S))`) and
`j' = (id, σ ∘ f) : X ⟶ W` (a section of `p₁`, with image `p₂⁻¹(σ(S))`).

Their Gysin classes `γ^{0,0}(1)` are the pullbacks `p₁^*ξ` and `p₂^*ξ` of the Gysin class
`ξ = γ^{0,0}(1)` of the section ([Stacks, Tag 0G8D], the images being preimages of `σ(S)`), and
`(id, σ ∘ f)^*η = ξ` for the Gysin class `η` of the diagonal, as `(σ ∘ f, id)^*η = ξ`
(`Stacks.DeRham.CohomologicalGysin.pullbackHgroup_diagonalGysinUnitClass`).

## Main definitions

* `Stacks.DeRham.CohomologicalGysin.sectionSnd`, `Stacks.DeRham.CohomologicalGysin.sectionFst`: the
  sections `j' = (id, σ ∘ f)` of `p₁` and `j = (σ ∘ f, id)` of `p₂`.

## Main results

* `Stacks.DeRham.CohomologicalGysin.isPullback_section_snd`,
  `Stacks.DeRham.CohomologicalGysin.isPullback_section_fst`: `p₂⁻¹(σ(S)) = j'(X)` and
  `p₁⁻¹(σ(S)) = j(X)`, as cartesian squares.
* `Stacks.DeRham.CohomologicalGysin.pullbackHgroup_sectionGysinClass_snd`: `p₂^*ξ = γ_{j'}(1)`.
* `Stacks.DeRham.CohomologicalGysin.pullbackHgroup_sectionGysinClass_fst`: `p₁^*ξ = γ_j(1)`.
* `Stacks.DeRham.CohomologicalGysin.smoothOfRelativeDimension_fst`,
  `Stacks.DeRham.CohomologicalGysin.smoothOfRelativeDimension_snd`: both projections are smooth of
  relative dimension `n`.
* `Stacks.DeRham.CohomologicalGysin.isPullback_diagonal_section'`,
  `Stacks.DeRham.CohomologicalGysin.pullbackHgroup_diagonalGysinUnitClass'`: `(id, σ ∘ f)^*η = ξ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.Gysin Stacks.DeRham.GysinCohomologyBaseChange
open AlgebraicGeometry.Scheme.Hom Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.DeRham.CohomologicalGysin

section Squares

variable {S X : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- The section `(id, σ ∘ f) : X ⟶ X ×_S X` of the first projection. -/
abbrev sectionSnd : X ⟶ pullback f f :=
  pullback.lift (𝟙 X) (f ≫ σ) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

/-- The section `(σ ∘ f, id) : X ⟶ X ×_S X` of the second projection. -/
abbrev sectionFst : X ⟶ pullback f f :=
  pullback.lift (f ≫ σ) (𝟙 X) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

include hσ in
/-- **`p₂⁻¹(σ(S))` is the image of `(id, σ ∘ f)`**: the square with `(id, σ ∘ f) : X ⟶ X ×_S X`,
`p₂`, `f` and `σ` is cartesian. It is the left half of the cartesian square of `p₁`, `p₂` over
`f`, the outer rectangle being the identity of `f`. -/
theorem isPullback_section_snd :
    IsPullback f (sectionSnd f σ hσ) σ (pullback.snd f f) := by
  refine (IsPullback.of_right (h₁₂ := pullback.fst f f) (v₁₃ := f) (h₂₂ := f) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f f)).flip
  rw [pullback.lift_fst, hσ]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

include hσ in
/-- **`p₁⁻¹(σ(S))` is the image of `(σ ∘ f, id)`**: the square with `(σ ∘ f, id) : X ⟶ X ×_S X`,
`p₁`, `f` and `σ` is cartesian. -/
theorem isPullback_section_fst :
    IsPullback f (sectionFst f σ hσ) σ (pullback.fst f f) := by
  refine (IsPullback.of_right (h₁₂ := pullback.snd f f) (v₁₃ := f) (h₂₂ := f) ?_
    (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f f).flip).flip
  rw [pullback.lift_snd, hσ]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

variable [IsSeparated f]

include hσ in
omit [IsSeparated f] in
/-- **The pullback of the diagonal along `(id, σ ∘ f)` is the section**: the square with
`σ : S ⟶ X` on both sides, the diagonal and `(id, σ ∘ f)` is cartesian. It is the square of
`isPullback_section_diagonal` moved by the symmetry of `X ×_S X`, which fixes the diagonal and
exchanges `(σ ∘ f, id)` and `(id, σ ∘ f)`. -/
theorem isPullback_diagonal_section' :
    IsPullback σ σ (pullback.diagonal f)
      (sectionSnd f σ hσ) := by
  refine (isPullback_section_diagonal f σ hσ).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (pullbackSymmetry f f) (by simp) (by simp) ?_ ?_
  · apply pullback.hom_ext <;> simp
  · apply pullback.hom_ext <;> simp [pullback.lift_fst, pullback.lift_snd]

end Squares

section Classes

/-- A base change of the section `σ` of `f` to a section `i'` of `r` along `g` carries
the Gysin class of `σ` to the Gysin class of `i'` (the common core of the two lemmas below). -/
private theorem pullbackHgroup_sectionGysinClass_aux {A : Type u} [CommRing A] {X W : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (n : ℕ) [SmoothOfRelativeDimension n f] (σ : Spec (.of A) ⟶ X)
    [IsClosedImmersion σ] [LocallyOfFinitePresentation σ] [Smooth (σ ≫ f)]
    [FormallyUnramified (σ ≫ f)] (i' : X ⟶ W) (g r : W ⟶ X) (π' : W ⟶ Spec (.of A))
    [SmoothOfRelativeDimension n r] [Smooth π'] (hi : i' ≫ r = 𝟙 X) (hπ : g ≫ f = π')
    (hcart : IsPullback f i' σ g) :
    haveI : IsClosedImmersion i' :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hcart inferInstance
    haveI : LocallyOfFinitePresentation i' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hcart inferInstance
    haveI : Smooth r := SmoothOfRelativeDimension.smooth n r
    haveI : Smooth (i' ≫ r) := by rw [hi]; infer_instance
    haveI : FormallyUnramified (i' ≫ r) := by rw [hi]; infer_instance
    (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom)
      (0 : ℤ) (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega)
      (formsBaseChangeHom g f π' (𝟙 _) (by rw [Category.comp_id, hπ])
        (((0 : ℕ) : ℤ) + (n : ℤ)))).hom
      (sectionGysinClass f σ n) =
      gysinUnitClass i' π' (isKoszulRegularImmersion_of_smooth_of_smooth _ r)
        (conormalRank_of_formallyUnramified _ r n) := by
  have : IsClosedImmersion i' :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hcart inferInstance
  have : LocallyOfFinitePresentation i' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hcart inferInstance
  have : Smooth r := SmoothOfRelativeDimension.smooth n r
  have : Smooth (i' ≫ r) := by rw [hi]; infer_instance
  have : FormallyUnramified (i' ≫ r) := by rw [hi]; infer_instance
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hE := conormalRank_of_formallyUnramified σ f n
  have hE' := conormalRank_of_formallyUnramified i' r n
  rw [sectionGysinClass_eq_gysinUnitClass]
  exact pullbackHgroup_gysinUnitClass σ f _ f g π' (𝟙 _) hE hE' hcart _
    (Stacks.Immersion.isIso_immersionConormalSheafMap_of_conormalRank _ σ f _ hcart.flip hE' hE)
    (isKoszulRegularImmersion_of_smooth_of_smooth σ f)
    (isKoszulRegularImmersion_of_smooth_of_smooth _ r)

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
  (n : ℕ) [SmoothOfRelativeDimension n f] (σ : Spec (.of A) ⟶ X) [IsClosedImmersion σ]
  [LocallyOfFinitePresentation σ] [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)]

omit [IsProper f] in
/-- The second projection of `X ×_A X` is smooth of relative dimension `n`, as the base change of
`f` along `f`. -/
theorem smoothOfRelativeDimension_snd : SmoothOfRelativeDimension n (pullback.snd f f) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback
    (IsPullback.of_hasPullback f f) inferInstance

omit [IsProper f] in
/-- The first projection of `X ×_A X` is smooth of relative dimension `n`, as the base change of
`f` along `f`. -/
theorem smoothOfRelativeDimension_fst : SmoothOfRelativeDimension n (pullback.fst f f) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback
    (IsPullback.of_hasPullback f f).flip inferInstance

include σ in
omit [IsProper f] in
/-- **`p₂^*ξ` is the Gysin class of `(id, σ ∘ f)`** ([Stacks, Tag 0G8D]): `(id, σ ∘ f)` is the base
change of the section along `p₂`, and both are Koszul regular of conormal rank `n`. -/
theorem pullbackHgroup_sectionGysinClass_snd (hσ : σ ≫ f = 𝟙 _) :
    haveI : IsClosedImmersion (sectionSnd f σ hσ) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (isPullback_section_snd f σ hσ) inferInstance
    haveI : LocallyOfFinitePresentation (sectionSnd f σ hσ) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
        (isPullback_section_snd f σ hσ) inferInstance
    haveI := smoothOfRelativeDimension_fst f n
    haveI : Smooth (pullback.fst f f) := SmoothOfRelativeDimension.smooth n _
    haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
    haveI : Smooth (sectionSnd f σ hσ ≫ pullback.fst f f) := by
      simpa only [pullback.lift_fst] using (inferInstance : Smooth (𝟙 X))
    haveI : FormallyUnramified (sectionSnd f σ hσ ≫ pullback.fst f f) := by
      simpa only [pullback.lift_fst] using (inferInstance : FormallyUnramified (𝟙 X))
    (pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.snd f f).toLRSHom.toShHom)
      (0 : ℤ) (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega)
      (formsBaseChangeHom (pullback.snd f f) f (pullback.fst f f ≫ f) (𝟙 _)
        (by rw [Category.comp_id, pullback.condition]) (((0 : ℕ) : ℤ) + (n : ℤ)))).hom
      (sectionGysinClass f σ n) =
      gysinUnitClass (sectionSnd f σ hσ) (pullback.fst f f ≫ f)
        (isKoszulRegularImmersion_of_smooth_of_smooth _ (pullback.fst f f))
        (conormalRank_of_formallyUnramified _ (pullback.fst f f) n) := by
  have := smoothOfRelativeDimension_fst f n
  have : Smooth (pullback.fst f f) := SmoothOfRelativeDimension.smooth n _
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  exact pullbackHgroup_sectionGysinClass_aux f n σ (sectionSnd f σ hσ) (pullback.snd f f)
    (pullback.fst f f) _ (pullback.lift_fst _ _ _) pullback.condition.symm
    (isPullback_section_snd f σ hσ)

include σ in
omit [IsProper f] in
/-- **`p₁^*ξ` is the Gysin class of `(σ ∘ f, id)`** ([Stacks, Tag 0G8D]): `(σ ∘ f, id)` is the base
change of the section along `p₁`, and both are Koszul regular of conormal rank `n`. -/
theorem pullbackHgroup_sectionGysinClass_fst (hσ : σ ≫ f = 𝟙 _) :
    haveI : IsClosedImmersion (sectionFst f σ hσ) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (isPullback_section_fst f σ hσ) inferInstance
    haveI : LocallyOfFinitePresentation (sectionFst f σ hσ) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
        (isPullback_section_fst f σ hσ) inferInstance
    haveI := smoothOfRelativeDimension_snd f n
    haveI : Smooth (pullback.snd f f) := SmoothOfRelativeDimension.smooth n _
    haveI := smoothOfRelativeDimension_fst f n
    haveI : Smooth (pullback.fst f f) := SmoothOfRelativeDimension.smooth n _
    haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
    haveI : Smooth (sectionFst f σ hσ ≫ pullback.snd f f) := by
      simpa only [pullback.lift_snd] using (inferInstance : Smooth (𝟙 X))
    haveI : FormallyUnramified (sectionFst f σ hσ ≫ pullback.snd f f) := by
      simpa only [pullback.lift_snd] using (inferInstance : FormallyUnramified (𝟙 X))
    (pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.fst f f).toLRSHom.toShHom)
      (0 : ℤ) (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega)
      (formsBaseChangeHom (pullback.fst f f) f (pullback.fst f f ≫ f) (𝟙 _)
        (by rw [Category.comp_id]) (((0 : ℕ) : ℤ) + (n : ℤ)))).hom
      (sectionGysinClass f σ n) =
      gysinUnitClass (sectionFst f σ hσ) (pullback.fst f f ≫ f)
        (isKoszulRegularImmersion_of_smooth_of_smooth _ (pullback.snd f f))
        (conormalRank_of_formallyUnramified _ (pullback.snd f f) n) := by
  have := smoothOfRelativeDimension_snd f n
  have := smoothOfRelativeDimension_fst f n
  have : Smooth (pullback.fst f f) := SmoothOfRelativeDimension.smooth n _
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  exact pullbackHgroup_sectionGysinClass_aux f n σ (sectionFst f σ hσ) (pullback.fst f f)
    (pullback.snd f f) _ (pullback.lift_snd _ _ _) rfl (isPullback_section_fst f σ hσ)


include σ in
/-- **The pullback of the Gysin class of the diagonal along `(id, σ ∘ f)` is the Gysin class of
the section**: the mirror of `pullbackHgroup_diagonalGysinUnitClass`. The preimage of the
diagonal is the image of the section (`isPullback_diagonal_section'`), both conormal sheaves have
rank `n`, and [Stacks, Tag 0G8D] applies. -/
theorem pullbackHgroup_diagonalGysinUnitClass' (hσ : σ ≫ f = 𝟙 _) :
    haveI : LocallyOfFinitePresentation (pullback.diagonal f) := by
      have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
        rw [pullback.diagonal_fst]; infer_instance
      exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)
    haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
    (pullbackHgroup (CohomologyPullbackComparison.canonical
        (sectionSnd f σ hσ).toLRSHom.toShHom) (0 : ℤ)
      (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega)
      (formsBaseChangeHom (sectionSnd f σ hσ) (pullback.fst f f ≫ f) f (𝟙 _)
        (by rw [pullback.lift_fst_assoc, Category.id_comp, Category.comp_id])
        (((0 : ℕ) : ℤ) + (n : ℤ)))).hom
      (gysinUnitClass (pullback.diagonal f) (pullback.fst f f ≫ f)
        (diagonal_koszul_and_conormalRank f n).1 (diagonal_koszul_and_conormalRank f n).2) =
      sectionGysinClass f σ n := by
  have : LocallyOfFinitePresentation (pullback.diagonal f) := by
    have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
      rw [pullback.diagonal_fst]; infer_instance
    exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hcart := isPullback_diagonal_section' f σ hσ
  have hE := conormalRank_of_formallyUnramified σ f n
  rw [sectionGysinClass_eq_gysinUnitClass]
  exact pullbackHgroup_gysinUnitClass (pullback.diagonal f) (pullback.fst f f ≫ f) σ σ _ f (𝟙 _)
    (diagonal_koszul_and_conormalRank f n).2 hE hcart _
    (Stacks.Immersion.isIso_immersionConormalSheafMap_of_conormalRank σ (pullback.diagonal f) σ
      _ hcart.flip hE (diagonal_koszul_and_conormalRank f n).2)
    (diagonal_koszul_and_conormalRank f n).1 (isKoszulRegularImmersion_of_smooth_of_smooth σ f)

end Classes

end Stacks.DeRham.CohomologicalGysin

end
