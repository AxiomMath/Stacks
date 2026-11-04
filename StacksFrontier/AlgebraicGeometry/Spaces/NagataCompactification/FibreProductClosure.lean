module

public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.DenseOpenProperExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionDenseOpenInSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange

/-!
# The closure of a fibre product of two proper extensions

Let `π₁ : X₁ ⟶ Y` be proper and `π₂ : X₂ ⟶ Y` separated, let `ιᵢ : Vᵢ ⟶ Xᵢ` be open immersions,
and let `ψᵢ : Vᵢ ⟶ U` be proper morphisms to an algebraic space `U` separated over `Y`, with
`ψᵢ ≫ q = ιᵢ ≫ πᵢ`. The fibre product `V₁₂ = V₁ ×_U V₂` maps to `X₁ ×_Y X₂` by an immersion: a
closed immersion into `V₁ ×_Y V₂` (a base change of the diagonal of `U ⟶ Y`, Stacks 03KN)
followed by an open immersion. Let `X₁₂` be its scheme-theoretic image. Then

* `V₁₂ ⟶ X₁₂` is an open immersion with dense image (Stacks 088G),
* the projection `p₂ : X₁₂ ⟶ X₂` is proper, and
* `p₂⁻¹(V₂) = V₁₂`, at the level of points: `V₁₂ ⟶ V₂` is proper, so `V₁₂` is closed in the open
  set `p₂⁻¹(V₂)`, in which it is dense (the footnote to the proof of Stacks 0F4B).

This is the space `X₁₂` of the proof of Stacks 0F4B.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_pullbackMap_of_isOpenImmersion_of_isOpenImmersion`:
  `V₁ ×_Y V₂ ⟶ X₁ ×_Y X₂` is an open immersion.
* `AlgebraicGeometry.Space.isImmersion_pullbackMap_of_isSeparated`: `V₁ ×_U V₂ ⟶ X₁ ×_Y X₂` is an
  immersion.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_denseRange_closure_pullback`: the space `X₁₂`
  and its properties.

## References

* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
* [Stacks Project, Tag 088G](https://stacks.math.columbia.edu/tag/088G)
* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

variable {Y U V₁ V₂ X₁ X₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The square exhibiting `V ×_Y Z ⟶ X ×_Y Z` as the base change of `ι : V ⟶ X` along the first
projection. -/
theorem isPullback_pullbackMap_fst_of_comp (ι : V₁ ⟶ X₁) (π : X₁ ⟶ Y) (g : X₂ ⟶ Y) :
    IsPullback (pullback.map (ι ≫ π) g π g ι (𝟙 X₂) (𝟙 Y) (by simp) (by simp))
      (pullback.fst (ι ≫ π) g) (pullback.fst π g) ι :=
  IsPullback.of_right (by simpa using (IsPullback.of_hasPullback (ι ≫ π) g).flip) (by simp)
    (IsPullback.of_hasPullback π g).flip

/-- **A product of open immersions is an open immersion.** For open immersions `ιᵢ : Vᵢ ⟶ Xᵢ`
over `Y`, the morphism `V₁ ×_Y V₂ ⟶ X₁ ×_Y X₂` is an open immersion. -/
theorem isOpenImmersion_pullbackMap_of_isOpenImmersion_of_isOpenImmersion {ι₁ : V₁ ⟶ X₁}
    {ι₂ : V₂ ⟶ X₂} (hι₁ : IsOpenImmersion B S hS ι₁) (hι₂ : IsOpenImmersion B S hS ι₂)
    (π₁ : X₁ ⟶ Y) (π₂ : X₂ ⟶ Y) {f₁ : V₁ ⟶ Y} {f₂ : V₂ ⟶ Y} (e₁ : f₁ = ι₁ ≫ π₁)
    (e₂ : f₂ = ι₂ ≫ π₂) :
    IsOpenImmersion B S hS
      (pullback.map f₁ f₂ π₁ π₂ ι₁ ι₂ (𝟙 Y) (by simp [e₁]) (by simp [e₂])) := by
  subst e₁ e₂
  have hA : IsOpenImmersion B S hS
      (pullback.map (ι₁ ≫ π₁) (ι₂ ≫ π₂) (ι₁ ≫ π₁) π₂ (𝟙 V₁) ι₂ (𝟙 Y) (by simp) (by simp)) :=
    isOpenImmersion_snd_of_isPullback (isPullback_pullbackMap_snd ι₂ π₂ (ι₁ ≫ π₁)).flip hι₂
  have hB : IsOpenImmersion B S hS
      (pullback.map (ι₁ ≫ π₁) π₂ π₁ π₂ ι₁ (𝟙 X₂) (𝟙 Y) (by simp) (by simp)) :=
    isOpenImmersion_snd_of_isPullback (isPullback_pullbackMap_fst_of_comp ι₁ π₁ π₂).flip hι₁
  have he : pullback.map (ι₁ ≫ π₁) (ι₂ ≫ π₂) (ι₁ ≫ π₁) π₂ (𝟙 V₁) ι₂ (𝟙 Y) (by simp) (by simp) ≫
      pullback.map (ι₁ ≫ π₁) π₂ π₁ π₂ ι₁ (𝟙 X₂) (𝟙 Y) (by simp) (by simp) =
      pullback.map (ι₁ ≫ π₁) (ι₂ ≫ π₂) π₁ π₂ ι₁ ι₂ (𝟙 Y) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp
  rw [← he]
  exact isOpenImmersion_comp B S hS _ _ hA hB

/-- **The graph of a pair of extensions is an immersion** (Stacks 03KN). For `q : U ⟶ Y`
separated and open immersions `ιᵢ : Vᵢ ⟶ Xᵢ` with `ψᵢ ≫ q = ιᵢ ≫ πᵢ`, the morphism
`V₁ ×_U V₂ ⟶ X₁ ×_Y X₂` is an immersion: a base change of the diagonal of `q` followed by an
open immersion. -/
theorem isImmersion_pullbackMap_of_isSeparated {ψ₁ : V₁ ⟶ U} {ψ₂ : V₂ ⟶ U} {q : U ⟶ Y}
    {π₁ : X₁ ⟶ Y} {π₂ : X₂ ⟶ Y} {ι₁ : V₁ ⟶ X₁} {ι₂ : V₂ ⟶ X₂} (hq : IsSeparated B S hS q)
    (hι₁ : IsOpenImmersion B S hS ι₁) (hι₂ : IsOpenImmersion B S hS ι₂)
    (h₁ : ψ₁ ≫ q = ι₁ ≫ π₁) (h₂ : ψ₂ ≫ q = ι₂ ≫ π₂) :
    IsImmersion B S hS (pullback.map ψ₁ ψ₂ π₁ π₂ ι₁ ι₂ q h₁ h₂) := by
  have hc : IsClosedImmersion B S hS
      (pullback.map ψ₁ ψ₂ (ψ₁ ≫ q) (ψ₂ ≫ q) _ _ q (Category.id_comp _).symm
        (Category.id_comp _).symm) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback
      (pullback_map_diagonal_isPullback ψ₁ ψ₂ q) hq
  have ho := isOpenImmersion_pullbackMap_of_isOpenImmersion_of_isOpenImmersion hι₁ hι₂ π₁ π₂ h₁ h₂
  have he : pullback.map ψ₁ ψ₂ (ψ₁ ≫ q) (ψ₂ ≫ q) _ _ q (Category.id_comp _).symm
        (Category.id_comp _).symm ≫
      pullback.map (ψ₁ ≫ q) (ψ₂ ≫ q) π₁ π₂ ι₁ ι₂ (𝟙 Y) (by simp [h₁]) (by simp [h₂]) =
      pullback.map ψ₁ ψ₂ π₁ π₂ ι₁ ι₂ q h₁ h₂ := by
    apply pullback.hom_ext <;> simp
  rw [← he]
  exact isImmersion_comp B S hS _ _ (isImmersion_of_isClosedImmersion B S hS hc)
    (isImmersion_of_isOpenImmersion B S hS ho)

/-- The base change of a proper morphism `f` along `g` is proper, in the second projection. -/
private theorem isProper_pullback_snd {f : X₁ ⟶ Y} {g : X₂ ⟶ Y} (hX₁ : IsAlgebraicSpace B S hS X₁)
    (hX₂ : IsAlgebraicSpace B S hS X₂) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsProper B S hS f) : IsProper B S hS (pullback.snd f g) := by
  rw [← pullbackSymmetry_hom_comp_fst]
  exact isProper_comp B S hS (isAlgebraicSpace_pullback B S hS f g hX₁ hX₂ hY)
    (isAlgebraicSpace_pullback B S hS g f hX₂ hX₁ hY) hX₂ _ _ (isProper_of_isIso B S hS _)
    (isProper_pullback_fst B S hS hX₁ hY hX₂ f g hf)

/-- **The closure `X₁₂` of `V₁ ×_U V₂` in `X₁ ×_Y X₂`.** Let `π₁ : X₁ ⟶ Y` be proper and
`π₂ : X₂ ⟶ Y` separated, `ιᵢ : Vᵢ ⟶ Xᵢ` open immersions, `ψᵢ : Vᵢ ⟶ U` proper and
`q : U ⟶ Y` separated and quasi-compact, with `ψᵢ ≫ q = ιᵢ ≫ πᵢ`. Then there are an algebraic
space `X₁₂` (the scheme-theoretic image of `V₁ ×_U V₂` in `X₁ ×_Y X₂`), a dense open immersion
`k : V₁ ×_U V₂ ⟶ X₁₂` and projections `pᵢ : X₁₂ ⟶ Xᵢ` over `Y` restricting to `ιᵢ` on
`V₁ ×_U V₂`, such that `p₂` is proper and every point of `X₁₂` over `V₂` lies in `V₁ ×_U V₂`. -/
theorem exists_isOpenImmersion_denseRange_closure_pullback (hY : IsAlgebraicSpace B S hS Y)
    (hU : IsAlgebraicSpace B S hS U) (hV₁ : IsAlgebraicSpace B S hS V₁)
    (hV₂ : IsAlgebraicSpace B S hS V₂) (hX₁ : IsAlgebraicSpace B S hS X₁)
    (hX₂ : IsAlgebraicSpace B S hS X₂) {ψ₁ : V₁ ⟶ U} {ψ₂ : V₂ ⟶ U} {q : U ⟶ Y}
    {π₁ : X₁ ⟶ Y} {π₂ : X₂ ⟶ Y} {ι₁ : V₁ ⟶ X₁} {ι₂ : V₂ ⟶ X₂} (hψ₁ : IsProper B S hS ψ₁)
    (hψ₂ : IsProper B S hS ψ₂) (hq : IsSeparated B S hS q) (hqc : IsQuasiCompact B S hS q)
    (hπ₁ : IsProper B S hS π₁) (hπ₂ : IsSeparated B S hS π₂)
    (hι₁ : IsOpenImmersion B S hS ι₁) (hι₂ : IsOpenImmersion B S hS ι₂)
    (h₁ : ψ₁ ≫ q = ι₁ ≫ π₁) (h₂ : ψ₂ ≫ q = ι₂ ≫ π₂) :
    ∃ (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (k : pullback ψ₁ ψ₂ ⟶ P) (p₁ : P ⟶ X₁)
      (p₂ : P ⟶ X₂),
      IsAlgebraicSpace B S hS P ∧ IsOpenImmersion B S hS k ∧
      DenseRange (pointsMap B S hS _ k) ∧
      k ≫ p₁ = pullback.fst ψ₁ ψ₂ ≫ ι₁ ∧ k ≫ p₂ = pullback.snd ψ₁ ψ₂ ≫ ι₂ ∧
      p₁ ≫ π₁ = p₂ ≫ π₂ ∧ IsProper B S hS p₂ ∧
      pointsMap B S hS P p₂ ⁻¹' Set.range (pointsMap B S hS V₂ ι₂) ⊆
        Set.range (pointsMap B S hS _ k) := by
  have hV₁₂ : IsAlgebraicSpace B S hS (pullback ψ₁ ψ₂) :=
    isAlgebraicSpace_pullback B S hS ψ₁ ψ₂ hV₁ hV₂ hU
  have hX₁₂ : IsAlgebraicSpace B S hS (pullback π₁ π₂) :=
    isAlgebraicSpace_pullback B S hS π₁ π₂ hX₁ hX₂ hY
  set k₀ := pullback.map ψ₁ ψ₂ π₁ π₂ ι₁ ι₂ q h₁ h₂ with hk₀
  have himm : IsImmersion B S hS k₀ := isImmersion_pullbackMap_of_isSeparated hq hι₁ hι₂ h₁ h₂
  -- the two projections of `V₁ ×_U V₂` are proper
  have hfst : IsProper B S hS (pullback.fst ψ₁ ψ₂) :=
    isProper_pullback_fst B S hS hV₂ hU hV₁ ψ₂ ψ₁ hψ₂
  have hsnd : IsProper B S hS (pullback.snd ψ₁ ψ₂) :=
    isProper_pullback_snd hV₁ hV₂ hU hψ₁
  have hP₂ : IsProper B S hS (pullback.snd π₁ π₂) := isProper_pullback_snd hX₁ hX₂ hY hπ₁
  -- `k₀` is quasi-compact
  have hqc₀ : IsQuasiCompact B S hS k₀ := by
    refine isQuasiCompact_of_comp_of_isQuasiSeparated B S hS k₀ (pullback.snd π₁ π₂ ≫ π₂) hV₁₂ hY ?_
      (isQuasiSeparated_of_isSeparated B S hS (isSeparated_comp B S hS _ _ hP₂.1 hπ₂))
    have : k₀ ≫ pullback.snd π₁ π₂ ≫ π₂ = pullback.snd ψ₁ ψ₂ ≫ ψ₂ ≫ q := by
      rw [hk₀, pullback.lift_snd_assoc, Category.assoc, h₂]
    rw [this]
    exact isQuasiCompact_comp B S hS hV₂ hY _ _ hsnd.2.1.2
      (isQuasiCompact_comp B S hS hU hY _ _ hψ₂.2.1.2 hqc)
  obtain ⟨hopen, -, -, -, hdense⟩ :=
    isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced B S hS hV₁₂ hX₁₂ k₀ himm
      (Or.inl hqc₀)
  set I := schemeTheoreticImageSubfunctor B S hS k₀ with hI
  have hIc : IsClosedSubspace B S hS I :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS k₀ hX₁₂
  set k := toSchemeTheoreticImage B S hS k₀ with hk
  have hkι : k ≫ I.ι = k₀ := toSchemeTheoreticImage_ι B S hS k₀
  have hp₂ : IsProper B S hS (I.ι ≫ pullback.snd π₁ π₂) :=
    isProper_comp B S hS hIc.1 hX₁₂ hX₂ _ _
      (isProper_of_isClosedImmersion B S hS hIc.1 hX₁₂ _ hIc.2) hP₂
  have hkp₂ : k ≫ I.ι ≫ pullback.snd π₁ π₂ = pullback.snd ψ₁ ψ₂ ≫ ι₂ := by
    rw [reassoc_of% hkι, hk₀, pullback.lift_snd]
  refine ⟨I.toFunctor, k, I.ι ≫ pullback.fst π₁ π₂, I.ι ≫ pullback.snd π₁ π₂, hIc.1, hopen,
    hdense, ?_, hkp₂, by simp [pullback.condition], hp₂, ?_⟩
  · rw [reassoc_of% hkι, hk₀, pullback.lift_fst]
  · exact preimage_range_subset_range_of_denseRange hX₂ hIc.1 hV₂ hV₁₂ hp₂.1 hι₂ hsnd hkp₂ hdense

end AlgebraicGeometry.Space

end
