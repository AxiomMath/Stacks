module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitWitnessHom

/-!
# A morphism descended to a finite stage restricts back to the given one over the limit

Let `c.pt = lim E k` be a cofiltered limit of affine objects of the big fppf site of `S`. For a
proper `p₁ : Y₁ ⟶ E i`, a `p₂ : Y₂ ⟶ E i` locally of finite presentation and a limit preserving
sheaf `G`, a morphism `a : c.pt ×_{E i} Y₁ ⟶ Y₂` over `E i` compatible with the maps to `G` is
the restriction of a morphism `a' : E k ×_{E i} Y₁ ⟶ Y₂` with the same compatibilities
(`AlgebraicGeometry.Space.exists_stage_hom_restricting_of_isLimit`). This is
`AlgebraicGeometry.Space.exists_stage_hom_of_isLimit` together with the restriction property, which
the existence and uniqueness halves of the proof of Stacks 0GI5 use.

## Main results

* `AlgebraicGeometry.Space.exists_stage_hom_restricting_of_isLimit`: the descent, with the
  restriction property.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Descent

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ BigFppfOver B S hS}
  {c : Cone E} (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
  (hE : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
  (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)) (i : I)

include hc hE hpt in
/-- **A morphism out of the base change to the limit of a proper algebraic space into an algebraic
space locally of finite presentation over a stage comes from a finite stage**, together with
its compatibilities with the maps to the stage and to a limit preserving sheaf `G`, and restricts
back to the given morphism over the limit. For a cofiltered limit `c.pt = lim E k` of affine
objects and `p₁ : Y₁ ⟶ E i` proper, `p₂ : Y₂ ⟶ E i` locally of finite presentation, a morphism
`a : c.pt ×_{E i} Y₁ ⟶ Y₂` over `E i` with `x₂ ∘ a = x₁ ∘ pr` is defined over some
`E k ×_{E i} Y₁` with the same two properties, by a morphism `a'` whose restriction along
`c.pt ×_{E i} Y₁ ⟶ E k ×_{E i} Y₁` is `a`. This strengthens
`AlgebraicGeometry.Space.exists_stage_hom_of_isLimit` by the last property.

Choose an affine étale atlas `N ⟶ Y₁` (`Y₁` is quasi-compact) with kernel pair `R`, affine because
`Y₁` is separated. The restriction of `a` to `c.pt ×_{E i} N` comes from a stage by relative
limit preservation of `p₂` (Stacks 04AK); its two pullbacks to the stages of `R` agree in the
limit, hence at a stage, and so do its composite with `x₂` and the restriction of `x₁` (limit
preservation of `G`); then it descends along the atlas `E k ×_{E i} N ⟶ E k ×_{E i} Y₁`
(Stacks 0262). This replaces Stacks 07SK, which needs the index category to be small for the
site. -/
theorem exists_stage_hom_restricting_of_isLimit
    {Y₁ Y₂ G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY₂ : IsAlgebraicSpace B S hS Y₂)
    (hGs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hG : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) G)
    (p₁ : Y₁ ⟶ yoneda.obj (E.obj i)) (hp₁ : IsProper B S hS p₁)
    (p₂ : Y₂ ⟶ yoneda.obj (E.obj i)) (hp₂ : IsLocallyOfFinitePresentation B S hS p₂)
    (x₁ : Y₁ ⟶ G) (x₂ : Y₂ ⟶ G) (a : pullback (yoneda.map (c.π.app i)) p₁ ⟶ Y₂)
    (hap : a ≫ p₂ = pullback.fst (yoneda.map (c.π.app i)) p₁ ≫ yoneda.map (c.π.app i))
    (hax : a ≫ x₂ = pullback.snd (yoneda.map (c.π.app i)) p₁ ≫ x₁) :
    ∃ (k : Over i) (a' : pullback (yoneda.map (E.map k.hom)) p₁ ⟶ Y₂),
      a' ≫ p₂ = pullback.fst (yoneda.map (E.map k.hom)) p₁ ≫ yoneda.map (E.map k.hom) ∧
        a' ≫ x₂ = pullback.snd (yoneda.map (E.map k.hom)) p₁ ≫ x₁ ∧
          pullback.lift (pullback.fst (yoneda.map (c.π.app i)) p₁ ≫ yoneda.map (c.π.app k.left))
            (pullback.snd (yoneda.map (c.π.app i)) p₁) (by
              rw [Category.assoc, ← Functor.map_comp, c.w k.hom, pullback.condition]) ≫ a' = a := by
  have hVi := isAlgebraicSpace_yoneda B S hS (E.obj i)
  have hrel := relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hY₂ hVi hp₂
  -- an affine étale atlas of `Y₁` and its kernel pair
  have hqc : IsQuasiCompactSpace B S hS Y₁ :=
    isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS (E.obj i) (hE i) hY₁ hVi p₁ hp₁.2.2
  obtain ⟨N, n, hN, hnsurj, hnet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y₁ hY₁).1 hqc
  have hnet' := (isEtale_iff_presheaf_of_yoneda B S hS n).1 hnet
  obtain ⟨R, s, t, hR⟩ := exists_kernelPair_of_etale_atlas B S hS n hnet'
  have hRaff : IsAffine ((BigFppfOver.toScheme B S hS).obj R) :=
    isAffine_of_isAbsolutelySeparated B S hS B.contains_terminal
      (isAbsolutelySeparated_of_isSeparated_to_affine B S hS B.contains_terminal (E.obj i) (hE i)
        p₁ hp₁.1) hR hN hN
  let n₀ : N ⟶ E.obj i := yoneda.preimage (n ≫ p₁)
  have hn₀ : yoneda.map n₀ = n ≫ p₁ := yoneda.map_preimage _
  have hst : s ≫ n₀ = t ≫ n₀ := yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, hn₀, ← Category.assoc, ← Category.assoc, hR.w])
  let r₀ : R ⟶ E.obj i := s ≫ n₀
  -- the restriction of `a` to `c.pt ×_{E i} N`
  let ν := chartToPullbackYoneda p₁ n n₀ hn₀ (c.π.app i)
  have hb : (ν ≫ a) ≫ p₂ = yoneda.map (pullback.snd (c.π.app i) n₀ ≫ n₀) := by
    rw [Category.assoc, hap, chartToPullbackYoneda_fst_assoc, ← Functor.map_comp,
      pullback.condition]
  obtain ⟨k₁, b₁, hb₁p, hb₁⟩ :=
    exists_stage_lift_of_isLimit_baseChange hc hE hpt i p₂ hrel hN n₀ (ν ≫ a) hb
  -- its two pullbacks to the kernel pair agree in the limit
  have hsr : s ≫ n₀ = r₀ := rfl
  have htr : t ≫ n₀ = r₀ := hst.symm
  let D₁ := overBaseChangeDiagram E i n₀
  let D₂ := overBaseChangeDiagram E i r₀
  let C₁ := overBaseChangeCone E c i n₀
  let C₂ := overBaseChangeCone E c i r₀
  have hDsnd : ∀ {k k' : Over i} (g : k' ⟶ k), D₁.map g ≫ pullback.snd (E.map k.hom) n₀ =
      pullback.snd (E.map k'.hom) n₀ := fun g => pullback.lift_snd _ _ _
  have hCsnd : ∀ k : Over i, C₁.π.app k ≫ pullback.snd (E.map k.hom) n₀ =
      pullback.snd (c.π.app i) n₀ := fun k => pullback.lift_snd _ _ _
  have hD₂ : ∀ {k k' : Over i} (g : k' ⟶ k) (u : R ⟶ N) (hu : u ≫ n₀ = r₀),
      D₂.map g ≫ pullbackMapRight (E.map k.hom) u hu =
        pullbackMapRight (E.map k'.hom) u hu ≫ D₁.map g := by
    intro k k' g u hu
    apply pullback.hom_ext <;> simp [D₁, D₂, pullbackMapRight]
  have hC₂ : ∀ (k : Over i) (u : R ⟶ N) (hu : u ≫ n₀ = r₀),
      C₂.π.app k ≫ pullbackMapRight (E.map k.hom) u hu =
        pullbackMapRight (c.π.app i) u hu ≫ C₁.π.app k := by
    intro k u hu
    apply pullback.hom_ext <;> simp [C₁, C₂, pullbackMapRight]
  let βs := yoneda.map (pullbackMapRight (E.map k₁.hom) s hsr) ≫ b₁
  let βt := yoneda.map (pullbackMapRight (E.map k₁.hom) t htr) ≫ b₁
  have hβ : ∀ (u : R ⟶ N) (hu : u ≫ n₀ = r₀),
      (yoneda.map (pullbackMapRight (E.map k₁.hom) u hu) ≫ b₁) ≫ p₂ =
        yoneda.map (pullback.snd (E.map k₁.hom) r₀ ≫ r₀) := by
    intro u hu
    rw [Category.assoc, hb₁p, ← Functor.map_comp, pullbackMapRight_snd_assoc, hu]
  have hνst : yoneda.map (pullbackMapRight (c.π.app i) s hsr) ≫ ν =
      yoneda.map (pullbackMapRight (c.π.app i) t htr) ≫ ν := by
    apply pullback.hom_ext
    · simp only [ν, Category.assoc, chartToPullbackYoneda_fst, ← Functor.map_comp,
        pullbackMapRight_fst]
    · rw [Category.assoc, Category.assoc, chartToPullbackYoneda_snd,
        ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        pullbackMapRight_snd, pullbackMapRight_snd, Functor.map_comp, Functor.map_comp,
        Category.assoc, Category.assoc, hR.w]
  have hlimR : yoneda.map (C₂.π.app k₁) ≫ βs = yoneda.map (C₂.π.app k₁) ≫ βt := by
    simp only [βs, βt, ← Category.assoc, ← Functor.map_comp, hC₂]
    simp only [Functor.map_comp, Category.assoc]
    rw [hb₁, ← Category.assoc, hνst, Category.assoc]
  obtain ⟨k₂, g₂, hg₂⟩ := exists_stage_eq_of_isLimit_baseChange hc hE hpt i p₂ hrel hRaff r₀ k₁
    βs βt (hβ s hsr) (hβ t htr) hlimR
  -- the composite with `x₂` and the restriction of `x₁` agree in the limit
  let b₂ := yoneda.map (D₁.map g₂) ≫ b₁
  have hb₂lim : yoneda.map (C₁.π.app k₂) ≫ b₂ = ν ≫ a := by
    simp only [b₂, ← Category.assoc, ← Functor.map_comp]
    rwa [C₁.w g₂]
  have hlimx : yoneda.map (C₁.π.app k₂) ≫ (b₂ ≫ x₂) =
      yoneda.map (C₁.π.app k₂) ≫ (yoneda.map (pullback.snd (E.map k₂.hom) n₀) ≫ n ≫ x₁) := by
    rw [← Category.assoc, hb₂lim, Category.assoc, hax, ← Category.assoc ν,
      chartToPullbackYoneda_snd, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, hCsnd,
      Category.assoc]
  obtain ⟨k₃, g₃, hg₃⟩ := exists_stage_eq_of_limitPreserving hc hE hpt i G hG hN n₀ k₂ _ _ hlimx
  -- the stage `k₃`
  let b₃ := yoneda.map (D₁.map g₃) ≫ b₂
  have hb₃p : b₃ ≫ p₂ = yoneda.map (pullback.snd (E.map k₃.hom) n₀ ≫ n₀) := by
    simp only [b₃, b₂, Category.assoc, hb₁p, ← Functor.map_comp]
    rw [← Category.assoc (D₁.map g₂), hDsnd, ← Category.assoc, hDsnd]
  have hb₃x : b₃ ≫ x₂ = yoneda.map (pullback.snd (E.map k₃.hom) n₀) ≫ n ≫ x₁ := by
    rw [Category.assoc, hg₃, ← Category.assoc, ← Functor.map_comp, hDsnd]
  have hb₃R : yoneda.map (pullbackMapRight (E.map k₃.hom) s hsr) ≫ b₃ =
      yoneda.map (pullbackMapRight (E.map k₃.hom) t htr) ≫ b₃ := by
    have e : ∀ (u : R ⟶ N) (hu : u ≫ n₀ = r₀),
        yoneda.map (pullbackMapRight (E.map k₃.hom) u hu) ≫ b₃ =
          yoneda.map (D₂.map g₃) ≫ yoneda.map (D₂.map g₂) ≫
            (yoneda.map (pullbackMapRight (E.map k₁.hom) u hu) ≫ b₁) := by
      intro u hu
      simp only [b₃, b₂, ← Category.assoc, ← Functor.map_comp]
      rw [hD₂]
    rw [e s hsr, e t htr]
    exact congrArg (yoneda.map (D₂.map g₃) ≫ ·) hg₂
  -- descend along the atlas of `E k₃ ×_{E i} Y₁`
  let ν₃ := chartToPullbackYoneda p₁ n n₀ hn₀ (E.map k₃.hom)
  have hpb₃ := isPullback_chartToPullbackYoneda p₁ n n₀ hn₀ (E.map k₃.hom)
  have het₃ := presheaf_of_isPullback B S hS hpb₃ hnet'
  have hsurj₃ := presheaf_of_isPullback B S hS hpb₃ hnsurj
  have hY₁₃ := isAlgebraicSpace_pullback B S hS (yoneda.map (E.map k₃.hom)) p₁
    (isAlgebraicSpace_yoneda B S hS _) hY₁ hVi
  obtain ⟨a', ha', -⟩ := existsUnique_hom_of_atlas_invariant B S hS hY₁₃.isSheaf hY₂.isSheaf ν₃
    hsurj₃ het₃ b₃ (by
      intro R' s' t' hsq
      have hw := hsq.w
      have hfst : s' ≫ pullback.fst (E.map k₃.hom) n₀ = t' ≫ pullback.fst (E.map k₃.hom) n₀ :=
        yoneda.map_injective (by
          have := congrArg (· ≫ pullback.fst (yoneda.map (E.map k₃.hom)) p₁) hw
          simpa only [ν₃, Category.assoc, chartToPullbackYoneda_fst, ← Functor.map_comp] using this)
      have hsnd : yoneda.map (s' ≫ pullback.snd (E.map k₃.hom) n₀) ≫ n =
          yoneda.map (t' ≫ pullback.snd (E.map k₃.hom) n₀) ≫ n := by
        have := congrArg (· ≫ pullback.snd (yoneda.map (E.map k₃.hom)) p₁) hw
        simpa only [ν₃, Category.assoc, chartToPullbackYoneda_snd, Functor.map_comp] using this
      let ρ₀ : R' ⟶ R := yoneda.preimage (hR.lift _ _ hsnd)
      have hρs : ρ₀ ≫ s = s' ≫ pullback.snd (E.map k₃.hom) n₀ := yoneda.map_injective (by
        rw [Functor.map_comp, yoneda.map_preimage, hR.lift_fst])
      have hρt : ρ₀ ≫ t = t' ≫ pullback.snd (E.map k₃.hom) n₀ := yoneda.map_injective (by
        rw [Functor.map_comp, yoneda.map_preimage, hR.lift_snd])
      let τ : R' ⟶ pullback (E.map k₃.hom) r₀ :=
        pullback.lift (s' ≫ pullback.fst _ _) ρ₀ (by
          rw [Category.assoc, pullback.condition, ← Category.assoc, ← hρs, Category.assoc])
      have hτs : τ ≫ pullbackMapRight (E.map k₃.hom) s hsr = s' := by
        apply pullback.hom_ext
        · simp [τ]
        · simp [τ, hρs]
      have hτt : τ ≫ pullbackMapRight (E.map k₃.hom) t htr = t' := by
        apply pullback.hom_ext
        · simp [τ, hfst]
        · simp [τ, hρt]
      rw [← hτs, ← hτt, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hb₃R])
  refine ⟨k₃, a', ?_, ?_, ?_⟩
  rotate_left 2
  · have hY₁c := isAlgebraicSpace_pullback B S hS (yoneda.map (c.π.app i)) p₁
      (isAlgebraicSpace_yoneda B S hS _) hY₁ hVi
    have hpbc := isPullback_chartToPullbackYoneda p₁ n n₀ hn₀ (c.π.app i)
    refine hom_ext_of_etale_atlas B S hS hY₁c.isSheaf hY₂.isSheaf ν
      (presheaf_of_isPullback B S hS hpbc hnsurj) (presheaf_of_isPullback B S hS hpbc hnet') ?_
    have hνm : ν ≫ pullback.lift (pullback.fst (yoneda.map (c.π.app i)) p₁ ≫
        yoneda.map (c.π.app k₃.left)) (pullback.snd (yoneda.map (c.π.app i)) p₁) (by
          rw [Category.assoc, ← Functor.map_comp, c.w k₃.hom, pullback.condition]) =
        yoneda.map (C₁.π.app k₃) ≫ ν₃ := by
      apply pullback.hom_ext
      · simp [ν, ν₃, C₁, ← Functor.map_comp]
      · simp only [ν, ν₃, C₁, Category.assoc, pullback.lift_snd, chartToPullbackYoneda_snd]
        rw [← Category.assoc, ← Functor.map_comp, pullback.lift_snd]
    rw [← Category.assoc, hνm, Category.assoc, ha', ← hb₂lim]
    simp only [b₃, ← Category.assoc, ← Functor.map_comp]
    rw [show C₁.π.app k₃ ≫ D₁.map g₃ = C₁.π.app k₂ from (C₁.w g₃)]
  · refine hom_ext_of_etale_atlas B S hS hY₁₃.isSheaf hVi.isSheaf ν₃ hsurj₃ het₃ ?_
    rw [← Category.assoc, ha', hb₃p, ← Category.assoc, chartToPullbackYoneda_fst,
      ← Functor.map_comp, pullback.condition]
  · refine hom_ext_of_etale_atlas B S hS hY₁₃.isSheaf hGs ν₃ hsurj₃ het₃ ?_
    rw [← Category.assoc, ha', hb₃x, chartToPullbackYoneda_snd_assoc]

end Descent

end AlgebraicGeometry.Space

end
