module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.LimitDescentHilbert
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.LimitDescentStage

/-!
# A relative cycle over a limit, after a completely decomposed proper cover, comes from a stage

Let `S = lim_i S_i` be the limit of a cofiltered system of Noetherian schemes with affine
transition morphisms, let `f₀ : X₀ ⟶ S_{i₀}` be of finite type and put `X = X₀ ×_{S_{i₀}} S`.
Let `α` be a family of `r`-cycles on the fibres of `X/S`, and suppose that there is a proper,
completely decomposed morphism `g : S' ⟶ S` of finite presentation such that `g^*α` is a cycle
class, that is, lies in the image of the cycle class map of Tag 0H6V. Then `α` is the base change
of a relative `r`-cycle on `X_i = X₀ ×_{S_{i₀}} S_i` over `S_i` for some stage `i`.

This is the descent argument of the surjectivity half of Lemma 0H5D, and the implication
(2) ⟹ (1) of Lemma 0H6W reduces to it. The cover `g` is descended to a stage by Limits,
Lemmas 01ZM and 081F and More on Morphisms, Lemma 0GTM
(`AlgebraicGeometry.exists_isProper_isCompletelyDecomposed_model_of_isLimit`); the members of
`Hilb` representing `g^*α` are descended to a later stage
(`Stacks.Chow.exists_map_ofIsPullback_eq`); and the resulting relative cycle on the descended
cover is descended along it (`Stacks.Chow.exists_relativeCycles_baseChangeFamily_eq_of_stage`).
What this file adds is the identification of the families of cycles at the three stages, through
the cartesian squares relating the fibre products involved.

## Main results

* `Stacks.Chow.exists_relativeCycles_baseChangeFamily_eq_of_pullbackInCycleClassImage`

## References

* [Stacks Project, Tag 0H5D](https://stacks.math.columbia.edu/tag/0H5D)
* [Stacks Project, Tag 0H6W](https://stacks.math.columbia.edu/tag/0H6W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **A family of cycles over a limit which becomes a cycle class after a completely decomposed
proper cover comes from a relative cycle at a finite stage.** Let `S = lim S_i` be the limit of a
cofiltered system of Noetherian schemes with affine transition morphisms, let `f₀ : X₀ ⟶ S_{i₀}`
be of finite type and let `α` be a family of `r`-cycles on the fibres of `X = X₀ ×_{S_{i₀}} S`
over `S`. If `g : S' ⟶ S` is proper, completely decomposed and locally of finite presentation and
`g^*α` lies in the image of the cycle class map of Tag 0H6V, then for some stage `u : i ⟶ i₀`
there is a relative `r`-cycle `αᵢ` on `X_i = X₀ ×_{S_{i₀}} S_i` over `S_i` whose base change to
`S` is `α`, read on `X` through the canonical isomorphism
`AlgebraicGeometry.limitComparison`.

The cover is descended to a stage, the members of `Hilb` representing `g^*α` to a later stage,
and the cycle class they define there is descended along the descended cover. -/
theorem exists_relativeCycles_baseChangeFamily_eq_of_pullbackInCycleClassImage {I : Type u}
    [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)] [∀ i, IsNoetherian (D.obj i)] (c : Cone D)
    (hc : IsLimit c) {i₀ : I} {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ D.obj i₀) [LocallyOfFiniteType f₀]
    [QuasiCompact f₀] (r : ℕ) (α : FamilyOfCycles (pullback.snd f₀ (c.π.app i₀)) r)
    {S' : Scheme.{u}} (g : S' ⟶ c.pt) [IsProper g] [LocallyOfFinitePresentation g]
    (hg : IsCompletelyDecomposed g)
    (hα : PullbackInCycleClassImage (pullback.snd f₀ (c.π.app i₀)) r α g) :
    ∃ (i : I) (u : i ⟶ i₀) (αᵢ : FamilyOfCycles (pullback.snd f₀ (D.map u)) r),
      αᵢ ∈ relativeCycles (pullback.snd f₀ (D.map u)) r ∧
      baseChangeFamily (pullback.snd f₀ (D.map u)) (c.π.app i) r αᵢ = fun s =>
        fiberCycleRestrict (pullback.snd f₀ (c.π.app i₀))
          (pullback.snd (pullback.snd f₀ (D.map u)) (c.π.app i))
          (limitComparison D c u f₀) (limitComparison_snd D c u f₀) s r (α s) := by
  -- Step 1: descend the cover to a stage `i`.
  obtain ⟨i, u, T, g₁, e, hprop₁, hlfp₁, hcd₁, he⟩ :=
    exists_isProper_isCompletelyDecomposed_model_of_isLimit D c hc g hg i₀
  have := hprop₁
  have hT : IsNoetherian T := isNoetherian_source_of_isProper g₁
  have hα₁ : PullbackInCycleClassImage (pullback.snd f₀ (c.π.app i₀)) r α
      (pullback.fst (c.π.app i) g₁) := by
    have h := pullbackInCycleClassImage_comp _ r α g e.inv hα
    rwa [show e.inv ≫ g = pullback.fst (c.π.app i) g₁ by rw [← he, Iso.inv_hom_id_assoc]] at h
  obtain ⟨C₀, hC₀⟩ := hα₁
  -- The scheme `Y = X_i ×_{S_i} T` over `T` and over `S_i`.
  let fᵢ := pullback.snd f₀ (D.map u)
  let ρ := pullback.snd fᵢ g₁
  let q := ρ ≫ g₁
  let F := overHom q g₁ ρ rfl
  have : LocallyOfFinitePresentation ρ := inferInstance
  have : QuasiCompact ρ := inferInstance
  have : CompactSpace ↥(pullback fᵢ g₁) := QuasiCompact.compactSpace_of_compactSpace ρ
  have : QuasiSeparatedSpace ↥(pullback fᵢ g₁) := quasiSeparatedSpace_of_quasiSeparated ρ
  -- `X = X_i ×_{S_i} S`.
  let θ : pullback f₀ (c.π.app i₀) ⟶ pullback f₀ (D.map u) :=
    pullback.lift (pullback.fst _ _) (pullback.snd f₀ (c.π.app i₀) ≫ c.π.app i) (by
      rw [pullback.condition, Category.assoc, c.w u])
  have sqθ : IsPullback θ (pullback.snd f₀ (c.π.app i₀)) fᵢ (c.π.app i) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, c.w u]
    exact IsPullback.of_hasPullback _ _
  -- The limit of `Y` over `S' = S ×_{S_i} T` is `X ×_S S'`.
  let ρL : pullback (c.π.app i) q ⟶ pullback (c.π.app i) g₁ :=
    AlgebraicGeometry.baseChangeMap (c.π.app i) (Over.mk q) (Over.mk g₁) F
  have S2 : IsPullback (pullback.fst fᵢ g₁) ρ fᵢ g₁ := IsPullback.of_hasPullback fᵢ g₁
  have S1 : IsPullback (pullback.snd (c.π.app i) q) ρL ρ (pullback.snd (c.π.app i) g₁) :=
    (baseChangeMap_isPullback (c.π.app i) (Over.mk q) (Over.mk g₁) F).flip
  have S12 := S1.paste_horiz S2
  have hcond : pullback.snd (c.π.app i) g₁ ≫ g₁ = pullback.fst (c.π.app i) g₁ ≫ c.π.app i :=
    pullback.condition.symm
  have hw : (pullback.snd (c.π.app i) q ≫ pullback.fst fᵢ g₁) ≫ fᵢ =
      (ρL ≫ pullback.fst (c.π.app i) g₁) ≫ c.π.app i := by
    rw [S12.w, Category.assoc, hcond]
  have sqY : IsPullback (sqθ.lift _ _ hw) ρL (pullback.snd f₀ (c.π.app i₀))
      (pullback.fst (c.π.app i) g₁) := by
    refine IsPullback.of_right ?_ (sqθ.lift_snd _ _ _) sqθ
    rw [sqθ.lift_fst, ← hcond]
    exact S12
  let ψ := sqY.isoPullback.hom
  have sqψ : IsPullback ψ ρL (pullback.snd (pullback.snd f₀ (c.π.app i₀))
      (pullback.fst (c.π.app i) g₁)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact sqY.isoPullback_hom_snd⟩
  let C₁ := FreeAbelianGroup.map (fun Z ↦ Z.ofIsPullback sqψ) C₀
  -- Step 2: descend the members of `Hilb` to a later stage `a`.
  obtain ⟨a, C', hC'⟩ := exists_map_ofIsPullback_eq D c hc q g₁ ρ rfl r C₁
  -- Step 3: the cycle class at the stage `a`, read on `X_a ×_{S_a} T_a`.
  let w := a.hom
  let fⱼ := pullback.snd f₀ (D.map (w ≫ u))
  let gⱼ := pullback.fst (D.map w) g₁
  have : IsProper gⱼ := inferInstance
  have hTⱼ : IsNoetherian (pullback (D.map w) g₁) := isNoetherian_source_of_isProper gⱼ
  have hcdⱼ : IsCompletelyDecomposed gⱼ := isCompletelyDecomposed_pullback_fst _ _ hcd₁
  let pⱼ := pullback.snd fⱼ gⱼ
  let ρa : pullback (D.map w) q ⟶ pullback (D.map w) g₁ :=
    AlgebraicGeometry.baseChangeMap (D.map w) (Over.mk q) (Over.mk g₁) F
  have R1 : IsPullback (pullback.snd (D.map w) q ≫ pullback.fst fᵢ g₁) ρa fᵢ
      (pullback.snd (D.map w) g₁ ≫ g₁) :=
    (show IsPullback (pullback.snd (D.map w) q) ρa ρ (pullback.snd (D.map w) g₁) from
      (baseChangeMap_isPullback (D.map w) (Over.mk q) (Over.mk g₁) F).flip).paste_horiz S2
  let θⱼ : pullback f₀ (D.map (w ≫ u)) ⟶ pullback f₀ (D.map u) :=
    pullback.lift (pullback.fst _ _) (fⱼ ≫ D.map w) (by
      rw [pullback.condition, Category.assoc, ← D.map_comp])
  have sqθⱼ : IsPullback θⱼ fⱼ fᵢ (D.map w) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, ← D.map_comp]
    exact IsPullback.of_hasPullback _ _
  have R2 : IsPullback (pullback.fst fⱼ gⱼ ≫ θⱼ) pⱼ fᵢ (pullback.snd (D.map w) g₁ ≫ g₁) := by
    rw [← pullback.condition]
    exact (IsPullback.of_hasPullback fⱼ gⱼ).paste_horiz sqθⱼ
  let σ := R2.isoIsPullback _ _ R1
  have sqσ : IsPullback σ.hom pⱼ ρa (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact R2.isoIsPullback_hom_snd _ _ R1⟩
  let C'' := FreeAbelianGroup.map (fun Z ↦ Z.ofIsPullback sqσ) C'
  have hα' : cycleClassMap pⱼ r C'' ∈ relativeCycles pⱼ r := by
    have h := (relativeCycleClassMap pⱼ C'').2
    rwa [relativeCycleClassMap_val] at h
  -- Step 4: the base change of this cycle class to `S ×_{S_a} T_a` is the base change of `α`.
  let τ := pullback.snd (c.π.app a.left) gⱼ
  let θT : pullback (c.π.app a.left) gⱼ ⟶ pullback (c.π.app i) g₁ :=
    pullback.lift (pullback.fst _ _) (τ ≫ pullback.snd (D.map w) g₁) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← pullback.condition,
        Category.assoc, c.w w])
  let πY : pullback (c.π.app i) q ⟶ pullback (D.map w) q :=
    (baseChangeCone D c i (Over.mk q)).π.app a
  let πT : pullback (c.π.app i) g₁ ⟶ pullback (D.map w) g₁ :=
    (baseChangeCone D c i (Over.mk g₁)).π.app a
  have sqc : IsPullback πY ρL ρa πT := baseChangeCone_π_isPullback D i F c a
  have hθT : θT ≫ πT = τ ≫ 𝟙 _ := by
    rw [Category.comp_id]
    refine pullback.hom_ext ?_ ?_
    · change θT ≫ πT ≫ pullback.fst (D.map w) g₁ = _
      rw [show πT ≫ pullback.fst (D.map w) g₁ = pullback.fst (c.π.app i) g₁ ≫ c.π.app a.left
        from baseChangeTransition_fst _ _ _ (c.w a.hom) _]
      rw [← Category.assoc, pullback.lift_fst, pullback.condition]
    · change θT ≫ πT ≫ pullback.snd (D.map w) g₁ = _
      rw [show πT ≫ pullback.snd (D.map w) g₁ = pullback.snd (c.π.app i) g₁
        from baseChangeTransition_snd _ _ _ (c.w a.hom) _, pullback.lift_snd]
  have L := (IsPullback.of_hasPullback pⱼ τ).paste_horiz sqσ
  have hζ : (pullback.fst pⱼ τ ≫ σ.hom) ≫ ρa = (pullback.snd pⱼ τ ≫ θT) ≫ πT := by
    rw [L.w, Category.assoc, hθT]
  let ζ := sqc.lift _ _ hζ
  have sqζ : IsPullback ζ (pullback.snd pⱼ τ) ρL θT := by
    refine IsPullback.of_right ?_ (sqc.lift_snd _ _ _) sqc
    rw [sqc.lift_fst, hθT]
    exact L
  have hbot : θT ≫ 𝟙 _ ≫ pullback.fst (c.π.app i) g₁ = pullback.fst (c.π.app a.left) gⱼ := by
    rw [Category.id_comp, pullback.lift_fst]
  have Big := sqζ.paste_horiz (sqψ.paste_horiz (IsPullback.of_hasPullback
    (pullback.snd f₀ (c.π.app i₀)) (pullback.fst (c.π.app i) g₁)))
  rw [hbot] at Big
  let Φ := Big.isoPullback.hom
  have hΦ₂ : Φ ≫ pullback.snd _ _ = pullback.snd pⱼ τ := Big.isoPullback_hom_snd
  have hΦ₁ : Φ ≫ pullback.fst _ _ ≫ pullback.fst f₀ (c.π.app i₀) =
      pullback.fst pⱼ τ ≫ pullback.fst fⱼ gⱼ ≫ pullback.fst f₀ (D.map (w ≫ u)) := by
    have e₁ : ψ ≫ pullback.fst (pullback.snd f₀ (c.π.app i₀)) (pullback.fst (c.π.app i) g₁) =
        sqθ.lift _ _ hw := sqY.isoPullback_hom_fst
    have e₂ : pullback.fst f₀ (c.π.app i₀) = θ ≫ pullback.fst f₀ (D.map u) :=
      (pullback.lift_fst _ _ _).symm
    have e₃ : ζ ≫ pullback.snd (c.π.app i) q =
        pullback.fst pⱼ τ ≫ σ.hom ≫ pullback.snd (D.map w) q := by
      have e : πY ≫ pullback.snd (D.map w) q = pullback.snd (c.π.app i) q :=
        baseChangeTransition_snd (D.map a.hom) (c.π.app i) (c.π.app a.left) (c.w a.hom)
          (Over.mk q)
      rw [← e, ← Category.assoc, sqc.lift_fst, Category.assoc]
    calc Φ ≫ pullback.fst _ _ ≫ pullback.fst f₀ (c.π.app i₀)
        = (Φ ≫ pullback.fst _ _) ≫ pullback.fst f₀ (c.π.app i₀) := (Category.assoc _ _ _).symm
      _ = (ζ ≫ ψ ≫ pullback.fst _ _) ≫ pullback.fst f₀ (c.π.app i₀) := by
          rw [Big.isoPullback_hom_fst]
      _ = ζ ≫ pullback.snd (c.π.app i) q ≫ pullback.fst fᵢ g₁ ≫ pullback.fst f₀ (D.map u) := by
          rw [e₁, e₂, Category.assoc, ← Category.assoc (sqθ.lift _ _ hw), sqθ.lift_fst,
            Category.assoc]
      _ = pullback.fst pⱼ τ ≫ (σ.hom ≫ pullback.snd (D.map w) q ≫ pullback.fst fᵢ g₁) ≫
            pullback.fst f₀ (D.map u) := by
          rw [← Category.assoc ζ, e₃]
          simp only [Category.assoc]
      _ = pullback.fst pⱼ τ ≫ pullback.fst fⱼ gⱼ ≫ pullback.fst f₀ (D.map (w ≫ u)) := by
          rw [R2.isoIsPullback_hom_fst _ _ R1, Category.assoc, pullback.lift_fst]
  have h : baseChangeFamily pⱼ τ r (cycleClassMap pⱼ r C'') = fun t =>
      fiberCycleRestrict (pullback.snd (pullback.snd f₀ (c.π.app i₀))
        (pullback.fst (c.π.app a.left) gⱼ)) (pullback.snd pⱼ τ) Φ hΦ₂ t r
        (baseChangeFamily (pullback.snd f₀ (c.π.app i₀)) (pullback.fst (c.π.app a.left) gⱼ)
          r α t) := by
    have : LocallyOfFinitePresentation ρa :=
      locallyOfFinitePresentation_baseChangeMap_overHom q g₁ ρ rfl _
    have : LocallyOfFinitePresentation ρL :=
      locallyOfFinitePresentation_baseChangeMap_overHom q g₁ ρ rfl _
    have hC'' : FreeAbelianGroup.map (fun Z ↦ Z.ofIsPullback sqc) C' = C₁ := hC'
    rw [← baseChangeFamilyOfIsPullback_eq (pullback.snd f₀ (c.π.app i₀)) Big r Φ
      Big.isoPullback_hom_fst hΦ₂ α, ← baseChangeFamilyOfIsPullback_of_hasPullback pⱼ (g := τ) r,
      HilbertCycleDatum.cycleClassMap_map_ofIsPullback sqσ C',
      baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback,
      baseChangeFamilyOfIsPullback_congr ρa (p := pullback.snd pⱼ τ) L (sqζ.paste_horiz sqc)
        (sqc.lift_fst _ _ hζ).symm hθT.symm r,
      ← baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback ρa sqc r sqζ,
      ← HilbertCycleDatum.cycleClassMap_map_ofIsPullback sqc C', hC'',
      HilbertCycleDatum.cycleClassMap_map_ofIsPullback sqψ C₀, hC₀,
      ← baseChangeFamilyOfIsPullback_of_hasPullback (pullback.snd f₀ (c.π.app i₀))
        (g := pullback.fst (c.π.app i) g₁) r α,
      baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback,
      baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback]
    exact baseChangeFamilyOfIsPullback_congr _ (p := pullback.snd pⱼ τ) _ _ rfl hbot r α
  -- Step 5: descend along the cover at the stage `a`.
  obtain ⟨j, v, αⱼ, hαⱼ, hbase⟩ := exists_relativeCycles_baseChangeFamily_eq_of_stage D c hc f₀ r
    α (w ≫ u) gⱼ hcdⱼ (cycleClassMap pⱼ r C'') hα' Φ hΦ₁ hΦ₂ h
  exact ⟨j, v ≫ w ≫ u, αⱼ, hαⱼ, hbase⟩

end Stacks.Chow

end
