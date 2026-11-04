module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceModel
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitOverRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Separatedness and finite type of a quotient by a closed étale equivalence relation

Let `Y` be an algebraic space over an object `V` of the big fppf site, with a surjective étale
atlas `q : h_N ⟶ Y` whose kernel pair is `R ⇉ N`. If `R ⟶ N ×_V N` is a closed immersion then
`Y ⟶ V` is separated: the diagonal of `Y` base-changes along the étale surjection
`h_{N ×_V N} ⟶ Y ×_V Y` to `R ⟶ N ×_V N` (Stacks 02WZ). If moreover `N` is affine and locally of
finite presentation over the affine `V`, then `Y ⟶ V` is of finite type.

These are the separatedness and finite type of the stage model of a separated space in the
proof of Stacks 0GI5.

## Main results

* `AlgebraicGeometry.Space.isSeparated_of_isClosedImmersion_lift_kernelPair`
* `AlgebraicGeometry.Space.isFiniteType_of_affine_atlas`

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A quotient by an étale equivalence relation closed in `N ×_V N` is separated over `V`.** -/
theorem isSeparated_of_isClosedImmersion_lift_kernelPair {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {V N R : BigFppfOver B S hS} (pY : Y ⟶ yoneda.obj V)
    {q : yoneda.obj N ⟶ Y}
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    {s t : R ⟶ N} (hR : IsPullback (yoneda.map s) (yoneda.map t) q q)
    {n₀ : N ⟶ V} (hn₀ : yoneda.map n₀ = q ≫ pY)
    (hci : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (pullback.lift s t (kernelPair_comp_eq hR hn₀)))) :
    IsSeparated B S hS pY := by
  let T := BigFppfOver.toScheme B S hS
  let ι := pullback.lift s t (kernelPair_comp_eq hR hn₀)
  have hY' : IsPullback (yoneda.map (pullback.fst n₀ n₀)) (yoneda.map (pullback.snd n₀ n₀))
      (q ≫ pY) (q ≫ pY) := by
    rw [← hn₀]
    exact (IsPullback.of_hasPullback n₀ n₀).map yoneda
  let m : yoneda.obj (pullback n₀ n₀) ⟶ pullback pY pY :=
    pullback.lift (yoneda.map (pullback.fst n₀ n₀) ≫ q) (yoneda.map (pullback.snd n₀ n₀) ≫ q)
      (by rw [Category.assoc, Category.assoc]; exact hY'.w)
  have hQ := pullback_map_diagonal_isPullback (f := q) (g := q) (i := pY)
  have hsq : IsPullback (yoneda.map s ≫ q) (yoneda.map ι) (pullback.diagonal pY) m := by
    refine hQ.of_iso hR.isoPullback.symm (Iso.refl _) hY'.isoPullback.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      rw [← Category.assoc, IsPullback.isoPullback_inv_fst]
    · simp only [Iso.symm_hom]
      rw [← cancel_mono hY'.isoPullback.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Category.assoc]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.comp_id, Category.assoc, Category.assoc,
          IsPullback.isoPullback_hom_fst, ← Functor.map_comp, pullback.lift_fst,
          IsPullback.isoPullback_inv_fst]
      · rw [pullback.lift_snd, Category.comp_id, Category.assoc, Category.assoc,
          IsPullback.isoPullback_hom_snd, ← Functor.map_comp, pullback.lift_snd,
          IsPullback.isoPullback_inv_snd]
    · simp
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc,
          IsPullback.isoPullback_inv_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc,
          IsPullback.isoPullback_inv_snd]
  have hcl : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) T).presheaf
      (yoneda.map ι) := (presheaf_yoneda_map_iff B S hS inferInstance ι).2 hci
  have hd := Stacks.SeparationLocal.relativelyRepresentable_diagonal B S hS hY pY
  have : MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Stacks.Descent.isLocalAtTarget_fppfPrecoverage _
  refine presheaf_of_etale_cover B S hS _ hd fun a g => ?_
  let g₁ := g ≫ pullback.fst pY pY
  let g₂ := g ≫ pullback.snd pY pY
  have chart : ∀ {a : BigFppfOver B S hS} (g : yoneda.obj a ⟶ Y),
      ∃ (b : BigFppfOver B S hS) (c : b ⟶ a) (e : yoneda.obj b ⟶ yoneda.obj N),
        e ≫ q = yoneda.map c ≫ g ∧ Surjective (T.map c) ∧ Etale (T.map c) :=
    fun g => ⟨_, hqe.rep.snd g, hqe.rep.fst g, hqe.rep.w g, hqs.property_snd g,
      hqe.property_snd g⟩
  obtain ⟨b₁, c₁, e₁, he₁, hc₁s, hc₁e⟩ := chart g₁
  obtain ⟨b, c₂, e₂, he₂, hc₂s, hc₂e⟩ := chart (yoneda.map c₁ ≫ g₂)
  let w₁ := yoneda.preimage (yoneda.map c₂ ≫ e₁)
  let w₂ := yoneda.preimage e₂
  have hw₁ : yoneda.map w₁ = yoneda.map c₂ ≫ e₁ := yoneda.map_preimage _
  have hw₂ : yoneda.map w₂ = e₂ := yoneda.map_preimage _
  have hw : w₁ ≫ n₀ = w₂ ≫ n₀ := yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, hw₁, hw₂, hn₀, Category.assoc, reassoc_of% he₁,
      reassoc_of% he₂]
    simp only [g₁, g₂, Category.assoc, pullback.condition])
  let w := pullback.lift w₁ w₂ hw
  have hwm : yoneda.map w ≫ m = yoneda.map (c₂ ≫ c₁) ≫ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, ← Functor.map_comp,
        pullback.lift_fst, hw₁, Category.assoc, he₁, Functor.map_comp]
      simp only [g₁, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ← Functor.map_comp,
        pullback.lift_snd, hw₂, he₂, Functor.map_comp]
      simp only [g₂, Category.assoc]
  refine ⟨b, c₂ ≫ c₁, ?_, ?_, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp]
    infer_instance
  · have sq := ((IsPullback.of_hasPullback ι w).map yoneda).paste_horiz hsq
    rw [hwm] at sq
    exact property_of_isPullback_of_isPullback B S hS (hd.isPullback _) sq
      (hcl.property _ _ _ ((IsPullback.of_hasPullback ι w).map yoneda))

/-- **A space with an affine étale atlas of finite presentation over an affine object is of
finite type over it.** -/
theorem isFiniteType_of_affine_atlas {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hY : IsAlgebraicSpace B S hS Y) {V N : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N)) (pY : Y ⟶ yoneda.obj V)
    {q : yoneda.obj N ⟶ Y}
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    {n₀ : N ⟶ V} (hn₀ : yoneda.map n₀ = q ≫ pY)
    (hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map n₀)) :
    IsFiniteType B S hS pY := by
  refine ⟨isLocallyOfFiniteType_of_exists_surjective_etale_source_chart B S hS
    ⟨N, q, hqs, hqe, ?_⟩, ?_⟩
  · rw [← hn₀]
    exact (isLocallyOfFiniteType_yoneda_map_iff B S hS n₀).2 hlft
  · have hqc : IsQuasiCompactSpace B S hS Y :=
      ⟨N, q, inferInstance, hqs, (isEtale_iff_presheaf_of_yoneda B S hS q).2 hqe⟩
    exact isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal
      (isAlgebraicSpace_yoneda B S hS V)
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS B.contains_terminal
        (isAffineSpace_yoneda B S hS V hV)) hqc pY

end AlgebraicGeometry.Space

end
