module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceRelation

/-!
# The normalization of an algebraic space, glued along one étale presentation

Let `F` be an algebraic space over `S`, let `w : h_U ⟶ F` be a surjective étale chart of `F`
and let `pr₁, pr₂ : R ⟶ U` exhibit `R` as `U ×_F U`.
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceRelation` makes the normalizations
`R^ν ⇉ U^ν` an étale equivalence relation; this file forms its quotient sheaf, equips it with a
morphism to `F`, and identifies `U^ν` with the fibre product of the quotient with the chart.

That identification is the chart condition of `AlgebraicGeometry.Space.NormalizationData` at
the chart the quotient was built from. The chart condition at an *arbitrary* surjective étale
chart is the subject of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceArbitraryChart`.

## Main definitions

* `AlgebraicGeometry.Space.NormSpaceGluing.normQuotient` is the quotient sheaf `U^ν/R^ν`, with
  `AlgebraicGeometry.Space.NormSpaceGluing.normQuotientMap` the quotient map from `U^ν`.
* `AlgebraicGeometry.Space.NormSpaceGluing.normQuotientToBase` is the normalization morphism
  `U^ν/R^ν ⟶ F`.

## Main results

* `AlgebraicGeometry.Space.NormSpaceGluing.isAlgebraicSpace_normQuotient`: the quotient is an
  algebraic space over `S`, by Tag 02WW.
* `AlgebraicGeometry.Space.NormSpaceGluing.isPullback_normQuotientMap`: the quotient map
  exhibits `U^ν` as the fibre product of the quotient with the chart.

## Implementation notes

This is the absolute-normalization counterpart of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasQuotient`, with the *source* of the
relative normalization absent: an absolute normalization datum has no canonical morphism from a
source and no factorization to record, so only one of the two legs is built here.

The cartesianness of the chart square is proved by showing that the comparison morphism
`h_{U^ν} ⟶ (U^ν/R^ν) ×_F U` is a monomorphism and locally surjective. Monomorphy is a
computation with the kernel pair of the quotient map and the diagonal of the relation, with no
locality: two points of `U^ν` with the same image in the quotient differ by a point of `R^ν`,
and if they also agree in `U` then that point lies on the diagonal. Local surjectivity is the
base change of local surjectivity of the quotient map, which is Tag 05VM. The two generic
steps — that a monomorphism of sheaves which is locally surjective is an isomorphism, and that
the quotient map is a surjective étale atlas — are reused from
`AlgebraicGeometry.Space.NormalizationGluing` rather than restated.

## References

* [Stacks Project, Tag 02WV](https://stacks.math.columbia.edu/tag/02WV)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space.NormSpaceGluing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U R : BigFppfOver B S hS}
  (w : yoneda.obj U ⟶ F) (pr₁ pr₂ : R ⟶ U)
  (hsq : IsPullback (yoneda.map pr₁) (yoneda.map pr₂) w w)
  (hwet : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w)
  (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
      (irreducibleComponents V).Finite)
  (hR : ∀ V : ((BigFppfOver.toScheme B S hS).obj R).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj R)) →
      (irreducibleComponents V).Finite)
  (hR₂ : ∀ V : ((BigFppfOver.toScheme B S hS).obj (Limits.pullback pr₂ pr₁)).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj (Limits.pullback pr₂ pr₁))) →
      (irreducibleComponents V).Finite)

/-! ### The quotient sheaf and its atlas -/

/-- **The normalization of `F`, glued along the presentation `R ⇉ U`**: the quotient sheaf of
the étale equivalence relation formed by the normalizations of the charts. -/
def normQuotient : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR)
      (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR))).obj

/-- The quotient map from the normalization of the chart onto the glued normalization. -/
def normQuotientMap : yoneda.obj (normSpace B S hS U hU) ⟶
    normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR :=
  quotientMap B S hS (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR)
    (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR)

include hsq hwet hR₂ in
/-- **Stacks 02WW.** The glued normalization is an algebraic space over `S`. -/
theorem isAlgebraicSpace_normQuotient :
    IsAlgebraicSpace B S hS (normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR) :=
  have _ := isEtaleEquivalenceRelation_normRel B S hS w pr₁ pr₂ hsq hwet hU hR hR₂
  isAlgebraicSpace_quotient_unconditional B S hS _ _

include hsq hwet hR₂ in
/-- **Stacks 02WV.** The relation is the kernel pair of the quotient map. -/
theorem isPullback_normQuotientMap_self :
    IsPullback (yoneda.map (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR))
      (yoneda.map (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR))
      (normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR)
      (normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR) :=
  have _ := isEtaleEquivalenceRelation_normRel B S hS w pr₁ pr₂ hsq hwet hU hR hR₂
  quotientMap_isPullback B S hS _ _

include hsq hwet hR₂ in
/-- **Stacks 02WW.** The quotient map is surjective. -/
theorem surjective_normQuotientMap :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR) :=
  have _ := isEtaleEquivalenceRelation_normRel B S hS w pr₁ pr₂ hsq hwet hU hR hR₂
  quotientMap_surjective_unconditional B S hS _ _

include hsq hwet hR₂ in
/-- **Stacks 02WW.** The quotient map is étale. -/
theorem etale_normQuotientMap :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR) :=
  have _ := isEtaleEquivalenceRelation_normRel B S hS w pr₁ pr₂ hsq hwet hU hR hR₂
  quotientMap_etale_unconditional B S hS _ _

/-! ### The normalization morphism of the glued object -/

variable (hF : IsAlgebraicSpace B S hS F)

include hsq hwet hR₂ hF in
/-- The glued normalization maps to `F`: the normalization morphisms of the charts are
invariant under the relation, so they descend along the quotient map. -/
theorem existsUnique_normQuotientToBase :
    ∃! d : normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR ⟶ F,
      normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR ≫ d =
        yoneda.map (normSpaceProj B S hS U hU) ≫ w := by
  refine existsUnique_desc_of_surjective_etale_atlas B S hS
    (isAlgebraicSpace_normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR hR₂).isSheaf _
    (isPullback_normQuotientMap_self B S hS w pr₁ pr₂ hsq hwet hU hR hR₂)
    (surjective_normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR hR₂)
    (etale_normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR hR₂) hF.isSheaf _ ?_
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    normRelSnd_comp_normSpaceProj, normRelFst_comp_normSpaceProj, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc, hsq.w]

/-- **The normalization morphism of the glued normalization.** -/
def normQuotientToBase : normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR ⟶ F :=
  (existsUnique_normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF).choose

/-- The quotient map followed by `normQuotientToBase` is the normalization morphism of the chart
followed by `w`. -/
@[reassoc]
lemma normQuotientMap_comp_normQuotientToBase :
    normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR ≫
        normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF =
      yoneda.map (normSpaceProj B S hS U hU) ≫ w :=
  (existsUnique_normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF).choose_spec.1

/-! ### The chart condition at the chart the quotient was built from -/

/-- The comparison morphism from the normalization of the chart to the fibre product of the
glued normalization with the chart. -/
def normQuotientChartComparison :
    yoneda.obj (normSpace B S hS U hU) ⟶
      Limits.pullback (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w :=
  Limits.pullback.lift (normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR)
    (yoneda.map (normSpaceProj B S hS U hU))
    (normQuotientMap_comp_normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF)

/-- The first component of `normQuotientChartComparison` is the quotient map. -/
@[reassoc]
lemma normQuotientChartComparison_comp_fst :
    normQuotientChartComparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF ≫
        Limits.pullback.fst
          (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w =
      normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR :=
  Limits.pullback.lift_fst _ _ _

/-- The second component of `normQuotientChartComparison` is the normalization morphism of the
chart. -/
@[reassoc]
lemma normQuotientChartComparison_comp_snd :
    normQuotientChartComparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF ≫
        Limits.pullback.snd
          (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w =
      yoneda.map (normSpaceProj B S hS U hU) :=
  Limits.pullback.lift_snd _ _ _

include hsq hwet hR₂ hF in
/-- **The comparison morphism is a monomorphism.** Two points of the chart normalization with
the same image in the glued normalization differ by a point of the relation, by Tag 02WV; if
they moreover agree in the chart, that point lies on the diagonal of the relation, and the two
points are equal. -/
theorem mono_normQuotientChartComparison :
    Mono (normQuotientChartComparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) := by
  have hker := isPullback_normQuotientMap_self B S hS w pr₁ pr₂ hsq hwet hU hR hR₂
  have hA := (isPullback_normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR).map yoneda
  have hBq := (isPullback_normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR).map yoneda
  have hdiag : ∀ p : R ⟶ U, NormalizationGluing.relDiag B S hS w pr₁ pr₂ hsq ≫ p = 𝟙 U →
      normRelDiag B S hS w pr₁ pr₂ hsq hwet hU hR ≫ normSpaceProj B S hS R hR ≫ p =
        normSpaceProj B S hS U hU := fun p hp => by
    rw [← Category.assoc, normRelDiag_comp_normSpaceProj, Category.assoc, hp, Category.comp_id]
  refine ⟨fun {Z} a b hab => ?_⟩
  have h1 : a ≫ normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR =
      b ≫ normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR := by
    rw [← normQuotientChartComparison_comp_fst B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF,
      ← Category.assoc, hab, Category.assoc]
  have h2 : a ≫ yoneda.map (normSpaceProj B S hS U hU) =
      b ≫ yoneda.map (normSpaceProj B S hS U hU) := by
    rw [← normQuotientChartComparison_comp_snd B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF,
      ← Category.assoc, hab, Category.assoc]
  have hr1 : hker.lift a b h1 ≫
      yoneda.map (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR) = a := hker.lift_fst _ _ _
  have hr2 : hker.lift a b h1 ≫
      yoneda.map (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR) = b := hker.lift_snd _ _ _
  have side : ∀ (p : R ⟶ U) (e : normSpace B S hS R hR ⟶ normSpace B S hS U hU),
      yoneda.map e ≫ yoneda.map (normSpaceProj B S hS U hU) =
        yoneda.map (normSpaceProj B S hS R hR) ≫ yoneda.map p →
      hker.lift a b h1 ≫ yoneda.map e ≫ yoneda.map (normSpaceProj B S hS U hU) =
        b ≫ yoneda.map (normSpaceProj B S hS U hU) →
      NormalizationGluing.relDiag B S hS w pr₁ pr₂ hsq ≫ p = 𝟙 U →
      (hker.lift a b h1 ≫ yoneda.map (normSpaceProj B S hS R hR)) ≫ yoneda.map p =
        ((b ≫ yoneda.map (normRelDiag B S hS w pr₁ pr₂ hsq hwet hU hR)) ≫
          yoneda.map (normSpaceProj B S hS R hR)) ≫ yoneda.map p := by
    intro p e he hb hp
    rw [Category.assoc, ← he, hb, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, hdiag p hp]
  have key : hker.lift a b h1 =
      b ≫ yoneda.map (normRelDiag B S hS w pr₁ pr₂ hsq hwet hU hR) := by
    refine hA.hom_ext ?_ (hsq.hom_ext ?_ ?_)
    · rw [hr2, Category.assoc, ← Functor.map_comp, normRelDiag_comp_normRelFst,
        CategoryTheory.Functor.map_id, Category.comp_id]
    · refine side pr₁ _ hA.w ?_ (NormalizationGluing.relDiag_comp_pr₁ B S hS w pr₁ pr₂ hsq)
      rw [← Category.assoc, hr2]
    · refine side pr₂ _ hBq.w ?_ (NormalizationGluing.relDiag_comp_pr₂ B S hS w pr₁ pr₂ hsq)
      rw [← Category.assoc, hr1, h2]
  rw [← hr1, key, Category.assoc, ← Functor.map_comp, normRelDiag_comp_normRelSnd,
    CategoryTheory.Functor.map_id, Category.comp_id]

include hsq hwet hR₂ hF in
/-- **The relation is the base change of the quotient map along the fibre product with the
chart.** -/
theorem isPullback_normRelSnd_comp_comparison :
    IsPullback (yoneda.map (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR))
      (yoneda.map (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR) ≫
        normQuotientChartComparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF)
      (normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR)
      (Limits.pullback.fst
        (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w) := by
  have hker := isPullback_normQuotientMap_self B S hS w pr₁ pr₂ hsq hwet hU hR hR₂
  have hA := (isPullback_normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR).map yoneda
  have hpb : IsPullback
      (Limits.pullback.fst
        (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w)
      (Limits.pullback.snd
        (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w)
      (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w :=
    IsPullback.of_hasPullback _ _
  have houter := hA.paste_vert hsq
  have hsnd : yoneda.map (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR) ≫
      normQuotientChartComparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF ≫
      Limits.pullback.snd
        (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w =
        yoneda.map (normSpaceProj B S hS R hR) ≫ yoneda.map pr₂ := by
    rw [normQuotientChartComparison_comp_snd, ← Functor.map_comp,
      normRelSnd_comp_normSpaceProj, Functor.map_comp]
  rw [← hsnd, ← Category.assoc,
    ← normQuotientMap_comp_normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF] at houter
  refine houter.of_bot ?_ hpb
  rw [Category.assoc, normQuotientChartComparison_comp_fst]
  exact hker.w.symm

include hsq hwet hR₂ hF in
/-- The relation's normalization is a representable surjective étale cover of the fibre product
of the glued normalization with the chart. -/
theorem isLocallySurjective_normRelSnd_comp_comparison :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (yoneda.map (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR) ≫
        normQuotientChartComparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) := by
  have hbc := isPullback_normRelSnd_comp_comparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  exact isLocallySurjective_of_surjective_etale B S hS _
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback hbc
      (surjective_normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR hR₂))
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback hbc
      (etale_normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR hR₂))

include hsq hwet hR₂ hF in
/-- **The comparison morphism is an isomorphism**, being a monomorphism which is locally
surjective between sheaves. -/
theorem isIso_normQuotientChartComparison :
    IsIso (normQuotientChartComparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) := by
  have hQ := isAlgebraicSpace_normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR hR₂
  have hUspace : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hpb : IsAlgebraicSpace B S hS
      (Limits.pullback
        (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w) :=
    isAlgebraicSpace_pullback B S hS _ w hQ hUspace hF
  have _ := isLocallySurjective_normRelSnd_comp_comparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF
  exact NormalizationGluing.isIso_of_mono_of_isLocallySurjective_of_isSheaf B S hS
    (isAlgebraicSpace_yoneda B S hS (normSpace B S hS U hU)).isSheaf hpb.isSheaf _
    (mono_normQuotientChartComparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF)
    (Presheaf.isLocallySurjective_of_isLocallySurjective (BigFppfOver.topology B S hS)
      (yoneda.map (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR))
      (normQuotientChartComparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF))

include hsq hwet hR₂ hF in
/-- **The chart condition at the chart the quotient was built from**: the normalization `U^ν` of
the chart is the fibre product of the glued normalization with the chart `U`, compatibly with
both legs. -/
theorem isPullback_normQuotientMap :
    IsPullback (normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR)
      (yoneda.map (normSpaceProj B S hS U hU))
      (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w := by
  have _ := isIso_normQuotientChartComparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF
  exact IsPullback.of_iso_pullback
    ⟨normQuotientMap_comp_normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF⟩
    (asIso (normQuotientChartComparison B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF))
    (normQuotientChartComparison_comp_fst B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF)
    (normQuotientChartComparison_comp_snd B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF)

end AlgebraicGeometry.Space.NormSpaceGluing

end
