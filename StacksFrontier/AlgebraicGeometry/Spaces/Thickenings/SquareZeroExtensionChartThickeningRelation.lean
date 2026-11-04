module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartThickeningMap

/-!
# Chart thickenings of a square-zero extension preserve equivalence relations

Let `E` be a square-zero extension of the small étale structure sheaf of an algebraic space `X`
by a quasi-coherent ideal (the data of Stacks 05ZT), and `U ↦ U'` the functor from the étale
charts of `X` to schemes it defines. Morphisms into a chart thickening `V'` which agree after
`V' ⟶ U'` and on the closed fibre over `U ⊂ U'` agree: `V' ⟶ U'` is étale and `U ⊂ U'` is a
thickening, so this is the uniqueness of sections of étale morphisms over a thickening
(Stacks 039R). Consequently a pair `t, s : R ⟶ U` of chart morphisms whose scheme morphisms are
jointly monic gives a jointly monic pair `t', s' : R' ⟶ U'`.

This is the monomorphism part of the assertion, in the proof of Stacks 05ZT, that applying
`U ↦ U'` to a presentation `X = U/R` gives an étale equivalence relation `R' ⇉ U'`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.eq_of_comp_chartRealizedSchemeMap_eq`
* `AlgebraicGeometry.Space.SquareZeroExtension.eq_of_comp_chartRealizedSchemeMap_eq_of_eq`
* `AlgebraicGeometry.Space.SquareZeroExtension.isPullback_chartRealizedSchemeMap_of_isPullback`
* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeEquivalenceRelation`
* `Stacks.Etale.isIso_of_isPullback_of_isPullback`

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

/-- **Rigidity of étale schemes over a thickening** (Stacks 039R): a morphism `φ : P ⟶ Q` of
schemes étale over `S` is an isomorphism as soon as its base change along a closed immersion
`i : S₀ ⟶ S` surjective on points is, in the form: `P₀ = P ×_S S₀` and `P₀ = Q ×_S S₀` through
`φ`. -/
theorem isIso_of_isPullback_of_isPullback {S₀ S : Scheme.{u}} (i : S₀ ⟶ S)
    [IsClosedImmersion i] (hi : Function.Surjective i.base) {P Q P₀ : Scheme.{u}}
    (p : P ⟶ S) (q : Q ⟶ S) [Etale p] [Etale q] (φ : P ⟶ Q) (hφ : φ ≫ q = p)
    (j : P₀ ⟶ P) (p₀ : P₀ ⟶ S₀) (h₁ : IsPullback j p₀ p i) (h₂ : IsPullback (j ≫ φ) p₀ q i) :
    IsIso φ := by
  let : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) i := ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let F : S.Etale ⥤ S₀.Etale :=
    MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ i
  have hF : F.IsEquivalence :=
    etalePullback_isEquivalence_of_surjective_isClosedImmersion i hi
  let φ' : Scheme.Etale.mk p ⟶ Scheme.Etale.mk q := MorphismProperty.Over.homMk φ hφ
  let e : pullback p i ≅ pullback q i := h₁.isoPullback.symm ≪≫ h₂.isoPullback
  have hefst : e.hom ≫ pullback.fst q i = pullback.fst p i ≫ φ := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, IsPullback.isoPullback_hom_fst]
    rw [← Category.assoc, IsPullback.isoPullback_inv_fst]
  have hesnd : e.hom ≫ pullback.snd q i = pullback.snd p i := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, IsPullback.isoPullback_hom_snd,
      IsPullback.isoPullback_inv_snd]
  have hleft : (F.map φ').left = e.hom :=
    pullback.hom_ext ((pullback.lift_fst _ _ _).trans hefst.symm)
      ((pullback.lift_snd _ _ _).trans ((Category.comp_id _).trans hesnd.symm))
  have : IsIso (F.map φ') := by
    refine ⟨MorphismProperty.Over.homMk e.inv
      ((e.inv_hom_id_assoc _).symm.trans (congrArg (e.inv ≫ ·) hesnd)).symm, ?_, ?_⟩
    · exact MorphismProperty.Over.Hom.ext ((congrArg (· ≫ e.inv) hleft).trans e.hom_inv_id)
    · exact MorphismProperty.Over.Hom.ext ((congrArg (e.inv ≫ ·) hleft).trans e.inv_hom_id)
  have : IsIso φ' := isIso_of_reflects_iso φ' F
  exact ⟨(inv φ').left, congrArg (fun m ↦ m.left) (IsIso.hom_inv_id φ'),
    congrArg (fun m ↦ m.left) (IsIso.inv_hom_id φ')⟩

end Stacks.Etale

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- The inclusion of an étale chart into its chart thickening is a closed immersion. -/
instance isClosedImmersion_chartInclusion (U : SmallEtale B S hS X.1) :
    AlgebraicGeometry.IsClosedImmersion (E.chartInclusion U) :=
  (E.isFirstOrderThickening_chartInclusion U).1

/-- The inclusion of an étale chart into its chart thickening is the identity on points. -/
theorem surjective_chartInclusion_base (U : SmallEtale B S hS X.1) :
    Function.Surjective (E.chartInclusion U).base :=
  fun x ↦ ⟨x, rfl⟩

/-- The inclusion of an étale chart into its chart thickening is surjective. -/
instance surjective_chartInclusion (U : SmallEtale B S hS X.1) :
    AlgebraicGeometry.Surjective (E.chartInclusion U) :=
  ⟨E.surjective_chartInclusion_base U⟩

/-- **Morphisms into a chart thickening are determined on the closed fibre**: two morphisms
`a, b : T ⟶ V'` with the same composite `u : T ⟶ U'` agree as soon as they agree on
`T ×_{U'} U`, by uniqueness of sections of the étale morphism `V' ⟶ U'` over the thickening
`T ×_{U'} U ⊂ T` (Stacks 039R). -/
theorem eq_of_comp_chartRealizedSchemeMap_eq {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    {T : Scheme.{u}} (a b : T ⟶ E.chartRealizedScheme V)
    (hab : a ≫ E.chartRealizedSchemeMap g = b ≫ E.chartRealizedSchemeMap g)
    (h₀ : pullback.fst (a ≫ E.chartRealizedSchemeMap g) (E.chartInclusion U) ≫ a =
      pullback.fst (a ≫ E.chartRealizedSchemeMap g) (E.chartInclusion U) ≫ b) : a = b := by
  have : Etale (E.chartRealizedSchemeMap g) := E.etale_chartRealizedSchemeMap g
  let u := a ≫ E.chartRealizedSchemeMap g
  let i := pullback.fst u (E.chartInclusion U)
  have hi : Function.Surjective i.base := AlgebraicGeometry.Surjective.surj
  let σa : T ⟶ pullback (E.chartRealizedSchemeMap g) u :=
    pullback.lift a (𝟙 T) (by rw [Category.id_comp])
  let σb : T ⟶ pullback (E.chartRealizedSchemeMap g) u :=
    pullback.lift b (𝟙 T) (by rw [Category.id_comp]; exact hab.symm)
  obtain ⟨σ, -, huniq⟩ := Stacks.Etale.existsUnique_section_of_isClosedImmersion_of_surjective
    i hi (pullback.snd (E.chartRealizedSchemeMap g) u) (i ≫ σa)
    (by rw [Category.assoc, pullback.lift_snd, Category.comp_id])
  have ha := huniq σa ⟨pullback.lift_snd _ _ _, rfl⟩
  have hb := huniq σb ⟨pullback.lift_snd _ _ _, pullback.hom_ext
    (by rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]; exact h₀.symm)
    (by rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd])⟩
  have e : σa = σb := ha.trans hb.symm
  have := congrArg (· ≫ pullback.fst (E.chartRealizedSchemeMap g) u) e
  simpa only [σa, σb, pullback.lift_fst] using this

/-- **`U ↦ U'` preserves jointly monic pairs**: if the scheme morphisms of chart morphisms
`t, s : R ⟶ U` are jointly monic, so are `t', s' : R' ⟶ U'`. -/
theorem eq_of_comp_chartRealizedSchemeMap_eq_of_eq {R U : SmallEtale B S hS X.1} (t s : R ⟶ U)
    (hts : ∀ {T : Scheme.{u}} (a b : T ⟶ chartScheme R), a ≫ chartSchemeMap t =
      b ≫ chartSchemeMap t → a ≫ chartSchemeMap s = b ≫ chartSchemeMap s → a = b)
    {T : Scheme.{u}} (a b : T ⟶ E.chartRealizedScheme R)
    (ht : a ≫ E.chartRealizedSchemeMap t = b ≫ E.chartRealizedSchemeMap t)
    (hs : a ≫ E.chartRealizedSchemeMap s = b ≫ E.chartRealizedSchemeMap s) : a = b := by
  refine E.eq_of_comp_chartRealizedSchemeMap_eq t a b ht ?_
  let i := pullback.fst (a ≫ E.chartRealizedSchemeMap t) (E.chartInclusion U)
  let p := pullback.snd (a ≫ E.chartRealizedSchemeMap t) (E.chartInclusion U)
  have pb := E.isPullback_chartRealizedSchemeMap t
  have hca : (i ≫ a) ≫ E.chartRealizedSchemeMap t = p ≫ E.chartInclusion U := by
    rw [Category.assoc]; exact pullback.condition
  have hcb : (i ≫ b) ≫ E.chartRealizedSchemeMap t = p ≫ E.chartInclusion U := by
    rw [Category.assoc, ← ht]; exact hca
  let a₀ := pb.lift (i ≫ a) p hca
  let b₀ := pb.lift (i ≫ b) p hcb
  have hs₀ : a₀ ≫ chartSchemeMap s = b₀ ≫ chartSchemeMap s := by
    rw [← cancel_mono (E.chartInclusion U), Category.assoc, Category.assoc,
      ← E.chartInclusion_comp_chartRealizedSchemeMap s, ← Category.assoc, ← Category.assoc,
      pb.lift_fst, pb.lift_fst, Category.assoc, Category.assoc, hs]
  have e : a₀ = b₀ := hts a₀ b₀ ((pb.lift_snd _ _ _).trans (pb.lift_snd _ _ _).symm) hs₀
  have := congrArg (· ≫ E.chartInclusion R) e
  simpa only [a₀, b₀, pb.lift_fst] using this

/-- **`U ↦ U'` preserves cartesian squares of étale charts**: if the scheme square of chart
morphisms `a : P ⟶ W`, `b : P ⟶ V`, `c : W ⟶ U`, `e : V ⟶ U` is cartesian, so is the square of
chart thickenings. The comparison `P' ⟶ W' ×_{U'} V'` is a morphism of schemes étale over `U'`
whose base change to `U` is the identification `P = W ×_U V`, hence an isomorphism (Stacks
039R). -/
theorem isPullback_chartRealizedSchemeMap_of_isPullback {P W V U : SmallEtale B S hS X.1}
    (a : P ⟶ W) (b : P ⟶ V) (c : W ⟶ U) (e : V ⟶ U)
    (h : IsPullback (chartSchemeMap a) (chartSchemeMap b) (chartSchemeMap c) (chartSchemeMap e)) :
    IsPullback (E.chartRealizedSchemeMap a) (E.chartRealizedSchemeMap b)
      (E.chartRealizedSchemeMap c) (E.chartRealizedSchemeMap e) := by
  have hcomm : a ≫ c = b ≫ e := hom_ext_of_toScheme_map_eq B S hS
    (((BigFppfOver.toScheme B S hS).map_comp _ _).trans
      (h.w.trans ((BigFppfOver.toScheme B S hS).map_comp _ _).symm))
  have := @E.etale_chartRealizedSchemeMap
  have hw : E.chartRealizedSchemeMap a ≫ E.chartRealizedSchemeMap c =
      E.chartRealizedSchemeMap b ≫ E.chartRealizedSchemeMap e := by
    rw [← chartRealizedSchemeMap_comp, ← chartRealizedSchemeMap_comp, hcomm]
  let φ : E.chartRealizedScheme P ⟶
      pullback (E.chartRealizedSchemeMap c) (E.chartRealizedSchemeMap e) :=
    pullback.lift _ _ hw
  have sqQ :=
    (IsPullback.of_hasPullback (E.chartRealizedSchemeMap c) (E.chartRealizedSchemeMap e)).flip
  -- `P = W ×_{U'} V'`.
  have big : IsPullback ((E.chartInclusion P ≫ φ) ≫ pullback.snd _ _) (chartSchemeMap a)
      (E.chartRealizedSchemeMap e) (E.chartInclusion W ≫ E.chartRealizedSchemeMap c) := by
    have h0 := h.flip.paste_horiz (E.isPullback_chartRealizedSchemeMap e)
    rwa [Category.assoc, pullback.lift_snd, E.chartInclusion_comp_chartRealizedSchemeMap,
      E.chartInclusion_comp_chartRealizedSchemeMap]
  have top : IsPullback (E.chartInclusion P ≫ φ) (chartSchemeMap a)
      (pullback.fst (E.chartRealizedSchemeMap c) (E.chartRealizedSchemeMap e))
      (E.chartInclusion W) :=
    IsPullback.of_right big (by
      rw [Category.assoc, pullback.lift_fst, E.chartInclusion_comp_chartRealizedSchemeMap]) sqQ
  have h₂ := top.paste_vert (E.isPullback_chartRealizedSchemeMap c)
  have h₁ : IsPullback (E.chartInclusion P) (chartSchemeMap a ≫ chartSchemeMap c)
      (E.chartRealizedSchemeMap a ≫ E.chartRealizedSchemeMap c) (E.chartInclusion U) := by
    have := E.isPullback_chartRealizedSchemeMap (a ≫ c)
    rwa [chartRealizedSchemeMap_comp, chartSchemeMap_comp] at this
  have : IsIso φ := Stacks.Etale.isIso_of_isPullback_of_isPullback (E.chartInclusion U)
    (E.surjective_chartInclusion_base U) _ _ φ (pullback.lift_fst_assoc _ _ _ _) _ _ h₁ h₂
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso φ) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

/-- **`U ↦ U'` carries an equivalence relation of étale charts to an equivalence relation of
schemes.** Let `t, s : R ⟶ U` be chart morphisms whose scheme morphisms are jointly monic, with
a reflexivity `r`, a symmetry `σ`, and a transitivity `c : R ×_{s, U, t} R ⟶ R` on a chart `R₂`
whose scheme square is cartesian. Then `t', s' : R' ⟶ U'` form an equivalence relation, with
the thickenings of `r`, `σ` and `c`. This is the assertion of the proof of Stacks 05ZT that
applying `U ↦ U'` to a presentation `X = U/R` gives an equivalence relation `R' ⇉ U'`. -/
noncomputable def chartRealizedSchemeEquivalenceRelation {R U R₂ : SmallEtale B S hS X.1}
    (t s : R ⟶ U)
    (hts : ∀ {T : Scheme.{u}} (a b : T ⟶ chartScheme R), a ≫ chartSchemeMap t =
      b ≫ chartSchemeMap t → a ≫ chartSchemeMap s = b ≫ chartSchemeMap s → a = b)
    (r : U ⟶ R) (hr₁ : r ≫ t = 𝟙 U) (hr₂ : r ≫ s = 𝟙 U)
    (σ : R ⟶ R) (hσ₁ : σ ≫ t = s) (hσ₂ : σ ≫ s = t)
    (p₁ p₂ c : R₂ ⟶ R)
    (hpb : IsPullback (chartSchemeMap p₁) (chartSchemeMap p₂) (chartSchemeMap s)
      (chartSchemeMap t))
    (hc₁ : c ≫ t = p₁ ≫ t) (hc₂ : c ≫ s = p₂ ≫ s) :
    EquivalenceRelation (E.chartRealizedSchemeMap t) (E.chartRealizedSchemeMap s) :=
  have hpb' := E.isPullback_chartRealizedSchemeMap_of_isPullback p₁ p₂ s t hpb
  { right_cancellation := fun _ a b h₁ h₂ ↦
      E.eq_of_comp_chartRealizedSchemeMap_eq_of_eq t s hts a b h₁ h₂
    r := E.chartRealizedSchemeMap r
    reflexivity₁ := by rw [← chartRealizedSchemeMap_comp, hr₁, chartRealizedSchemeMap_id]
    reflexivity₂ := by rw [← chartRealizedSchemeMap_comp, hr₂, chartRealizedSchemeMap_id]
    s := E.chartRealizedSchemeMap σ
    symmetry₁ := by rw [← chartRealizedSchemeMap_comp, hσ₁]
    symmetry₂ := by rw [← chartRealizedSchemeMap_comp, hσ₂]
    c := hpb'.cone
    isLimit := hpb'.isLimit
    t := E.chartRealizedSchemeMap c
    transitivity₁ := (E.chartRealizedSchemeMap_comp t c).symm.trans
      ((congrArg E.chartRealizedSchemeMap hc₁).trans (E.chartRealizedSchemeMap_comp t p₁))
    transitivity₂ := (E.chartRealizedSchemeMap_comp s c).symm.trans
      ((congrArg E.chartRealizedSchemeMap hc₂).trans (E.chartRealizedSchemeMap_comp s p₂)) }

end AlgebraicGeometry.Space.SquareZeroExtension

end
