module

public import StacksFrontier.RingTheory.Descent.NilpotentEqualizerLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineChartOfAffineThickening
public import StacksFrontier.AlgebraicGeometry.KerDetected.RingColimit
public import StacksFrontier.AlgebraicGeometry.Thickenings.KernelGlobalSections

/-!
# Lifting a function from a finite-order thickening of an affine, on one étale chart

Let `G ⊆ X` be a finite-order thickening of algebraic spaces over `S` whose closed member `G` is
affine, `G ≅ h_{T_G}`, and let `φ : h_V → X` be a surjective étale chart with `V` affine and
`U = V ×_X G`. Every regular function on `T_G` is the restriction to `U` of a regular function on
`V` whose pullbacks along any two maps into `V` agreeing over `X` coincide. This is the chart form
of the surjectivity `Γ(X, 𝒪_X) → Γ(G, 𝒪_G)` of Stacks 05ZQ, in the finite-order case.

## Main results

* `AlgebraicGeometry.Space.exists_reduction_hom`: the reductions of two charts over a morphism of
  charts are related by a cartesian square.
* `AlgebraicGeometry.Space.exists_lift_invariant_of_isFiniteOrderThickening`: the lift.

## References

* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


/-- A cartesian square of represented presheaves is a cartesian square of schemes. -/
lemma isPullback_toScheme_of_isPullback_yoneda {P Q R' W : BigFppfOver B S hS}
    {f : P ⟶ Q} {g : P ⟶ R'} {h : Q ⟶ W} {k : R' ⟶ W}
    (sq : IsPullback (yoneda.map f) (yoneda.map g) (yoneda.map h) (yoneda.map k)) :
    IsPullback ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map g)
      ((BigFppfOver.toScheme B S hS).map h) ((BigFppfOver.toScheme B S hS).map k) :=
  (IsPullback.of_map_of_faithful yoneda sq).map (BigFppfOver.toScheme B S hS)

/-- A commuting square in the big fppf category gives a commuting square of the ring maps on
global functions. -/
lemma appTop_comp_eq {P Q Q' W : BigFppfOver B S hS} (f : P ⟶ Q) (g : Q ⟶ W) (f' : P ⟶ Q')
    (g' : Q' ⟶ W) (h : f ≫ g = f' ≫ g') :
    ((BigFppfOver.toScheme B S hS).map f).appTop.hom.comp
        ((BigFppfOver.toScheme B S hS).map g).appTop.hom =
      ((BigFppfOver.toScheme B S hS).map f').appTop.hom.comp
        ((BigFppfOver.toScheme B S hS).map g').appTop.hom := by
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, ← Functor.map_comp, ← Functor.map_comp, h]

/-- A cartesian square of represented presheaves whose corners `Q`, `R'`, `W` are affine gives a
pushout square of the rings of global functions. -/
lemma isPushout_ofHom_appTop {P Q R' W : BigFppfOver B S hS}
    {f : P ⟶ Q} {g : P ⟶ R'} {h : Q ⟶ W} {k : R' ⟶ W}
    (sq : IsPullback (yoneda.map f) (yoneda.map g) (yoneda.map h) (yoneda.map k))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj R')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] :
    IsPushout (CommRingCat.ofHom ((BigFppfOver.toScheme B S hS).map h).appTop.hom)
      (CommRingCat.ofHom ((BigFppfOver.toScheme B S hS).map k).appTop.hom)
      (CommRingCat.ofHom ((BigFppfOver.toScheme B S hS).map f).appTop.hom)
      (CommRingCat.ofHom ((BigFppfOver.toScheme B S hS).map g).appTop.hom) :=
  isPushout_appTop_of_isPullback (isPullback_toScheme_of_isPullback_yoneda B S hS sq)

/-- The ring map on global functions of `f ≫ g` is that of `g` followed by that of `f`. -/
lemma appTop_hom_comp {P Q W : BigFppfOver B S hS} (f : P ⟶ Q) (g : Q ⟶ W) :
    ((BigFppfOver.toScheme B S hS).map (f ≫ g)).appTop.hom =
      ((BigFppfOver.toScheme B S hS).map f).appTop.hom.comp
        ((BigFppfOver.toScheme B S hS).map g).appTop.hom := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]

/-- If `f ≫ g = 𝟙 P`, the ring map on global functions of `g` followed by that of `f` is the
identity. -/
lemma appTop_comp_eq_id {P Q : BigFppfOver B S hS} (f : P ⟶ Q) (g : Q ⟶ P) (h : f ≫ g = 𝟙 P) :
    ((BigFppfOver.toScheme B S hS).map f).appTop.hom.comp
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom = RingHom.id _ := by
  rw [← appTop_hom_comp, h, CategoryTheory.Functor.map_id]
  rfl

/-- A cartesian square with represented legs lifts any compatible pair of maps of the big
fppf category. -/
private theorem exists_comp_eq_of_isPullback_yoneda {P Q R' Z : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : P ⟶ Q} {g : P ⟶ R'} {h : yoneda.obj Q ⟶ X}
    {k : yoneda.obj R' ⟶ X} (sq : IsPullback (yoneda.map f) (yoneda.map g) h k) (a : Z ⟶ Q)
    (b : Z ⟶ R') (hab : yoneda.map a ≫ h = yoneda.map b ≫ k) :
    ∃ l : Z ⟶ P, l ≫ f = a ∧ l ≫ g = b := by
  obtain ⟨l, hl⟩ := yoneda.map_surjective (sq.lift (yoneda.map a) (yoneda.map b) hab)
  exact ⟨l, yoneda.map_injective (by rw [Functor.map_comp, hl, IsPullback.lift_fst]),
    yoneda.map_injective (by rw [Functor.map_comp, hl, IsPullback.lift_snd])⟩

/-- **The base change of a chart square along a morphism of charts.** Given two charts of `X`
with their cartesian squares over a subfunctor `G` and a morphism `w` of charts, the reductions
are related by a morphism `m` making `W₂₀ = W₂ ×_{W₁} W₁₀`. -/
theorem exists_reduction_hom {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}
    {W₁ W₂ W₁₀ W₂₀ : BigFppfOver B S hS} {c₁ : yoneda.obj W₁ ⟶ X.1}
    {c₂ : yoneda.obj W₂ ⟶ X.1} (w : W₂ ⟶ W₁) (hw : yoneda.map w ≫ c₁ = c₂)
    {j₁ : W₁₀ ⟶ W₁} {q₁ : yoneda.obj W₁₀ ⟶ G.toFunctor}
    (h₁ : IsPullback q₁ (yoneda.map j₁) G.ι c₁)
    {j₂ : W₂₀ ⟶ W₂} {q₂ : yoneda.obj W₂₀ ⟶ G.toFunctor}
    (h₂ : IsPullback q₂ (yoneda.map j₂) G.ι c₂) :
    ∃ m : W₂₀ ⟶ W₁₀, yoneda.map m ≫ q₁ = q₂ ∧ m ≫ j₁ = j₂ ≫ w ∧
      IsPullback (yoneda.map m) (yoneda.map j₂) (yoneda.map j₁) (yoneda.map w) := by
  obtain ⟨m, hm⟩ := yoneda.map_surjective (h₁.lift q₂ (yoneda.map j₂ ≫ yoneda.map w)
    (by rw [h₂.w, Category.assoc, hw]))
  have hm₁ : yoneda.map m ≫ q₁ = q₂ := by rw [hm, IsPullback.lift_fst]
  have hm₂ : yoneda.map m ≫ yoneda.map j₁ = yoneda.map j₂ ≫ yoneda.map w := by
    rw [hm, IsPullback.lift_snd]
  refine ⟨m, hm₁, yoneda.map_injective (by rw [Functor.map_comp, Functor.map_comp, hm₂]), ?_⟩
  refine IsPullback.of_right ?_ hm₂ h₁
  rwa [hm₁, hw]

/-- **Lifting functions along a finite-order thickening of an affine, on one chart.** Let
`G ⊆ X` be a finite-order thickening with `G` affine, `G ≅ h_{T_G}`, and let `φ : h_V → X` be a
surjective étale chart with `V` affine and `U = V ×_X G`. Then every regular function `a` on
`T_G` is the restriction to `U` of a regular function `b` on `V` whose two pullbacks along any
pair of maps into `V` agreeing over `X` are equal. -/
theorem exists_lift_invariant_of_isFiniteOrderThickening
    (X : AlgebraicSpaces B S hS) (G : Subfunctor X.1) (hG : IsFiniteOrderThickening B S hS X G)
    {TG : BigFppfOver B S hS} (hTG : IsAffine ((BigFppfOver.toScheme B S hS).obj TG))
    (eG : G.toFunctor ≅ yoneda.obj TG)
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (φ : yoneda.obj V ⟶ X.1)
    (hφs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (hφe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    {U : BigFppfOver B S hS} (ιU : U ⟶ V) (πU : U ⟶ TG)
    (sqU : IsPullback (yoneda.map ιU) (yoneda.map πU ≫ eG.inv) φ G.ι)
    (a : Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤)) :
    ∃ b : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤),
      ((BigFppfOver.toScheme B S hS).map ιU).appTop b =
        ((BigFppfOver.toScheme B S hS).map πU).appTop a ∧
      ∀ ⦃W : BigFppfOver B S hS⦄ (r₁ r₂ : W ⟶ V), yoneda.map r₁ ≫ φ = yoneda.map r₂ ≫ φ →
        ((BigFppfOver.toScheme B S hS).map r₁).appTop b =
          ((BigFppfOver.toScheme B S hS).map r₂).appTop b := by
  classical
  obtain ⟨n, hn⟩ := hG
  have hGt : IsThickening B S hS X G := hn.1
  have hGaff : IsAffineSpace B S hS G.toFunctor := ⟨TG, hTG, ⟨eG⟩⟩
  set pU : yoneda.obj U ⟶ G.toFunctor := yoneda.map πU ≫ eG.inv with hpU
  have sqU' : IsPullback pU (yoneda.map ιU) G.ι φ := sqU.flip
  have := hV
  have := hTG
  have hιci :
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ιU) :=
    hGt.1.2.property φ pU ιU sqU'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map ιU)
  have sqUT : IsPullback (yoneda.map ιU) (yoneda.map πU) φ (eG.inv ≫ G.ι) :=
    sqU'.flip.of_iso (Iso.refl _) (Iso.refl _) eG (Iso.refl _) (by simp) (by simp [hpU])
      (by simp) (by simp)
  have hπet : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map πU) :=
    hφe.property (eG.inv ≫ G.ι) (yoneda.map ιU) πU sqUT
  have hπsurj : _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map πU) :=
    hφs.property (eG.inv ≫ G.ι) (yoneda.map ιU) πU sqUT
  let hrep : yoneda.relativelyRepresentable φ := hφe.rep
  let R := hrep.pullback φ
  let p₁ : R ⟶ V := hrep.fst' φ
  let p₂ : R ⟶ V := hrep.snd φ
  have hpb : IsPullback (yoneda.map p₁) (yoneda.map p₂) φ φ := hrep.isPullback' φ
  have hp₂et : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p₂) :=
    hφe.property_snd φ
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj R) :=
    isAffine_of_isPullback_of_isThickening B S hS hGt hGaff hV φ p₁ p₂ hpb
  let T := hrep.pullback (yoneda.map p₁ ≫ φ)
  let v : T ⟶ V := hrep.fst' (yoneda.map p₁ ≫ φ)
  let w : T ⟶ R := hrep.snd (yoneda.map p₁ ≫ φ)
  have hT : IsPullback (yoneda.map v) (yoneda.map w) φ (yoneda.map p₁ ≫ φ) :=
    hrep.isPullback' (yoneda.map p₁ ≫ φ)
  have hwet : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map w) :=
    hφe.property_snd (yoneda.map p₁ ≫ φ)
  obtain ⟨δ, hδ₁, hδ₂⟩ := exists_comp_eq_of_isPullback_yoneda B S hS hpb (𝟙 V) (𝟙 V) rfl
  obtain ⟨e₁₂, he₁₂₁, he₁₂₂⟩ := exists_comp_eq_of_isPullback_yoneda B S hS hpb v (w ≫ p₁)
    (by rw [hT.w, Functor.map_comp, Category.assoc])
  obtain ⟨e₁₃, he₁₃₁, he₁₃₂⟩ := exists_comp_eq_of_isPullback_yoneda B S hS hpb v (w ≫ p₂)
    (by rw [hT.w, Functor.map_comp, Category.assoc, hpb.w])
  obtain ⟨R₀, jR, qR, sqR, hjR⟩ :=
    exists_thickening_chart_pullback_subfunctor B S hS hGt R (yoneda.map p₁ ≫ φ)
  obtain ⟨T₀, jT, qT, sqT, hjT⟩ :=
    exists_thickening_chart_pullback_subfunctor B S hS hGt T (yoneda.map v ≫ φ)
  have := hjR.1
  have := hjT.1
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj R₀) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map jR)
  obtain ⟨m₁, hm₁q, hm₁j, Q₁⟩ := exists_reduction_hom B S hS p₁ rfl sqU' sqR
  obtain ⟨m₂, hm₂q, hm₂j, Q₂⟩ := exists_reduction_hom B S hS p₂ hpb.w.symm sqU' sqR
  obtain ⟨ē₁₂, hē₁₂q, hē₁₂j, -⟩ := exists_reduction_hom B S hS e₁₂
    (by rw [← Category.assoc, ← Functor.map_comp, he₁₂₁]) sqR sqT
  obtain ⟨ū, hūq, hūj, Qu⟩ := exists_reduction_hom B S hS w hT.w.symm sqR sqT
  have e1 : yoneda.map jR ≫ yoneda.map p₁ = yoneda.map m₁ ≫ yoneda.map ιU := by
    rw [← Functor.map_comp, ← Functor.map_comp, hm₁j]
  have hO : IsPullback (yoneda.map m₂) (yoneda.map m₁ ≫ yoneda.map ιU) (pU ≫ G.ι) φ := by
    have := Q₂.paste_vert hpb.flip
    rwa [e1, ← sqU'.w] at this
  have hP1T : IsPullback (yoneda.map m₁) (yoneda.map m₂) (yoneda.map πU) (yoneda.map πU) :=
    ((IsPullback.of_bot hO (by rw [hm₁q, hm₂q]) sqU').of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) eG (by simp) (by simp) (by simp [hpU]) (by simp [hpU])).flip
  have hsite : (ē₁₂ ≫ m₁) ≫ ιU = jT ≫ v := by
    rw [Category.assoc, hm₁j, ← Category.assoc, hē₁₂j, Category.assoc, he₁₂₁]
  have e2 : yoneda.map jT ≫ yoneda.map v = yoneda.map (ē₁₂ ≫ m₁) ≫ yoneda.map ιU := by
    rw [← Functor.map_comp, ← Functor.map_comp, hsite]
  have hO' :
      IsPullback (yoneda.map ū) (yoneda.map (ē₁₂ ≫ m₁) ≫ yoneda.map ιU) (qR ≫ G.ι) φ := by
    have := Qu.flip.paste_horiz hT
    rw [e2, ← sqR.w] at this
    exact this.flip
  have hqR : qR = yoneda.map (m₁ ≫ πU) ≫ eG.inv := by
    rw [← hm₁q, hpU, Functor.map_comp, Category.assoc]
  have hP2T : IsPullback (yoneda.map (ē₁₂ ≫ m₁)) (yoneda.map ū) (yoneda.map πU)
      (yoneda.map (m₁ ≫ πU)) :=
    ((IsPullback.of_bot hO' (by rw [hūq, Functor.map_comp, Category.assoc, hm₁q, hē₁₂q])
        sqU').of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eG (by simp) (by simp)
      (by simp [hqR]) (by simp [hpU])).flip
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) :=
    .of_isPullback (isPullback_toScheme_of_isPullback_yoneda B S hS hP2T)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    Stacks.Thickenings.isAffine_of_isThickening hjT
  obtain ⟨U₁, j₁, p₁', sq₁, hj₁⟩ := exists_nthOrderThickening_chart_pullback B S hS hn V φ
    ((isEtale_iff_presheaf_of_yoneda B S hS φ).1 (isEtale_of_presheaf_etale B S hS hφe))
  obtain ⟨m, -, hmj, Qm⟩ := exists_reduction_hom B S hS (𝟙 V) (Category.id_comp φ) sq₁ sqU'
  have : IsIso (yoneda.map m) := by
    have : IsIso (yoneda.map (𝟙 V)) := by rw [CategoryTheory.Functor.map_id]; infer_instance
    exact Qm.isIso_fst_of_isIso
  have : IsIso m := isIso_of_reflects_iso m yoneda
  have := hj₁.1
  have hnil : IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map ιU).appTop.hom) := by
    refine ⟨n + 1, ?_⟩
    have hιU : ιU = m ≫ j₁ := by rw [hmj, Category.comp_id]
    rw [hιU, appTop_hom_comp, RingHom.ker_comp_of_injective]
    · exact Scheme.ker_appTop_pow_eq_bot _ inferInstance hj₁.2
    · exact Function.LeftInverse.injective (g := ((BigFppfOver.toScheme B S hS).map
        (inv m)).appTop.hom) fun x => by
          rw [← RingHom.comp_apply, appTop_comp_eq_id B S hS _ _ (IsIso.inv_hom_id m),
            RingHom.id_apply]
  have hsurjB := (IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map ιU)).2
  have hsurjC := (IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map jR)).2
  have hsurjD := (IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map jT)).2
  have hKs := GoodDiagramKer.ker_eq_map_of_isPushout_of_surjective _ _ _ _
    (isPushout_ofHom_appTop B S hS Q₁) hsurjB
  have hKt := GoodDiagramKer.ker_eq_map_of_isPushout_of_surjective _ _ _ _
    (isPushout_ofHom_appTop B S hS Q₂) hsurjB
  have hL := GoodDiagramKer.ker_eq_map_of_isPushout_of_surjective _ _ _ _
    (isPushout_ofHom_appTop B S hS Qu) hsurjC
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map πU).appTop.hom.toAlgebra
  have : Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine _).1
      ⟨inferInstance, inferInstance⟩
  have P1 := isPushout_ofHom_appTop B S hS hP1T
  have P2 := isPushout_ofHom_appTop B S hS hP2T
  rw [appTop_hom_comp, appTop_hom_comp] at P2
  obtain ⟨b, hst, hπ⟩ := Module.Descent.exists_eq_of_isNilpotent_ker
    ((BigFppfOver.toScheme B S hS).map p₁).appTop.hom
    ((BigFppfOver.toScheme B S hS).map p₂).appTop.hom
    ((BigFppfOver.toScheme B S hS).map δ).appTop.hom
    ((BigFppfOver.toScheme B S hS).map e₁₂).appTop.hom
    ((BigFppfOver.toScheme B S hS).map e₁₃).appTop.hom
    ((BigFppfOver.toScheme B S hS).map w).appTop.hom hsurjB hsurjC hsurjD
    ((BigFppfOver.toScheme B S hS).map m₁).appTop.hom
    ((BigFppfOver.toScheme B S hS).map m₂).appTop.hom
    ((BigFppfOver.toScheme B S hS).map ē₁₂).appTop.hom
    ((BigFppfOver.toScheme B S hS).map ū).appTop.hom
    (appTop_comp_eq B S hS _ _ _ _ hm₁j.symm) (appTop_comp_eq B S hS _ _ _ _ hm₂j.symm)
    (appTop_comp_eq B S hS _ _ _ _ hē₁₂j.symm) (appTop_comp_eq B S hS _ _ _ _ hūj.symm)
    (appTop_comp_eq_id B S hS _ _ hδ₁) (appTop_comp_eq_id B S hS _ _ hδ₂)
    (appTop_comp_eq B S hS _ _ _ _ (he₁₂₁.trans he₁₃₁.symm))
    (appTop_comp_eq B S hS _ _ _ _ he₁₂₂) (appTop_comp_eq B S hS _ _ _ _ he₁₃₂)
    hKs hKt hL (Scheme.Hom.flat_appTop _) (Scheme.Hom.flat_appTop _) hnil P1 P2 a
  refine ⟨b, hπ, fun W r₁ r₂ hr => ?_⟩
  obtain ⟨h, hh₁, hh₂⟩ := exists_comp_eq_of_isPullback_yoneda B S hS hpb r₁ r₂ hr
  show ((BigFppfOver.toScheme B S hS).map r₁).appTop.hom b =
    ((BigFppfOver.toScheme B S hS).map r₂).appTop.hom b
  rw [← hh₁, ← hh₂, appTop_hom_comp, appTop_hom_comp, RingHom.comp_apply, RingHom.comp_apply,
    hst]

end AlgebraicGeometry.Space

end
