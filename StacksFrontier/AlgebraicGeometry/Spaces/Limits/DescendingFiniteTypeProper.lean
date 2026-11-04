module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingProperness
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# Stacks 0CPE: properness descends to the system of scheme-theoretic images

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces
over a scheme `S` with affine transition morphisms, as in Situation 0CP6, and let
`f : X ⟶ Y` be a morphism of algebraic spaces quasi-separated and of finite type over `B`.
Writing `X = lim_{i ≥ i₁} X_i` and `Y = lim_{i ≥ i₂} Y_i` for the limit descriptions by
scheme-theoretic images of Stacks 0CP9 attached to two diagrams as in Stacks 0CP8, Stacks 0CPA
describes `f` as the limit of a morphism `(f_i)_{i ≥ i₀}` of the two inverse systems. Stacks 0CPE
asserts that if `f` is proper, then so is `f_i` for every sufficiently large `i`.

The proof is the first proof of the source. By Stacks 0A0W there is a closed immersion
`X ⟶ X'` over `Y` with `X' ⟶ Y` proper and of finite presentation. By Stacks 07SK and 08K1 the
morphism `X' ⟶ Y` is the base change of a proper morphism `W ⟶ Y_m` along `Y ⟶ Y_m` for some
stage `m`. The square `X ⟶ W` over `B ⟶ B_m` is then a diagram as in Stacks 0CP8 for `X`, and
for `i ≥ m` the member `X'_i` of its image system is a closed subspace of `Y_i ×_{Y_m} W`, hence
proper over `Y_i`. The comparison of Remark 0CPB between the image systems of the two diagrams
for `X` (`AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_systemMorphism_inv`),
together with the eventual uniqueness of Stacks 0CPA, transfers this to the given system.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_isProper`: **Stacks 0CPE**.

## Implementation notes

The stage `i₃` is produced with `i₀ ≤ i₃`, and the conclusion holds at every stage `k ≥ i₃` of
the tail above `i₀`, as in the library's Stacks 0CPD. The size condition on the index type and the
algebraicity of `X` and `Y` are the hypotheses under which the library identifies `X` and `Y`
with the limits of their image systems, Stacks 0CP9. That `f` lies over `B` is not assumed: it
follows from the morphism of systems.

## References

* [Stacks Project, Tag 0CPE](https://stacks.math.columbia.edu/tag/0CPE)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
* [Stacks Project, Tag 0CPB](https://stacks.math.columbia.edu/tag/0CPB)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0A0W](https://stacks.math.columbia.edu/tag/0A0W)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace GoodDiagram

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt} {pY : Y ⟶ D.limitCone.pt}

/-! ### A proper morphism of finite presentation descends to a proper model -/

/-- A morphism into a pullback whose first projection is composed with the (isomorphic) pullback
along an identity has the same properness as the first projection of the source pullback. -/
private lemma isProper_iff_of_comp_fst_eq {A T U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g : A ⟶ T} {u : U ⟶ T} (ml : pullback g u ⟶ pullback g (𝟙 T))
    (h : ml ≫ pullback.fst g (𝟙 T) = pullback.fst g u) :
    IsProper B S hS ml ↔ IsProper B S hS (pullback.fst g u) := by
  rw [← h, isProper_comp_isIso_iff]

/-- A proper morphism `f : X ⟶ Y` of finite presentation is the base change, along a projection
`Y ⟶ Y_n` of the image system of `Y`, of a proper morphism `u : U ⟶ Y_n`: Stacks 07SK descends
`f` to some stage, and Stacks 08K1 makes it proper after increasing the stage. -/
private theorem exists_proper_model (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsY : IsQuasiSeparated B S hS pY)
    (small : Cardinal.mk I < B.cutoff.ord.cof) (GY : GoodDiagram B S hS hZ D pY) {i₀ : I}
    (leY : GY.index ≤ i₀) (f : X ⟶ Y) (proper : IsProper B S hS f)
    (fp : IsFinitePresentation B S hS f) :
    ∃ (n : Over (op i₀)) (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B S hS U) (u : U ⟶ (tailSystem GY leY).obj n) (toU : X ⟶ U),
      IsProper B S hS u ∧ IsPullback toU f u ((tailCone GY leY).π.app n) := by
  classical
  let Yr := tailSystem GY leY
  let cY := tailCone GY leY
  have hcY : IsLimit cY := isLimit_tailCone GY leY algY small
  have hJ : Cardinal.mk (Over (op i₀)) < B.cutoff.ord.cof :=
    (cardinal_mk_over_op_le i₀).trans_lt small
  have hJh : ∀ j k : Over (op i₀), Cardinal.mk (j ⟶ k) < B.cutoff.ord.cof :=
    cardinal_mk_hom_over_op_lt B i₀
  have aYr := tailSystem_isAlgebraicSpace GY leY
  have qcYr := tailSystem_isQuasiCompactSpace GY leY
  have qsYr := tailSystem_isAbsolutelyQuasiSeparated GY leY algY qsY small
  have afYr : ∀ {j k : Over (op i₀)} (a : j ⟶ k), IsAffineHom B S hS (Yr.map a) :=
    fun a => tailSystem_map_isAffineHom GY leY a
  -- Stacks 07SK: `f` is the base change of a morphism `u : U ⟶ Y_m` of finite presentation.
  let eY : Y ≅ limit Yr := hcY.conePointUniqueUpToIso (limit.isLimit Yr)
  have heY : ∀ j, eY.hom ≫ limit.π Yr j = cY.π.app j :=
    fun j => hcY.conePointUniqueUpToIso_hom_comp (limit.isLimit Yr) j
  have algL : IsAlgebraicSpace B S hS (limit Yr) := Space.isAlgebraicSpace_of_iso B S hS eY algY
  obtain ⟨m, Uo, algU, fpU, ⟨φ⟩⟩ := exists_model_of_finitePresentation B S hS hZ Yr hJ hJh
    aYr afYr qcYr qsYr (Over.mk (f ≫ eY.hom)) algX
    (isFinitePresentation_comp_iso algX algY algL f eY fp)
  let U := Uo.left
  let u : U ⟶ Yr.obj m := Uo.hom
  let toU : X ⟶ U := φ.hom.left ≫ pullback.fst _ _
  have sqU : IsPullback toU f u (cY.π.app m) := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback u (limit.π Yr m))
      ((Over.forget _).mapIso φ.symm) (Iso.refl _) eY.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [toU]
      rfl
    · have hw : φ.inv.left ≫ f ≫ eY.hom = pullback.snd u (limit.π Yr m) := Over.w φ.inv
      rw [← hw]
      simp
    · simp
    · simp [← heY]
  -- Stacks 08K1: after increasing `m`, the morphism `u` is proper.
  let k := m.left.unop
  let E : (Set.Ici k)ᵒᵖ ⥤ Over (op k) := iciOpToOverOp k
  let M : Over (op k) ⥤ Over (op i₀) := Over.map m.hom
  let base : (Set.Ici k)ᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := E ⋙ M ⋙ Yr
  have : E.Initial := inferInstanceAs (iciOpEquivalenceOverOp k).functor.Initial
  have hcB : IsLimit (cY.whisker (E ⋙ M)) :=
    (Functor.Initial.isLimitWhiskerEquiv (E ⋙ M) cY).symm hcY
  let eB : Y ≅ limit base := hcB.conePointUniqueUpToIso (limit.isLimit base)
  have heB : ∀ j, eB.hom ≫ limit.π base j = cY.π.app ((E ⋙ M).obj j) :=
    fun j => hcB.conePointUniqueUpToIso_hom_comp (limit.isLimit base) j
  let i0 : Set.Ici k := ⟨k, le_rfl⟩
  have qcU : IsQuasiCompactSpace B S hS U :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS u (aYr m) (qcYr m) fpU
  have qsU : IsAbsolutelyQuasiSeparated B S hS hZ U :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ algU (qsYr m) fpU.2.2
  let Dm : MorphismDescentSystem B S hS hZ (Set.Ici k) :=
    { base := base
      indexSize := (Cardinal.mk_subtype_le _).trans_lt small
      base_isAlgebraicSpace := fun i => aYr _
      transition_affine := fun a => afYr _
      limit_isAlgebraicSpace := Space.isAlgebraicSpace_of_iso B S hS eB algY
      initial := i0
      source₀ := U
      target₀ := Yr.obj m
      sourceToBase := u
      targetToBase := 𝟙 _
      map₀ := u
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := algU
      target₀_isAlgebraicSpace := aYr m
      base₀_quasiCompact := qcYr m
      base₀_quasiSeparated := qsYr m
      source₀_quasiCompact := qcU
      source₀_quasiSeparated := qsU
      target₀_quasiCompact := qcYr m
      target₀_quasiSeparated := qsYr m }
  have properLimit : IsProper B S hS Dm.mapLimit := by
    let π0 : limit base ⟶ Yr.obj m := limit.π base (op i0)
    have sq' : IsPullback (f ≫ eB.hom) toU π0 u :=
      IsPullback.of_iso sqU.flip (Iso.refl _) eB (Iso.refl _) (Iso.refl _) (by simp) (by simp)
        (by simp only [Iso.refl_hom, Category.comp_id]; exact (heB (op i0)).symm) (by simp)
    have hfst : IsProper B S hS (pullback.fst π0 u) := by
      rwa [← sq'.isoPullback_inv_fst, isProper_isIso_comp_iff B S hS,
        isProper_comp_isIso_iff B S hS]
    exact (isProper_iff_of_comp_fst_eq Dm.mapLimit Dm.mapLimit_fst).2 hfst
  obtain ⟨i1, le1, proper1⟩ := Dm.exists_isProper_mapAt properLimit
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS fpU.1)
  let m1 : Over m := Over.mk (M.map (E.map (homOfLE le1).op))
  have properM1 : IsProper B S hS (pullback.fst (Yr.map m1.hom) u) := by
    exact (isProper_iff_of_comp_fst_eq _ (Dm.mapAt_fst i1 le1)).1 proper1
  have sqR : IsPullback (pullback.snd (Yr.map m1.hom) u) (pullback.fst (Yr.map m1.hom) u) u
      (Yr.map m1.hom) := (IsPullback.of_hasPullback (Yr.map m1.hom) u).flip
  refine ⟨m1.left, pullback (Yr.map m1.hom) u,
    isAlgebraicSpace_pullback B S hS _ _ (aYr _) algU (aYr _), pullback.fst _ _,
    pullback.lift (f ≫ cY.π.app m1.left) toU ?_, properM1, ?_⟩
  · rw [Category.assoc, cY.w m1.hom]
    exact sqU.w.symm
  · refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) sqR
    rw [pullback.lift_snd, cY.w m1.hom]
    exact sqU

/-! ### The diagram of Stacks 0CP8 attached to a proper model -/

/-- The comparison `B ×_{B_m} W ⟶ B ×_{B_m} Y_m` induced by `w : W ⟶ Y_m` is the base change of
`w` along `B ×_{B_m} Y_m ⟶ Y_m`. -/
private lemma isPullback_pullbackLift_snd {C : Type*} [Category C] [HasPullbacks C]
    {T Tm Ym W : C} (p : T ⟶ Tm) (b : Ym ⟶ Tm) (w : W ⟶ Ym) :
    IsPullback (pullback.snd p (w ≫ b))
      (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ w)
        (by rw [Category.assoc, pullback.condition]) : pullback p (w ≫ b) ⟶ pullback p b)
      w (pullback.snd p b) := by
  refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm (IsPullback.of_hasPullback p b).flip
  rw [pullback.lift_fst]
  exact (IsPullback.of_hasPullback p (w ≫ b)).flip

/-- A morphism followed by the image of an endomorphism of a stage under the system is itself:
the endomorphism is an identity. -/
private lemma comp_system_map_endo (D : NoetherianLimitSystem B S hS hZ I)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : Iᵒᵖ} (g : T ⟶ D.system.obj a) (e : a ⟶ a) :
    g ≫ D.system.map e = g := by
  rw [Subsingleton.elim e (𝟙 a), D.system.map_id, Category.comp_id]

section ProperModel

variable (GY : GoodDiagram B S hS hZ D pY) (f : X ⟶ Y) (hf : f ≫ pY = pX) {m : I}
  (hm : GY.index ≤ m) {W X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (algW : IsAlgebraicSpace B S hS W) (w : W ⟶ stageAt GY m hm) (ft : IsFiniteType B S hS w)
  (ι : X ⟶ X') (hι : IsClosedImmersion B S hS ι) (p' : X' ⟶ Y) (toW : X' ⟶ W)
  (sq : IsPullback toW p' w (stageπ GY m hm)) (hιp : ι ≫ p' = f)

include sq hιp hf in
/-- The square `X ⟶ W` over `B ⟶ B_m` built from a closed immersion `X ⟶ X'` into the base
change `X' = Y ×_{Y_m} W` of a morphism `w : W ⟶ Y_m` commutes. -/
private lemma properModel_commutes :
    pX ≫ D.limitCone.π.app (op m) =
      (ι ≫ toW) ≫ w ≫ (stageImage GY (Over.mk (homOfLE hm).op)).ι ≫ pullback.fst _ _ := by
  simp only [Category.assoc]
  rw [reassoc_of% sq.w, stageπ_ι_fst, reassoc_of% hιp, reassoc_of% hf]

include hι in
/-- The morphism `X ⟶ B ×_{B_m} W` is a closed immersion: it is `X ⟶ X'` followed by the base
change of the closed immersion `Y ⟶ B ×_{B_m} Y_m` along `B ×_{B_m} W ⟶ B ×_{B_m} Y_m`. -/
private lemma isClosedImmersion_properModel :
    IsClosedImmersion B S hS (pullback.lift pX (ι ≫ toW)
      (properModel_commutes GY f hf hm w ι p' toW sq hιp)) := by
  have hR := isPullback_pullbackLift_snd (D.limitCone.π.app (op m))
    ((stageImage GY (Over.mk (homOfLE hm).op)).ι ≫ pullback.fst _ _) w
  let φ : X' ⟶ pullback (D.limitCone.π.app (op m))
      (w ≫ (stageImage GY (Over.mk (homOfLE hm).op)).ι ≫ pullback.fst _ _) :=
    pullback.lift (p' ≫ pY) toW (by
      rw [Category.assoc, ← stageπ_ι_fst GY m hm, reassoc_of% sq.w])
  have hφ₁ : φ ≫ pullback.fst _ _ = p' ≫ pY := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd _ _ = toW := pullback.lift_snd _ _ _
  have hlift : pullback.lift pX (ι ≫ toW) (properModel_commutes GY f hf hm w ι p' toW sq hιp) =
      ι ≫ φ := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, hφ₁, reassoc_of% hιp, hf]
    · rw [pullback.lift_snd, Category.assoc, hφ₂]
  let ψ : pullback (D.limitCone.π.app (op m))
        (w ≫ (stageImage GY (Over.mk (homOfLE hm).op)).ι ≫ pullback.fst _ _) ⟶
      stageBaseChange GY m hm :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ w) (by
      rw [Category.assoc, pullback.condition])
  have hψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ w := pullback.lift_snd _ _ _
  have hL : IsPullback φ p' ψ (toStageBaseChange GY m hm) := by
    refine IsPullback.of_right ?_ ?_ hR
    · rw [hφ₂, toStageBaseChange_snd]
      exact sq
    · refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, hψ₁, toStageBaseChange_fst, hφ₁]
      · simp only [Category.assoc, hψ₂, toStageBaseChange_snd, reassoc_of% hφ₂, sq.w]
  rw [hlift]
  exact isClosedImmersion_comp B S hS _ _ hι
    ((isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback hL.flip
      (isClosedImmersion_toStageBaseChange GY m hm))

/-- **The diagram of the proof of Stacks 0CPE.** A closed immersion `X ⟶ X'` into the base change
`X' = Y ×_{Y_m} W` of a morphism `w : W ⟶ Y_m` of finite type to a member of the image system of
`Y` gives a diagram as in Stacks 0CP8 for `X`, with model `W` over the stage `B_m`. -/
private noncomputable abbrev properModel : GoodDiagram B S hS hZ D pX where
  index := m
  model := W
  model_isAlgebraicSpace := algW
  modelMap := w ≫ (stageImage GY (Over.mk (homOfLE hm).op)).ι ≫ pullback.fst _ _
  toModel := ι ≫ toW
  commutes := properModel_commutes GY f hf hm w ι p' toW sq hιp
  isFiniteType := isFiniteType_comp' B S hS w _ (imageSystem_isAlgebraicSpace GY _)
    (D.system_isAlgebraicSpace m) ft
    ⟨isLocallyOfFiniteType_tailBase GY hm (Over.mk (𝟙 _)),
      isQuasiCompact_of_isQuasiCompactSpace B S hS hZ (D.system_isAlgebraicSpace m)
        (D.noetherian m).2.1 (imageSystem_isQuasiCompactSpace GY _) _⟩
  isClosedImmersion := isClosedImmersion_properModel GY f hf hm w ι hι p' toW sq hιp

private lemma properModel_modelMap :
    (properModel GY f hf hm algW w ft ι hι p' toW sq hιp).modelMap =
      w ≫ (stageImage GY (Over.mk (homOfLE hm).op)).ι ≫ pullback.fst _ _ := rfl

private lemma properModel_toModel :
    (properModel GY f hf hm algW w ft ι hι p' toW sq hιp).toModel = ι ≫ toW := rfl

/-- The morphism `X'_m ⟶ Y_m` of the members at the stage `m` of the two image systems, as a
morphism of image systems on the tail above `m`. -/
private theorem exists_systemMorphism_properModel :
    ∃ F' : SystemMorphism (properModel GY f hf hm algW w ft ι hι p' toW sq hιp) GY f m
        (le_refl m) hm, ∀ (i : I) (h : m ≤ i),
      F'.app i h ≫ stageTransition GY hm h =
        stageTransition (properModel GY f hf hm algW w ft ι hι p' toW sq hιp) (le_refl m) h ≫
          (stageImage (properModel GY f hf hm algW w ft ι hι p' toW sq hιp)
            (Over.mk (homOfLE (le_refl m)).op)).ι ≫ pullback.snd _ _ ≫ w := by
  refine exists_systemMorphism_of_stage_hom _ GY f hf (le_refl m) hm _ ?_ ?_
  · refine Eq.trans (?_ : _ =
      (stageImage (properModel GY f hf hm algW w ft ι hι p' toW sq hιp)
        (Over.mk (homOfLE (le_refl m)).op)).ι ≫ pullback.fst _ _ ≫
          D.system.map (Over.mk (homOfLE (le_refl m)).op).hom) ?_
    · simp only [Category.assoc]
      exact (congrArg (_ ≫ ·) pullback.condition).symm
    · rw [← Category.assoc]
      exact comp_system_map_endo D _ _
  · rw [stageπ_ι_snd_assoc, properModel_toModel, Category.assoc, sq.w, reassoc_of% hιp]

include sq in
/-- The components of a morphism of image systems as in `exists_systemMorphism_properModel` are
proper when `w` is: the member `X'_i` of the image system of `properModel` is a closed subspace of
`Y_i ×_{Y_m} W`, which is proper over `Y_i`. -/
private theorem isProper_app_properModel (proper : IsProper B S hS w)
    (F' : SystemMorphism (properModel GY f hf hm algW w proper.2.1 ι hι p' toW sq hιp) GY f m
      (le_refl m) hm)
    (hF' : ∀ (i : I) (h : m ≤ i),
      F'.app i h ≫ stageTransition GY hm h =
        stageTransition (properModel GY f hf hm algW w proper.2.1 ι hι p' toW sq hιp)
            (le_refl m) h ≫
          (stageImage (properModel GY f hf hm algW w proper.2.1 ι hι p' toW sq hιp)
            (Over.mk (homOfLE (le_refl m)).op)).ι ≫ pullback.snd _ _ ≫ w)
    (i : I) (h : m ≤ i) : IsProper B S hS (F'.app i h) := by
  classical
  let G' := properModel GY f hf hm algW w proper.2.1 ι hι p' toW sq hιp
  let Yt := stageTransition GY hm h
  have algYi := imageSystem_isAlgebraicSpace GY (Over.mk (homOfLE (hm.trans h)).op)
  have algYm := imageSystem_isAlgebraicSpace GY (Over.mk (homOfLE hm).op)
  have algXi := imageSystem_isAlgebraicSpace G' (Over.mk (homOfLE ((le_refl m).trans h)).op)
  have algP : IsAlgebraicSpace B S hS (pullback Yt w) :=
    isAlgebraicSpace_pullback B S hS _ _ algYi algW algYm
  have hfst : IsProper B S hS (pullback.fst Yt w) :=
    isProper_of_isPullback_presheaf B S hS algP algW algYi algYm
      (IsPullback.of_hasPullback Yt w).flip proper
  let ιX := (stageImage G' (Over.mk (homOfLE ((le_refl m).trans h)).op)).ι
  have hc : F'.app i h ≫ Yt = (ιX ≫ pullback.snd _ _) ≫ w := by
    rw [hF', stageTransition_ι_snd_assoc, Category.assoc]
  let c : stageAt G' i ((le_refl m).trans h) ⟶ pullback Yt w :=
    pullback.lift (F'.app i h) (ιX ≫ pullback.snd _ _) hc
  let k : pullback Yt w ⟶
      pullback (D.system.map (Over.mk (homOfLE ((le_refl m).trans h)).op).hom) G'.modelMap :=
    pullback.lift
      (pullback.fst _ _ ≫ (stageImage GY (Over.mk (homOfLE (hm.trans h)).op)).ι ≫
        pullback.fst _ _)
      (pullback.snd _ _) (by
        rw [properModel_modelMap, ← pullback.condition_assoc, stageTransition_ι_fst]
        simp only [Category.assoc]
        rfl)
  have hk : Mono k := ⟨fun {T} u v huv => by
    have e₁ := congrArg (· ≫ pullback.fst _ _) huv
    have e₂ := congrArg (· ≫ pullback.snd _ _) huv
    simp only [Category.assoc, k, pullback.lift_fst, pullback.lift_snd] at e₁ e₂
    refine pullback.hom_ext ?_ e₂
    refine stage_hom_ext GY hm h ?_ ?_
    · simpa only [Category.assoc] using e₁
    · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% e₂]⟩
  have hck : c ≫ k = ιX := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, F'.app_over_base]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hcl : IsClosedImmersion B S hS c :=
    isClosedImmersion_of_comp_mono B S hS c k (by
      rw [hck]
      exact (isClosedSubspace_stageImage G' _).2)
  have hcF : c ≫ pullback.fst _ _ = F'.app i h := pullback.lift_fst _ _ _
  rw [← hcF]
  exact isProper_comp' B S hS c _ algP algYi
    (isProper_of_isClosedImmersion B S hS algXi algP c hcl) hfst

end ProperModel

/-! ### Stacks 0CPE -/

namespace SystemMorphism

variable {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y}
  {i₀ : I} {leX : GX.index ≤ i₀} {leY : GY.index ≤ i₀}

/-- A morphism of image systems inducing `f` makes `f` a morphism over `B`: the two composites
`X ⟶ B` agree after every projection `B ⟶ B_i`. -/
private lemma comp_structureMap_eq (F : SystemMorphism GX GY f i₀ leX leY) : f ≫ pY = pX := by
  refine D.isLimit.hom_ext fun j => ?_
  obtain ⟨j⟩ := j
  obtain ⟨k, hjk, hk⟩ := exists_ge_ge j i₀
  have key : f ≫ pY ≫ D.limitCone.π.app (op k) = pX ≫ D.limitCone.π.app (op k) := by
    rw [← stageπ_ι_fst GY k (leY.trans hk), ← stageπ_ι_fst GX k (leX.trans hk),
      ← F.app_over_base k hk, ← reassoc_of% (F.stageπ_app k hk)]
  rw [← D.limitCone.w (homOfLE hjk).op]
  simp only [Category.assoc]
  rw [reassoc_of% key]

/-- **Stacks 0CPE.** In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic spaces
quasi-separated over `B`, let `GX` and `GY` be diagrams as in Stacks 0CP8 for `X` and `Y`, and
let `(f_i)_{i ≥ i₀}` be a morphism of the inverse systems of scheme-theoretic images
`X = lim X_i` and `Y = lim Y_i` whose limit is `f`, as in Stacks 0CPA. If `f` is proper, then
there is a stage `i₃ ≥ i₀` such that `f_i` is proper for every `i ≥ i₃`. -/
@[stacks 0CPE]
theorem exists_isProper (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsX : IsQuasiSeparated B S hS pX)
    (qsY : IsQuasiSeparated B S hS pY) (small : Cardinal.mk I < B.cutoff.ord.cof)
    (F : SystemMorphism GX GY f i₀ leX leY) (proper : IsProper B S hS f) :
    ∃ i₃ : I, i₀ ≤ i₃ ∧ ∀ k : Over (op i₀), i₃ ≤ k.left.unop →
      IsProper B S hS (F.maps.app k) := by
  classical
  have hf : f ≫ pY = pX := F.comp_structureMap_eq
  -- `Y` is quasi-compact and quasi-separated.
  have qcY : IsQuasiCompactSpace B S hS Y :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS
      (tailSystem_isAlgebraicSpace GY leY (Over.mk (𝟙 (op i₀))))
      (tailSystem_isQuasiCompactSpace GY leY _)
      (isQuasiCompact_tailCone_π GY leY small (Over.mk (𝟙 (op i₀))))
  have qsYa : IsAbsolutelyQuasiSeparated B S hS hZ Y :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_limitCone algY small qsY
  -- Stacks 0A0W: a closed immersion `X ⟶ X'` with `X'` proper and of finite presentation over `Y`.
  obtain ⟨J, _, _, ⟨j⟩, D', t, pr, algD', htD', -, hpr, hprt, -⟩ :=
    exists_isLimit_isProper_isFinitePresentation_of_isProper B S hS algX algY f proper qcY qsYa
  have hιp : pr.app (op j) ≫ t.app (op j) = f := by
    simpa using congrArg (fun φ => φ.app (op j)) hprt
  -- Stacks 07SK and 08K1: `X' ⟶ Y` is the base change of a proper `W ⟶ Y_m`.
  obtain ⟨n, W, algW, w, toW, properW, sqW⟩ :=
    exists_proper_model (algD' _) algY qsY small GY leY (t.app (op j)) (htD' _).1 (htD' _).2
  have hm : i₀ ≤ n.left.unop := leOfHom n.hom.unop
  let w' : W ⟶ stageAt GY n.left.unop (leY.trans hm) := w
  have sqW' : IsPullback toW (t.app (op j)) w' (stageπ GY n.left.unop (leY.trans hm)) := sqW
  -- The image system of the diagram `X ⟶ W` over `B ⟶ B_m` is proper over that of `Y`.
  obtain ⟨F', hF'⟩ := exists_systemMorphism_properModel GY f hf (leY.trans hm) algW w'
    properW.2.1 (pr.app (op j)) (hpr _) (t.app (op j)) toW sqW' hιp
  have hF'p := isProper_app_properModel GY f hf (leY.trans hm) algW w' (pr.app (op j)) (hpr _)
    (t.app (op j)) toW sqW' hιp properW F' hF'
  -- Remark 0CPB: the two image systems of `X` are eventually isomorphic.
  obtain ⟨a, ha, ha', E, E', i₁, h₁, hinv⟩ := exists_systemMorphism_inv algX qsX small GX
    (properModel GY f hf (leY.trans hm) algW w' properW.2.1 (pr.app (op j)) (hpr _)
      (t.app (op j)) toW sqW' hιp)
  obtain ⟨c, hac, hmc⟩ := exists_ge_ge a n.left.unop
  -- Stacks 0CPA, eventual uniqueness: `F` eventually factors through the comparison.
  obtain ⟨i₂, h₀₂, hc₂, heq⟩ := exists_forall_app_eq algX qsX small F
    ((E.restrict hac).comp (F'.restrict hmc) (Category.id_comp f))
  obtain ⟨i₃, h₂₃, h₁₃⟩ := exists_ge_ge i₂ i₁
  refine ⟨i₃, h₀₂.trans h₂₃, fun k hk => ?_⟩
  have hi₂ : i₂ ≤ k.left.unop := h₂₃.trans hk
  have hi₁ : i₁ ≤ k.left.unop := h₁₃.trans hk
  have key : F.app k.left.unop (h₀₂.trans hi₂) =
      E.app _ (h₁.trans hi₁) ≫ F'.app _ (hmc.trans (hc₂.trans hi₂)) := by
    rw [heq _ hi₂]
    rfl
  have : IsIso (E.app k.left.unop (h₁.trans hi₁)) :=
    ⟨⟨E'.app _ (h₁.trans hi₁), (hinv _ hi₁).1, (hinv _ hi₁).2⟩⟩
  have hP : IsProper B S hS (E.app _ (h₁.trans hi₁) ≫ F'.app _ (hmc.trans (hc₂.trans hi₂))) :=
    isProper_of_isPullback_presheaf B S hS (imageSystem_isAlgebraicSpace GX _)
      (imageSystem_isAlgebraicSpace _ _) (imageSystem_isAlgebraicSpace GY _)
      (imageSystem_isAlgebraicSpace GY _)
      (IsPullback.of_horiz_isIso (fst := E.app _ (h₁.trans hi₁)) (g := 𝟙 _)
        ⟨(Category.comp_id _).symm⟩) (hF'p _ _)
  rwa [← key] at hP

end SystemMorphism

end GoodDiagram

end AlgebraicGeometry.Space

end
