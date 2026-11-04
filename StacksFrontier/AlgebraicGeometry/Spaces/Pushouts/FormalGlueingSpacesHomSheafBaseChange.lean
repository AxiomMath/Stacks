module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGlueBaseChange

/-!
# Base change of the sheaf of glueing-data morphisms

Let `c : D ⟶ D'` be a cartesian morphism of formal glueing situations over `q : X' ⟶ X`
(`AlgebraicGeometry.Space.FormalGlueingSituation.CartesianMap`) and `G` a glueing triple for `D`,
with base change `G'` for `D'`. For a space `A` over `X'`, a morphism of glueing data
`Φ_{D'}(A) ⟶ G'` is the same as a morphism `Φ_D(A) ⟶ G`, where `A` is read over `X` through
`q`: on each leg this is the universal property of the base change, and the two compatibilities
over the overlaps correspond. Consequently the sheaf `W ↦ {(w, φ : Φ(W, w) ⟶ G)}` of
glueing-data morphisms base changes along `q` to the corresponding sheaf for `D'` and `G'`.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.CartesianMap.commaHomEquiv`: the bijection
  `(Φ_{D'}(A) ⟶ G') ≃ (Φ_D(A) ⟶ G)`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.CartesianMap.homPresheafBaseChange`: the
  induced morphism of sheaves.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.CartesianMap.isPullback_homPresheafBaseChange`:
  the square formed with the two projections and `q` is cartesian.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space.FormalGlueingSituation

/-! ### Generalities on morphisms into a base change -/

/-- Morphisms into a base change `M ×_U U'`, read over `U` through an identification of the
source with an object over `U`. -/
noncomputable def overPullbackHomEquiv {C : Type w} [Category.{v} C] [HasPullbacks C] {U U' : C}
    (g : U' ⟶ U) {L : Over U'} {K M : Over U} (e : L.left ≅ K.left)
    (he : e.hom ≫ K.hom = L.hom ≫ g) :
    (L ⟶ (Over.pullback g).obj M) ≃ (K ⟶ M) where
  toFun m := Over.homMk (e.inv ≫ m.left ≫ pullback.fst M.hom g) (by
    have h1 : m.left ≫ pullback.snd M.hom g = L.hom := Over.w m
    have h2 : e.inv ≫ L.hom ≫ g = K.hom := by rw [← he, e.inv_hom_id_assoc]
    simp only [Category.assoc, pullback.condition, reassoc_of% h1, h2])
  invFun k := Over.homMk (pullback.lift (e.hom ≫ k.left) L.hom (by
      rw [Category.assoc, Over.w k, he])) (pullback.lift_snd _ _ _)
  left_inv m := by
    have h1 : m.left ≫ pullback.snd M.hom g = L.hom := Over.w m
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · simp only [Over.homMk_left, Over.pullback_obj_left, pullback.lift_fst, e.hom_inv_id_assoc]
    · simp only [Over.homMk_left, Over.pullback_obj_left, pullback.lift_snd, h1]
  right_inv k := by
    refine Over.OverMorphism.ext ?_
    simp only [Over.homMk_left, Over.pullback_obj_left, pullback.lift_fst, e.inv_hom_id_assoc]

/-- The underlying morphism of `overPullbackHomEquiv g e he m` is `e⁻¹ ≫ m ≫ pr₁`. -/
theorem overPullbackHomEquiv_apply_left {C : Type w} [Category.{v} C] [HasPullbacks C] {U U' : C}
    (g : U' ⟶ U) {L : Over U'} {K M : Over U} (e : L.left ≅ K.left)
    (he : e.hom ≫ K.hom = L.hom ≫ g) (m : L ⟶ (Over.pullback g).obj M) :
    (overPullbackHomEquiv g e he m).left = e.inv ≫ m.left ≫ pullback.fst M.hom g :=
  rfl

/-- Two morphisms over `V` into a base change `M ×_X V` agree once their first projections
agree. -/
theorem overPullback_hom_ext {C : Type w} [Category.{v} C] [HasPullbacks C] {X V : C} (j : V ⟶ X)
    {P : Over V} {M : Over X} {a b : P ⟶ (Over.pullback j).obj M}
    (h : a.left ≫ pullback.fst M.hom j = b.left ≫ pullback.fst M.hom j) : a = b := by
  refine Over.OverMorphism.ext (pullback.hom_ext h ?_)
  have ha : a.left ≫ pullback.snd M.hom j = P.hom := Over.w a
  have hb : b.left ≫ pullback.snd M.hom j = P.hom := Over.w b
  rw [ha, hb]

/-- Two morphisms over `V'` into an iterated base change `(M ×_Y Y') ×_{Y'} V'` agree once their
projections to `M` agree. -/
theorem overPullback_pullback_hom_ext {C : Type w} [Category.{v} C] [HasPullbacks C] {Y Y' V' : C}
    (g : Y' ⟶ Y) (j : V' ⟶ Y') {P : Over V'} {M : Over Y}
    {a b : P ⟶ (Over.pullback j).obj ((Over.pullback g).obj M)}
    (h : a.left ≫ pullback.fst (pullback.snd M.hom g) j ≫ pullback.fst M.hom g =
      b.left ≫ pullback.fst (pullback.snd M.hom g) j ≫ pullback.fst M.hom g) : a = b := by
  refine overPullback_hom_ext j (pullback.hom_ext (by simp only [Category.assoc]; exact h) ?_)
  have ha : a.left ≫ pullback.snd (pullback.snd M.hom g) j = P.hom := Over.w a
  have hb : b.left ≫ pullback.snd (pullback.snd M.hom g) j = P.hom := Over.w b
  simp only [Over.pullback_obj_hom, Over.pullback_obj_left, Category.assoc] at ha hb ⊢
  rw [pullback.condition, reassoc_of% ha, reassoc_of% hb]

/-! ### The bijection of glueing-data morphisms -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {D D' : FormalGlueingSituation B S hS} (c : CartesianMap D D') (G : glueingData D)

/-- `A ×_{X'} U' = A ×_X U`, for `A` over `X'`. -/
theorem CartesianMap.isPullbackU (A : Over D'.X) :
    IsPullback (pullback.fst A.hom D'.U.ι) (pullback.snd A.hom D'.U.ι ≫ c.gU) (A.hom ≫ c.q)
      D.U.ι :=
  (IsPullback.of_hasPullback A.hom D'.U.ι).paste_vert c.hUsq.flip

/-- `A ×_{X'} Y' = A ×_X Y`, for `A` over `X'`. -/
theorem CartesianMap.isPullbackY (A : Over D'.X) :
    IsPullback (pullback.fst A.hom D'.f) (pullback.snd A.hom D'.f ≫ c.gY) (A.hom ≫ c.q) D.f :=
  (IsPullback.of_hasPullback A.hom D'.f).paste_vert c.hYsq.flip

/-- The identification of the `U`-leg of `Φ_{D'}(A)` with that of `Φ_D(A)`. -/
noncomputable abbrev CartesianMap.isoU (A : Over D'.X) :
    pullback A.hom D'.U.ι ≅ pullback (A.hom ≫ c.q) D.U.ι :=
  (c.isPullbackU A).isoPullback

/-- The identification of the `Y`-leg of `Φ_{D'}(A)` with that of `Φ_D(A)`. -/
noncomputable abbrev CartesianMap.isoY (A : Over D'.X) :
    pullback A.hom D'.f ≅ pullback (A.hom ≫ c.q) D.f :=
  (c.isPullbackY A).isoPullback

/-- Morphisms into the `U`-leg of `G'`, read as morphisms into the `U`-leg of `G`. -/
noncomputable abbrev CartesianMap.legUEquiv (A : Over D'.X) :
    ((Over.pullback D'.U.ι).obj A ⟶ (Over.pullback c.gU).obj G.obj.left) ≃
      ((Over.pullback D.U.ι).obj (Over.mk (A.hom ≫ c.q)) ⟶ G.obj.left) :=
  overPullbackHomEquiv c.gU (c.isoU A) (c.isPullbackU A).isoPullback_hom_snd

/-- Morphisms into the `Y`-leg of `G'`, read as morphisms into the `Y`-leg of `G`. -/
noncomputable abbrev CartesianMap.legYEquiv (A : Over D'.X) :
    ((Over.pullback D'.f).obj A ⟶ (Over.pullback c.gY).obj G.obj.right) ≃
      ((Over.pullback D.f).obj (Over.mk (A.hom ≫ c.q)) ⟶ G.obj.right) :=
  overPullbackHomEquiv c.gY (c.isoY A) (c.isPullbackY A).isoPullback_hom_snd

/-- The overlap `(A ×_{X'} U') ×_{U'} V'` of `Φ_{D'}(A)` is the overlap `(A ×_X U) ×_U V` of
`Φ_D(A)`. -/
theorem CartesianMap.isPullbackOverlap (A : Over D'.X) :
    IsPullback (pullback.fst (pullback.snd A.hom D'.U.ι) (D'.U.fromPreimage D'.f) ≫
        (c.isoU A).hom)
      (pullback.snd (pullback.snd A.hom D'.U.ι) (D'.U.fromPreimage D'.f) ≫ c.gV)
      (pullback.snd (A.hom ≫ c.q) D.U.ι) (D.U.fromPreimage D.f) := by
  have big := (IsPullback.of_hasPullback (pullback.snd A.hom D'.U.ι)
    (D'.U.fromPreimage D'.f)).paste_vert c.hWsq
  have hsq : IsPullback (c.isoU A).hom (pullback.snd A.hom D'.U.ι ≫ c.gU)
      (pullback.snd (A.hom ≫ c.q) D.U.ι) (𝟙 D.U.toFunctor) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, (c.isPullbackU A).isoPullback_hom_snd]⟩
  have h := big.paste_horiz hsq
  rwa [Category.comp_id] at h

/-- The identification of the overlaps of `Φ_{D'}(A)` and `Φ_D(A)`. -/
noncomputable abbrev CartesianMap.isoOverlap (A : Over D'.X) :
    pullback (pullback.snd A.hom D'.U.ι) (D'.U.fromPreimage D'.f) ≅
      pullback (pullback.snd (A.hom ≫ c.q) D.U.ι) (D.U.fromPreimage D.f) :=
  (c.isPullbackOverlap A).isoPullback

/-- The identification of the overlaps commutes with the first projections, via `isoU`. -/
@[reassoc]
theorem CartesianMap.isoOverlap_hom_fst (A : Over D'.X) :
    (c.isoOverlap A).hom ≫ pullback.fst (pullback.snd (A.hom ≫ c.q) D.U.ι) (D.U.fromPreimage D.f) =
      pullback.fst (pullback.snd A.hom D'.U.ι) (D'.U.fromPreimage D'.f) ≫ (c.isoU A).hom :=
  (c.isPullbackOverlap A).isoPullback_hom_fst

/-- The identification of the overlaps commutes with the second projections, via `c.gV`. -/
@[reassoc]
theorem CartesianMap.isoOverlap_hom_snd (A : Over D'.X) :
    (c.isoOverlap A).hom ≫ pullback.snd (pullback.snd (A.hom ≫ c.q) D.U.ι) (D.U.fromPreimage D.f) =
      pullback.snd (pullback.snd A.hom D'.U.ι) (D'.U.fromPreimage D'.f) ≫ c.gV :=
  (c.isPullbackOverlap A).isoPullback_hom_snd

/-- The overlap identifications of `Φ_{D'}(A)` and of `Φ_D(A)` correspond. -/
theorem CartesianMap.isoOverlap_comparison (A : Over D'.X) :
    (c.isoOverlap A).hom ≫ ((restrictionComparison D).hom.app (Over.mk (A.hom ≫ c.q))).left ≫
        pullback.fst (pullback.snd (A.hom ≫ c.q) D.f) D.V.ι =
      ((restrictionComparison D').hom.app A).left ≫
        pullback.fst (pullback.snd A.hom D'.f) D'.V.ι ≫ (c.isoY A).hom := by
  refine pullback.hom_ext ?_ ?_
  · have h₁ := restrictionComparison_hom_app_left_fst_fst D (Over.mk (A.hom ≫ c.q))
    have h₂ := restrictionComparison_hom_app_left_fst_fst D' A
    simp only [Over.mk_hom] at h₁
    simp only [Category.assoc, (c.isPullbackY A).isoPullback_hom_fst]
    rw [h₁, h₂, c.isoOverlap_hom_fst_assoc, (c.isPullbackU A).isoPullback_hom_fst]
  · have hw : ((restrictionComparison D).hom.app (Over.mk (A.hom ≫ c.q))).left ≫
        pullback.snd (pullback.snd (A.hom ≫ c.q) D.f) D.V.ι =
          pullback.snd (pullback.snd (A.hom ≫ c.q) D.U.ι) (D.U.fromPreimage D.f) :=
      Over.w ((restrictionComparison D).hom.app (Over.mk (A.hom ≫ c.q)))
    have hw' : ((restrictionComparison D').hom.app A).left ≫
        pullback.snd (pullback.snd A.hom D'.f) D'.V.ι =
          pullback.snd (pullback.snd A.hom D'.U.ι) (D'.U.fromPreimage D'.f) :=
      Over.w ((restrictionComparison D').hom.app A)
    simp only [Category.assoc, (c.isPullbackY A).isoPullback_hom_snd]
    rw [pullback.condition, reassoc_of% hw, c.isoOverlap_hom_snd_assoc,
      pullback.condition_assoc, reassoc_of% hw', c.hVsq.w]

/-- The map `(G_U ×_U U') ×_{U'} V' ⟶ G_U ×_U V` underlying the overlap of `G'`. -/
noncomputable abbrev CartesianMap.overlapLeftMap :
    pullback (pullback.snd G.obj.left.hom c.gU) (D'.U.fromPreimage D'.f) ⟶
      pullback G.obj.left.hom (D.U.fromPreimage D.f) :=
  pullback.lift (pullback.fst (pullback.snd G.obj.left.hom c.gU) (D'.U.fromPreimage D'.f) ≫
      pullback.fst G.obj.left.hom c.gU)
    (pullback.snd (pullback.snd G.obj.left.hom c.gU) (D'.U.fromPreimage D'.f) ≫ c.gV) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc, c.hW])

/-- The overlap identification of `G'`, read on the projections to `G_Y`. -/
theorem CartesianMap.overlapIso_hom_fst_fst :
    (c.overlapIso G).hom ≫ pullback.fst (pullback.snd G.obj.right.hom c.gY) D'.V.ι ≫
        pullback.fst G.obj.right.hom c.gY =
      c.overlapLeftMap G ≫ G.obj.hom.left ≫ pullback.fst G.obj.right.hom D.V.ι := by
  have hO := IsPullback.isoIsPullback_hom_fst _ _ (c.isPullback_left_comp G)
    (c.isPullback_right G)
  have h := hO =≫ pullback.fst G.obj.right.hom D.V.ι
  simp only [Category.assoc, pullback.lift_fst] at h
  exact h

/-- The left side of the compatibility over the overlap, for `D'` and for `D`. -/
theorem CartesianMap.overlap_left (A : Over D'.X)
    (l' : (Over.pullback D'.U.ι).obj A ⟶ (Over.pullback c.gU).obj G.obj.left) :
    ((Over.pullback (D'.U.fromPreimage D'.f)).map l').left ≫ (c.overlapIso G).hom ≫
        pullback.fst (pullback.snd G.obj.right.hom c.gY) D'.V.ι ≫
        pullback.fst G.obj.right.hom c.gY =
      (c.isoOverlap A).hom ≫ ((Over.pullback (D.U.fromPreimage D.f)).map
        (c.legUEquiv G A l')).left ≫ G.obj.hom.left ≫ pullback.fst G.obj.right.hom D.V.ι := by
  have key : ((Over.pullback (D'.U.fromPreimage D'.f)).map l').left ≫ c.overlapLeftMap G =
      (c.isoOverlap A).hom ≫ ((Over.pullback (D.U.fromPreimage D.f)).map
        (c.legUEquiv G A l')).left := by
    have e1 := overPullback_map_left_comp_fst (D'.U.fromPreimage D'.f) l'
    have e2 := overPullback_map_left_comp_snd (D'.U.fromPreimage D'.f) l'
    have e3 := overPullback_map_left_comp_fst (D.U.fromPreimage D.f) (c.legUEquiv G A l')
    have e4 := overPullback_map_left_comp_snd (D.U.fromPreimage D.f) (c.legUEquiv G A l')
    simp only [Over.pullback_obj_hom, Over.pullback_obj_left, Over.mk_hom] at e1 e2 e3 e4
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, reassoc_of% e1, e3,
        c.isoOverlap_hom_fst_assoc]
      simp [overPullbackHomEquiv_apply_left]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, reassoc_of% e2, e4,
        c.isoOverlap_hom_snd]
  rw [c.overlapIso_hom_fst_fst G, reassoc_of% key]

/-- The right side of the compatibility over the overlap, for `D'` and for `D`. -/
theorem CartesianMap.overlap_right (A : Over D'.X)
    (r' : (Over.pullback D'.f).obj A ⟶ (Over.pullback c.gY).obj G.obj.right) :
    ((restrictionComparison D').hom.app A).left ≫ ((Over.pullback D'.V.ι).map r').left ≫
        pullback.fst (pullback.snd G.obj.right.hom c.gY) D'.V.ι ≫
        pullback.fst G.obj.right.hom c.gY =
      (c.isoOverlap A).hom ≫ ((restrictionComparison D).hom.app (Over.mk (A.hom ≫ c.q))).left ≫
        ((Over.pullback D.V.ι).map (c.legYEquiv G A r')).left ≫
        pullback.fst G.obj.right.hom D.V.ι := by
  have e1 := overPullback_map_left_comp_fst D'.V.ι r'
  have e2 := overPullback_map_left_comp_fst D.V.ι (c.legYEquiv G A r')
  simp only [Over.pullback_obj_hom, Over.pullback_obj_left, Over.mk_hom] at e1 e2 ⊢
  rw [reassoc_of% e1, e2, reassoc_of% (c.isoOverlap_comparison A)]
  simp [overPullbackHomEquiv_apply_left]

/-- **The compatibility over the overlap corresponds.** A pair of morphisms into the two legs
of `G'` is a morphism of glueing data for `D'` exactly when the corresponding pair into the two
legs of `G` is one for `D`. -/
theorem CartesianMap.w_iff (A : Over D'.X)
    (l' : (Over.pullback D'.U.ι).obj A ⟶ (Over.pullback c.gU).obj G.obj.left)
    (r' : (Over.pullback D'.f).obj A ⟶ (Over.pullback c.gY).obj G.obj.right) :
    (Over.pullback (D'.U.fromPreimage D'.f)).map l' ≫ (glueingBaseChange c G).obj.hom =
        (restrictionComparison D').hom.app A ≫ (Over.pullback D'.V.ι).map r' ↔
      (Over.pullback (D.U.fromPreimage D.f)).map (c.legUEquiv G A l') ≫ G.obj.hom =
        (restrictionComparison D).hom.app (Over.mk (A.hom ≫ c.q)) ≫
          (Over.pullback D.V.ι).map (c.legYEquiv G A r') := by
  have hl := c.overlap_left G A l'
  have hr := c.overlap_right G A r'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine overPullback_hom_ext _ ?_
    have h' := congrArg (fun k => k.left ≫ pullback.fst (pullback.snd G.obj.right.hom c.gY)
      D'.V.ι ≫ pullback.fst G.obj.right.hom c.gY) h
    simp only [Over.comp_left, Category.assoc] at h' ⊢
    refine (cancel_epi (c.isoOverlap A).hom).1 ?_
    rwa [← hl, ← hr]
  · refine overPullback_pullback_hom_ext _ _ ?_
    have e1 : ((Over.pullback (D'.U.fromPreimage D'.f)).map l' ≫
        (glueingBaseChange c G).obj.hom).left =
          ((Over.pullback (D'.U.fromPreimage D'.f)).map l').left ≫ (c.overlapIso G).hom := rfl
    have e2 : ((restrictionComparison D').hom.app A ≫ (Over.pullback D'.V.ι).map r').left =
        ((restrictionComparison D').hom.app A).left ≫ ((Over.pullback D'.V.ι).map r').left := rfl
    rw [e1, e2, Category.assoc, Category.assoc, hl, hr]
    have h' := congrArg (fun k => k.left ≫ pullback.fst G.obj.right.hom D.V.ι) h
    simp only [Over.comp_left, Category.assoc] at h'
    rw [h']

/-- **Morphisms of glueing data into `G'` are morphisms into `G`.** For `A` over `X'`, a morphism
`Φ_{D'}(A) ⟶ G'` is the same as a morphism `Φ_D(A) ⟶ G`, `A` read over `X` through `q`. -/
noncomputable def CartesianMap.commaHomEquiv (A : Over D'.X) :
    ((restrictionDiagram D').obj A ⟶ (glueingBaseChange c G).obj) ≃
      ((restrictionDiagram D).obj (Over.mk (A.hom ≫ c.q)) ⟶ G.obj) where
  toFun φ' :=
    { left := c.legUEquiv G A φ'.left
      right := c.legYEquiv G A φ'.right
      w := (c.w_iff G A φ'.left φ'.right).1 φ'.w }
  invFun φ :=
    { left := (c.legUEquiv G A).symm φ.left
      right := (c.legYEquiv G A).symm φ.right
      w := (c.w_iff G A _ _).2 (by
        rw [(c.legUEquiv G A).apply_symm_apply φ.left,
          (c.legYEquiv G A).apply_symm_apply φ.right]
        exact φ.w) }
  left_inv φ' := Comma.hom_ext _ _ ((c.legUEquiv G A).symm_apply_apply φ'.left)
    ((c.legYEquiv G A).symm_apply_apply φ'.right)
  right_inv φ := Comma.hom_ext _ _ ((c.legUEquiv G A).apply_symm_apply φ.left)
    ((c.legYEquiv G A).apply_symm_apply φ.right)

/-- The `U`-leg of `c.commaHomEquiv G A φ'` is `isoU⁻¹ ≫ φ'_U ≫ pr₁`. -/
theorem CartesianMap.commaHomEquiv_left (A : Over D'.X)
    (φ' : (restrictionDiagram D').obj A ⟶ (glueingBaseChange c G).obj) :
    (c.commaHomEquiv G A φ').left.left =
      (c.isoU A).inv ≫ φ'.left.left ≫ pullback.fst G.obj.left.hom c.gU := by
  dsimp only [CartesianMap.commaHomEquiv, Equiv.coe_fn_mk]
  exact overPullbackHomEquiv_apply_left _ _ _ _

/-- The `Y`-leg of `c.commaHomEquiv G A φ'` is `isoY⁻¹ ≫ φ'_Y ≫ pr₁`. -/
theorem CartesianMap.commaHomEquiv_right (A : Over D'.X)
    (φ' : (restrictionDiagram D').obj A ⟶ (glueingBaseChange c G).obj) :
    (c.commaHomEquiv G A φ').right.left =
      (c.isoY A).inv ≫ φ'.right.left ≫ pullback.fst G.obj.right.hom c.gY := by
  dsimp only [CartesianMap.commaHomEquiv, Equiv.coe_fn_mk]
  exact overPullbackHomEquiv_apply_left _ _ _ _

/-- A morphism over `X'`, read over `X`. -/
abbrev CartesianMap.overHom {A₁ A₂ : Over D'.X} (h : A₁ ⟶ A₂) :
    Over.mk (A₁.hom ≫ c.q) ⟶ Over.mk (A₂.hom ≫ c.q) :=
  Over.homMk h.left (by simp)

/-- The comparison of base changes along a pullback square over `q` is natural in the object
over `X'`. -/
private theorem overPullback_map_left_comp_isoPullback_hom {C : Type w} [Category.{v} C]
    [HasPullbacks C] {X X' Z Z' : C} (q : X' ⟶ X) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : Z' ⟶ Z)
    {A₁ A₂ : Over X'} (h : A₁ ⟶ A₂)
    (P₁ : IsPullback (pullback.fst A₁.hom i') (pullback.snd A₁.hom i' ≫ g) (A₁.hom ≫ q) i)
    (P₂ : IsPullback (pullback.fst A₂.hom i') (pullback.snd A₂.hom i' ≫ g) (A₂.hom ≫ q) i) :
    ((Over.pullback i').map h).left ≫ P₂.isoPullback.hom =
      P₁.isoPullback.hom ≫ ((Over.pullback i).map
        (Over.homMk h.left (by simp) : Over.mk (A₁.hom ≫ q) ⟶ Over.mk (A₂.hom ≫ q))).left := by
  have e1 := overPullback_map_left_comp_fst i' h
  have e2 := overPullback_map_left_comp_snd i' h
  have e3 := overPullback_map_left_comp_fst i
    (Over.homMk h.left (by simp) : Over.mk (A₁.hom ≫ q) ⟶ Over.mk (A₂.hom ≫ q))
  have e4 := overPullback_map_left_comp_snd i
    (Over.homMk h.left (by simp) : Over.mk (A₁.hom ≫ q) ⟶ Over.mk (A₂.hom ≫ q))
  simp only [Over.mk_hom, Over.homMk_left] at e1 e2 e3 e4
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, P₂.isoPullback_hom_fst, e1, e3,
      P₁.isoPullback_hom_fst_assoc]
  · rw [Category.assoc, Category.assoc, P₂.isoPullback_hom_snd, reassoc_of% e2, e4,
      P₁.isoPullback_hom_snd]

/-- The identification `isoU` is natural in the space over `X'`. -/
@[reassoc]
theorem CartesianMap.isoU_hom_naturality {A₁ A₂ : Over D'.X} (h : A₁ ⟶ A₂) :
    ((Over.pullback D'.U.ι).map h).left ≫ (c.isoU A₂).hom =
      (c.isoU A₁).hom ≫ ((Over.pullback D.U.ι).map (c.overHom h)).left :=
  overPullback_map_left_comp_isoPullback_hom c.q _ _ _ h _ _

/-- The identification `isoY` is natural in the space over `X'`. -/
@[reassoc]
theorem CartesianMap.isoY_hom_naturality {A₁ A₂ : Over D'.X} (h : A₁ ⟶ A₂) :
    ((Over.pullback D'.f).map h).left ≫ (c.isoY A₂).hom =
      (c.isoY A₁).hom ≫ ((Over.pullback D.f).map (c.overHom h)).left :=
  overPullback_map_left_comp_isoPullback_hom c.q _ _ _ h _ _

/-- The bijection is natural in the space over `X'`. -/
theorem CartesianMap.commaHomEquiv_naturality {A₁ A₂ : Over D'.X} (h : A₁ ⟶ A₂)
    (φ' : (restrictionDiagram D').obj A₂ ⟶ (glueingBaseChange c G).obj) :
    c.commaHomEquiv G A₁ ((restrictionDiagram D').map h ≫ φ') =
      (restrictionDiagram D).map (c.overHom h) ≫ c.commaHomEquiv G A₂ φ' := by
  refine Comma.hom_ext _ _ (Over.OverMorphism.ext ?_) (Over.OverMorphism.ext ?_)
  · rw [c.commaHomEquiv_left, Comma.comp_left, Comma.comp_left, Over.comp_left, Over.comp_left,
      c.commaHomEquiv_left]
    show (c.isoU A₁).inv ≫ (((Over.pullback D'.U.ι).map h).left ≫ φ'.left.left) ≫
        pullback.fst G.obj.left.hom c.gU =
      ((Over.pullback D.U.ι).map (c.overHom h)).left ≫ (c.isoU A₂).inv ≫ φ'.left.left ≫
        pullback.fst G.obj.left.hom c.gU
    rw [Iso.inv_comp_eq]
    simp only
    rw [← c.isoU_hom_naturality_assoc, Iso.hom_inv_id_assoc]
    exact Category.assoc _ _ _
  · rw [c.commaHomEquiv_right, Comma.comp_right, Comma.comp_right, Over.comp_left,
      Over.comp_left, c.commaHomEquiv_right]
    show (c.isoY A₁).inv ≫ (((Over.pullback D'.f).map h).left ≫ φ'.right.left) ≫
        pullback.fst G.obj.right.hom c.gY =
      ((Over.pullback D.f).map (c.overHom h)).left ≫ (c.isoY A₂).inv ≫ φ'.right.left ≫
        pullback.fst G.obj.right.hom c.gY
    rw [Iso.inv_comp_eq]
    simp only
    rw [← c.isoY_hom_naturality_assoc, Iso.hom_inv_id_assoc]
    exact Category.assoc _ _ _

/-! ### The base change of the sheaf of glueing-data morphisms -/

/-- A pair `(a, φ')` for `D'` and `G'` read as a pair `(a ≫ q, φ)` for `D` and `G`. -/
noncomputable def CartesianMap.glueSectionsMap {W : BigFppfOver B S hS}
    (s : glueSections D' (glueingBaseChange c G) W) : glueSections D G W :=
  ⟨s.1 ≫ c.q, c.commaHomEquiv G (Over.mk s.1) s.2⟩

/-- `glueSectionsMap` commutes with restriction along a morphism `W' ⟶ W`. -/
theorem CartesianMap.glueSectionsMap_restrict {W W' : BigFppfOver B S hS} (g : W' ⟶ W)
    (s : glueSections D' (glueingBaseChange c G) W) :
    (c.glueSectionsMap G s).restrict g = c.glueSectionsMap G (s.restrict g) := by
  refine glueSections.ext' (Category.assoc _ _ _) ?_
  show (restrictionDiagram D).map _ ≫ c.commaHomEquiv G (Over.mk s.1) s.2 =
    _ ≫ c.commaHomEquiv G (Over.mk (yoneda.map g ≫ s.1)) ((restrictionDiagram D').map _ ≫ s.2)
  rw [c.commaHomEquiv_naturality]
  have h : (restrictionDiagram D).map (Over.homMk (yoneda.map g) (by simp) :
      Over.mk (yoneda.map g ≫ s.1 ≫ c.q) ⟶ Over.mk (s.1 ≫ c.q)) =
      (restrictionDiagram D).map (Over.homMk (𝟙 _) (by simp) :
        Over.mk (yoneda.map g ≫ s.1 ≫ c.q) ⟶ Over.mk ((yoneda.map g ≫ s.1) ≫ c.q)) ≫
      (restrictionDiagram D).map (c.overHom (Over.homMk (yoneda.map g) rfl :
        Over.mk (yoneda.map g ≫ s.1) ⟶ Over.mk s.1)) := by
    rw [← Functor.map_comp]
    congr 1
  exact (congrArg (· ≫ c.commaHomEquiv G (Over.mk s.1) s.2) h).trans (Category.assoc _ _ _)

/-- **The base change of the sheaf of glueing-data morphisms**: the morphism
`(a, φ') ↦ (a ≫ q, φ)` from the sheaf for `D'` and `G'` to the sheaf for `D` and `G`. -/
noncomputable def CartesianMap.homPresheafBaseChange :
    homPresheaf D' (glueingBaseChange c G) ⟶ homPresheaf D G where
  app W := ↾fun s => equivShrink (glueSections D G W.unop)
    (c.glueSectionsMap G ((equivShrink _).symm s))
  naturality W W' g := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    change equivShrink _ (c.glueSectionsMap G ((equivShrink _).symm (equivShrink _
        (((equivShrink (glueSections D' (glueingBaseChange c G) W.unop)).symm s).restrict
          g.unop)))) =
      equivShrink _ (((equivShrink _).symm (equivShrink (glueSections D G W.unop)
        (c.glueSectionsMap G ((equivShrink _).symm s)))).restrict g.unop)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, c.glueSectionsMap_restrict]

/-- `homPresheafBaseChange` lies over `q`: composed with the projection for `D` and `G`, it is
the projection for `D'` and `G'` followed by `q`. -/
theorem CartesianMap.homPresheafBaseChange_projection :
    c.homPresheafBaseChange G ≫ homPresheafProjection D G =
      homPresheafProjection D' (glueingBaseChange c G) ≫ c.q := by
  refine NatTrans.ext (funext fun W => ConcreteCategory.hom_ext _ _ fun s => ?_)
  show yonedaEquiv ((equivShrink _).symm (equivShrink _
    (c.glueSectionsMap G ((equivShrink _).symm s)))).1 =
      c.q.app W (yonedaEquiv ((equivShrink _).symm s).1)
  rw [Equiv.symm_apply_apply]
  exact yonedaEquiv_comp _ _

/-- `homPresheafBaseChange` sends the section corresponding to `s` to the one corresponding to
`c.glueSectionsMap G s`. -/
theorem CartesianMap.homPresheafBaseChange_app {W : BigFppfOver B S hS}
    (s : glueSections D' (glueingBaseChange c G) W) :
    (c.homPresheafBaseChange G).app (op W) (equivShrink _ s) =
      equivShrink _ (c.glueSectionsMap G s) := by
  show equivShrink _ (c.glueSectionsMap G ((equivShrink _).symm (equivShrink _ s))) = _
  rw [Equiv.symm_apply_apply]

/-- The projection sends the section corresponding to a pair `(a, φ)` to `a`. -/
theorem homPresheafProjection_app {D : FormalGlueingSituation B S hS} {G : glueingData D}
    {W : BigFppfOver B S hS} (s : glueSections D G W) :
    (homPresheafProjection D G).app (op W) (equivShrink _ s) = yonedaEquiv s.1 := by
  show yonedaEquiv ((equivShrink _).symm (equivShrink _ s)).1 = _
  rw [Equiv.symm_apply_apply]

/-- **The sheaf of glueing-data morphisms base changes along a cartesian morphism of
situations**: the square formed by `homPresheafBaseChange` and the two projections is
cartesian. -/
theorem CartesianMap.isPullback_homPresheafBaseChange :
    IsPullback (c.homPresheafBaseChange G) (homPresheafProjection D' (glueingBaseChange c G))
      (homPresheafProjection D G) c.q := by
  refine IsPullback.of_forall_isPullback_app fun W => ?_
  obtain ⟨W⟩ := W
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun k => k.app (op W)) (c.homPresheafBaseChange_projection G), ?_, ?_⟩
  · intro x y ⟨hxy, hxy'⟩
    obtain ⟨⟨a, φ⟩, rfl⟩ := (equivShrink (glueSections D' (glueingBaseChange c G) W)).surjective x
    obtain ⟨⟨b, ψ⟩, rfl⟩ := (equivShrink (glueSections D' (glueingBaseChange c G) W)).surjective y
    rw [c.homPresheafBaseChange_app, c.homPresheafBaseChange_app] at hxy
    replace hxy := (equivShrink (glueSections D G W)).injective hxy
    rw [homPresheafProjection_app, homPresheafProjection_app] at hxy'
    obtain rfl : a = b := yonedaEquiv.injective hxy'
    congr 1
    exact congrArg _ ((c.commaHomEquiv G (Over.mk a)).injective (eq_of_heq (Sigma.mk.inj hxy).2))
  · intro x a hxa
    obtain ⟨⟨w, φ⟩, rfl⟩ := (equivShrink (glueSections D G W)).surjective x
    rw [homPresheafProjection_app] at hxa
    have hw : yonedaEquiv.symm a ≫ c.q = w := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, hxa]
    refine ⟨equivShrink (glueSections D' (glueingBaseChange c G) W)
      ⟨yonedaEquiv.symm a, (c.commaHomEquiv G (Over.mk _)).symm
        ((restrictionDiagram D).map (Over.homMk (𝟙 _) (by rw [hw, Category.id_comp]) :
          Over.mk (yonedaEquiv.symm a ≫ c.q) ⟶ Over.mk w) ≫ φ)⟩, ?_, ?_⟩
    · rw [c.homPresheafBaseChange_app]
      congr 1
      refine glueSections.ext' hw ?_
      show c.commaHomEquiv G _ ((c.commaHomEquiv G _).symm _) = _
      rw [Equiv.apply_symm_apply]
    · rw [homPresheafProjection_app]
      exact Equiv.apply_symm_apply _ _

/-! ### Affineness over an arbitrary base -/

/-- **The sheaf of glueing-data morphisms into a triple with affine legs is affine over `X`**,
granted clause (1) of Stacks 0AF4 over affine bases. Its base change along a morphism from an
affine scheme `Z` is the corresponding sheaf for the base change of the situation to `Z`
(`CartesianMap.isPullback_homPresheafBaseChange`), which is affine over `Z` by
`isAffineHom_homPresheafProjection_of_affine`. -/
theorem isAffineHom_homPresheafProjection (hA : AffineBaseEssSurj B S hS)
    (D : FormalGlueingSituation B S hS) (G : glueingData D) (hG : affineLegs D G) :
    IsAffineHom B S hS (homPresheafProjection D G) := by
  intro Z g
  let c := CartesianMap.baseChangeAlong D
    (isAlgebraicSpace_yoneda B S hS ((BigAffineFppf.inclusion B S hS).obj Z)) g
  have h' := isAffineHom_homPresheafProjection_of_affine
    (D := D.baseChangeAlong (isAlgebraicSpace_yoneda B S hS _) g) hA
    ⟨(BigAffineFppf.inclusion B S hS).obj Z, Z.property, ⟨Iso.refl _⟩⟩
    (glueingBaseChange c G) (affineLegs_glueingBaseChange c G hG)
  obtain ⟨W, p, q, hpq⟩ := h' Z (𝟙 _)
  refine ⟨W, p ≫ c.homPresheafBaseChange G, q, ?_⟩
  convert hpq.paste_horiz (c.isPullback_homPresheafBaseChange G) using 1
  exact (Category.id_comp g).symm

end AlgebraicGeometry.Space.FormalGlueingSituation

end
