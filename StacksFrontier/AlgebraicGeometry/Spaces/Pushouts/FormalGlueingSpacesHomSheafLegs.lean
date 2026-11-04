module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafCounit

/-!
# The legs of the sheaf of glueing-data morphisms

In a formal glueing situation write `P = homPresheaf D G` for the sheaf of glueing-data
morphisms into a triple `G` with affine legs, and `π : P ⟶ X` for its projection. Granted
clause (1) of Stacks 0AF4 over affine bases, the evaluation morphisms `P ×_X U ⟶ G_U` and
`P ×_X Y ⟶ G_Y` are isomorphisms. Over an affine base this is the realization itself: there `P`
is the space realizing `G`. Over an arbitrary base the evaluation is compared, on sections over
an affine `W`, with the evaluation for the base change of the situation to `W`, which has an
affine base, along the cartesian morphism of situations of
`AlgebraicGeometry.Space.FormalGlueingSituation.CartesianMap.baseChangeAlong`.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.legEval_baseChange`: the evaluation commutes
  with base change along a cartesian morphism of situations.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isIso_legEvalU` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.isIso_legEvalY`: the two evaluations are
  isomorphisms.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Base change of the evaluation -/

section BaseChange

variable {D D' : FormalGlueingSituation B S hS} (c : CartesianMap D D') {G : glueingData D}
  {J : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : J ⟶ D.X) (M : Over J)
  (leg : ∀ A : Over D.X, ((restrictionDiagram D).obj A ⟶ G.obj) →
    ((Over.pullback j).obj A ⟶ M))
  (hleg : ∀ {A A' : Over D.X} (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj),
      leg A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback j).map h ≫ leg A' φ)
  {J' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j' : J' ⟶ D'.X) (gJ : J' ⟶ J)
  (hJ : gJ ≫ j = j' ≫ c.q)
  (leg' : ∀ A : Over D'.X, ((restrictionDiagram D').obj A ⟶ (glueingBaseChange c G).obj) →
    ((Over.pullback j').obj A ⟶ (Over.pullback gJ).obj M))
  (hleg' : ∀ {A A' : Over D'.X} (h : A ⟶ A')
      (φ : (restrictionDiagram D').obj A' ⟶ (glueingBaseChange c G).obj),
      leg' A ((restrictionDiagram D').map h ≫ φ) = (Over.pullback j').map h ≫ leg' A' φ)
  (hcomm : ∀ (A : Over D'.X)
      (φ' : (restrictionDiagram D').obj A ⟶ (glueingBaseChange c G).obj),
      (leg' A φ').left ≫ pullback.fst M.hom gJ =
        pullback.lift (pullback.fst A.hom j') (pullback.snd A.hom j' ≫ gJ) (by
          rw [Category.assoc, hJ, ← Category.assoc, ← pullback.condition, Category.assoc]
          rfl) ≫
          (leg (Over.mk (A.hom ≫ c.q)) (c.commaHomEquiv G A φ')).left)

/-- `legEval₀` depends on the morphism `b` only through its value. -/
theorem legEval₀_congr {D : FormalGlueingSituation B S hS} {G : glueingData D}
    {J : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : J ⟶ D.X) (M : Over J)
    (leg : ∀ A : Over D.X, ((restrictionDiagram D).obj A ⟶ G.obj) →
      ((Over.pullback j).obj A ⟶ M))
    {W : BigFppfOver B S hS} (t : glueSections D G W) {b b₂ : yoneda.obj W ⟶ J}
    (h : t.1 = b ≫ j) (hb : b = b₂) :
    legEval₀ j M leg t b h = legEval₀ j M leg t b₂ (hb ▸ h) := by
  subst hb
  rfl

/-- The glueing section corresponding to `y ≫ homPresheafBaseChange c G` is the image under
`glueSectionsMap` of the glueing section corresponding to `y`. -/
theorem homPresheafBaseChange_symm_yonedaEquiv {W : BigFppfOver B S hS}
    (y : yoneda.obj W ⟶ homPresheaf D' (glueingBaseChange c G)) :
    (equivShrink (glueSections D G W)).symm (yonedaEquiv (y ≫ c.homPresheafBaseChange G)) =
      c.glueSectionsMap G ((equivShrink _).symm (yonedaEquiv y)) := by
  rw [yonedaEquiv_comp]
  obtain ⟨s, hs⟩ := (equivShrink (glueSections D' (glueingBaseChange c G) W)).surjective
    (yonedaEquiv y)
  rw [← hs, c.homPresheafBaseChange_app, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

include hcomm in
/-- `legEval₀` commutes with base change along a cartesian morphism of situations. -/
theorem legEval₀_baseChange {W : BigFppfOver B S hS}
    (t' : glueSections D' (glueingBaseChange c G) W) (b' : yoneda.obj W ⟶ J')
    (h' : t'.1 = b' ≫ j') (h₂ : (c.glueSectionsMap G t').1 = (b' ≫ gJ) ≫ j) :
    legEval₀ j' ((Over.pullback gJ).obj M) leg' t' b' h' ≫ pullback.fst M.hom gJ =
      legEval₀ j M leg (c.glueSectionsMap G t') (b' ≫ gJ) h₂ := by
  obtain ⟨a', φ'⟩ := t'
  dsimp only [legEval₀, CartesianMap.glueSectionsMap] at h' h₂ ⊢
  rw [Category.assoc, hcomm, ← Category.assoc]
  congr 1
  refine pullback.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans ?_
    exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans ?_
    exact (pullback.lift_snd_assoc _ _ _ _).trans (pullback.lift_snd _ _ _).symm

include hcomm in
/-- **The evaluation commutes with base change along a cartesian morphism of situations.** -/
theorem legEval_baseChange :
    legEval j' ((Over.pullback gJ).obj M) leg' hleg' ≫ pullback.fst M.hom gJ =
      pullback.map (homPresheafProjection D' (glueingBaseChange c G)) j'
        (homPresheafProjection D G) j (c.homPresheafBaseChange G) gJ c.q
        (c.homPresheafBaseChange_projection G).symm hJ.symm ≫ legEval j M leg hleg := by
  refine hom_ext_yoneda fun W x => ?_
  rw [← Category.assoc, comp_legEval, ← Category.assoc, comp_legEval]
  have hx : (x ≫ pullback.map (homPresheafProjection D' (glueingBaseChange c G)) j'
      (homPresheafProjection D G) j (c.homPresheafBaseChange G) gJ c.q
      (c.homPresheafBaseChange_projection G).symm hJ.symm) ≫
        pullback.fst (homPresheafProjection D G) j =
      (x ≫ pullback.fst _ _) ≫ c.homPresheafBaseChange G := by
    simp only [Category.assoc, pullback.lift_fst]
  have hxs : (x ≫ pullback.map (homPresheafProjection D' (glueingBaseChange c G)) j'
      (homPresheafProjection D G) j (c.homPresheafBaseChange G) gJ c.q
      (c.homPresheafBaseChange_projection G).symm hJ.symm) ≫
        pullback.snd (homPresheafProjection D G) j =
      (x ≫ pullback.snd _ _) ≫ gJ := by
    simp only [Category.assoc, pullback.lift_snd]
  rw [legEvalYoneda_eq j M leg _ _ (by rw [hx, homPresheafBaseChange_symm_yonedaEquiv])
    (by
      change (_ : yoneda.obj W ⟶ D'.X) ≫ c.q = _
      rw [symm_yonedaEquiv_fst, hxs]
      simp only [Category.assoc, hJ]),
    legEval₀_congr j M leg _ _ hxs]
  exact legEval₀_baseChange c j M leg j' gJ hJ leg' hcomm _ _ _ _

/-- The base change of `P ×_X J` along a cartesian morphism of situations is `P' ×_{X'} J'`. -/
theorem isPullback_pullbackMap :
    IsPullback (pullback.map (homPresheafProjection D' (glueingBaseChange c G)) j'
        (homPresheafProjection D G) j (c.homPresheafBaseChange G) gJ c.q
        (c.homPresheafBaseChange_projection G).symm hJ.symm)
      (pullback.snd _ _) (pullback.snd _ _) gJ := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback (homPresheafProjection D G) j)
  rw [pullback.lift_fst, hJ]
  exact (IsPullback.of_hasPullback _ _).paste_horiz (c.isPullback_homPresheafBaseChange G)

end BaseChange

/-! ### The evaluations are isomorphisms -/

section Iso

variable {D : FormalGlueingSituation B S hS} {G : glueingData D}
  {J : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : J ⟶ D.X) (M : Over J)
  (leg : ∀ A : Over D.X, ((restrictionDiagram D).obj A ⟶ G.obj) →
    ((Over.pullback j).obj A ⟶ M))
  (hleg : ∀ {A A' : Over D.X} (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj),
      leg A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback j).map h ≫ leg A' φ)

/-- **The evaluation is an isomorphism once it is one after suitable base changes.** If over
every affine `W` and every `b : W ⟶ J` there is a cartesian morphism of situations through
whose `J`-part `b` factors and for which the evaluation is an isomorphism, then the evaluation
is an isomorphism. -/
theorem isIso_legEval_of_baseChange
    (hJs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) J)
    (hMs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) M.left)
    (H : ∀ (W : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
      ∀ b : yoneda.obj W ⟶ J, ∃ (D' : FormalGlueingSituation B S hS) (c : CartesianMap D D')
        (J' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j' : J' ⟶ D'.X) (gJ : J' ⟶ J)
        (hJ : gJ ≫ j = j' ≫ c.q)
        (leg' : ∀ A : Over D'.X,
          ((restrictionDiagram D').obj A ⟶ (glueingBaseChange c G).obj) →
          ((Over.pullback j').obj A ⟶ (Over.pullback gJ).obj M))
        (hleg' : ∀ {A A' : Over D'.X} (h : A ⟶ A')
          (φ : (restrictionDiagram D').obj A' ⟶ (glueingBaseChange c G).obj),
          leg' A ((restrictionDiagram D').map h ≫ φ) = (Over.pullback j').map h ≫ leg' A' φ)
        (_ : ∀ (A : Over D'.X)
          (φ' : (restrictionDiagram D').obj A ⟶ (glueingBaseChange c G).obj),
          (leg' A φ').left ≫ pullback.fst M.hom gJ =
            pullback.lift (pullback.fst A.hom j') (pullback.snd A.hom j' ≫ gJ) (by
              rw [Category.assoc, hJ, ← Category.assoc, ← pullback.condition, Category.assoc]
              rfl) ≫
              (leg (Over.mk (A.hom ≫ c.q)) (c.commaHomEquiv G A φ')).left)
        (k : yoneda.obj W ⟶ J'), k ≫ gJ = b ∧
          IsIso (legEval j' ((Over.pullback gJ).obj M) leg' hleg')) :
    IsIso (legEval j M leg hleg) := by
  have hPs : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (pullback (homPresheafProjection D G) j) :=
    Presheaf.isSheaf_pullback _ _ _ (isSheaf_homPresheaf D G) hJs D.algebraicSpace_X.isSheaf
  refine isIso_of_bijective_app_of_isAffine hPs hMs _ fun W hW => ⟨fun x₁ x₂ hx => ?_,
    fun m => ?_⟩
  · have hx' : yonedaEquiv.symm x₁ ≫ legEval j M leg hleg =
        yonedaEquiv.symm x₂ ≫ legEval j M leg hleg := by
      rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, hx]
    have hb : yonedaEquiv.symm x₁ ≫ pullback.snd _ _ =
        yonedaEquiv.symm x₂ ≫ pullback.snd _ _ := by
      rw [← legEval_hom j M leg hleg, reassoc_of% hx']
    obtain ⟨D', c, J', j', gJ, hJ, leg', hleg', hcomm, k, hk, hiso⟩ :=
      H W hW (yonedaEquiv.symm x₁ ≫ pullback.snd _ _)
    have hpb := isPullback_pullbackMap c j gJ hJ (D' := D') (j' := j') (G := G)
    let y₁ := hpb.lift (yonedaEquiv.symm x₁) k hk.symm
    let y₂ := hpb.lift (yonedaEquiv.symm x₂) k (by rw [hk, hb])
    have hy : y₁ = y₂ := by
      rw [← cancel_mono (legEval j' ((Over.pullback gJ).obj M) leg' hleg')]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc,
          legEval_baseChange c j M leg hleg j' gJ hJ leg' hleg' hcomm, hpb.lift_fst_assoc,
          hpb.lift_fst_assoc, hx']
      · rw [Category.assoc, Category.assoc]
        have e := legEval_hom j' ((Over.pullback gJ).obj M) leg' hleg'
        simp only [Over.pullback_obj_hom] at e
        rw [e, hpb.lift_snd, hpb.lift_snd]
    apply yonedaEquiv.symm.injective
    rw [← hpb.lift_fst (yonedaEquiv.symm x₁) k hk.symm,
      ← hpb.lift_fst (yonedaEquiv.symm x₂) k (by rw [hk, hb])]
    exact congrArg (· ≫ _) hy
  · obtain ⟨D', c, J', j', gJ, hJ, leg', hleg', hcomm, k, hk, hiso⟩ :=
      H W hW (yonedaEquiv.symm m ≫ M.hom)
    have hpb := isPullback_pullbackMap c j gJ hJ (D' := D') (j' := j') (G := G)
    let m' : yoneda.obj W ⟶ ((Over.pullback gJ).obj M).left :=
      pullback.lift (yonedaEquiv.symm m) k hk.symm
    refine ⟨yonedaEquiv ((m' ≫ inv (legEval j' ((Over.pullback gJ).obj M) leg' hleg')) ≫
      pullback.map _ _ _ _ (c.homPresheafBaseChange G) gJ c.q
        (c.homPresheafBaseChange_projection G).symm hJ.symm), ?_⟩
    rw [← yonedaEquiv_comp, Category.assoc,
      ← legEval_baseChange c j M leg hleg j' gJ hJ leg' hleg' hcomm, Category.assoc,
      IsIso.inv_hom_id_assoc]
    change yonedaEquiv (pullback.lift _ _ _ ≫ pullback.fst _ _) = m
    rw [pullback.lift_fst, Equiv.apply_symm_apply]

end Iso

/-! ### Over an affine base, and in general -/

section Realization

variable (hA : AffineBaseEssSurj B S hS)

include hA in
/-- **Over an affine base the evaluation is an isomorphism**: there the sheaf of glueing-data
morphisms is the space realizing the triple, and the evaluation is the realization. -/
theorem isIso_legEval_of_affine (D : FormalGlueingSituation B S hS)
    (hX : ∃ Z : BigFppfOver B S hS,
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧ Nonempty (D.X ≅ yoneda.obj Z))
    (G : glueingData D) (hG : affineLegs D G)
    {J : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : J ⟶ D.X) (M : Over J)
    (leg : ∀ A : Over D.X, ((restrictionDiagram D).obj A ⟶ G.obj) →
      ((Over.pullback j).obj A ⟶ M))
    (hleg : ∀ {A A' : Over D.X} (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj),
      leg A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback j).map h ≫ leg A' φ)
    (hlegT : ∀ (T : spacesOverX D) (θ : (formalGlueingFunctor D).1.obj T ≅ G),
      IsIso (leg T.obj θ.hom.hom).left) :
    IsIso (legEval j M leg hleg) := by
  obtain ⟨⟨T, hT⟩, ⟨ε⟩⟩ := (hA D hX).mem_essImage ⟨G, hG⟩
  let θ : (formalGlueingFunctor D).1.obj T ≅ G := (affineLegs D).ι.mapIso ε
  have : IsIso (toHomPresheaf D T) := isIso_toHomPresheaf_of_affineBaseEssSurj D hA T hT
  have : IsIso (homPresheafMap D θ.hom) := (homPresheafMapIso D θ).isIso_hom
  have he : toHomPresheafPullback j T θ.hom = pullback.map T.obj.hom j
      (homPresheafProjection D G) j (toHomPresheaf D T ≫ homPresheafMap D θ.hom) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, Category.assoc, homPresheafMap_projection,
        toHomPresheaf_projection]) (by rw [Category.comp_id, Category.id_comp]) := by
    refine pullback.hom_ext ?_ ?_
    · exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
    · exact (pullback.lift_snd _ _ _).trans ((pullback.lift_snd _ _ _).trans
        (Category.comp_id _)).symm
  have : IsIso (toHomPresheafPullback j T θ.hom) := by
    rw [he]
    infer_instance
  have : IsIso (leg T.obj θ.hom.hom).left := hlegT T θ
  have h2 : legEval j M leg hleg = inv (toHomPresheafPullback j T θ.hom) ≫
      (leg T.obj θ.hom.hom).left := by
    rw [← legEval_toHomPresheaf j M leg hleg T θ.hom, IsIso.inv_hom_id_assoc]
  rw [h2]
  infer_instance

/-- The canonical map into a pullback, computed on a pullback square, is its `isoPullback`. -/
private theorem lift_snd_comp_eq_isoPullback_hom {C : Type*} [Category C] [HasPullbacks C]
    {A Y Y' Z X : C} {a : A ⟶ Z} {y : Y ⟶ Z} {g : Y ⟶ Y'} {b : A ⟶ X} {ι : Y' ⟶ X}
    (h : IsPullback (pullback.fst a y) (pullback.snd a y ≫ g) b ι) (w) :
    pullback.lift (pullback.fst a y) (pullback.snd a y ≫ g) w = h.isoPullback.hom :=
  pullback.hom_ext ((pullback.lift_fst _ _ _).trans h.isoPullback_hom_fst.symm)
    ((pullback.lift_snd _ _ _).trans h.isoPullback_hom_snd.symm)

/-- The comma components of an isomorphism of glueing triples are isomorphisms. -/
theorem isIso_left_left_of_iso {D : FormalGlueingSituation B S hS} {G₁ G₂ : glueingData D}
    (θ : G₁ ≅ G₂) : IsIso θ.hom.hom.left.left ∧ IsIso θ.hom.hom.right.left := by
  have : IsIso θ.hom.hom := Functor.map_isIso (ObjectProperty.ι _) θ.hom
  have : IsIso θ.hom.hom.left := Functor.map_isIso (Comma.fst _ _) θ.hom.hom
  have : IsIso θ.hom.hom.right := Functor.map_isIso (Comma.snd _ _) θ.hom.hom
  exact ⟨Functor.map_isIso (Over.forget _) θ.hom.hom.left,
    Functor.map_isIso (Over.forget _) θ.hom.hom.right⟩

/-- The `U`-component of a morphism of glueing data. -/
def legU (D : FormalGlueingSituation B S hS) (G : glueingData D) (A : Over D.X)
    (φ : (restrictionDiagram D).obj A ⟶ G.obj) : (Over.pullback D.U.ι).obj A ⟶ G.obj.left :=
  φ.left

/-- The `Y`-component of a morphism of glueing data. -/
def legY (D : FormalGlueingSituation B S hS) (G : glueingData D) (A : Over D.X)
    (φ : (restrictionDiagram D).obj A ⟶ G.obj) : (Over.pullback D.f).obj A ⟶ G.obj.right :=
  φ.right

/-- `legU` is compatible with restriction along a morphism `A ⟶ A'`. -/
theorem legU_comp (D : FormalGlueingSituation B S hS) (G : glueingData D) {A A' : Over D.X}
    (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj) :
    legU D G A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback D.U.ι).map h ≫ legU D G A' φ :=
  rfl

/-- `legY` is compatible with restriction along a morphism `A ⟶ A'`. -/
theorem legY_comp (D : FormalGlueingSituation B S hS) (G : glueingData D) {A A' : Over D.X}
    (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj) :
    legY D G A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback D.f).map h ≫ legY D G A' φ :=
  rfl

/-- The evaluation of the `U`-leg. -/
noncomputable abbrev legEvalU (D : FormalGlueingSituation B S hS) (G : glueingData D) :
    pullback (homPresheafProjection D G) D.U.ι ⟶ G.obj.left.left :=
  legEval D.U.ι G.obj.left (legU D G) (legU_comp D G)

/-- The evaluation of the `Y`-leg. -/
noncomputable abbrev legEvalY (D : FormalGlueingSituation B S hS) (G : glueingData D) :
    pullback (homPresheafProjection D G) D.f ⟶ G.obj.right.left :=
  legEval D.f G.obj.right (legY D G) (legY_comp D G)

include hA in
/-- **The evaluation of the `U`-leg is an isomorphism** `P ×_X U ≅ G_U`, granted clause (1) of
Stacks 0AF4 over affine bases. -/
theorem isIso_legEvalU (D : FormalGlueingSituation B S hS) (G : glueingData D)
    (hG : affineLegs D G) : IsIso (legEvalU D G) := by
  refine isIso_legEval_of_baseChange D.U.ι G.obj.left (legU D G) (legU_comp D G)
    (isOpenSubspace_U D).1.isSheaf G.property.2.1.isSheaf fun W hW b => ?_
  let D' := D.baseChangeAlong (isAlgebraicSpace_yoneda B S hS W) (b ≫ D.U.ι)
  let c : CartesianMap D D' :=
    CartesianMap.baseChangeAlong D (isAlgebraicSpace_yoneda B S hS W) (b ≫ D.U.ι)
  refine ⟨_, c, _, _, c.gU, c.hUsq.w, legU D' (glueingBaseChange c G),
    legU_comp D' (glueingBaseChange c G), fun A φ' => ?_,
    c.hUsq.lift b (𝟙 _) (Category.id_comp _).symm, c.hUsq.lift_fst _ _ _, ?_⟩
  · change φ'.left.left ≫ _ = _ ≫ (c.commaHomEquiv G A φ').left.left
    rw [c.commaHomEquiv_left]
    rw [lift_snd_comp_eq_isoPullback_hom (c.isPullbackU A) _]
    exact (Iso.hom_inv_id_assoc _ _).symm
  · exact isIso_legEval_of_affine hA _ ⟨W, hW, ⟨Iso.refl _⟩⟩ (glueingBaseChange c G)
      (affineLegs_glueingBaseChange c G hG) _ _ _ _ fun T θ => (isIso_left_left_of_iso θ).1

include hA in
/-- **The evaluation of the `Y`-leg is an isomorphism** `P ×_X Y ≅ G_Y`, granted clause (1) of
Stacks 0AF4 over affine bases. -/
theorem isIso_legEvalY (D : FormalGlueingSituation B S hS) (G : glueingData D)
    (hG : affineLegs D G) : IsIso (legEvalY D G) := by
  refine isIso_legEval_of_baseChange D.f G.obj.right (legY D G) (legY_comp D G)
    D.algebraicSpace_Y.isSheaf G.property.2.2.isSheaf fun W hW b => ?_
  let D' := D.baseChangeAlong (isAlgebraicSpace_yoneda B S hS W) (b ≫ D.f)
  let c : CartesianMap D D' :=
    CartesianMap.baseChangeAlong D (isAlgebraicSpace_yoneda B S hS W) (b ≫ D.f)
  refine ⟨_, c, _, _, c.gY, c.hYsq.w, legY D' (glueingBaseChange c G),
    legY_comp D' (glueingBaseChange c G), fun A φ' => ?_,
    c.hYsq.lift b (𝟙 _) (Category.id_comp _).symm, c.hYsq.lift_fst _ _ _, ?_⟩
  · change φ'.right.left ≫ _ = _ ≫ (c.commaHomEquiv G A φ').right.left
    rw [c.commaHomEquiv_right]
    rw [lift_snd_comp_eq_isoPullback_hom (c.isPullbackY A) _]
    exact (Iso.hom_inv_id_assoc _ _).symm
  · exact isIso_legEval_of_affine hA _ ⟨W, hW, ⟨Iso.refl _⟩⟩ (glueingBaseChange c G)
      (affineLegs_glueingBaseChange c G hG) _ _ _ _ fun T θ => (isIso_left_left_of_iso θ).2

end Realization

end AlgebraicGeometry.Space.FormalGlueingSituation

end
