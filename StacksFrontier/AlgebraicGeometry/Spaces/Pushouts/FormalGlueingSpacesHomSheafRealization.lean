module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafLegs

/-!
# The sheaf of glueing-data morphisms realizes the triple

In a formal glueing situation write `P = homPresheaf D G` for the sheaf of glueing-data
morphisms into a triple `G` with affine legs. Granted clause (1) of Stacks 0AF4 over affine
bases, the two evaluations `P ×_X U ⟶ G_U` and `P ×_X Y ⟶ G_Y` are isomorphisms
(`AlgebraicGeometry.Space.FormalGlueingSituation.isIso_legEvalU`,
`AlgebraicGeometry.Space.FormalGlueingSituation.isIso_legEvalY`). This module shows that they
are compatible over `V`, so that they form an isomorphism of glueing triples `F(P) ≅ G` as
soon as `P` is an algebraic space; `P` is then affine over `X`
(`AlgebraicGeometry.Space.FormalGlueingSituation.isAffineHom_homPresheafProjection`), so `G`
lies in the essential image of clause (1) of Stacks 0AF4.

## Main results

* `legEval_comm`: the two evaluations are compatible over `V`.
* `exists_realization_of_isAlgebraicSpace_homPresheaf`: `G` is realized by `P` once `P` is an
  algebraic space.
* `essSurj_affineGlueingFunctor_of_isAlgebraicSpace`: hence essential surjectivity in clause (1)
  of Stacks 0AF4 from the algebraicity of these sheaves.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : FormalGlueingSituation B S hS}

/-- The comparison of the two restrictions of `A` to `V`, on points. -/
theorem restrictionComparison_left_fst {W : BigFppfOver B S hS} (A : Over D.X)
    (z : yoneda.obj W ⟶ pullback (pullback.snd A.hom D.U.ι) (D.U.fromPreimage D.f)) :
    z ≫ ((restrictionComparison D).hom.app A).left ≫ pullback.fst (pullback.snd A.hom D.f) D.V.ι =
      pullback.lift (z ≫ pullback.fst _ _ ≫ pullback.fst _ _) (z ≫ pullback.snd _ _ ≫ D.V.ι) (by
        simp only [Category.assoc]
        rw [pullback.condition, pullback.condition_assoc, Subfunctor.fromPreimage_ι]) := by
  have hw : ((restrictionComparison D).hom.app A).left ≫
      pullback.snd (pullback.snd A.hom D.f) D.V.ι =
        pullback.snd (pullback.snd A.hom D.U.ι) (D.U.fromPreimage D.f) :=
    Over.w ((restrictionComparison D).hom.app A)
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, Category.assoc, Category.assoc,
      restrictionComparison_hom_app_left_fst_fst]
  · rw [pullback.lift_snd, Category.assoc, Category.assoc, pullback.condition,
      reassoc_of% hw]

/-- A point of the restriction of `A` to `V` is determined by its two legs. -/
theorem restrictionComparison_left_fst_eq {W : BigFppfOver B S hS} (A : Over D.X)
    (z : yoneda.obj W ⟶ pullback (pullback.snd A.hom D.U.ι) (D.U.fromPreimage D.f))
    (l : yoneda.obj W ⟶ pullback A.hom D.f)
    (h₁ : l ≫ pullback.fst A.hom D.f = z ≫ pullback.fst (pullback.snd A.hom D.U.ι)
      (D.U.fromPreimage D.f) ≫ pullback.fst A.hom D.U.ι)
    (h₂ : l ≫ pullback.snd A.hom D.f =
      z ≫ pullback.snd (pullback.snd A.hom D.U.ι) (D.U.fromPreimage D.f) ≫ D.V.ι) :
    z ≫ ((restrictionComparison D).hom.app A).left ≫
      pullback.fst (pullback.snd A.hom D.f) D.V.ι = l :=
  (restrictionComparison_left_fst A z).trans (pullback.hom_ext
    ((pullback.lift_fst _ _ _).trans h₁.symm) ((pullback.lift_snd _ _ _).trans h₂.symm))

/-- Two points of base changes along `g` agree after base changing `α` and `β` once their legs
agree after `α` and `β`. -/
theorem comp_overPullback_map_left_eq {C : Type*} [Category C] [HasPullbacks C] {X V T : C}
    (g : V ⟶ X) {A A' M : Over X} (α : A ⟶ M) (β : A' ⟶ M)
    (x : T ⟶ pullback A.hom g) (z : T ⟶ pullback A'.hom g)
    (h₁ : x ≫ pullback.fst A.hom g ≫ α.left = z ≫ pullback.fst A'.hom g ≫ β.left)
    (h₂ : x ≫ pullback.snd A.hom g = z ≫ pullback.snd A'.hom g) :
    x ≫ ((Over.pullback g).map α).left = z ≫ ((Over.pullback g).map β).left :=
  pullback.hom_ext (by simpa only [Category.assoc, overPullback_map_left_comp_fst] using h₁)
    (by simpa only [Category.assoc, overPullback_map_left_comp_snd] using h₂)

variable (G : glueingData D)

/-- The composite of a point `y` of `P ×_X J` with `legEval j M leg hleg` is `legEval₀` evaluated
at the glueing section `t` and the point `b` of `J` that `y` determines. -/
theorem comp_legEval_eq {J : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : J ⟶ D.X) (M : Over J)
    (leg : ∀ A : Over D.X, ((restrictionDiagram D).obj A ⟶ G.obj) →
      ((Over.pullback j).obj A ⟶ M))
    (hleg : ∀ {A A' : Over D.X} (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj),
      leg A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback j).map h ≫ leg A' φ)
    {W : BigFppfOver B S hS} (y : yoneda.obj W ⟶ pullback (homPresheafProjection D G) j)
    (t : glueSections D G W)
    (ht : (equivShrink (glueSections D G W)).symm
      (yonedaEquiv (y ≫ pullback.fst (homPresheafProjection D G) j)) = t)
    (b : yoneda.obj W ⟶ J) (hb : y ≫ pullback.snd (homPresheafProjection D G) j = b)
    (h : t.1 = b ≫ j) :
    y ≫ legEval j M leg hleg = legEval₀ j M leg t b h := by
  subst ht hb
  exact comp_legEval j M leg hleg y

/-- **The two evaluations are compatible over `V`.** -/
theorem legEval_comm :
    ((Over.pullback (D.U.fromPreimage D.f)).map (Over.homMk (legEvalU D G)
        (legEval_hom D.U.ι G.obj.left (legU D G) (legU_comp D G)) :
          (Over.pullback D.U.ι).obj (Over.mk (homPresheafProjection D G)) ⟶
            G.obj.left)).left ≫ G.obj.hom.left ≫ pullback.fst G.obj.right.hom D.V.ι =
      ((restrictionComparison D).hom.app (Over.mk (homPresheafProjection D G))).left ≫
        pullback.fst _ _ ≫ legEvalY D G := by
  refine hom_ext_yoneda fun W x => ?_
  let π := homPresheafProjection D G
  let x₁ := x ≫ pullback.fst (pullback.snd π D.U.ι) (D.U.fromPreimage D.f)
  let x₂ := x ≫ pullback.snd (pullback.snd π D.U.ι) (D.U.fromPreimage D.f)
  let s := x₁ ≫ pullback.fst π D.U.ι
  let u := x₁ ≫ pullback.snd π D.U.ι
  have hu : u = x₂ ≫ D.U.fromPreimage D.f := by
    simp only [u, x₁, x₂, Category.assoc, pullback.condition]
  obtain ⟨⟨w, φ⟩, ht⟩ : ∃ t, (equivShrink (glueSections D G W)).symm (yonedaEquiv s) = t :=
    ⟨_, rfl⟩
  have hw : w = u ≫ D.U.ι :=
    (congrArg Sigma.fst ht).symm.trans (symm_yonedaEquiv_fst (D := D) (G := G) D.U.ι x₁)
  have hU : x₁ ≫ legEvalU D G = pullback.lift (𝟙 _) u (by rwa [Category.id_comp]) ≫
      (legU D G _ φ).left :=
    comp_legEval_eq G D.U.ι G.obj.left (legU D G) (legU_comp D G) x₁ _ ht u rfl hw
  let z : yoneda.obj W ⟶
      ((Over.pullback (D.U.fromPreimage D.f)).obj ((Over.pullback D.U.ι).obj (Over.mk w))).left :=
    pullback.lift (pullback.lift (𝟙 _) u (by rwa [Category.id_comp])) x₂
      ((pullback.lift_snd _ _ _).trans hu)
  let εU : (Over.pullback D.U.ι).obj (Over.mk π) ⟶ G.obj.left := Over.homMk (legEvalU D G)
    (legEval_hom D.U.ι G.obj.left (legU D G) (legU_comp D G))
  have hz : x ≫ ((Over.pullback (D.U.fromPreimage D.f)).map εU).left =
      z ≫ ((Over.pullback (D.U.fromPreimage D.f)).map (legU D G _ φ)).left :=
    comp_overPullback_map_left_eq _ εU (legU D G _ φ) x z
      (hU.trans (congrArg (· ≫ (legU D G _ φ).left) (pullback.lift_fst _ _ _).symm))
      (pullback.lift_snd _ _ _).symm
  have hφ' : (Over.pullback (D.U.fromPreimage D.f)).map (legU D G _ φ) ≫ G.obj.hom =
      (restrictionComparison D).hom.app (Over.mk w) ≫
        (Over.pullback D.V.ι).map (legY D G _ φ) := φ.w
  have hφ := congrArg (fun k => z ≫ k.left ≫ pullback.fst G.obj.right.hom D.V.ι) hφ'
  simp only [Over.comp_left, Category.assoc] at hφ
  have hV : (x₂ ≫ D.V.ι) ≫ D.f = u ≫ D.U.ι := by
    simp only [hu, Category.assoc, Subfunctor.fromPreimage_ι]
  let y : yoneda.obj W ⟶ pullback π D.f := pullback.lift s (x₂ ≫ D.V.ι) (by
    rw [hV]
    simp only [s, u, Category.assoc, pullback.condition])
  have hy : x ≫ ((restrictionComparison D).hom.app (Over.mk π)).left ≫
      pullback.fst (pullback.snd π D.f) D.V.ι = y :=
    restrictionComparison_left_fst_eq _ x y (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  let l : yoneda.obj W ⟶ pullback (Over.mk w).hom D.f :=
    pullback.lift (𝟙 _) (x₂ ≫ D.V.ι) (by rwa [Category.id_comp, hV])
  have hY : y ≫ legEvalY D G = l ≫ (legY D G _ φ).left :=
    comp_legEval_eq G D.f G.obj.right (legY D G) (legY_comp D G) y _
      ((congrArg _ (congrArg yonedaEquiv (pullback.lift_fst _ _ _))).trans ht) _
      (pullback.lift_snd _ _ _) (hw.trans hV.symm)
  have hzc : z ≫ ((restrictionComparison D).hom.app (Over.mk w)).left ≫
      pullback.fst (pullback.snd (Over.mk w).hom D.f) D.V.ι = l :=
    restrictionComparison_left_fst_eq (Over.mk w) z l
      ((pullback.lift_fst _ _ _).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _))).symm)
      ((pullback.lift_snd _ _ _).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ D.V.ι) (pullback.lift_snd _ _ _))).symm)
  have e5 := overPullback_map_left_comp_fst D.V.ι (legY D G _ φ)
  simp only [Over.pullback_obj_hom, Over.pullback_obj_left] at e5
  rw [reassoc_of% hz, hφ, e5, reassoc_of% hzc, ← hY, ← hy]
  simp only [Category.assoc]
  rfl

variable (hA : AffineBaseEssSurj B S hS)

include hA in
/-- **The triple is realized by the sheaf of glueing-data morphisms, once that sheaf is an
algebraic space**, granted clause (1) of Stacks 0AF4 over affine bases. -/
theorem exists_realization_of_isAlgebraicSpace_homPresheaf (hG : affineLegs D G)
    (hT : IsAlgebraicSpace B S hS (homPresheaf D G)) :
    ∃ (T : spacesOverX D), affineOverX D T ∧ Nonempty ((formalGlueingFunctor D).1.obj T ≅ G) := by
  let T : spacesOverX D := ⟨Over.mk (homPresheafProjection D G), hT⟩
  let eY : (Over.pullback D.f).obj (Over.mk (homPresheafProjection D G)) ≅ G.obj.right :=
    Over.isoMk (@asIso _ _ _ _ (legEvalY D G) (isIso_legEvalY hA D G hG))
      (legEval_hom D.f G.obj.right (legY D G) (legY_comp D G))
  refine ⟨T, isAffineHom_homPresheafProjection hA D G hG,
    ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
    (Comma.isoMk (Over.isoMk (@asIso _ _ _ _ (legEvalU D G) (isIso_legEvalU hA D G hG))
      (legEval_hom D.U.ι G.obj.left (legU D G) (legU_comp D G))) eY ?_)⟩⟩
  refine overPullback_hom_ext _ ?_
  simp only [Over.comp_left, Category.assoc]
  have e := overPullback_map_left_comp_fst D.V.ι eY.hom
  refine (legEval_comm G).trans ?_
  refine Eq.trans ?_ (congrArg (_ ≫ ·) e.symm)
  rfl

include hA in
/-- **Essential surjectivity in clause (1) of Stacks 0AF4 from the algebraicity of the sheaves
of glueing-data morphisms**, granted clause (1) over affine bases. -/
theorem essSurj_affineGlueingFunctor_of_isAlgebraicSpace (D : FormalGlueingSituation B S hS)
    (h : ∀ G : glueingData D, affineLegs D G → IsAlgebraicSpace B S hS (homPresheaf D G)) :
    (affineGlueingFunctor D).EssSurj := by
  refine ⟨fun Y => ?_⟩
  obtain ⟨T, hT, ⟨e⟩⟩ := exists_realization_of_isAlgebraicSpace_homPresheaf Y.obj hA Y.property
    (h Y.obj Y.property)
  exact ⟨⟨T, hT⟩, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso e⟩⟩

include hA in
/-- **Clause (1) of Stacks 0AF4 from the algebraicity of the sheaves of glueing-data
morphisms**, granted clause (1) over affine bases. -/
theorem isEquivalence_affineGlueingFunctor_of_isAlgebraicSpace
    (h : ∀ (D : FormalGlueingSituation B S hS) (G : glueingData D), affineLegs D G →
      IsAlgebraicSpace B S hS (homPresheaf D G)) (D : FormalGlueingSituation B S hS) :
    (affineGlueingFunctor D).IsEquivalence :=
  isEquivalence_affineGlueingFunctor_of_realization D
    (essSurj_affineGlueingFunctor_of_isAlgebraicSpace hA D (h D))
    (closedSliceRealization_of_essSurj_affine D fun D' =>
      essSurj_affineGlueingFunctor_of_isAlgebraicSpace hA D' (h D'))

include hA in
/-- **Clause (2) of Stacks 0AF4 from the algebraicity of the sheaves of glueing-data
morphisms**, granted clause (1) over affine bases. -/
theorem isEquivalence_closedGlueingFunctor_of_isAlgebraicSpace
    (h : ∀ (D : FormalGlueingSituation B S hS) (G : glueingData D), affineLegs D G →
      IsAlgebraicSpace B S hS (homPresheaf D G)) (D : FormalGlueingSituation B S hS) :
    (closedGlueingFunctor D).IsEquivalence :=
  isEquivalence_closedGlueingFunctor D
    (isEquivalence_affineGlueingFunctor_of_isAlgebraicSpace hA h D)

include hA in
/-- **Clause (3) of Stacks 0AF4 from the algebraicity of the sheaves of glueing-data
morphisms**, granted clause (1) over affine bases. -/
theorem isEquivalence_finiteGlueingFunctor_of_isAlgebraicSpace
    (h : ∀ (D : FormalGlueingSituation B S hS) (G : glueingData D), affineLegs D G →
      IsAlgebraicSpace B S hS (homPresheaf D G)) (D : FormalGlueingSituation B S hS) :
    (finiteGlueingFunctor D).IsEquivalence :=
  isEquivalence_finiteGlueingFunctor D
    (isEquivalence_affineGlueingFunctor_of_isAlgebraicSpace hA h D)

end AlgebraicGeometry.Space.FormalGlueingSituation

end
