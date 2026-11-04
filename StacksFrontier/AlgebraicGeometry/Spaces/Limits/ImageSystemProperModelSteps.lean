module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFilteredColimitOfApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AllChartLimitBridges
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentOfLimitBridges
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageConeLimitOfAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemPropertiesOfAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.LimitDescriptionIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SystemMorphismOfAlgebraicLimit

/-!
# Image systems re-indexed by a tail, and the proper model of a diagram

In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic spaces quasi-separated and of
finite type over `B = lim B_i`, and let `GX` and `GY` be diagrams for `X` and `Y` as in Stacks
0CP8. This module holds the re-indexing of an image system by a tail of the index set and the
first steps of the source's proof of Stacks 0CPE (a model with a closed immersion into a proper
model gives a proper morphism of image systems). It is part of a copy of a proof of
Stacks 0CQ1 used by Chow's lemma for algebraic stacks (the library's own proof of Stacks 0CPE
is in `StacksFrontier/AlgebraicGeometry/Spaces/Limits/DescendingFiniteTypeProper.lean`); the statement of 0CPE itself is not copied.

## References

* [Stacks Project, Tag 0CPE](https://stacks.math.columbia.edu/tag/0CPE)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
* [Stacks Project, Tag 0CPB](https://stacks.math.columbia.edu/tag/0CPB)
* [Stacks Project, Tag 0A0W](https://stacks.math.columbia.edu/tag/0A0W)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pY : Y ⟶ D.limitCone.pt}

/-- The comparison `T ×_{B_{i₂}} V ⟶ B_m ×_{B_{i₂}} V` induced by a morphism `T ⟶ B_m`. -/
noncomputable abbrev baseChangeComparison (G : GoodDiagram B S hS hZ D pY) {m : I}
    (h : G.index ≤ m) {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : T ⟶ D.system.obj (op m))
    (c : T ⟶ D.system.obj (op G.index)) (hc : b ≫ D.system.map (homOfLE h).op = c) :
    pullback c G.modelMap ⟶
      pullback (D.system.map (Over.mk (homOfLE h).op).hom) G.modelMap :=
  pullback.lift (pullback.fst c G.modelMap ≫ b) (pullback.snd c G.modelMap) (by
    rw [Category.assoc]
    exact (congrArg (pullback.fst c G.modelMap ≫ ·) hc).trans pullback.condition)

/-- The morphism `Y_m ⟶ B_m` from a member of the image system to its stage. -/
noncomputable abbrev stageToBase (G : GoodDiagram B S hS hZ D pY) {m : I}
    (h : G.index ≤ m) : (imageSystem G).obj (Over.mk (homOfLE h).op) ⟶ D.system.obj (op m) :=
  (stageImage G (Over.mk (homOfLE h).op)).ι ≫ pullback.fst _ _

/-- **A closed subspace of `T ×_{B_{i₂}} V` lying in `T ×_{B_m} Y_m`.** Let
`y : Y' ⟶ T ×_{B_{i₂}} V` be a closed immersion and `r : Y' ⟶ Y_m` a morphism to a member of
the image system compatible with `y`. Then `(y, r) : Y' ⟶ T ×_{B_m} Y_m` is a closed immersion:
it is followed by the base change of the closed immersion `Y_m ⟶ B_m ×_{B_{i₂}} V`, a
monomorphism, and the composite is `y`. -/
theorem isClosedImmersion_lift_stage (G : GoodDiagram B S hS hZ D pY) {m : I}
    (h : G.index ≤ m) {T Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : T ⟶ D.system.obj (op m))
    (c : T ⟶ D.system.obj (op G.index)) (hc : b ≫ D.system.map (homOfLE h).op = c)
    (y : Y' ⟶ pullback c G.modelMap) (hy : IsClosedImmersion B S hS y)
    (r : Y' ⟶ (imageSystem G).obj (Over.mk (homOfLE h).op))
    (hr : r ≫ (stageImage G (Over.mk (homOfLE h).op)).ι =
      y ≫ baseChangeComparison G h b c hc) :
    IsClosedImmersion B S hS (pullback.lift (y ≫ pullback.fst _ _) r (by
      simp only [stageToBase, reassoc_of% hr, baseChangeComparison, pullback.lift_fst,
        Category.assoc]) :
        Y' ⟶ pullback b (stageToBase G h)) := by
  have hlam : pullback.fst b (stageToBase G h) ≫ c =
      (pullback.snd b (stageToBase G h) ≫ (stageImage G (Over.mk (homOfLE h).op)).ι ≫
        pullback.snd _ _) ≫ G.modelMap := by
    rw [← hc, ← Category.assoc, pullback.condition]
    simp only [Category.assoc]
    exact congrArg (fun z => pullback.snd b (stageToBase G h) ≫
      (stageImage G (Over.mk (homOfLE h).op)).ι ≫ z) pullback.condition
  set lam : pullback b (stageToBase G h) ⟶ pullback c G.modelMap :=
    pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ (stageImage G (Over.mk (homOfLE h).op)).ι ≫ pullback.snd _ _) hlam
  have hμ : IsPullback (baseChangeComparison G h b c hc) (pullback.fst c G.modelMap)
      (pullback.fst _ _) b := by
    refine IsPullback.of_right (h₁₂ := pullback.snd _ _)
      (h₂₂ := D.system.map (Over.mk (homOfLE h).op).hom) ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback _ _).flip
    rw [pullback.lift_snd, show b ≫ D.system.map (Over.mk (homOfLE h).op).hom = c from hc]
    exact (IsPullback.of_hasPullback c G.modelMap).flip
  have hsq : IsPullback (pullback.snd b (stageToBase G h)) lam
      (stageImage G (Over.mk (homOfLE h).op)).ι (baseChangeComparison G h b c hc) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst c G.modelMap) (v₂₂ := pullback.fst _ _)
      (h₃₁ := b) ?_ ?_ hμ
    · rw [pullback.lift_fst]
      exact (IsPullback.of_hasPullback b (stageToBase G h)).flip
    · refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, baseChangeComparison, pullback.lift_fst, lam,
          pullback.lift_fst_assoc]
        exact pullback.condition.symm
      · simp only [Category.assoc, baseChangeComparison, pullback.lift_snd, lam]
  have hlamc : IsClosedImmersion B S hS lam :=
    (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback hsq
      (isClosedSubspace_stageImage G (Over.mk (homOfLE h).op)).2
  have : Mono lam := mono_of_isClosedImmersion B S hS lam hlamc
  refine isClosedImmersion_of_comp_mono B S hS _ lam ?_
  convert hy using 1
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, lam, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, reassoc_of% hr]
    simp only [baseChangeComparison, pullback.lift_snd]

/-- **`X ⟶ B ×_{B_m} X_m` is a closed immersion** for every member `X_m` of the image system of a
diagram as in Stacks 0CP8: it is the closed immersion `X ⟶ B ×_{B_i} W` of the diagram, read
through the closed subspace `B ×_{B_m} X_m` of `B ×_{B_i} W`. -/
theorem isClosedImmersion_lift_imageCone_π (G : GoodDiagram B S hS hZ D pY) {m : I}
    (h : G.index ≤ m) :
    IsClosedImmersion B S hS (pullback.lift pY ((imageCone G).π.app (Over.mk (homOfLE h).op))
      (by rw [imageCone_π_ι_assoc, stageMap_fst]; rfl) :
        Y ⟶ pullback (D.limitCone.π.app (op m))
          ((stageImage G (Over.mk (homOfLE h).op)).ι ≫ pullback.fst _ _)) := by
  have hc : D.limitCone.π.app (op m) ≫ D.system.map (homOfLE h).op =
      D.limitCone.π.app (op G.index) := D.limitCone.w (homOfLE h).op
  have key := isClosedImmersion_lift_stage G h (D.limitCone.π.app (op m))
    (D.limitCone.π.app (op G.index)) hc (G.induced) G.isClosedImmersion
    ((imageCone G).π.app (Over.mk (homOfLE h).op)) (by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, imageCone_π_ι_assoc, stageMap_fst, baseChangeComparison,
          pullback.lift_fst, pullback.lift_fst_assoc]
        rfl
      · simp only [Category.assoc, imageCone_π_ι_assoc, stageMap_snd, baseChangeComparison,
          pullback.lift_snd])
  convert key using 2
  simp only [pullback.lift_fst]

/-- **A base change of the closed immersion of the previous lemma.** If `κ : Y' ⟶ T ×_{B_m} Y_m`
is a closed immersion, `q : W ⟶ Y_m` any morphism and `Z' = Y' ×_{Y_m} W`, then
`Z' ⟶ T ×_{B_m} W` is a closed immersion, being the base change of `κ` along
`T ×_{B_m} W ⟶ T ×_{B_m} Y_m`. -/
private theorem isClosedImmersion_lift_stage_pullback (G : GoodDiagram B S hS hZ D pY) {m : I}
    (h : G.index ≤ m) {T Y' W Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (b : T ⟶ D.system.obj (op m)) (κ : Y' ⟶ pullback b (stageToBase G h))
    (hκ : IsClosedImmersion B S hS κ) (q : W ⟶ (imageSystem G).obj (Over.mk (homOfLE h).op))
    (z₁ : Z' ⟶ Y') (z₂ : Z' ⟶ W) (hz : IsPullback z₁ z₂ (κ ≫ pullback.snd _ _) q)
    (r : W ⟶ D.system.obj (op m)) (hr : q ≫ stageToBase G h = r) :
    IsClosedImmersion B S hS (pullback.lift (z₁ ≫ κ ≫ pullback.fst _ _) z₂ (by
      rw [← hr]; simp only [Category.assoc, pullback.condition, reassoc_of% hz.w]) :
        Z' ⟶ pullback b r) := by
  subst hr
  set w : Z' ⟶ pullback b (q ≫ stageToBase G h) := pullback.lift (z₁ ≫ κ ≫ pullback.fst _ _) z₂
    (by simp only [Category.assoc, pullback.condition, reassoc_of% hz.w])
  set Φ : pullback b (q ≫ stageToBase G h) ⟶ pullback b (stageToBase G h) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ q) (by
      rw [pullback.condition, Category.assoc])
  have ht : IsPullback (pullback.snd b (q ≫ stageToBase G h)) Φ q (pullback.snd _ _) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst b (stageToBase G h))
      (v₂₂ := stageToBase G h) (h₃₁ := b) ?_ (pullback.lift_snd _ _ _).symm
      (IsPullback.of_hasPullback b (stageToBase G h)).flip
    rw [pullback.lift_fst]
    exact (IsPullback.of_hasPullback b (q ≫ stageToBase G h)).flip
  have hsq : IsPullback w z₁ Φ κ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (h₂₂ := pullback.snd _ _) ?_ ?_ ht
    · rw [pullback.lift_snd]
      exact hz.flip
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hz.w]
  exact (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback hsq.flip hκ


/-! ### Re-indexing an image system by a tail of the index set -/

/-- The stages at or above `i`, as a functor to the slice of `Iᵒᵖ` over `i`. -/
noncomputable def tailFunctor {I : Type u} [Preorder I] (i : I) :
    {j : I // i ≤ j}ᵒᵖ ⥤ Over (op i) where
  obj j := Over.mk (homOfLE j.unop.2).op
  map g := Over.homMk (homOfLE (leOfHom g.unop)).op (Subsingleton.elim _ _)
  map_id _ := Over.OverMorphism.ext (Subsingleton.elim _ _)
  map_comp _ _ := Over.OverMorphism.ext (Subsingleton.elim _ _)

/-- The stages at or above `i` form a directed set. -/
theorem isDirected_tail {I : Type u} [Preorder I] [IsDirectedOrder I] (i : I) :
    IsDirected {j : I // i ≤ j} (· ≤ ·) :=
  ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩

/-- The tail functor is initial, so a limit over `Over (op i)` may be computed on the stages at
or above `i`. -/
theorem tailFunctor_initial {I : Type u} [Preorder I] [IsDirectedOrder I] (i : I) :
    (tailFunctor i).Initial := by
  have := isDirected_tail i
  refine Functor.initial_of_exists_of_isCofiltered _
    (fun d => ⟨op ⟨d.left.unop, leOfHom d.hom.unop⟩,
      ⟨Over.homMk (𝟙 _) (Subsingleton.elim _ _)⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, Over.OverMorphism.ext (Subsingleton.elim _ _)⟩)

/-- The projection of a fibre product along an identity is an isomorphism. -/
theorem isIso_pullback_fst_id {C : Type*} [Category C] {A Z : C} (a : A ⟶ Z)
    [HasPullback a (𝟙 Z)] : IsIso (pullback.fst a (𝟙 Z)) :=
  ⟨⟨pullback.lift (𝟙 _) a (by simp), by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition,
        Category.comp_id], pullback.lift_fst _ _ _⟩⟩

/-- Properness depends only on the arrow up to isomorphism. -/
private theorem isProper_of_arrowIso' {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hX' : IsAlgebraicSpace B S hS X') (hY' : IsAlgebraicSpace B S hS Y')
    (f : X ⟶ Y) (f' : X' ⟶ Y') (e₁ : X ≅ X') (e₂ : Y ≅ Y')
    (w : e₁.hom ≫ f' = f ≫ e₂.hom) (hf : IsProper B S hS f) : IsProper B S hS f' := by
  rw [show f' = e₁.inv ≫ f ≫ e₂.hom by rw [← w, Iso.inv_hom_id_assoc]]
  exact isProper_comp B S hS hX' hX hY' e₁.inv (f ≫ e₂.hom) (isProper_of_isIso B S hS _)
    (isProper_comp B S hS hX hY hY' f e₂.hom hf (isProper_of_isIso B S hS _))

section Main

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}


/-- **The diagram of Stacks 0CP8 with a proper model.** Let `q : W ⟶ Y_m` be a morphism of finite
type to a member of the image system of `GY`, and let `X ⟶ X'` be a closed immersion into the
base change `X' = Y ×_{Y_m} W` (exhibited by the cartesian square `hpb`). Then `W ⟶ Y_m ⟶ B_m`
is the model of a diagram as in Stacks 0CP8 for `X`. -/
private noncomputable def properModelDiagram (GY : GoodDiagram B S hS hZ D pY) {m : I}
    (h : GY.index ≤ m) {W X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (q : W ⟶ (imageSystem GY).obj (Over.mk (homOfLE h).op))
    (hq : IsFiniteType B S hS q) (f : X ⟶ Y) (hf : f ≫ pY = pX) (ι : X ⟶ X')
    (hι : IsClosedImmersion B S hS ι) (f' : X' ⟶ Y) (hιf' : ι ≫ f' = f) (τ' : X' ⟶ W)
    (hpb : IsPullback f' τ' ((imageCone GY).π.app (Over.mk (homOfLE h).op)) q) :
    GoodDiagram B S hS hZ D pX := by
  have hπmbase : (imageCone GY).π.app (Over.mk (homOfLE h).op) ≫ stageToBase GY h =
      pY ≫ D.limitCone.π.app (op m) := by
    simp only [stageToBase]
    rw [imageCone_π_ι_assoc, stageMap_fst]
    rfl
  have hcomm : pX ≫ D.limitCone.π.app (op m) = (ι ≫ τ') ≫ q ≫ stageToBase GY h := by
    rw [Category.assoc, ← Category.assoc τ', ← hpb.w, Category.assoc, hπmbase,
      reassoc_of% hιf', reassoc_of% hf]
  let κ : Y ⟶ pullback (D.limitCone.π.app (op m)) (stageToBase GY h) :=
    pullback.lift pY ((imageCone GY).π.app (Over.mk (homOfLE h).op)) hπmbase.symm
  have hκ : IsClosedImmersion B S hS κ := isClosedImmersion_lift_imageCone_π GY h
  have hκfst : κ ≫ pullback.fst _ _ = pY := pullback.lift_fst _ _ _
  have hκsnd : κ ≫ pullback.snd _ _ = (imageCone GY).π.app (Over.mk (homOfLE h).op) :=
    pullback.lift_snd _ _ _
  have hΛ := isClosedImmersion_lift_stage_pullback GY h (D.limitCone.π.app (op m)) κ hκ q
    f' τ' (by rw [hκsnd]; exact hpb) _ rfl
  have hfst : IsFiniteType B S hS
      (pullback.fst (D.system.map (Over.mk (homOfLE h).op).hom) GY.modelMap) :=
    (isFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_homMk B S hS GY.model_isAlgebraicSpace (D.system_isAlgebraicSpace m)
        (D.system_isAlgebraicSpace GY.index) (isAlgebraicSpace_stageTarget GY _)
        (IsPullback.of_hasPullback _ _).flip) GY.isFiniteType
  exact
    { index := m
      model := W
      model_isAlgebraicSpace := hW
      modelMap := q ≫ stageToBase GY h
      toModel := ι ≫ τ'
      commutes := hcomm
      isFiniteType := isFiniteType_comp B S hS hW (imageSystem_isAlgebraicSpace GY _)
        (D.system_isAlgebraicSpace m) q (stageToBase GY h) hq
        (isFiniteType_comp B S hS (imageSystem_isAlgebraicSpace GY _)
          (isAlgebraicSpace_stageTarget GY _) (D.system_isAlgebraicSpace m) _ _
          (isFiniteType_of_isClosedImmersion B S hS _
            (isClosedSubspace_stageImage GY (Over.mk (homOfLE h).op)).2) hfst)
      isClosedImmersion := by
        have e : pullback.lift pX (ι ≫ τ') hcomm =
            ι ≫ pullback.lift (f' ≫ κ ≫ pullback.fst _ _) τ' (by
              rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hκsnd,
                ← Category.assoc, hpb.w, Category.assoc]) := by
          apply pullback.hom_ext
          · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, hκfst, reassoc_of% hιf',
              hf]
          · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
        rw [e]
        exact isClosedImmersion_comp B S hS _ _ hι hΛ }

/-- The component of the morphism of image systems of `exists_isProper_systemMorphism` at a
stage factors as a closed immersion into `Y_j ×_{Y_m} W` followed by the base change of
`q : W ⟶ Y_m`. -/
private theorem exists_factor_stage_component (G' : GoodDiagram B S hS hZ D pX)
    (GY : GoodDiagram B S hS hZ D pY) (h : GY.index ≤ G'.index)
    (q : G'.model ⟶ (imageSystem GY).obj (Over.mk (homOfLE h).op))
    (hmap : G'.modelMap = q ≫ stageToBase GY h) (j : Over (op G'.index))
    (mm : (imageSystem G').obj ((Over.map (homOfLE (le_refl G'.index)).op).obj j) ⟶
      (imageSystem GY).obj ((Over.map (homOfLE h).op).obj j))
    (hmm_fst : mm ≫ (stageImage GY ((Over.map (homOfLE h).op).obj j)).ι ≫ pullback.fst _ _ =
      (stageImage G' ((Over.map (homOfLE (le_refl G'.index)).op).obj j)).ι ≫ pullback.fst _ _)
    (hmm_snd : mm ≫ (stageImage GY ((Over.map (homOfLE h).op).obj j)).ι ≫ pullback.snd _ _ =
      (stageImage G' ((Over.map (homOfLE (le_refl G'.index)).op).obj j)).ι ≫ pullback.snd _ _ ≫
        q ≫ (stageImage GY (Over.mk (homOfLE h).op)).ι ≫ pullback.snd _ _) :
    ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (n : (imageSystem G').obj ((Over.map (homOfLE (le_refl G'.index)).op).obj j) ⟶ Z)
      (p : Z ⟶ (imageSystem GY).obj ((Over.map (homOfLE h).op).obj j)) (s : Z ⟶ G'.model)
      (r : (imageSystem GY).obj ((Over.map (homOfLE h).op).obj j) ⟶
        (imageSystem GY).obj (Over.mk (homOfLE h).op)),
      IsPullback p s r q ∧ IsAlgebraicSpace B S hS Z ∧ IsClosedImmersion B S hS n ∧
        n ≫ p = mm := by
  let aY : ((Over.map (homOfLE h).op).obj j) ⟶ Over.mk (homOfLE h).op :=
    Over.homMk (((Over.map (homOfLE (le_refl G'.index)).op).obj j)).hom (Subsingleton.elim _ _)
  have hc : D.system.map (((Over.map (homOfLE (le_refl G'.index)).op).obj j)).hom ≫
      D.system.map (homOfLE h).op = D.system.map (((Over.map (homOfLE h).op).obj j)).hom := by
    rw [← Functor.map_comp]
    rfl
  have hr : (imageSystem GY).map aY ≫ (stageImage GY (Over.mk (homOfLE h).op)).ι =
      (stageImage GY (((Over.map (homOfLE h).op).obj j))).ι ≫
        baseChangeComparison GY h
          (D.system.map (((Over.map (homOfLE (le_refl G'.index)).op).obj j)).hom)
          (D.system.map (((Over.map (homOfLE h).op).obj j)).hom) hc := by
    rw [imageSystem_map_ι]
    rfl
  have hκ := isClosedImmersion_lift_stage GY h
    (D.system.map (((Over.map (homOfLE (le_refl G'.index)).op).obj j)).hom)
    (D.system.map (((Over.map (homOfLE h).op).obj j)).hom) hc
    (stageImage GY (((Over.map (homOfLE h).op).obj j))).ι
    (isClosedSubspace_stageImage GY (((Over.map (homOfLE h).op).obj j))).2 _ hr
  let κ : (imageSystem GY).obj (((Over.map (homOfLE h).op).obj j)) ⟶
      pullback (D.system.map (((Over.map (homOfLE (le_refl G'.index)).op).obj j)).hom)
        (stageToBase GY h) :=
    pullback.lift ((stageImage GY (((Over.map (homOfLE h).op).obj j))).ι ≫ pullback.fst _ _)
      ((imageSystem GY).map aY) (by
        simp only [stageToBase, reassoc_of% hr, baseChangeComparison, pullback.lift_fst,
          Category.assoc])
  have hκsnd : κ ≫ pullback.snd _ _ = (imageSystem GY).map aY := pullback.lift_snd _ _ _
  have hκfst : κ ≫ pullback.fst _ _ =
      (stageImage GY (((Over.map (homOfLE h).op).obj j))).ι ≫ pullback.fst _ _ :=
    pullback.lift_fst _ _ _
  have hΛ := isClosedImmersion_lift_stage_pullback GY h
    (D.system.map (((Over.map (homOfLE (le_refl G'.index)).op).obj j)).hom) κ hκ q
    (pullback.fst (κ ≫ pullback.snd _ _) q) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    G'.modelMap hmap.symm
  let w : pullback (κ ≫ pullback.snd _ _) q ⟶
      pullback (D.system.map (((Over.map (homOfLE (le_refl G'.index)).op).obj j)).hom)
        G'.modelMap :=
    pullback.lift (pullback.fst _ _ ≫ κ ≫ pullback.fst _ _) (pullback.snd _ _) (by
      rw [hmap]
      simp only [Category.assoc, pullback.condition,
        reassoc_of% (IsPullback.of_hasPullback (κ ≫ pullback.snd _ _) q).w])
  have e_mod : ((stageImage G' (((Over.map (homOfLE (le_refl G'.index)).op).obj j))).ι ≫
        pullback.snd _ _) ≫ q ≫ stageToBase GY h =
      ((stageImage G' (((Over.map (homOfLE (le_refl G'.index)).op).obj j))).ι ≫ pullback.fst _ _) ≫
        D.system.map (((Over.map (homOfLE (le_refl G'.index)).op).obj j)).hom := by
    rw [← hmap, Category.assoc, Category.assoc, ← pullback.condition]
  have htr : mm ≫ (imageSystem GY).map aY =
      (stageImage G' (((Over.map (homOfLE (le_refl G'.index)).op).obj j))).ι ≫
        pullback.snd _ _ ≫ q := by
    refine (cancel_mono (stageImage GY (Over.mk (homOfLE h).op)).ι).1 ?_
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [imageSystem_map_ι_assoc, stageTargetMap_fst, reassoc_of% hmm_fst]
      simp only [Category.assoc, stageToBase] at e_mod
      rw [e_mod]
      rfl
    · simp only [Category.assoc]
      rw [imageSystem_map_ι_assoc, stageTargetMap_snd, hmm_snd]
  have hnjc : mm ≫ κ ≫ pullback.snd _ _ =
      ((stageImage G' (((Over.map (homOfLE (le_refl G'.index)).op).obj j))).ι ≫
        pullback.snd _ _) ≫ q := by
    rw [hκsnd, htr, Category.assoc]
  obtain ⟨nj, hnj1, hnj2⟩ : ∃ nj : (imageSystem G').obj
      (((Over.map (homOfLE (le_refl G'.index)).op).obj j)) ⟶
      pullback (κ ≫ pullback.snd _ _) q, nj ≫ pullback.fst _ _ = mm ∧
        nj ≫ pullback.snd _ _ =
          (stageImage G' (((Over.map (homOfLE (le_refl G'.index)).op).obj j))).ι ≫
            pullback.snd _ _ :=
    ⟨pullback.lift _ _ hnjc, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hnw : nj ≫ w = (stageImage G' (((Over.map (homOfLE (le_refl G'.index)).op).obj j))).ι := by
    apply pullback.hom_ext
    · rwa [Category.assoc, pullback.lift_fst, ← Category.assoc, hnj1, hκfst]
    · rw [Category.assoc]
      exact (congrArg (nj ≫ ·) (pullback.lift_snd _ _ _)).trans hnj2
  have : Mono w := mono_of_isClosedImmersion B S hS w hΛ
  have hZalg : IsAlgebraicSpace B S hS (pullback (κ ≫ pullback.snd _ _) q) :=
    isAlgebraicSpace_pullback B S hS _ _
      (imageSystem_isAlgebraicSpace GY (((Over.map (homOfLE h).op).obj j)))
      G'.model_isAlgebraicSpace (imageSystem_isAlgebraicSpace GY _)
  have hnj : IsClosedImmersion B S hS nj := by
    refine isClosedImmersion_of_comp_mono B S hS nj w ?_
    rw [hnw]
    exact (isClosedSubspace_stageImage G' (((Over.map (homOfLE (le_refl G'.index)).op).obj j))).2
  exact ⟨_, nj, _, _, _, IsPullback.of_hasPullback _ _, hZalg, hnj, hnj1⟩

/-- The component of the morphism of image systems of `exists_isProper_systemMorphism` at a
stage is proper: it factors as a closed immersion into `Y_j ×_{Y_m} W` followed by the base
change of the proper morphism `q : W ⟶ Y_m`. -/
private theorem isProper_stage_component (G' : GoodDiagram B S hS hZ D pX)
    (GY : GoodDiagram B S hS hZ D pY) (h : GY.index ≤ G'.index)
    (q : G'.model ⟶ (imageSystem GY).obj (Over.mk (homOfLE h).op)) (hqp : IsProper B S hS q)
    (hmap : G'.modelMap = q ≫ stageToBase GY h) (j : Over (op G'.index))
    (mm : (imageSystem G').obj ((Over.map (homOfLE (le_refl G'.index)).op).obj j) ⟶
      (imageSystem GY).obj ((Over.map (homOfLE h).op).obj j))
    (hmm_fst : mm ≫ (stageImage GY ((Over.map (homOfLE h).op).obj j)).ι ≫ pullback.fst _ _ =
      (stageImage G' ((Over.map (homOfLE (le_refl G'.index)).op).obj j)).ι ≫ pullback.fst _ _)
    (hmm_snd : mm ≫ (stageImage GY ((Over.map (homOfLE h).op).obj j)).ι ≫ pullback.snd _ _ =
      (stageImage G' ((Over.map (homOfLE (le_refl G'.index)).op).obj j)).ι ≫ pullback.snd _ _ ≫
        q ≫ (stageImage GY (Over.mk (homOfLE h).op)).ι ≫ pullback.snd _ _) :
    IsProper B S hS mm := by
  obtain ⟨Z, n, p, s', r, hpb, hZalg, hn, hnp⟩ :=
    exists_factor_stage_component G' GY h q hmap j mm hmm_fst hmm_snd
  rw [← hnp]
  exact isProper_comp B S hS
    (imageSystem_isAlgebraicSpace G' ((Over.map (homOfLE (le_refl G'.index)).op).obj j)) hZalg
    (imageSystem_isAlgebraicSpace GY ((Over.map (homOfLE h).op).obj j)) n p
    (isProper_of_isClosedImmersion B S hS
      (imageSystem_isAlgebraicSpace G' ((Over.map (homOfLE (le_refl G'.index)).op).obj j))
      hZalg n hn)
    (isProper_of_isPullback B S hS hZalg G'.model_isAlgebraicSpace
      (imageSystem_isAlgebraicSpace GY ((Over.map (homOfLE h).op).obj j))
      (imageSystem_isAlgebraicSpace GY (Over.mk (homOfLE h).op)) hpb.flip hqp)

end Main

end GoodDiagram

end AlgebraicGeometry.Space

end
