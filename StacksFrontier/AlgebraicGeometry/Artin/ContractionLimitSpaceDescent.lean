module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitRelationDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationAffine
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceModel
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitOverRelation
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceSeparated
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitAffineModel
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitWitnessHom

/-!
# Descending a separated algebraic space of finite presentation along a limit of affine schemes

Let `V = lim V_k` be a cofiltered limit of affine objects of the big fppf site of `S`, with index
category of arbitrary size `u`. A separated algebraic space `Y` of finite presentation over `V` is
the base change of an algebraic space `Y_k` over some stage `V_k` (the separated case of Stacks
07SK, without the size bound on the index which the base result needs to form limits of
algebraic spaces): an affine étale atlas `N` of `Y` and its kernel pair `R`, which is affine and
closed in `N ×_V N`, descend to a stage together with the two projections and the axioms of an
étale equivalence relation, and `Y_k` is the quotient.

This file contains the scheme-level part: models at a stage of a pair of morphisms `s, t : R ⟶ N`
of schemes of finite presentation over the limit (`AlgebraicGeometry.exists_stage_pair_model`),
transported along the canonical base-change isomorphisms of the stages
(`CategoryTheory.Over.stageRebaseIso`).

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Over

variable {I : Type*} [Category I] {C : Type*} [Category C] [HasPullbacks C] (D : I ⥤ C)
  (c : Cone D)

/-- The canonical isomorphism between the base change to the limit of the base change to a later
stage `j ⟶ i`, and the base change to the limit from stage `i`. -/
noncomputable def stageRebaseIso {i j : I} (e : j ⟶ i) (X : Over (D.obj i)) :
    (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj X) ≅
      (Over.pullback (c.π.app i)).obj X :=
  Over.isoMk (pullbackLeftPullbackSndIso X.hom (D.map e) (c.π.app j) ≪≫
    pullback.congrHom rfl (c.w e)) (by simp)

/-- The isomorphism `stageRebaseIso` followed by the first projection to `X` is the composite of
the first projections of the two base changes. -/
@[reassoc]
theorem stageRebaseIso_hom_left_fst {i j : I} (e : j ⟶ i) (X : Over (D.obj i)) :
    (stageRebaseIso D c e X).hom.left ≫ pullback.fst X.hom (c.π.app i) =
      pullback.fst _ (c.π.app j) ≫ pullback.fst X.hom (D.map e) := by
  simp [stageRebaseIso]

/-- **Comparison maps pinned by their first projection are natural.** -/
theorem stage_pinned_naturality {i j : I} (e : j ⟶ i) {X Y : Over (D.obj i)} (f : X ⟶ Y)
    (α : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj X) ⟶
      (Over.pullback (c.π.app i)).obj X)
    (β : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj Y) ⟶
      (Over.pullback (c.π.app i)).obj Y)
    (hα : α.left ≫ pullback.fst X.hom (c.π.app i) =
      pullback.fst _ (c.π.app j) ≫ pullback.fst X.hom (D.map e))
    (hβ : β.left ≫ pullback.fst Y.hom (c.π.app i) =
      pullback.fst _ (c.π.app j) ≫ pullback.fst Y.hom (D.map e)) :
    α ≫ (Over.pullback (c.π.app i)).map f =
      (Over.pullback (c.π.app j)).map ((Over.pullback (D.map e)).map f) ≫ β := by
  have h₁ := Over.w α
  have h₂ := Over.w β
  simp only [Over.pullback_obj_hom] at h₁ h₂
  have k₁ : ((Over.pullback (c.π.app i)).map f).left ≫ pullback.fst Y.hom (c.π.app i) =
      pullback.fst X.hom (c.π.app i) ≫ f.left := pullback.lift_fst _ _ _
  have k₂ : ((Over.pullback (c.π.app i)).map f).left ≫ pullback.snd Y.hom (c.π.app i) =
      pullback.snd X.hom (c.π.app i) := pullback.lift_snd _ _ _
  have k₃ : ((Over.pullback (c.π.app j)).map ((Over.pullback (D.map e)).map f)).left ≫
      pullback.fst _ (c.π.app j) =
        pullback.fst _ _ ≫ ((Over.pullback (D.map e)).map f).left := pullback.lift_fst _ _ _
  have k₄ : ((Over.pullback (c.π.app j)).map ((Over.pullback (D.map e)).map f)).left ≫
      pullback.snd _ (c.π.app j) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have k₅ : ((Over.pullback (D.map e)).map f).left ≫ pullback.fst Y.hom (D.map e) =
      pullback.fst X.hom (D.map e) ≫ f.left := pullback.lift_fst _ _ _
  ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    rw [k₁, reassoc_of% hα, hβ, reassoc_of% k₃, k₅]
  · simp only [Over.comp_left, Category.assoc]
    rw [k₂, h₁, h₂]
    exact k₄.symm

/-- A comparison map pinned by its first projection is the canonical one. -/
theorem eq_stageRebaseIso_hom {i j : I} (e : j ⟶ i) {X : Over (D.obj i)}
    (α : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj X) ⟶
      (Over.pullback (c.π.app i)).obj X)
    (hα : α.left ≫ pullback.fst X.hom (c.π.app i) =
      pullback.fst _ (c.π.app j) ≫ pullback.fst X.hom (D.map e)) :
    α = (stageRebaseIso D c e X).hom := by
  simpa using stage_pinned_naturality D c e (𝟙 X) α (stageRebaseIso D c e X).hom hα
    (stageRebaseIso_hom_left_fst D c e X)

/-- The canonical comparison maps are natural. -/
@[reassoc]
theorem stageRebaseIso_hom_naturality {i j : I} (e : j ⟶ i) {X Y : Over (D.obj i)} (f : X ⟶ Y) :
    (stageRebaseIso D c e X).hom ≫ (Over.pullback (c.π.app i)).map f =
      (Over.pullback (c.π.app j)).map ((Over.pullback (D.map e)).map f) ≫
        (stageRebaseIso D c e Y).hom :=
  stage_pinned_naturality D c e f _ _ (stageRebaseIso_hom_left_fst D c e X)
    (stageRebaseIso_hom_left_fst D c e Y)

end CategoryTheory.Over

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]

include hc in
/-- **A morphism between base changes descends, with the canonical comparison maps.** -/
theorem exists_hom_stageRebase (i : I) (X Y : Over (D.obj i)) (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj X ⟶ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj X ⟶ (Over.pullback (D.map e)).obj Y),
      (Over.stageRebaseIso D c e X).hom ≫ f =
        (Over.pullback (c.π.app j)).map g ≫ (Over.stageRebaseIso D c e Y).hom := by
  obtain ⟨j, e, g, α, β, hα, hβ, h⟩ := exists_morphism_after_baseChange D c hc i X Y hX hY f
  refine ⟨j, e, g, ?_⟩
  rw [← Over.eq_stageRebaseIso_hom D c e α.hom hα, ← Over.eq_stageRebaseIso_hom D c e β.hom hβ, h]

include hc in
/-- **An affine scheme of finite presentation over the limit, as an object over a stage.** -/
theorem exists_affine_over_model {N : Scheme.{u}} [IsAffine N] (n : N ⟶ c.pt)
    [LocallyOfFinitePresentation n] :
    ∃ (i : I) (Ni : Over (D.obj i)) (_ : (Over.pullback (c.π.app i)).obj Ni ≅ Over.mk n),
      IsAffine Ni.left ∧ LocallyOfFinitePresentation Ni.hom := by
  obtain ⟨i, Ni, ni, θ, hNi, hni, hpb⟩ := Scheme.exists_affine_model_of_isLimit D c hc n
  exact ⟨i, Over.mk ni, Over.isoMk hpb.isoPullback.symm (by simp), hNi, hni⟩

omit [IsCofiltered I] [EssentiallySmall.{u} I] [∀ i, IsAffine (D.obj i)] in
/-- The base change of an affine model to a later stage is an affine model. -/
theorem isAffine_overPullback_left {i j : I} (e : j ⟶ i) (X : Over (D.obj i)) [IsAffine X.left] :
    IsAffine ((Over.pullback (D.map e)).obj X).left := by
  change IsAffine (pullback X.hom (D.map e))
  infer_instance

omit [IsCofiltered I] [EssentiallySmall.{u} I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, IsAffine (D.obj i)] in
/-- The base change of an object locally of finite presentation is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_overPullback_hom {i j : I} (e : j ⟶ i) (X : Over (D.obj i))
    [LocallyOfFinitePresentation X.hom] :
    LocallyOfFinitePresentation ((Over.pullback (D.map e)).obj X).hom := by
  change LocallyOfFinitePresentation (pullback.snd X.hom (D.map e))
  infer_instance

omit [IsCofiltered I] [EssentiallySmall.{u} I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, IsAffine (D.obj i)] in
/-- A binary product of affine schemes over an affine scheme is affine. -/
theorem isAffine_prod_left {T : Scheme.{u}} [IsAffine T] (X Y : Over T) [IsAffine X.left]
    [IsAffine Y.left] : IsAffine (X ⨯ Y).left :=
  .of_isIso (Over.prodLeftIsoPullback X Y).hom

/-- A binary product of schemes locally of finite presentation over `T` is locally of finite
presentation over `T`. -/
theorem locallyOfFinitePresentation_prod_hom {T : Scheme.{u}} (X Y : Over T)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] :
    LocallyOfFinitePresentation (X ⨯ Y).hom := by
  have : (X ⨯ Y).hom = (Over.prodLeftIsoPullback X Y).hom ≫ pullback.fst X.hom Y.hom ≫ X.hom := by
    rw [Over.prodLeftIsoPullback_hom_fst_assoc, Over.w]
  rw [this]
  infer_instance

include hc in
/-- **Models at one stage of a pair of morphisms of affine schemes of finite presentation over
the limit.** Given `s, t : R ⟶ N` of affine schemes locally of finite presentation over the
limit, there are affine models `R_j, N_j` over a stage, locally of finite presentation, and
`s_j, t_j : R_j ⟶ N_j` whose base changes to the limit are `s, t` up to isomorphisms
`ψ_R, ψ_N`. -/
theorem exists_stage_pair_model {N R : Over c.pt} [IsAffine N.left] [IsAffine R.left]
    [LocallyOfFinitePresentation N.hom] [LocallyOfFinitePresentation R.hom] (s t : R ⟶ N) :
    ∃ (j : I) (Nj Rj : Over (D.obj j)) (sj tj : Rj ⟶ Nj)
      (ψN : (Over.pullback (c.π.app j)).obj Nj ≅ N) (ψR : (Over.pullback (c.π.app j)).obj Rj ≅ R),
      IsAffine Nj.left ∧ IsAffine Rj.left ∧ LocallyOfFinitePresentation Nj.hom ∧
        LocallyOfFinitePresentation Rj.hom ∧
        ψR.hom ≫ s = (Over.pullback (c.π.app j)).map sj ≫ ψN.hom ∧
        ψR.hom ≫ t = (Over.pullback (c.π.app j)).map tj ≫ ψN.hom := by
  obtain ⟨i₁, N₁, φN₁, hN₁, hn₁⟩ := exists_affine_over_model D c hc N.hom
  obtain ⟨i₂, R₁, φR₁, hR₁, hr₁⟩ := exists_affine_over_model D c hc R.hom
  let i := IsCofiltered.min i₁ i₂
  let e₁ : i ⟶ i₁ := IsCofiltered.minToLeft _ _
  let e₂ : i ⟶ i₂ := IsCofiltered.minToRight _ _
  let N₀ := (Over.pullback (D.map e₁)).obj N₁
  let R₀ := (Over.pullback (D.map e₂)).obj R₁
  have hN₀ : IsAffine N₀.left := isAffine_overPullback_left D e₁ N₁
  have hR₀ : IsAffine R₀.left := isAffine_overPullback_left D e₂ R₁
  have hn₀ : LocallyOfFinitePresentation N₀.hom :=
    locallyOfFinitePresentation_overPullback_hom D e₁ N₁
  have hr₀ : LocallyOfFinitePresentation R₀.hom :=
    locallyOfFinitePresentation_overPullback_hom D e₂ R₁
  let φN : (Over.pullback (c.π.app i)).obj N₀ ≅ Over.mk N.hom :=
    Over.stageRebaseIso D c e₁ N₁ ≪≫ φN₁
  let φR : (Over.pullback (c.π.app i)).obj R₀ ≅ Over.mk R.hom :=
    Over.stageRebaseIso D c e₂ R₁ ≪≫ φR₁
  let ηN : Over.mk N.hom ≅ N := Over.isoMk (Iso.refl _) (by simp)
  let ηR : Over.mk R.hom ≅ R := Over.isoMk (Iso.refl _) (by simp)
  let G := Over.pullback (c.π.app i)
  -- the pair `(s, t)` as one morphism into the product
  let P₀ := N₀ ⨯ N₀
  let κ : G.obj P₀ ≅ G.obj N₀ ⨯ G.obj N₀ := PreservesLimitPair.iso G N₀ N₀
  let f : G.obj R₀ ⟶ G.obj P₀ :=
    (φR ≪≫ ηR).hom ≫ prod.lift (s ≫ (φN ≪≫ ηN).inv) (t ≫ (φN ≪≫ ηN).inv) ≫ κ.inv
  have : IsAffine P₀.left := isAffine_prod_left N₀ N₀
  have : LocallyOfFinitePresentation P₀.hom := locallyOfFinitePresentation_prod_hom N₀ N₀
  obtain ⟨j, e, g, hg⟩ := exists_hom_stageRebase D c hc i R₀ P₀
    (finitePresentation_of_isAffine _) (finitePresentation_of_isAffine _) f
  let Ge := Over.pullback (D.map e)
  let Gj := Over.pullback (c.π.app j)
  let ι : Ge.obj R₀ ⟶ Ge.obj N₀ ⨯ Ge.obj N₀ := g ≫ (PreservesLimitPair.iso Ge N₀ N₀).hom
  let ψN := Over.stageRebaseIso D c e N₀ ≪≫ φN ≪≫ ηN
  let ψR := Over.stageRebaseIso D c e R₀ ≪≫ φR ≪≫ ηR
  have key : ∀ (π : P₀ ⟶ N₀) (π' : Ge.obj N₀ ⨯ Ge.obj N₀ ⟶ Ge.obj N₀) (u : R ⟶ N),
      (PreservesLimitPair.iso Ge N₀ N₀).hom ≫ π' = Ge.map π →
      prod.lift (s ≫ (φN ≪≫ ηN).inv) (t ≫ (φN ≪≫ ηN).inv) ≫ κ.inv ≫ G.map π =
        u ≫ (φN ≪≫ ηN).inv →
      ψR.hom ≫ u = Gj.map (ι ≫ π') ≫ ψN.hom := by
    intro π π' u hπ' hu
    have h1 : Gj.map (ι ≫ π') = Gj.map g ≫ Gj.map (Ge.map π) := by
      rw [← Gj.map_comp, Category.assoc, hπ']
    have h2 := Over.stageRebaseIso_hom_naturality D c e π
    calc ψR.hom ≫ u = (Over.stageRebaseIso D c e R₀).hom ≫ f ≫ G.map π ≫ (φN ≪≫ ηN).hom := by
          simp only [f, ψR, Iso.trans_hom, Category.assoc]
          rw [reassoc_of% hu]
          simp
      _ = Gj.map (ι ≫ π') ≫ ψN.hom := by
          rw [reassoc_of% hg, h1, Category.assoc, reassoc_of% h2]
          simp only [ψN, Iso.trans_hom]
          rfl
  refine ⟨j, Ge.obj N₀, Ge.obj R₀, ι ≫ prod.fst, ι ≫ prod.snd, ψN, ψR,
    isAffine_overPullback_left D e N₀, isAffine_overPullback_left D e R₀,
    locallyOfFinitePresentation_overPullback_hom D e N₀,
    locallyOfFinitePresentation_overPullback_hom D e R₀, ?_, ?_⟩
  · refine key prod.fst prod.fst s (by simp [PreservesLimitPair.iso_hom]) ?_
    simp only [κ, Iso.trans_inv, PreservesLimitPair.iso_inv_fst]
    exact prod.lift_fst _ _
  · refine key prod.snd prod.snd t (by simp [PreservesLimitPair.iso_hom]) ?_
    simp only [κ, Iso.trans_inv, PreservesLimitPair.iso_inv_snd]
    exact prod.lift_snd _ _

omit [IsCofiltered I] [EssentiallySmall.{u} I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, IsAffine (D.obj i)] in
/-- A fibre product of affine schemes over an affine scheme, in the slice category, is affine. -/
theorem isAffine_pullback_left {T : Scheme.{u}} [IsAffine T] {X Y Z : Over T} (f : X ⟶ Z)
    (g : Y ⟶ Z) [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left] :
    IsAffine (pullback f g).left := by
  have : IsAffine ((Over.forget T).obj X) := ‹IsAffine X.left›
  have : IsAffine ((Over.forget T).obj Y) := ‹IsAffine Y.left›
  have : IsAffine ((Over.forget T).obj Z) := ‹IsAffine Z.left›
  exact .of_isIso (PreservesPullback.iso (Over.forget T) f g).hom

omit [IsCofiltered I] [EssentiallySmall.{u} I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, IsAffine (D.obj i)] in
/-- Two maps into the image of a binary product under a functor preserving it agree as soon as
their composites with the images of the projections agree. -/
theorem hom_ext_map_prod {C C' : Type*} [Category C] [Category C'] [HasBinaryProducts C]
    [HasBinaryProducts C'] (G : C ⥤ C') [PreservesLimitsOfShape (Discrete WalkingPair) G]
    {X A : C} {W : C'} (x y : W ⟶ G.obj (X ⨯ A))
    (h₁ : x ≫ G.map prod.fst = y ≫ G.map prod.fst) (h₂ : x ≫ G.map prod.snd = y ≫ G.map prod.snd) :
    x = y := by
  rw [← cancel_mono (PreservesLimitPair.iso G X A).hom]
  apply prod.hom_ext
  · rw [Category.assoc, Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst, h₁]
  · rw [Category.assoc, Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd, h₂]

include hc in
/-- **An étale equivalence relation with closed embedding, of affine schemes of finite
presentation over the limit, has a model at one stage.** If `s, t : R ⟶ N` are étale, with
`(s, t) : R ⟶ N ×_{lim} N` a closed immersion, and reflexive, symmetric and transitive (with
witnesses), then at one stage `k` there are affine models `R_k, N_k` with `s_k, t_k : R_k ⟶ N_k`
étale, jointly monic, reflexive, symmetric and transitive, whose base changes to the limit are
`s, t` up to isomorphisms `ψ_R, ψ_N`. -/
theorem exists_stage_etaleRelation_model {N R : Over c.pt} [IsAffine N.left] [IsAffine R.left]
    [LocallyOfFinitePresentation N.hom] [LocallyOfFinitePresentation R.hom] (s t : R ⟶ N)
    (hst : IsClosedImmersion (prod.lift s t).left) (hs : Etale s.left) (ht : Etale t.left)
    (hrefl : ∃ r : N ⟶ R, r ≫ s = 𝟙 N ∧ r ≫ t = 𝟙 N)
    (hsymm : ∃ σ : R ⟶ R, σ ≫ s = t ∧ σ ≫ t = s)
    (htrans : ∃ τ : pullback t s ⟶ R, τ ≫ s = pullback.fst t s ≫ s ∧
      τ ≫ t = pullback.snd t s ≫ t) :
    ∃ (k : I) (Nk Rk : Over (D.obj k)) (sk tk : Rk ⟶ Nk)
      (ψN : (Over.pullback (c.π.app k)).obj Nk ≅ N) (ψR : (Over.pullback (c.π.app k)).obj Rk ≅ R),
      IsAffine Nk.left ∧ IsAffine Rk.left ∧ LocallyOfFinitePresentation Nk.hom ∧
        LocallyOfFinitePresentation Rk.hom ∧ Etale sk.left ∧ Etale tk.left ∧
        IsClosedImmersion (prod.lift sk tk).left ∧
        (∀ {W : Over (D.obj k)} (x y : W ⟶ Rk), x ≫ sk = y ≫ sk → x ≫ tk = y ≫ tk → x = y) ∧
        (∃ r : Nk ⟶ Rk, r ≫ sk = 𝟙 _ ∧ r ≫ tk = 𝟙 _) ∧
        (∃ σ : Rk ⟶ Rk, σ ≫ sk = tk ∧ σ ≫ tk = sk) ∧
        (∃ τ : pullback tk sk ⟶ Rk,
          τ ≫ sk = pullback.fst tk sk ≫ sk ∧ τ ≫ tk = pullback.snd tk sk ≫ tk) ∧
        ψR.hom ≫ s = (Over.pullback (c.π.app k)).map sk ≫ ψN.hom ∧
        ψR.hom ≫ t = (Over.pullback (c.π.app k)).map tk ≫ ψN.hom := by
  obtain ⟨j, Nj, Rj, sj, tj, ψN, ψR, hNa, hRa, hNf, hRf, hsj, htj⟩ :=
    exists_stage_pair_model D c hc s t
  let G := Over.pullback (c.π.app j)
  let ι₀ : Rj ⟶ Nj ⨯ Nj := prod.lift sj tj
  have hι₁ : ι₀ ≫ prod.fst = sj := prod.lift_fst _ _
  have hι₂ : ι₀ ≫ prod.snd = tj := prod.lift_snd _ _
  have hGs : G.map sj = ψR.hom ≫ s ≫ ψN.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]; exact hsj.symm
  have hGt : G.map tj = ψR.hom ≫ t ≫ ψN.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]; exact htj.symm
  have hGι : G.map ι₀ ≫ G.map prod.fst = G.map sj := by rw [← G.map_comp, hι₁]
  have hGι' : G.map ι₀ ≫ G.map prod.snd = G.map tj := by rw [← G.map_comp, hι₂]
  -- instances
  have := hNa
  have := hRa
  have := hNf
  have := hRf
  have : IsAffine (Nj ⨯ Nj).left := isAffine_prod_left Nj Nj
  have : LocallyOfFinitePresentation (Nj ⨯ Nj).hom := locallyOfFinitePresentation_prod_hom Nj Nj
  have : IsAffine (pullback (ι₀ ≫ prod.snd) (ι₀ ≫ prod.fst)).left := isAffine_pullback_left _ _
  have hlfp : ∀ {X Y : Over (D.obj j)} (f : X ⟶ Y) [LocallyOfFinitePresentation X.hom]
      [LocallyOfFinitePresentation Y.hom], LocallyOfFinitePresentation f.left := by
    intro X Y f _ _
    have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
    exact locallyOfFinitePresentation_of_comp f.left Y.hom
  have := hlfp ι₀
  have := hlfp (ι₀ ≫ prod.fst)
  have := hlfp (ι₀ ≫ prod.snd)
  -- the isomorphism-invariance of the properties of morphisms used
  have hiso : ∀ {X Y : Over c.pt} (e : X ≅ Y), IsIso e.hom.left := fun e =>
    (Over.forget _).map_isIso e.hom
  have hisoInv : ∀ {X Y : Over c.pt} (e : X ≅ Y), IsIso e.inv.left := fun e =>
    (Over.forget _).map_isIso e.inv
  -- the six properties over the limit
  have hci : IsClosedImmersion (G.map ι₀).left := by
    let κ := PreservesLimitPair.iso G Nj Nj
    have hfac : G.map ι₀ = ψR.hom ≫ prod.lift s t ≫ prod.map ψN.inv ψN.inv ≫ κ.inv := by
      apply hom_ext_map_prod G
      · rw [hGι, hGs]
        simp only [Functor.const_obj_obj, prod.lift_map_assoc, Category.assoc,
          PreservesLimitPair.iso_inv_fst, Iso.cancel_iso_hom_left, κ]
        exact (prod.lift_fst _ _).symm
      · rw [hGι', hGt]
        simp only [Functor.const_obj_obj, prod.lift_map_assoc, Category.assoc,
          PreservesLimitPair.iso_inv_snd, Iso.cancel_iso_hom_left, κ]
        exact (prod.lift_snd _ _).symm
    rw [hfac]
    have := hiso ψR
    have : IsIso (prod.map ψN.inv ψN.inv).left := (Over.forget _).map_isIso (prod.map ψN.inv ψN.inv)
    have : IsIso κ.inv.left := (Over.forget _).map_isIso κ.inv
    simp only [Over.comp_left]
    infer_instance
  have het : ∀ (u : R ⟶ N) (uj : Rj ⟶ Nj), Etale u.left → G.map uj = ψR.hom ≫ u ≫ ψN.inv →
      Etale (G.map uj).left := by
    intro u uj hu h
    rw [h]
    have := hiso ψR
    have := hisoInv ψN
    simp only [Over.comp_left]
    infer_instance
  have het₁ : Etale (G.map (ι₀ ≫ prod.fst)).left := het s _ hs (by rw [hι₁]; exact hGs)
  have het₂ : Etale (G.map (ι₀ ≫ prod.snd)).left := het t _ ht (by rw [hι₂]; exact hGt)
  have hrefl' : ∃ ψ, ψ ≫ G.map ι₀ = G.map (relRefl Nj) := by
    obtain ⟨r, hr₁, hr₂⟩ := hrefl
    refine ⟨ψN.hom ≫ r ≫ ψR.inv, hom_ext_map_prod G _ _ ?_ ?_⟩
    · rw [Category.assoc, hGι, hGs, ← G.map_comp, prod.lift_fst, G.map_id]
      simp [reassoc_of% hr₁]
    · rw [Category.assoc, hGι', hGt, ← G.map_comp, prod.lift_snd, G.map_id]
      simp [reassoc_of% hr₂]
  have hsymm' : ∃ ψ, ψ ≫ G.map ι₀ = G.map (relSymm ι₀) := by
    obtain ⟨σ, hσ₁, hσ₂⟩ := hsymm
    refine ⟨ψR.hom ≫ σ ≫ ψR.inv, hom_ext_map_prod G _ _ ?_ ?_⟩
    · have hr : G.map (relSymm ι₀) ≫ G.map prod.fst = G.map tj := by
        rw [← G.map_comp, relSymm, Category.assoc, prod.lift_fst, hι₂]
      rw [Category.assoc, hGι, hGs, hr, hGt]
      simp [reassoc_of% hσ₁]
    · have hr : G.map (relSymm ι₀) ≫ G.map prod.snd = G.map sj := by
        rw [← G.map_comp, relSymm, Category.assoc, prod.lift_snd, hι₁]
      rw [Category.assoc, hGι', hGt, hr, hGs]
      simp [reassoc_of% hσ₂]
  have htrans' : ∃ ψ, ψ ≫ G.map ι₀ = G.map (relTrans ι₀) := by
    obtain ⟨τ, hτ₁, hτ₂⟩ := htrans
    let e := PreservesPullback.iso G (ι₀ ≫ prod.snd) (ι₀ ≫ prod.fst)
    have h₁ : G.map (ι₀ ≫ prod.snd) ≫ ψN.hom = ψR.hom ≫ t := by rw [hι₂]; exact htj.symm
    have h₂ : G.map (ι₀ ≫ prod.fst) ≫ ψN.hom = ψR.hom ≫ s := by rw [hι₁]; exact hsj.symm
    have w : pullback.fst (G.map (ι₀ ≫ prod.snd)) (G.map (ι₀ ≫ prod.fst)) ≫ ψR.hom ≫ t =
        pullback.snd (G.map (ι₀ ≫ prod.snd)) (G.map (ι₀ ≫ prod.fst)) ≫ ψR.hom ≫ s := by
      rw [← h₁, ← h₂, pullback.condition_assoc]
    let m := pullback.lift (pullback.fst _ _ ≫ ψR.hom) (pullback.snd _ _ ≫ ψR.hom)
      (by simpa only [Category.assoc] using w) ≫ τ
    refine ⟨e.hom ≫ m ≫ ψR.inv, hom_ext_map_prod G _ _ ?_ ?_⟩
    · have hr : G.map (relTrans ι₀) ≫ G.map prod.fst =
          G.map (pullback.fst (ι₀ ≫ prod.snd) (ι₀ ≫ prod.fst)) ≫ G.map sj := by
        rw [← G.map_comp, ← G.map_comp, ← hι₁]
        exact congrArg G.map (prod.lift_fst _ _)
      rw [hr, Category.assoc, Category.assoc, hGι, hGs]
      simp only [m, Category.assoc, Iso.inv_hom_id_assoc]
      rw [reassoc_of% hτ₁, pullback.lift_fst_assoc]
      simp only [Category.assoc]
      rw [PreservesPullback.iso_hom_fst_assoc]
    · have hr : G.map (relTrans ι₀) ≫ G.map prod.snd =
          G.map (pullback.snd (ι₀ ≫ prod.snd) (ι₀ ≫ prod.fst)) ≫ G.map tj := by
        rw [← G.map_comp, ← G.map_comp, ← hι₂]
        exact congrArg G.map (prod.lift_snd _ _)
      rw [hr, Category.assoc, Category.assoc, hGι', hGt]
      simp only [m, Category.assoc, Iso.inv_hom_id_assoc]
      rw [reassoc_of% hτ₂, pullback.lift_snd_assoc]
      simp only [Category.assoc]
      rw [PreservesPullback.iso_hom_snd_assoc]
  obtain ⟨a, hca, hea₁, hea₂, hra, hsa, hta⟩ :=
    exists_stage_relation D c hc j ι₀ hci het₁ het₂ hrefl' hsymm' htrans'
  obtain ⟨hjm, hr, hσ, hτ⟩ := exists_relationData D j ι₀ a.hom hca hra hsa hta
  let Ga := Over.pullback (D.map a.hom)
  refine ⟨a.left, Ga.obj Nj, Ga.obj Rj, Ga.map (ι₀ ≫ prod.fst), Ga.map (ι₀ ≫ prod.snd),
    Over.stageRebaseIso D c a.hom Nj ≪≫ ψN, Over.stageRebaseIso D c a.hom Rj ≪≫ ψR,
    isAffine_overPullback_left D a.hom Nj, isAffine_overPullback_left D a.hom Rj,
    locallyOfFinitePresentation_overPullback_hom D a.hom Nj,
    locallyOfFinitePresentation_overPullback_hom D a.hom Rj, hea₁, hea₂, ?_, hjm, hr, hσ,
    hτ, ?_, ?_⟩
  · have e : prod.lift (Ga.map (ι₀ ≫ prod.fst)) (Ga.map (ι₀ ≫ prod.snd)) =
        Ga.map ι₀ ≫ (PreservesLimitPair.iso Ga Nj Nj).hom := by
      apply prod.hom_ext
      · rw [prod.lift_fst, Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst,
          Ga.map_comp]
      · rw [prod.lift_snd, Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd,
          Ga.map_comp]
    rw [e, Over.comp_left]
    have : IsIso (PreservesLimitPair.iso Ga Nj Nj).hom.left :=
      (Over.forget _).map_isIso (PreservesLimitPair.iso Ga Nj Nj).hom
    infer_instance
  · rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, hsj, ← hι₁,
      Over.stageRebaseIso_hom_naturality_assoc]
  · rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, htj, ← hι₂,
      Over.stageRebaseIso_hom_naturality_assoc]

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A pair of maps into the base of a kernel pair of `yoneda` objects which agree after the atlas
map factors through the kernel pair. -/
private theorem exists_comp_eq_of_isPullback_yoneda {C : Type*} [Category C] {R N R' : C}
    {Y : Cᵒᵖ ⥤ Type _} {s t : R ⟶ N} {n : yoneda.obj N ⟶ Y}
    (hR : IsPullback (yoneda.map s) (yoneda.map t) n n) (s' t' : R' ⟶ N)
    (h : yoneda.map s' ≫ n = yoneda.map t' ≫ n) : ∃ ρ : R' ⟶ R, ρ ≫ s = s' ∧ ρ ≫ t = t' :=
  ⟨yoneda.preimage (hR.lift _ _ h),
    yoneda.map_injective (by rw [Functor.map_comp, Functor.map_preimage, hR.lift_fst]),
    yoneda.map_injective (by rw [Functor.map_comp, Functor.map_preimage, hR.lift_snd])⟩

/-- **The base change of a quotient is the quotient of the base change.** Let `Y` and `Y_k` be
algebraic spaces over `V` and `V_k` with surjective étale atlases `n : N ⟶ Y`, `q : N_k ⟶ Y_k`
and kernel pairs `R`, `R_k`. If `f : V ⟶ V_k` identifies `N` with `V ×_{V_k} N_k` over `V`, and
`R` with `V ×_{V_k} R_k` compatibly with both projections, then `Y` is the base change of `Y_k`
along `f`. -/
theorem exists_isPullback_of_atlas_baseChange
    {Y Yk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYk : IsAlgebraicSpace B S hS Yk)
    {V Vk N R Nk Rk : BigFppfOver B S hS} (f : V ⟶ Vk)
    (p : Y ⟶ yoneda.obj V) (pk : Yk ⟶ yoneda.obj Vk)
    (n : yoneda.obj N ⟶ Y)
    (hns : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf n)
    (hne : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf n)
    {s t : R ⟶ N} (hR : IsPullback (yoneda.map s) (yoneda.map t) n n)
    (q : yoneda.obj Nk ⟶ Yk)
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    {sk tk : Rk ⟶ Nk} (hRk : IsPullback (yoneda.map sk) (yoneda.map tk) q q)
    (n₀ : N ⟶ V) (hn₀ : yoneda.map n₀ = n ≫ p) (nk : Nk ⟶ Vk) (hnk : yoneda.map nk = q ≫ pk)
    (θN : N ≅ pullback f nk) (hθN : θN.hom ≫ pullback.fst f nk = n₀)
    (rk : Rk ⟶ Vk) (hrk : sk ≫ nk = rk) (θR : R ≅ pullback f rk)
    (hθs : θR.hom ≫ pullbackMapRight f sk hrk = s ≫ θN.hom)
    (hθt : θR.hom ≫ pullbackMapRight f tk ((kernelPair_comp_eq hRk hnk).symm.trans hrk) =
      t ≫ θN.hom) :
    ∃ a : Y ⟶ Yk, n ≫ a = yoneda.map (θN.hom ≫ pullback.snd f nk) ≫ q ∧
      IsPullback p a (yoneda.map f) pk := by
  have hYs := hY.isSheaf
  have hYks := hYk.isSheaf
  have hst : s ≫ n₀ = t ≫ n₀ := kernelPair_comp_eq hR hn₀
  have hstk : sk ≫ nk = tk ≫ nk := kernelPair_comp_eq hRk hnk
  -- the morphism `a`
  let k : yoneda.obj N ⟶ Yk := yoneda.map (θN.hom ≫ pullback.snd f nk) ≫ q
  obtain ⟨a, ha, -⟩ := existsUnique_hom_of_atlas_invariant B S hS hYs hYks n hns hne k
    (by
      intro R' s' t' hsq
      obtain ⟨ρ, hρs, hρt⟩ := exists_comp_eq_of_isPullback_yoneda hR s' t' hsq.w
      have e : ∀ (u : R ⟶ N) (uk : Rk ⟶ Nk) (huk : uk ≫ nk = rk),
          θR.hom ≫ pullbackMapRight f uk huk = u ≫ θN.hom →
          yoneda.map (ρ ≫ u) ≫ k = yoneda.map (ρ ≫ θR.hom ≫ pullback.snd f rk) ≫
            yoneda.map uk ≫ q := by
        intro u uk huk hu
        simp only [k, ← Functor.map_comp_assoc, Category.assoc]
        rw [← reassoc_of% hu, pullbackMapRight_snd]
      rw [← hρs, ← hρt, e s sk hrk hθs, e t tk (hstk.symm.trans hrk) hθt, hRk.w])
  have hw : p ≫ yoneda.map f = a ≫ pk := by
    apply hom_ext_of_etale_atlas B S hS hYs (isAlgebraicSpace_yoneda B S hS Vk).isSheaf n hns hne
    rw [← Category.assoc, ← hn₀, ← Category.assoc, ha, Category.assoc, ← hnk, ← Functor.map_comp,
      ← Functor.map_comp, Category.assoc, ← pullback.condition, reassoc_of% hθN]
  -- the comparison map to the base change and its inverse
  let φ : Y ⟶ pullback (yoneda.map f) pk := pullback.lift p a hw
  let ν := chartToPullbackYoneda pk q nk hnk f
  have hpbν := isPullback_chartToPullbackYoneda pk q nk hnk f
  have hνe := presheaf_of_isPullback B S hS hpbν hqe
  have hνs := presheaf_of_isPullback B S hS hpbν hqs
  have hPs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback (yoneda.map f) pk) :=
    (isAlgebraicSpace_pullback B S hS (yoneda.map f) pk (isAlgebraicSpace_yoneda B S hS V) hYk
      (isAlgebraicSpace_yoneda B S hS Vk)).isSheaf
  obtain ⟨ψ, hψ, -⟩ := existsUnique_hom_of_atlas_invariant B S hS hPs hYs ν hνs hνe
    (yoneda.map θN.inv ≫ n) (by
      intro R' s' t' hsq
      have hw' := hsq.w
      have hfst : s' ≫ pullback.fst f nk = t' ≫ pullback.fst f nk := yoneda.map_injective (by
        have := congrArg (· ≫ pullback.fst (yoneda.map f) pk) hw'
        simpa only [ν, Category.assoc, chartToPullbackYoneda_fst, ← Functor.map_comp] using this)
      have hsnd : yoneda.map (s' ≫ pullback.snd f nk) ≫ q =
          yoneda.map (t' ≫ pullback.snd f nk) ≫ q := by
        have := congrArg (· ≫ pullback.snd (yoneda.map f) pk) hw'
        simpa only [ν, Category.assoc, chartToPullbackYoneda_snd, Functor.map_comp] using this
      obtain ⟨ρk, hρs, hρt⟩ := exists_comp_eq_of_isPullback_yoneda hRk _ _ hsnd
      let l : R' ⟶ pullback f rk := pullback.lift (s' ≫ pullback.fst f nk) ρk (by
        simp only [Category.assoc]
        rw [pullback.condition, ← reassoc_of% hρs, hrk])
      have key : ∀ (u : R ⟶ N) (uk : Rk ⟶ Nk) (huk : uk ≫ nk = rk) (u' : R' ⟶ pullback f nk),
          θR.hom ≫ pullbackMapRight f uk huk = u ≫ θN.hom →
          s' ≫ pullback.fst f nk = u' ≫ pullback.fst f nk → ρk ≫ uk = u' ≫ pullback.snd f nk →
          yoneda.map u' ≫ yoneda.map θN.inv = yoneda.map (l ≫ θR.inv) ≫ yoneda.map u := by
        intro u uk huk u' hu h₁ h₂
        have hl : l ≫ pullbackMapRight f uk huk = u' := by
          apply pullback.hom_ext
          · simp only [Category.assoc, pullbackMapRight_fst]
            exact (pullback.lift_fst _ _ _).trans h₁
          · simp only [Category.assoc, pullbackMapRight_snd]
            exact (pullback.lift_snd_assoc _ _ _ _).trans h₂
        have hθ : θR.inv ≫ u = pullbackMapRight f uk huk ≫ θN.inv := by
          rw [Iso.inv_comp_eq, reassoc_of% hu]; simp
        rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, hθ, ← Category.assoc, hl]
      rw [← Category.assoc, key s sk hrk s' hθs rfl hρs, ← Category.assoc,
        key t tk (hstk.symm.trans hrk) t' hθt hfst hρt, Category.assoc, Category.assoc, hR.w])
  have hnφ : n ≫ φ = yoneda.map θN.hom ≫ ν := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, chartToPullbackYoneda_fst, ← hn₀,
        ← Functor.map_comp, hθN]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, chartToPullbackYoneda_snd, ha]
      simp only [k, Functor.map_comp, Category.assoc]
  have h₁ : φ ≫ ψ = 𝟙 Y := by
    apply hom_ext_of_etale_atlas B S hS hYs hYs n hns hne
    rw [reassoc_of% hnφ, hψ, ← Functor.map_comp_assoc, Iso.hom_inv_id, yoneda.map_id,
      Category.id_comp, Category.comp_id]
  have h₂ : ψ ≫ φ = 𝟙 _ := by
    apply hom_ext_of_etale_atlas B S hS hPs hPs ν hνs hνe
    rw [reassoc_of% hψ, hnφ, ← Functor.map_comp_assoc, Iso.inv_hom_id, yoneda.map_id,
      Category.id_comp, Category.comp_id]
  refine ⟨a, ha, IsPullback.of_iso_pullback ⟨hw⟩ ⟨φ, ψ, h₁, h₂⟩ (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)⟩

/-- **A site isomorphism with a base change, from an isomorphism of schemes over the base.** An
isomorphism of schemes over `V` between `V ×_{V_k} X` and `N` gives an isomorphism of objects
of the site between `N` and the fibre product `V ×_{V_k} X`, over `V`. -/
theorem exists_iso_pullback_of_overIso {V Vk N : BigFppfOver B S hS} (f : V ⟶ Vk) (n₀ : N ⟶ V)
    (X : Over ((BigFppfOver.toScheme B S hS).obj Vk)) (hX : B.Contains X.left)
    (ψ : (Over.pullback ((BigFppfOver.toScheme B S hS).map f)).obj X ≅
      Over.mk ((BigFppfOver.toScheme B S hS).map n₀)) :
    ∃ θ : N ≅ pullback f (overSiteToBase X hX), θ.hom ≫ pullback.fst _ _ = n₀ ∧
      (BigFppfOver.toScheme B S hS).map (θ.hom ≫ pullback.snd _ _) =
        ψ.inv.left ≫ pullback.fst X.hom ((BigFppfOver.toScheme B S hS).map f) := by
  let T := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan T := comp_preservesLimitsOfShape _ _
  let h : T.obj N ⟶ X.left := ψ.inv.left ≫ pullback.fst X.hom (T.map f)
  have hψ : ψ.inv.left ≫ pullback.snd X.hom (T.map f) = T.map n₀ := Over.w ψ.inv
  have hh : h ≫ X.hom = T.map n₀ ≫ T.map f := by
    simp only [h, Category.assoc, pullback.condition, reassoc_of% hψ]
  have hincl : ∀ {A A' : BigFppfOver B S hS} (g : A ⟶ A'),
      T.map g ≫ B.inclusion.map A'.hom = B.inclusion.map A.hom := fun g => by
    change B.inclusion.map g.left ≫ _ = _
    rw [← Functor.map_comp, Over.w g]
  let w : N ⟶ overSiteObj X hX :=
    BigFppfOver.homMk B S hS hX (X.hom ≫ B.inclusion.map Vk.hom) h (by
      rw [← Category.assoc, hh, Category.assoc, hincl f, hincl n₀])
  have hw : T.map w = h := rfl
  let θhom : N ⟶ pullback f (overSiteToBase X hX) := pullback.lift n₀ w
    (BigFppfOver.map_toScheme_injective B S hS (by
      change T.map (n₀ ≫ f) = T.map (w ≫ overSiteToBase X hX)
      rw [T.map_comp, T.map_comp, hw, toScheme_map_overSiteToBase]
      exact hh.symm))
  have hsq₁ : IsPullback (T.map n₀) h (T.map f) X.hom := by
    refine (IsPullback.of_hasPullback X.hom (T.map f)).flip.of_iso ((Over.forget _).mapIso ψ)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · exact (Category.comp_id _).trans (Over.w ψ.hom).symm
    · simp [h]
  have hsq₂ := (IsPullback.of_hasPullback f (overSiteToBase X hX)).map T
  have hT : IsIso (T.map θhom) := by
    have e : T.map θhom = (hsq₁.isoIsPullback _ _ hsq₂).hom := by
      apply hsq₂.hom_ext
      · rw [← T.map_comp, pullback.lift_fst]
        exact (IsPullback.isoIsPullback_hom_fst _ _ hsq₁ hsq₂).symm
      · rw [← T.map_comp, pullback.lift_snd, hw]
        exact (IsPullback.isoIsPullback_hom_snd _ _ hsq₁ hsq₂).symm
    rw [e]
    infer_instance
  have : IsIso θhom := isIso_of_reflects_iso θhom T
  refine ⟨asIso θhom, pullback.lift_fst _ _ _, ?_⟩
  change T.map (θhom ≫ pullback.snd _ _) = _
  rw [pullback.lift_snd, hw]

/-- **A separated algebraic space of finite presentation over a limit of affine objects descends to
a stage** (the separated case of Stacks 07SK, for an index category of any size `u`). Let
`V = lim V_k` be a cofiltered limit of affine objects of the site and `p : Y ⟶ V` a separated
morphism locally of finite presentation from a quasi-compact algebraic space. Then `Y` is the
base change of an algebraic space `Y_k ⟶ V_k` over some stage. -/
theorem exists_stage_model_of_isSeparated
    {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ BigFppfOver B S hS} {c : Cone E}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (p : Y ⟶ yoneda.obj c.pt) (hsep : IsSeparated B S hS p)
    (hqc : IsQuasiCompactSpace B S hS Y) (hlfp : IsLocallyOfFinitePresentation B S hS p) :
    ∃ (k : I) (Yk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Yk)
      (pk : Yk ⟶ yoneda.obj (E.obj k)) (a : Y ⟶ Yk),
      IsPullback p a (yoneda.map (c.π.app k)) pk ∧ IsSeparated B S hS pk ∧
        IsFiniteType B S hS pk := by
  let T := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan T := comp_preservesLimitsOfShape _ _
  let D := E ⋙ T
  let c' := T.mapCone c
  have : EssentiallySmall.{u} I := essentiallySmallSelf.{u} I
  have : ∀ i, IsAffine (D.obj i) := hE
  have : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map f) :=
    fun f => isAffineHom_of_isAffine _
  have : IsAffine c'.pt := hpt
  -- an affine étale atlas of `Y` and its kernel pair
  obtain ⟨N, n, hN, hnsurj, hnet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y hY).1 hqc
  have hnet' := (isEtale_iff_presheaf_of_yoneda B S hS n).1 hnet
  obtain ⟨R, s, t, hR⟩ := exists_kernelPair_of_etale_atlas B S hS n hnet'
  have hRaff : IsAffine (T.obj R) :=
    isAffine_of_isAbsolutelySeparated B S hS B.contains_terminal
      (isAbsolutelySeparated_of_isSeparated_to_affine B S hS B.contains_terminal c.pt hpt p hsep)
      hR hN hN
  have : IsAffine (T.obj N) := hN
  let n₀ : N ⟶ c.pt := yoneda.preimage (n ≫ p)
  have hn₀ : yoneda.map n₀ = n ≫ p := yoneda.map_preimage _
  have hst : s ≫ n₀ = t ≫ n₀ := kernelPair_comp_eq hR hn₀
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
      (yoneda.map (𝟙 c.pt)) :=
    (presheaf_yoneda_map_iff B S hS inferInstance (𝟙 c.pt)).2 (by
      change Etale (T.map (𝟙 c.pt))
      rw [T.map_id]
      infer_instance)
  have hnlfp : LocallyOfFinitePresentation (T.map n₀) :=
    hlfp N c.pt n (yoneda.map (𝟙 c.pt)) n₀ hnet' hid (by rw [yoneda.map_id, Category.comp_id, hn₀])
  obtain ⟨hse, hte⟩ := etale_kernelPair hR hnet'
  have hci := isClosedImmersion_lift_kernelPair hR hsep hn₀
  -- the scheme-level relation over the limit
  let Nov : Over c'.pt := Over.mk (T.map n₀)
  let Rov : Over c'.pt := Over.mk (T.map (s ≫ n₀))
  have : IsAffine Nov.left := hN
  have : IsAffine Rov.left := hRaff
  have : LocallyOfFinitePresentation Nov.hom := hnlfp
  have : LocallyOfFinitePresentation Rov.hom := by
    change LocallyOfFinitePresentation (T.map (s ≫ n₀))
    rw [T.map_comp]
    infer_instance
  let sov : Rov ⟶ Nov := Over.homMk (T.map s) (T.map_comp _ _).symm
  let tov : Rov ⟶ Nov := Over.homMk (T.map t) (by
    change T.map t ≫ T.map n₀ = T.map (s ≫ n₀)
    rw [← T.map_comp, hst])
  have hlift : AlgebraicGeometry.IsClosedImmersion (prod.lift sov tov).left := by
    have e : (prod.lift sov tov).left = T.map (pullback.lift s t hst) ≫
        (PreservesPullback.iso T n₀ n₀).hom ≫ (Over.prodLeftIsoPullback Nov Nov).inv := by
      rw [← cancel_mono (Over.prodLeftIsoPullback Nov Nov).hom, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      apply pullback.hom_ext
      · rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst, ← Over.comp_left, prod.lift_fst]
        change T.map s = T.map (pullback.lift s t hst) ≫ (PreservesPullback.iso T n₀ n₀).hom ≫
          pullback.fst (T.map n₀) (T.map n₀)
        rw [PreservesPullback.iso_hom_fst, ← T.map_comp, pullback.lift_fst]
      · rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd, ← Over.comp_left, prod.lift_snd]
        change T.map t = T.map (pullback.lift s t hst) ≫ (PreservesPullback.iso T n₀ n₀).hom ≫
          pullback.snd (T.map n₀) (T.map n₀)
        rw [PreservesPullback.iso_hom_snd, ← T.map_comp, pullback.lift_snd]
    rw [e]
    infer_instance
  have hreflov : ∃ r : Nov ⟶ Rov, r ≫ sov = 𝟙 Nov ∧ r ≫ tov = 𝟙 Nov := by
    obtain ⟨r, hr₁, hr₂⟩ := exists_refl_kernelPair hR
    refine ⟨Over.homMk (T.map r) (by
      change T.map r ≫ T.map (s ≫ n₀) = T.map n₀
      rw [← T.map_comp, reassoc_of% hr₁]), ?_, ?_⟩
    · ext1
      change T.map r ≫ T.map s = 𝟙 _
      rw [← T.map_comp, hr₁, T.map_id]
    · ext1
      change T.map r ≫ T.map t = 𝟙 _
      rw [← T.map_comp, hr₂, T.map_id]
  have hsymmov : ∃ σ : Rov ⟶ Rov, σ ≫ sov = tov ∧ σ ≫ tov = sov := by
    obtain ⟨σ, hσ₁, hσ₂⟩ := exists_symm_kernelPair hR
    refine ⟨Over.homMk (T.map σ) (by
      change T.map σ ≫ T.map (s ≫ n₀) = T.map (s ≫ n₀)
      rw [← T.map_comp, reassoc_of% hσ₁, hst]), ?_, ?_⟩
    · ext1
      change T.map σ ≫ T.map s = T.map t
      rw [← T.map_comp, hσ₁]
    · ext1
      change T.map σ ≫ T.map t = T.map s
      rw [← T.map_comp, hσ₂]
  have htransov : ∃ τ : pullback tov sov ⟶ Rov, τ ≫ sov = pullback.fst tov sov ≫ sov ∧
      τ ≫ tov = pullback.snd tov sov ≫ tov := by
    obtain ⟨τ, hτ₁, hτ₂⟩ := exists_trans_kernelPair hR
    let e₁ : (pullback tov sov).left ≅ pullback (T.map t) (T.map s) :=
      PreservesPullback.iso (Over.forget c'.pt) tov sov
    let e₂ : T.obj (pullback t s) ≅ pullback (T.map t) (T.map s) := PreservesPullback.iso T t s
    have k₁ : e₁.hom ≫ pullback.fst (T.map t) (T.map s) = (pullback.fst tov sov).left :=
      PreservesPullback.iso_hom_fst (Over.forget c'.pt) tov sov
    have k₂ : e₁.hom ≫ pullback.snd (T.map t) (T.map s) = (pullback.snd tov sov).left :=
      PreservesPullback.iso_hom_snd (Over.forget c'.pt) tov sov
    have k₃ : e₂.inv ≫ T.map (pullback.fst t s) = pullback.fst (T.map t) (T.map s) :=
      PreservesPullback.iso_inv_fst T t s
    have k₄ : e₂.inv ≫ T.map (pullback.snd t s) = pullback.snd (T.map t) (T.map s) :=
      PreservesPullback.iso_inv_snd T t s
    have hτu : ∀ (u : R ⟶ N) (a : pullback t s ⟶ R) (b : (pullback tov sov).left ⟶ T.obj R)
        (c : pullback (T.map t) (T.map s) ⟶ T.obj R), τ ≫ u = a ≫ u →
        e₂.inv ≫ T.map a = c → e₁.hom ≫ c = b →
        (e₁.hom ≫ e₂.inv ≫ T.map τ) ≫ T.map u = b ≫ T.map u := by
      intro u a b c h hc hb
      rw [← hb, ← hc]
      simp only [Category.assoc, ← T.map_comp, h]
    have hτs := hτu s _ _ _ hτ₁ k₃ k₁
    have hτt := hτu t _ _ _ hτ₂ k₄ k₂
    refine ⟨Over.homMk (e₁.hom ≫ e₂.inv ≫ T.map τ) ?_, ?_, ?_⟩
    · change (e₁.hom ≫ e₂.inv ≫ T.map τ) ≫ T.map (s ≫ n₀) = (pullback tov sov).hom
      rw [T.map_comp, ← Category.assoc, hτs, ← Over.w (pullback.fst tov sov)]
      simp only [Category.assoc]
      rfl
    · ext1
      exact hτs
    · ext1
      exact hτt
  -- the model at a stage
  obtain ⟨k, Nk, Rk, sk, tk, ψN, ψR, hNka, hRka, hNkf, hRkf, hske, htke, hjc, hjm, ⟨r, hr₁, hr₂⟩,
    ⟨σ, hσ₁, hσ₂⟩, ⟨τ, hτ₁, hτ₂⟩, hψs, hψt⟩ :=
    exists_stage_etaleRelation_model D c' hc sov tov hlift hse hte hreflov hsymmov htransov
  have hcont : ∀ X : Over (D.obj k), IsAffine X.left → LocallyOfFinitePresentation X.hom →
      B.Contains X.left := fun X hXa hXf => by
    have : AlgebraicGeometry.QuasiCompact X.hom := quasiCompact_of_compactSpace X.hom
    exact contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Y₀ := E.obj k) X.hom
  have hNc := hcont Nk hNka hNkf
  have hRc := hcont Rk hRka hRkf
  obtain ⟨Yk, hYk, q, pk, hqs, hqe, hqk, hqp⟩ :=
    exists_quotient_of_overRelation (V := E.obj k) hNc hRc sk tk hske htke hjm r hr₁ hr₂
      σ hσ₁ hσ₂ τ hτ₁ hτ₂
  -- the comparison with `Y`
  obtain ⟨θN, hθN₁, hθN₂⟩ := exists_iso_pullback_of_overIso (c.π.app k) n₀ Nk hNc ψN
  obtain ⟨θR, hθR₁, hθR₂⟩ := exists_iso_pullback_of_overIso (c.π.app k) (s ≫ n₀) Rk hRc ψR
  have hsq : ∀ (u : R ⟶ N) (uk : Rk ⟶ Nk) (uov : Rov ⟶ Nov), T.map u = uov.left →
      ψR.hom ≫ uov = (Over.pullback (c'.π.app k)).map uk ≫ ψN.hom →
      (huk : overSiteHom hRc hNc uk ≫ overSiteToBase Nk hNc = overSiteToBase Rk hRc) →
      u ≫ n₀ = s ≫ n₀ →
      θR.hom ≫ pullbackMapRight (c.π.app k) (overSiteHom hRc hNc uk) huk = u ≫ θN.hom := by
    intro u uk uov hu hψ huk hun
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackMapRight_fst, hθR₁, Category.assoc, hθN₁, hun]
    · apply BigFppfOver.map_toScheme_injective B S hS
      have h' : uov ≫ ψN.inv = ψR.inv ≫ (Over.pullback (c'.π.app k)).map uk := by
        rw [Iso.comp_inv_eq, Category.assoc, ← hψ, Iso.inv_hom_id_assoc]
      have h'' : uov.left ≫ ψN.inv.left =
          ψR.inv.left ≫ ((Over.pullback (c'.π.app k)).map uk).left := congrArg (fun m => m.left) h'
      have hG : ((Over.pullback (c'.π.app k)).map uk).left ≫ pullback.fst Nk.hom (c'.π.app k) =
          pullback.fst Rk.hom (c'.π.app k) ≫ uk.left := pullback.lift_fst _ _ _
      have L : T.map (θR.hom ≫ pullbackMapRight (c.π.app k) (overSiteHom hRc hNc uk) huk ≫
          pullback.snd _ _) = ψR.inv.left ≫ pullback.fst Rk.hom (c'.π.app k) ≫ uk.left := by
        rw [pullbackMapRight_snd, ← Category.assoc, T.map_comp]
        exact (congrArg (· ≫ T.map (overSiteHom hRc hNc uk)) hθR₂).trans (Category.assoc _ _ _)
      have Rr : T.map (u ≫ θN.hom ≫ pullback.snd _ _) =
          uov.left ≫ ψN.inv.left ≫ pullback.fst Nk.hom (c'.π.app k) := by
        rw [T.map_comp, hθN₂, hu]
        rfl
      have key : ψR.inv.left ≫ pullback.fst Rk.hom (c'.π.app k) ≫ uk.left =
          uov.left ≫ ψN.inv.left ≫ pullback.fst Nk.hom (c'.π.app k) := by
        rw [← hG, ← Category.assoc, ← h'', Category.assoc]
      change T.map (θR.hom ≫ pullbackMapRight _ _ huk ≫ pullback.snd _ _) =
        T.map (u ≫ θN.hom ≫ pullback.snd _ _)
      exact L.trans (key.trans Rr.symm)
  obtain ⟨a, -, hpb⟩ := exists_isPullback_of_atlas_baseChange hY hYk (c.π.app k) p pk n hnsurj
    hnet' hR q hqs hqe hqk n₀ hn₀ (overSiteToBase Nk hNc) hqp.symm θN hθN₁
    (overSiteToBase Rk hRc) (overSiteHom_comp_overSiteToBase hRc hNc sk) θR
    (hsq s sk sov rfl hψs _ rfl) (hsq t tk tov rfl hψt _ hst.symm)
  -- separatedness and finite type of the stage model
  have hci : AlgebraicGeometry.IsClosedImmersion (T.map (pullback.lift (overSiteHom hRc hNc sk)
      (overSiteHom hRc hNc tk) (kernelPair_comp_eq hqk hqp.symm))) := by
    have := hjc
    have r₁ : ((prod.lift sk tk).left ≫ (Over.prodLeftIsoPullback Nk Nk).hom) ≫
        pullback.fst Nk.hom Nk.hom = sk.left := by
      rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst, ← Over.comp_left, prod.lift_fst]
    have r₂ : ((prod.lift sk tk).left ≫ (Over.prodLeftIsoPullback Nk Nk).hom) ≫
        pullback.snd Nk.hom Nk.hom = tk.left := by
      rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd, ← Over.comp_left, prod.lift_snd]
    have e : T.map (pullback.lift (overSiteHom hRc hNc sk) (overSiteHom hRc hNc tk)
        (kernelPair_comp_eq hqk hqp.symm)) ≫ (PreservesPullback.iso T _ _).hom =
        (prod.lift sk tk).left ≫ (Over.prodLeftIsoPullback Nk Nk).hom := by
      apply pullback.hom_ext
      · rw [Category.assoc, PreservesPullback.iso_hom_fst, ← T.map_comp, pullback.lift_fst]
        exact r₁.symm
      · rw [Category.assoc, PreservesPullback.iso_hom_snd, ← T.map_comp, pullback.lift_snd]
        exact r₂.symm
    rw [← MorphismProperty.cancel_right_of_respectsIso
      (P := @AlgebraicGeometry.IsClosedImmersion) _ (PreservesPullback.iso T _ _).hom, e]
    exact (MorphismProperty.cancel_right_of_respectsIso
      (P := @AlgebraicGeometry.IsClosedImmersion) (prod.lift sk tk).left
      (Over.prodLeftIsoPullback Nk Nk).hom).2 hjc
  have hsepk : IsSeparated B S hS pk :=
    isSeparated_of_isClosedImmersion_lift_kernelPair hYk pk hqs hqe hqk hqp.symm hci
  have hftk : IsFiniteType B S hS pk :=
    isFiniteType_of_affine_atlas hYk (hE k) (V := E.obj k) (N := overSiteObj Nk hNc) hNka pk hqs hqe
      hqp.symm
      (show LocallyOfFiniteType Nk.hom from inferInstance)
  exact ⟨k, Yk, hYk, pk, a, hpb, hsepk, hftk⟩

end AlgebraicGeometry.Space

end
