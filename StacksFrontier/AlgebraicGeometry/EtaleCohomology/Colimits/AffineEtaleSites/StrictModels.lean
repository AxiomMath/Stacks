module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.CoveringsAndDescent
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.BaseChange
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.CoveringsAndDescent

/-!
# Affine étale models over a limit and strict small models of the stages

`Stacks.EtaleCohomology.exists_affine_etale_model_of_isLimit`: an affine étale object over a limit
of schemes with affine transition morphisms descends to a finite stage. The strict small models
of the small affine étale sites of the `X_i`, with strictly functorial transition functors and
functors to the small affine étale site of the limit, are then assembled into a strict inverse
system of finite sites (Stacks 0A34, Stacks 0EYL).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)

/-- **An affine étale object over a limit of schemes with affine transition morphisms has an
affine étale model at some stage**: it is isomorphic to the base change of an affine scheme étale
over that stage. -/
public lemma exists_affine_etale_model_of_isLimit (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (A : Over c.pt) [IsAffine A.left] [Etale A.hom] :
    ∃ (i : Iᵒᵖ) (Aᵢ : Over (D.obj i)), IsAffine Aᵢ.left ∧ Etale Aᵢ.hom ∧
      Nonempty (A ≅ (Over.pullback (c.π.app i)).obj Aᵢ) := by
  obtain ⟨i, Aᵢ, haff, hfp, ⟨e⟩⟩ :=
    exists_affine_model_of_locallyOfFinitePresentation D c hc A inferInstance
  let modelAffine : IsAffine Aᵢ.left := haff
  let modelLfp : LocallyOfFinitePresentation Aᵢ.hom := hfp
  have : Etale ((Over.pullback (c.π.app i)).obj Aᵢ).hom := etale_of_overIso e
  let E : AsSmall.{max u v} Iᵒᵖ ⥤ Iᵒᵖ := AsSmall.down
  have : E.IsEquivalence :=
    (AsSmall.equiv : Iᵒᵖ ≌ AsSmall.{max u v} Iᵒᵖ).isEquivalence_inverse
  have : IsCofiltered (AsSmall.{max u v} Iᵒᵖ) :=
    IsCofiltered.of_equivalence (AsSmall.equiv : Iᵒᵖ ≌ AsSmall.{max u v} Iᵒᵖ)
  have {j k : AsSmall.{max u v} Iᵒᵖ} (a : j ⟶ k) :
      IsAffineHom ((E ⋙ D).map a) := by
    show IsAffineHom (D.map (E.map a))
    infer_instance
  have : Etale ((Over.pullback ((c.whisker E).π.app (AsSmall.up.obj i))).obj Aᵢ).hom :=
    show Etale ((Over.pullback (c.π.app i)).obj Aᵢ).hom from inferInstance
  obtain ⟨j, hj⟩ := @exists_etale_baseChange_of_compact_source (AsSmall.{max u v} Iᵒᵖ) _ _
    (E ⋙ D) (c.whisker E) ((Functor.Initial.isLimitWhiskerEquiv E c).symm hc)
    (fun {_ _} a => show IsAffineHom (D.map (E.map a)) from inferInstance)
    (AsSmall.up.obj i) Aᵢ inferInstance hfp
    (show Etale ((Over.pullback (c.π.app i)).obj Aᵢ).hom from inferInstance)
  let a : E.obj j.left ⟶ i := E.map j.hom
  let Aⱼ := (Over.pullback (D.map a)).obj Aᵢ
  refine ⟨E.obj j.left, Aⱼ, ?_, hj, ?_⟩
  · show IsAffine (pullback Aᵢ.hom (D.map a))
    exact isAffine_of_isAffineHom (pullback.fst Aᵢ.hom (D.map a))
  · exact ⟨e ≪≫ eqToIso (congrArg (fun f => (Over.pullback f).obj Aᵢ)
      (c.w a).symm) ≪≫ (Over.pullbackComp (c.π.app (E.obj j.left)) (D.map a)).app Aᵢ⟩

/-- An affine étale object over a limit of schemes has an affine étale model. -/
private alias exists_affine_etale_model := exists_affine_etale_model_of_isLimit


section Models


/-- A stage object together with a specified geometric pullback to the limit. -/
private structure AffineEtaleModel where
  index : Iᵒᵖ
  obj : AlgebraicGeometry.SmallAffineEtale B (D.obj index) (hD index)
  limitObj : AlgebraicGeometry.SmallAffineEtale B c.pt hX
  fst : (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).obj limitObj ⟶
    (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj index) (hD index)).obj obj
  isPullback : IsPullback fst
    (limitAffineEtaleStructureMorphism D c B hX limitObj)
    (affineEtaleStructureMorphism D B hD index obj) (c.π.app index)

/-- An object represented at an earlier stage, retaining its specified pullback to the limit. -/
private structure AffineEtaleModelAt (i : Iᵒᵖ) where
  model : AffineEtaleModel D c B hD hX
  arrow : i ⟶ model.index

variable [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

private noncomputable abbrev AffineEtaleModelAt.eval {i : Iᵒᵖ}
    (A : AffineEtaleModelAt D c B hD hX i) :
    AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i) :=
  affineEtaleBaseChangeObject B (hD A.model.index) (hD i) (D.map A.arrow) A.model.obj

private noncomputable instance affineEtaleModelAtCategory (i : Iᵒᵖ) :
    Category (AffineEtaleModelAt D c B hD hX i) :=
  inferInstanceAs (Category (InducedCategory _ (AffineEtaleModelAt.eval D c B hD hX)))

private noncomputable def modelEvaluation (i : Iᵒᵖ) :
    AffineEtaleModelAt D c B hD hX i ⥤ AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i) :=
  inducedFunctor (AffineEtaleModelAt.eval D c B hD hX)

private noncomputable instance modelEvaluationFull (i : Iᵒᵖ) :
    (modelEvaluation D c B hD hX i).Full :=
  inferInstanceAs (inducedFunctor _).Full

private noncomputable instance modelEvaluationFaithful (i : Iᵒᵖ) :
    (modelEvaluation D c B hD hX i).Faithful :=
  inferInstanceAs (inducedFunctor _).Faithful

/-- A morphism of small affine étale objects commutes with the structure maps. -/
private lemma toScheme_map_comp_structureMorphism (B : AlgebraicGeometry.BigEtaleSite.{u})
    {S : Scheme.{u}} {hS : B.Contains S}
    {A A' : AlgebraicGeometry.SmallAffineEtale B S hS} (f : A ⟶ A') :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map f ≫ B.inclusion.map A'.obj.obj.hom =
      B.inclusion.map A.obj.obj.hom :=
  Over.w ((affineEtaleToOver B S hS).map f)

/-- The chosen limit object has a canonical projection to each representative. -/
private noncomputable def modelLimitFst {i : Iᵒᵖ}
    (A : AffineEtaleModelAt D c B hD hX i) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).obj A.model.limitObj ⟶
      (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).obj
        (A.eval D c B hD hX) :=
  pullback.lift A.model.fst
    (limitAffineEtaleStructureMorphism D c B hX A.model.limitObj ≫ c.π.app i)
    (by rw [Category.assoc, c.w A.arrow]; exact A.model.isPullback.w)

omit [Nonempty I] [IsDirected I (· ≤ ·)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- Pasting a pullback square along the canonical pullback of the cospan `f`, `g`. -/
private lemma isPullback_lift_pullback {C : Type*} [Category* C] [HasPullbacks C]
    {A S S' T L : C} (f : A ⟶ S) (g : S' ⟶ S)
    (u : L ⟶ A) (v : L ⟶ T) (π : T ⟶ S') (h : IsPullback u v f (π ≫ g)) :
    IsPullback (pullback.lift u (v ≫ π) (by rw [Category.assoc]; exact h.w)) v
      (pullback.snd f g) π := by
  apply IsPullback.of_right (h₁₂ := pullback.fst _ _) (h₂₂ := g)
  · rw [pullback.lift_fst]
    exact h
  · exact pullback.lift_snd _ _ _
  · exact IsPullback.of_hasPullback _ _

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelLimitFst_isPullback {i : Iᵒᵖ}
    (A : AffineEtaleModelAt D c B hD hX i) :
    IsPullback (modelLimitFst D c B hD hX A)
      (limitAffineEtaleStructureMorphism D c B hX A.model.limitObj)
      (affineEtaleStructureMorphism D B hD i (A.eval D c B hD hX)) (c.π.app i) := by
  dsimp only [affineEtaleStructureMorphism, AffineEtaleModelAt.eval]
  rw [affineEtaleBaseChangeObject_structureMap]
  exact isPullback_lift_pullback _ _ _ _ _ (by rw [c.w]; exact A.model.isPullback)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The chosen limit projection recovers the chosen geometric pullback. -/
private lemma modelLimitFst_fst {i : Iᵒᵖ} (A : AffineEtaleModelAt D c B hD hX i) :
    modelLimitFst D c B hD hX A ≫
        pullback.fst (affineEtaleStructureMorphism D B hD A.model.index A.model.obj)
          (D.map A.arrow) = A.model.fst :=
  pullback.lift_fst _ _ _

/-- A morphism at a stage induces a morphism between the specified limit objects. -/
private noncomputable def modelLimitMap {i : Iᵒᵖ}
    {A A' : AffineEtaleModelAt D c B hD hX i} (f : A ⟶ A') :
    A.model.limitObj ⟶ A'.model.limitObj := by
  let F := AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)
  let L := affineEtaleToOver B c.pt hX
  letI : L.Full := show (affineEtaleToOver B c.pt hX).Full from inferInstance
  let g := (modelLimitFst_isPullback D c B hD hX A').lift
    (modelLimitFst D c B hD hX A ≫ F.map f.hom)
    (limitAffineEtaleStructureMorphism D c B hX A.model.limitObj)
    (by
      rw [Category.assoc]
      rw [toScheme_map_comp_structureMorphism B f.hom]
      exact (modelLimitFst_isPullback D c B hD hX A).w)
  exact L.preimage (Over.homMk g ((modelLimitFst_isPullback D c B hD hX A').lift_snd _ _ _))

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelLimitMap_fst {i : Iᵒᵖ}
    {A A' : AffineEtaleModelAt D c B hD hX i} (f : A ⟶ A') :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).map
        (modelLimitMap D c B hD hX f) ≫ modelLimitFst D c B hD hX A' =
      modelLimitFst D c B hD hX A ≫
        (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).map f.hom := by
  show ((affineEtaleToOver B c.pt hX).map
    (modelLimitMap D c B hD hX f)).left ≫ _ = _
  unfold modelLimitMap
  rw [Functor.map_preimage]
  exact (modelLimitFst_isPullback D c B hD hX A').lift_fst _ _ _

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelLimitMap_ext {i : Iᵒᵖ}
    {A A' : AffineEtaleModelAt D c B hD hX i}
    {f g : A.model.limitObj ⟶ A'.model.limitObj}
    (h : (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).map f ≫
        modelLimitFst D c B hD hX A' =
      (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).map g ≫
        modelLimitFst D c B hD hX A') : f = g := by
  apply (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).map_injective
  apply (modelLimitFst_isPullback D c B hD hX A').hom_ext h
  exact (toScheme_map_comp_structureMorphism B f).trans
    (toScheme_map_comp_structureMorphism B g).symm

private noncomputable def modelToLimit (i : Iᵒᵖ) :
    AffineEtaleModelAt D c B hD hX i ⥤ AlgebraicGeometry.SmallAffineEtale B c.pt hX where
  obj A := A.model.limitObj
  map f := modelLimitMap D c B hD hX f
  map_id A := by
    apply modelLimitMap_ext D c B hD hX (A := A) (A' := A)
    rw [modelLimitMap_fst]
    change _ ≫ (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).map (𝟙 _) = _
    simp
  map_comp f g := by
    apply modelLimitMap_ext D c B hD hX
    rw [modelLimitMap_fst]
    simp only [Functor.map_comp, Category.assoc, modelLimitMap_fst]
    rw [← Category.assoc, modelLimitMap_fst]
    rfl


/-- Restriction changes only the arrow to the stage of definition. -/
private def modelRestrictObj {i j : Iᵒᵖ} (a : i ⟶ j)
    (A : AffineEtaleModelAt D c B hD hX j) : AffineEtaleModelAt D c B hD hX i :=
  ⟨A.model, a ≫ A.arrow⟩

omit [Nonempty I] [IsDirected I (· ≤ ·)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- The pullback condition along a composite transition morphism, split at the middle stage. -/
private lemma pullback_fst_comp_map {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    {M : Scheme.{max u v}} (g : M ⟶ D.obj k) :
    pullback.fst g (D.map (a ≫ b)) ≫ g =
      (pullback.snd g (D.map (a ≫ b)) ≫ D.map a) ≫ D.map b := by
  rw [Category.assoc, ← D.map_comp]
  exact pullback.condition

private noncomputable def modelTransitionFst {i j : Iᵒᵖ} (a : i ⟶ j)
    (A : AffineEtaleModelAt D c B hD hX j) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).obj
        ((modelRestrictObj D c B hD hX a A).eval D c B hD hX) ⟶
      (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj j) (hD j)).obj
        (A.eval D c B hD hX) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ D.map a)
    (pullback_fst_comp_map D a A.arrow
      (affineEtaleStructureMorphism D B hD A.model.index A.model.obj))

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition projection is compatible with the chosen geometric pullbacks. -/
private lemma modelTransitionFst_fst {i j : Iᵒᵖ} (a : i ⟶ j)
    (A : AffineEtaleModelAt D c B hD hX j) :
    modelTransitionFst D c B hD hX a A ≫
        pullback.fst (affineEtaleStructureMorphism D B hD A.model.index A.model.obj)
          (D.map A.arrow) =
      pullback.fst (affineEtaleStructureMorphism D B hD A.model.index A.model.obj)
        (D.map (a ≫ A.arrow)) :=
  pullback.lift_fst _ _ _

omit [Nonempty I] [IsDirected I (· ≤ ·)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- The canonical pullback of `g` along a composite transition map, cut out by the projection
through the middle stage, is a pullback square. -/
private lemma pullback_lift_isPullback_comp_map {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    {M : Scheme.{max u v}} (g : M ⟶ D.obj k) :
    IsPullback
      (pullback.lift (pullback.fst g (D.map (a ≫ b))) (pullback.snd g (D.map (a ≫ b)) ≫ D.map a)
        (pullback_fst_comp_map D a b g))
      (pullback.snd g (D.map (a ≫ b))) (pullback.snd g (D.map b)) (D.map a) :=
  isPullback_lift_pullback _ _ _ _ _ (by rw [← D.map_comp]; exact .of_hasPullback _ _)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelTransitionFst_isPullback {i j : Iᵒᵖ} (a : i ⟶ j)
    (A : AffineEtaleModelAt D c B hD hX j) :
    IsPullback (modelTransitionFst D c B hD hX a A)
      (affineEtaleStructureMorphism D B hD i
        ((modelRestrictObj D c B hD hX a A).eval D c B hD hX))
      (affineEtaleStructureMorphism D B hD j (A.eval D c B hD hX)) (D.map a) := by
  dsimp only [affineEtaleStructureMorphism, AffineEtaleModelAt.eval]
  rw [affineEtaleBaseChangeObject_structureMap, affineEtaleBaseChangeObject_structureMap]
  exact pullback_lift_isPullback_comp_map D a A.arrow _

private noncomputable def modelRestrictMap {i j : Iᵒᵖ} (a : i ⟶ j)
    {A A' : AffineEtaleModelAt D c B hD hX j} (f : A ⟶ A') :
    modelRestrictObj D c B hD hX a A ⟶ modelRestrictObj D c B hD hX a A' := by
  let F := AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj j) (hD j)
  let L := affineEtaleToOver B (D.obj i) (hD i)
  letI : L.Full := show (affineEtaleToOver B (D.obj i) (hD i)).Full from inferInstance
  let g := (modelTransitionFst_isPullback D c B hD hX a A').lift
    (modelTransitionFst D c B hD hX a A ≫ F.map f.hom)
    (affineEtaleStructureMorphism D B hD i
      ((modelRestrictObj D c B hD hX a A).eval D c B hD hX))
    (by
      rw [Category.assoc]
      rw [toScheme_map_comp_structureMorphism B f.hom]
      exact (modelTransitionFst_isPullback D c B hD hX a A).w)
  exact InducedCategory.homMk (L.preimage (Over.homMk g
    ((modelTransitionFst_isPullback D c B hD hX a A').lift_snd _ _ _)))

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelRestrictMap_fst {i j : Iᵒᵖ} (a : i ⟶ j)
    {A A' : AffineEtaleModelAt D c B hD hX j} (f : A ⟶ A') :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).map
        (modelRestrictMap D c B hD hX a f).hom ≫
          modelTransitionFst D c B hD hX a A' =
      modelTransitionFst D c B hD hX a A ≫
        (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj j) (hD j)).map f.hom := by
  show ((affineEtaleToOver B (D.obj i) (hD i)).map
    (modelRestrictMap D c B hD hX a f).hom).left ≫ _ = _
  unfold modelRestrictMap
  dsimp only [InducedCategory.homMk]
  rw [Functor.map_preimage]
  exact (modelTransitionFst_isPullback D c B hD hX a A').lift_fst _ _ _

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelRestrictMap_ext {i j : Iᵒᵖ} (a : i ⟶ j)
    {A A' : AffineEtaleModelAt D c B hD hX j}
    {f g : modelRestrictObj D c B hD hX a A ⟶ modelRestrictObj D c B hD hX a A'}
    (h : (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).map f.hom ≫
        modelTransitionFst D c B hD hX a A' =
      (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).map g.hom ≫
        modelTransitionFst D c B hD hX a A') : f = g := by
  apply InducedCategory.hom_ext
  apply (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).map_injective
  apply (modelTransitionFst_isPullback D c B hD hX a A').hom_ext h
  exact (toScheme_map_comp_structureMorphism B f.hom).trans
    (toScheme_map_comp_structureMorphism B g.hom).symm

private noncomputable def modelRestrict {i j : Iᵒᵖ} (a : i ⟶ j) :
    AffineEtaleModelAt D c B hD hX j ⥤ AffineEtaleModelAt D c B hD hX i where
  obj := modelRestrictObj D c B hD hX a
  map := modelRestrictMap D c B hD hX a
  map_id A := by
    apply modelRestrictMap_ext D c B hD hX a
    rw [modelRestrictMap_fst]
    change _ ≫ (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj j) (hD j)).map (𝟙 _) =
      (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).map (𝟙 _) ≫ _
    simp
  map_comp f g := by
    apply modelRestrictMap_ext D c B hD hX a
    rw [modelRestrictMap_fst]
    change _ ≫ (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj j) (hD j)).map
          (f.hom ≫ g.hom) =
      (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).map
        ((modelRestrictMap D c B hD hX a f).hom ≫ (modelRestrictMap D c B hD hX a g).hom) ≫ _
    simp only [Functor.map_comp, Category.assoc, modelRestrictMap_fst]
    simp only [← Category.assoc, modelRestrictMap_fst]

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelLimitFst_transition {i j : Iᵒᵖ} (a : i ⟶ j)
    (A : AffineEtaleModelAt D c B hD hX j) :
    modelLimitFst D c B hD hX ((modelRestrict D c B hD hX a).obj A) ≫
        modelTransitionFst D c B hD hX a A = modelLimitFst D c B hD hX A := by
  refine (affineEtaleBaseChangeObject_isPullback B (hD A.model.index) (hD j)
    (D.map A.arrow) A.model.obj).hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg
      (fun z => modelLimitFst D c B hD hX ((modelRestrict D c B hD hX a).obj A) ≫ z)
      (modelTransitionFst_fst D c B hD hX a A)).trans ?_
    exact (modelLimitFst_fst D c B hD hX ((modelRestrict D c B hD hX a).obj A)).trans
      (modelLimitFst_fst D c B hD hX A).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg
      (fun z => modelLimitFst D c B hD hX ((modelRestrict D c B hD hX a).obj A) ≫ z)
      (modelTransitionFst_isPullback D c B hD hX a A).w).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ D.map a)
      (modelLimitFst_isPullback D c B hD hX
        ((modelRestrict D c B hD hX a).obj A)).w).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg
      (fun z => limitAffineEtaleStructureMorphism D c B hX A.model.limitObj ≫ z)
      (c.w a)).trans ?_
    exact (modelLimitFst_isPullback D c B hD hX A).w.symm

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelRestrict_toLimit {i j : Iᵒᵖ} (a : i ⟶ j) :
    modelRestrict D c B hD hX a ⋙ modelToLimit D c B hD hX i =
      modelToLimit D c B hD hX j := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro A; rfl
  intro A A' f
  refine heq_of_eq ?_
  dsimp only [Functor.comp_obj, Functor.comp_map, modelToLimit, modelRestrict]
  apply modelLimitMap_ext D c B hD hX (A := A) (A' := A')
  refine (congrArg (fun z => (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).map
      (modelLimitMap D c B hD hX (modelRestrictMap D c B hD hX a f)) ≫ z)
    (modelLimitFst_transition D c B hD hX a A').symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ modelTransitionFst D c B hD hX a A')
    (modelLimitMap_fst D c B hD hX (modelRestrictMap D c B hD hX a f))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg
    (fun z => modelLimitFst D c B hD hX (modelRestrictObj D c B hD hX a A) ≫ z)
    (modelRestrictMap_fst D c B hD hX a f)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫
      (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj j) (hD j)).map f.hom)
    (modelLimitFst_transition D c B hD hX a A)).trans ?_
  exact (modelLimitMap_fst D c B hD hX f).symm


omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelTransitionFst_id (i : Iᵒᵖ)
    (A : AffineEtaleModelAt D c B hD hX i) :
    modelTransitionFst D c B hD hX (𝟙 i) A = 𝟙 _ := by
  refine (affineEtaleBaseChangeObject_isPullback B (hD A.model.index) (hD i)
    (D.map A.arrow) A.model.obj).hom_ext ?_ ?_
  · exact (modelTransitionFst_fst D c B hD hX (𝟙 i) A).trans (Category.id_comp _).symm
  · refine (modelTransitionFst_isPullback D c B hD hX (𝟙 i) A).w.trans ?_
    refine (congrArg (fun z => affineEtaleStructureMorphism D B hD i
      ((modelRestrictObj D c B hD hX (𝟙 i) A).eval D c B hD hX) ≫ z) (D.map_id i)).trans ?_
    exact (Category.comp_id _).trans (Category.id_comp _).symm

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelTransitionFst_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    (A : AffineEtaleModelAt D c B hD hX k) :
    modelTransitionFst D c B hD hX (a ≫ b) A =
      modelTransitionFst D c B hD hX a ((modelRestrict D c B hD hX b).obj A) ≫
        modelTransitionFst D c B hD hX b A := by
  refine (affineEtaleBaseChangeObject_isPullback B (hD A.model.index) (hD k)
    (D.map A.arrow) A.model.obj).hom_ext ?_ ?_
  · refine (modelTransitionFst_fst D c B hD hX (a ≫ b) A).trans (Eq.symm ?_)
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => modelTransitionFst D c B hD hX a
        ((modelRestrict D c B hD hX b).obj A) ≫ z)
      (modelTransitionFst_fst D c B hD hX b A)).trans ?_
    exact modelTransitionFst_fst D c B hD hX a ((modelRestrict D c B hD hX b).obj A)
  · refine (modelTransitionFst_isPullback D c B hD hX (a ≫ b) A).w.trans (Eq.symm ?_)
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => modelTransitionFst D c B hD hX a
        ((modelRestrict D c B hD hX b).obj A) ≫ z)
      (modelTransitionFst_isPullback D c B hD hX b A).w).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ D.map b)
      (modelTransitionFst_isPullback D c B hD hX a
        ((modelRestrict D c B hD hX b).obj A)).w).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (fun z => affineEtaleStructureMorphism D B hD i
      ((modelRestrictObj D c B hD hX a ((modelRestrict D c B hD hX b).obj A)).eval
        D c B hD hX) ≫ z) (D.map_comp a b).symm

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelRestrict_id (i : Iᵒᵖ) :
    modelRestrict D c B hD hX (𝟙 i) = 𝟭 _ := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro A; rfl
  intro A A' f
  refine heq_of_eq ?_
  dsimp only [modelRestrict, Functor.id_map]
  apply modelRestrictMap_ext D c B hD hX (𝟙 i)
  rw [modelRestrictMap_fst, modelTransitionFst_id, modelTransitionFst_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma modelRestrict_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    modelRestrict D c B hD hX (a ≫ b) =
      modelRestrict D c B hD hX b ⋙ modelRestrict D c B hD hX a := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro A; rfl
  intro A A' f
  refine heq_of_eq ?_
  dsimp only [modelRestrict, Functor.comp_map]
  apply modelRestrictMap_ext D c B hD hX (a ≫ b)
  rw [modelRestrictMap_fst D c B hD hX (a ≫ b) f,
    modelTransitionFst_comp, modelTransitionFst_comp]
  dsimp only [modelRestrict]
  refine Eq.symm ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ modelTransitionFst D c B hD hX b A')
    (modelRestrictMap_fst D c B hD hX a (modelRestrictMap D c B hD hX b f))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => modelTransitionFst D c B hD hX a
      (modelRestrictObj D c B hD hX b A) ≫ z)
    (modelRestrictMap_fst D c B hD hX b f)).trans ?_
  exact (Category.assoc _ _ _).symm


/-- Every affine étale object gives a representative with a chosen pullback to the limit. -/
private noncomputable def modelAtSelf (hc : IsLimit c) (i : Iᵒᵖ)
    (A : AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i)) :
    AffineEtaleModelAt D c B hD hX i := by
  letI := limitProjection_affine hc i
  exact {
    model := {
      index := i
      obj := A
      limitObj := affineEtaleBaseChangeObject B (hD i) hX (c.π.app i) A
      fst := pullback.fst _ _
      isPullback := affineEtaleBaseChangeObject_isPullback B (hD i) hX (c.π.app i) A }
    arrow := 𝟙 i }

private lemma modelEvaluationEssSurj (hc : IsLimit c) (i : Iᵒᵖ) :
    (modelEvaluation D c B hD hX i).EssSurj where
  mem_essImage A := by
    refine ⟨modelAtSelf D c B hD hX hc i A, ⟨?_⟩⟩
    let F := affineEtaleToOver B (D.obj i) (hD i)
    let : F.Full := show (affineEtaleToOver B (D.obj i) (hD i)).Full from inferInstance
    have : IsIso (D.map (𝟙 i)) := by
      rw [D.map_id]
      exact inferInstanceAs (IsIso (𝟙 (D.obj i)))
    let φ := asIso (pullback.fst (affineEtaleStructureMorphism D B hD i A) (D.map (𝟙 i)))
    let e : F.obj ((modelEvaluation D c B hD hX i).obj
        (modelAtSelf D c B hD hX hc i A)) ≅ F.obj A :=
      Over.isoMk φ (by
          dsimp only [φ, asIso_hom, F, affineEtaleToOver, Functor.comp_obj, Over.post_obj]
          show pullback.fst _ _ ≫ affineEtaleStructureMorphism D B hD i A =
            affineEtaleStructureMorphism D B hD i
              ((modelAtSelf D c B hD hX hc i A).eval D c B hD hX)
          dsimp only [affineEtaleStructureMorphism, AffineEtaleModelAt.eval]
          rw [affineEtaleBaseChangeObject_structureMap]
          show pullback.fst _ _ ≫ affineEtaleStructureMorphism D B hD i A =
            pullback.snd (affineEtaleStructureMorphism D B hD i A) (D.map (𝟙 i))
          exact (pullback.condition (f := affineEtaleStructureMorphism D B hD i A)
            (g := D.map (𝟙 i))).trans (by
              rw [D.map_id]
              exact Category.comp_id _))
    exact F.preimageIso e

private noncomputable def modelLevelEquiv (hc : IsLimit c) (i : Iᵒᵖ) :
    AffineEtaleModelAt D c B hD hX i ≌ AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i) := by
  letI : (modelEvaluation D c B hD hX i).EssSurj :=
    modelEvaluationEssSurj D c B hD hX hc i
  letI : (modelEvaluation D c B hD hX i).IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  exact (modelEvaluation D c B hD hX i).asEquivalence


/-- Raising only the morphism universe makes the representative categories small. -/
private noncomputable abbrev SmallModelAt (i : Iᵒᵖ) :=
  AsSmall.{max u v + 1} (AffineEtaleModelAt D c B hD hX i)

private noncomputable def smallModelRestrict {i j : Iᵒᵖ} (a : i ⟶ j) :
    SmallModelAt D c B hD hX j ⥤ SmallModelAt D c B hD hX i :=
  AsSmall.down ⋙ modelRestrict D c B hD hX a ⋙ AsSmall.up

private noncomputable def smallModelToLimit (i : Iᵒᵖ) :
    SmallModelAt D c B hD hX i ⥤ AlgebraicGeometry.SmallAffineEtale B c.pt hX :=
  AsSmall.down ⋙ modelToLimit D c B hD hX i

private noncomputable def smallModelEquiv (hc : IsLimit c) (i : Iᵒᵖ) :
    SmallModelAt D c B hD hX i ≌ AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i) :=
  AsSmall.equiv.symm.trans (modelLevelEquiv D c B hD hX hc i)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma smallModelRestrict_id (i : Iᵒᵖ) :
    smallModelRestrict D c B hD hX (𝟙 i) = 𝟭 _ := by
  unfold smallModelRestrict
  rw [modelRestrict_id]
  rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma smallModelRestrict_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    smallModelRestrict D c B hD hX (a ≫ b) =
      smallModelRestrict D c B hD hX b ⋙ smallModelRestrict D c B hD hX a := by
  show AsSmall.down ⋙ modelRestrict D c B hD hX (a ≫ b) ⋙ AsSmall.up =
    AsSmall.down ⋙ (modelRestrict D c B hD hX b ⋙ modelRestrict D c B hD hX a) ⋙ AsSmall.up
  rw [modelRestrict_comp]

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma smallModelRestrict_toLimit {i j : Iᵒᵖ} (a : i ⟶ j) :
    smallModelRestrict D c B hD hX a ⋙ smallModelToLimit D c B hD hX i =
      smallModelToLimit D c B hD hX j := by
  show AsSmall.down ⋙ (modelRestrict D c B hD hX a ⋙ modelToLimit D c B hD hX i) = _
  rw [modelRestrict_toLimit]
  rfl

private noncomputable def smallModelTransitionFst (hc : IsLimit c) {i j : Iᵒᵖ} (a : i ⟶ j) :
    smallModelRestrict D c B hD hX a ⋙ (smallModelEquiv D c B hD hX hc i).functor ⋙
      AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i) ⟶
    (smallModelEquiv D c B hD hX hc j).functor ⋙
      AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj j) (hD j) where
  app A := modelTransitionFst D c B hD hX a (ULift.down A)
  naturality _ _ f := modelRestrictMap_fst D c B hD hX a (ULift.down f)

private noncomputable def smallModelLimitFst (hc : IsLimit c) (i : Iᵒᵖ) :
    smallModelToLimit D c B hD hX i ⋙ AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX ⟶
      (smallModelEquiv D c B hD hX hc i).functor ⋙
        AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i) where
  app A := modelLimitFst D c B hD hX (ULift.down A)
  naturality _ _ f := modelLimitMap_fst D c B hD hX (ULift.down f)


/-- The stage topology transported to the category of representatives. -/
private noncomputable def smallModelTopology (hc : IsLimit c) (i : Iᵒᵖ) :
    GrothendieckTopology (SmallModelAt D c B hD hX i) :=
  (smallModelEquiv D c B hD hX hc i).functor.inducedTopology
    (AlgebraicGeometry.SmallAffineEtale.topology B (D.obj i) (hD i))

private lemma smallModelTopology_cover (hc : IsLimit c) (i : Iᵒᵖ)
    (A : SmallModelAt D c B hD hX i) (R : Presieve A) :
    R ∈ (smallModelTopology D c B hD hX hc i).toPrecoverage A ↔
      R.map (smallModelEquiv D c B hD hX hc i).functor ∈
        (AlgebraicGeometry.SmallAffineEtale.topology B (D.obj i) (hD i)).toPrecoverage
          ((smallModelEquiv D c B hD hX hc i).functor.obj A) := by
  simp only [smallModelTopology, GrothendieckTopology.mem_toPrecoverage_iff,
    Functor.mem_inducedTopology_iff_of_isCoverDense, Sieve.generate_map_eq_functorPushforward]

private lemma smallModelTopology_finite (hc : IsLimit c) (i : Iᵒᵖ)
    {A : SmallModelAt D c B hD hX i} (R : Sieve A)
    (hR : R ∈ smallModelTopology D c B hD hX hc i A) :
    ∃ S : Presieve A, S ≤ R.arrows ∧
      S ∈ (smallModelTopology D c B hD hX hc i).toPrecoverage A ∧
      S ∈ Precoverage.finite (SmallModelAt D c B hD hX i) A := by
  let e := (smallModelEquiv D c B hD hX hc i).symm
  obtain ⟨ι, hι, V, f, hle, hcov⟩ := finite_refinement_equiv e
    (AlgebraicGeometry.SmallAffineEtale.topology B (D.obj i) (hD i)) hR
    (fun h => finite_refinement_smallAffineEtale B (D.obj i) (hD i) h)
  let := hι
  exact ⟨Presieve.ofArrows V f, (Sieve.generate_le_iff _ _).mp hle,
    hcov, Precoverage.ofArrows_mem_finite V f⟩

private lemma smallModel_hasPullbacks (hc : IsLimit c) (i : Iᵒᵖ) :
    HasPullbacks (SmallModelAt D c B hD hX i) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (smallModelEquiv D c B hD hX hc i).functor


private noncomputable abbrev smallModelToOver (hc : IsLimit c) (i : Iᵒᵖ) :
    SmallModelAt D c B hD hX i ⥤ Over (D.obj i) :=
  (smallModelEquiv D c B hD hX hc i).functor ⋙ affineEtaleToOver B (D.obj i) (hD i)

private noncomputable def smallModelRestrictIso (hc : IsLimit c) {i j : Iᵒᵖ} (a : i ⟶ j) :
    smallModelRestrict D c B hD hX a ⋙ smallModelToOver D c B hD hX hc i ≅
      smallModelToOver D c B hD hX hc j ⋙ Over.pullback (D.map a) :=
  overPullbackComparison (D.map a) (smallModelToOver D c B hD hX hc j)
    (smallModelRestrict D c B hD hX a ⋙ smallModelToOver D c B hD hX hc i)
    (smallModelTransitionFst D c B hD hX hc a)
    (fun A => modelTransitionFst_isPullback D c B hD hX a (ULift.down A))

private lemma smallModelRestrict_preservesPullbacks (hc : IsLimit c) {i j : Iᵒᵖ}
    (a : i ⟶ j) : PreservesLimitsOfShape WalkingCospan (smallModelRestrict D c B hD hX a) := by
  let G := smallModelToOver D c B hD hX hc i
  let F := smallModelToOver D c B hD hX hc j
  have : PreservesLimitsOfShape WalkingCospan (F ⋙ Over.forget (D.obj j)) := by
    show PreservesLimitsOfShape WalkingCospan
      ((smallModelEquiv D c B hD hX hc j).functor ⋙
        AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj j) (hD j))
    infer_instance
  have : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_of_reflects_of_preserves F (Over.forget (D.obj j))
  have : PreservesLimitsOfShape WalkingCospan
      (smallModelRestrict D c B hD hX a ⋙ G) :=
    preservesLimitsOfShape_of_natIso (smallModelRestrictIso D c B hD hX hc a).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves (smallModelRestrict D c B hD hX a) G




private instance smallModelEquiv_dense (hc : IsLimit c) (i : Iᵒᵖ) :
    (smallModelEquiv D c B hD hX hc i).functor.IsDenseSubsite
      (smallModelTopology D c B hD hX hc i)
      (AlgebraicGeometry.SmallAffineEtale.topology B (D.obj i) (hD i)) := by
  dsimp only [smallModelTopology]
  infer_instance

private noncomputable abbrev smallModelToEtale (hc : IsLimit c) (i : Iᵒᵖ) :=
  (smallModelEquiv D c B hD hX hc i).functor ⋙
    AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj i) (hD i)

private lemma smallModelToEtale_continuous (hc : IsLimit c) (i : Iᵒᵖ) :
    (smallModelToEtale D c B hD hX hc i).IsContinuous
      (smallModelTopology D c B hD hX hc i)
      (AlgebraicGeometry.SmallEtale.topology B (D.obj i) (hD i)) := by
  let h := AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous B (D.obj i) (hD i)
  have := h.2
  exact Functor.isContinuous_comp _ _ _
    (AlgebraicGeometry.SmallAffineEtale.topology B (D.obj i) (hD i)) _

private lemma smallModelToEtale_sheafEquiv (hc : IsLimit c) (i : Iᵒᵖ) :
    letI := smallModelToEtale_continuous D c B hD hX hc i
    ((smallModelToEtale D c B hD hX hc i).sheafPushforwardContinuous
      (Type (max u v + 1)) (smallModelTopology D c B hD hX hc i)
      (AlgebraicGeometry.SmallEtale.topology B (D.obj i) (hD i))).IsEquivalence := by
  let h := AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous B (D.obj i) (hD i)
  have := h.2
  exact Functor.isEquivalence_of_iso (Functor.sheafPushforwardContinuousComp
    (smallModelEquiv D c B hD hX hc i).functor
    (AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj i) (hD i))
    (Type (max u v + 1)) (smallModelTopology D c B hD hX hc i)
    (AlgebraicGeometry.SmallAffineEtale.topology B (D.obj i) (hD i))
    (AlgebraicGeometry.SmallEtale.topology B (D.obj i) (hD i)))

private noncomputable def smallModelRestrictEtaleIso (hc : IsLimit c)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    smallModelRestrict D c B hD hX a ⋙ smallModelToEtale D c B hD hX hc i ≅
      smallModelToEtale D c B hD hX hc j ⋙
        AlgebraicGeometry.smallEtaleBaseChange B
          (ObjectProperty.homMk (X := B.obj (D.obj i) (hD i))
            (Y := B.obj (D.obj j) (hD j)) (D.map a)) := by
  apply Functor.fullyFaithfulCancelRight (smallEtaleToOver B (D.obj i) (hD i))
  exact smallModelRestrictIso D c B hD hX hc a ≪≫
    (Functor.isoWhiskerLeft (smallModelToEtale D c B hD hX hc j)
      (smallEtaleBaseChangeToOverIso B
        (ObjectProperty.homMk (X := B.obj (D.obj i) (hD i))
          (Y := B.obj (D.obj j) (hD j)) (D.map a)))).symm

private lemma smallModelRestrict_morphismOfSites (hc : IsLimit c)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallModelRestrict D c B hD hX a).IsMorphismOfSites
      (smallModelTopology D c B hD hX hc j)
      (smallModelTopology D c B hD hX hc i) := by
  have := smallModelToEtale_continuous D c B hD hX hc i
  have := smallModelToEtale_continuous D c B hD hX hc j
  have := smallModelToEtale_sheafEquiv D c B hD hX hc i
  have := smallModelToEtale_sheafEquiv D c B hD hX hc j
  exact morphismOfSites_of_sheaf_comparison _ _ _ _ _ _ _ _
    (smallModelRestrictEtaleIso D c B hD hX hc a)
    (AlgebraicGeometry.smallEtaleBaseChange_isMorphismOfSites B _)


private noncomputable def smallModelToLimitEtaleIso (hc : IsLimit c) (i : Iᵒᵖ) :
    smallModelToLimit D c B hD hX i ⋙ AlgebraicGeometry.SmallAffineEtale.inclusion B c.pt hX ≅
      smallModelToEtale D c B hD hX hc i ⋙
        AlgebraicGeometry.smallEtaleBaseChange B
          (ObjectProperty.homMk (X := B.obj c.pt hX) (Y := B.obj (D.obj i) (hD i))
            (c.π.app i)) := by
  apply Functor.fullyFaithfulCancelRight (smallEtaleToOver B c.pt hX)
  refine overPullbackComparison (c.π.app i) (smallModelToOver D c B hD hX hc i)
    (smallModelToLimit D c B hD hX i ⋙ affineEtaleToOver B c.pt hX)
    (smallModelLimitFst D c B hD hX hc i)
    (fun A => modelLimitFst_isPullback D c B hD hX (ULift.down A)) ≪≫ ?_
  exact (Functor.isoWhiskerLeft (smallModelToEtale D c B hD hX hc i)
    (smallEtaleBaseChangeToOverIso B
      (ObjectProperty.homMk (X := B.obj c.pt hX) (Y := B.obj (D.obj i) (hD i)) (c.π.app i)))).symm

private lemma smallModelToLimit_continuous (hc : IsLimit c) (i : Iᵒᵖ) :
    (smallModelToLimit D c B hD hX i).IsContinuous
      (smallModelTopology D c B hD hX hc i)
      (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX) := by
  have := smallModelToEtale_continuous D c B hD hX hc i
  have := (AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous B c.pt hX).2
  let g := ObjectProperty.homMk (X := B.obj c.pt hX) (Y := B.obj (D.obj i) (hD i)) (c.π.app i)
  have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B g
  exact continuous_of_sheaf_comparison
    (smallModelTopology D c B hD hX hc i)
    (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX)
    (AlgebraicGeometry.SmallEtale.topology B (D.obj i) (hD i))
    (AlgebraicGeometry.SmallEtale.topology B c.pt hX)
    (smallModelToLimit D c B hD hX i) (smallModelToEtale D c B hD hX hc i)
    (AlgebraicGeometry.SmallAffineEtale.inclusion B c.pt hX)
    (AlgebraicGeometry.smallEtaleBaseChange B g)
    (smallModelToLimitEtaleIso D c B hD hX hc i)

/-- Quasi-compact objects locally of finite type over a bounded scheme remain bounded. -/
private lemma modelSource_mem (B : AlgebraicGeometry.BigEtaleSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (A : Over S) [CompactSpace A.left]
    [LocallyOfFiniteType A.hom] : B.Contains A.left :=
  (Scheme.size_le_of_locallyOfFiniteType A.hom).trans_lt hS

/-- An affine étale scheme over a bounded base defines an object of its affine étale site. -/
private noncomputable def boundedAffineEtaleObject (B : AlgebraicGeometry.BigEtaleSite.{u})
    {S : Scheme.{u}} (hS : B.Contains S) (A : Over S) [IsAffine A.left] [Etale A.hom] :
    AlgebraicGeometry.SmallAffineEtale B S hS :=
  ⟨⟨Over.mk (ObjectProperty.homMk (P := AlgebraicGeometry.schemeSizeBelow B.cutoff)
    (X := B.obj A.left (modelSource_mem B hS A)) (Y := B.obj S hS) A.hom),
    show Etale A.hom from inferInstance⟩, show IsAffine A.left from inferInstance⟩

/-- An isomorphism in a slice supplies the chosen geometric pullback square. -/
private lemma isPullback_of_overIso {C : Type*} [Category* C] [HasPullbacks C]
    {S T : C} (f : T ⟶ S) (A : Over S) (Z : Over T)
    (e : Z ≅ (Over.pullback f).obj A) :
    IsPullback (e.hom.left ≫ pullback.fst A.hom f) Z.hom A.hom f := by
  apply IsPullback.of_iso_pullback
    (i := (Over.forget T).mapIso e)
  · refine ⟨?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun k => k ≫ f) (Over.w e.hom)
  · rfl
  · exact Over.w e.hom

private lemma smallModel_obj_descends (hc : IsLimit c)
    (Z : AlgebraicGeometry.SmallAffineEtale B c.pt hX) :
    ∃ (i : Iᵒᵖ) (A : SmallModelAt D c B hD hX i),
      (smallModelToLimit D c B hD hX i).obj A = Z := by
  let Z' := (affineEtaleToOver B c.pt hX).obj Z
  have : IsAffine Z'.left := Z.property
  have : Etale Z'.hom := Z.obj.property
  obtain ⟨i, A, haff, het, ⟨e⟩⟩ :=
    exists_affine_etale_model D c hc Z'
  let := haff
  let := het
  let A' := boundedAffineEtaleObject B (hD i) A
  let m : AffineEtaleModel D c B hD hX := {
    index := i
    obj := A'
    limitObj := Z
    fst := e.hom.left ≫ pullback.fst A.hom (c.π.app i)
    isPullback := isPullback_of_overIso (c.π.app i) A Z' e }
  exact ⟨i, ULift.up ⟨m, 𝟙 i⟩, rfl⟩



private lemma finite_presieve_map {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X : C} {R : Presieve X}
    (hR : R ∈ Precoverage.finite C X) : R.map F ∈ Precoverage.finite D (F.obj X) := by
  have : Finite R.preZeroHypercover.I₀ := Set.Finite.to_subtype hR
  rw [← R.presieve₀_preZeroHypercover, PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
  exact Precoverage.ofArrows_mem_finite _ _

private lemma smallModelRestrict_coverPreserving (hc : IsLimit c)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    ((smallModelTopology D c B hD hX hc j).toPrecoverage ⊓
      Precoverage.finite (SmallModelAt D c B hD hX j)) ≤
    ((smallModelTopology D c B hD hX hc i).toPrecoverage ⊓
      Precoverage.finite (SmallModelAt D c B hD hX i)).comap
        (smallModelRestrict D c B hD hX a) := by
  have := (smallModelRestrict_morphismOfSites D c B hD hX hc a).isContinuous
  intro X R hR
  refine ⟨?_, finite_presieve_map _ hR.2⟩
  rw [GrothendieckTopology.mem_toPrecoverage_iff, Sieve.generate_map_eq_functorPushforward]
  exact (CoverPreserving.of_isContinuous _ _ _).cover_preserve hR.1

private noncomputable def smallModelSystem (hc : IsLimit c) :
    InverseSystemOfFiniteSites.{v, v, max v (max u v + 1)} where
  I := Iᵒᵖ
  C := SmallModelAt D c B hD hX
  J := smallModelTopology D c B hD hX hc
  finiteCoverings := smallModelTopology_finite D c B hD hX hc
  u := smallModelRestrict D c B hD hX
  isMorphismOfSites := smallModelRestrict_morphismOfSites D c B hD hX hc
  hasPullbacks i := by
    let := smallModel_hasPullbacks D c B hD hX hc i
    infer_instance
  coverPreserving := smallModelRestrict_coverPreserving D c B hD hX hc
  preservesPullbacks a _ _ _ := by
    let := smallModelRestrict_preservesPullbacks D c B hD hX hc a
    infer_instance
  comp := smallModelRestrict_comp D c B hD hX
  id_map := smallModelRestrict_id D c B hD hX

end Models

end Stacks.EtaleCohomology

end
