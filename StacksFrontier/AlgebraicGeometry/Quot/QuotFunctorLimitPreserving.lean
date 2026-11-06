module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitRelative
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFibreRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.AffineCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SurjectiveCriterion

/-!
# `Quot_{F/X/B} ⟶ B` is locally of finite presentation when `F` is (Stacks 09TU, second clause)

Let `f : X ⟶ B` be a morphism of finite presentation of algebraic spaces over `S` and `F` a
quasi-coherent `𝒪_X`-module of finite presentation. Let `T = lim T_j` be a cofiltered limit of
affine schemes, and let `F_T ⟶ Q` be a quotient classified by `Quot_{F/X/B}` over `T` whose
morphism `T ⟶ B` comes from a stage `T_i`. Then the quotient comes from a quotient over a later
stage `T_j`, lying over `T_j ⟶ T_i ⟶ B`:

* the object `(T, Q)` of `Coh_{X/B}` comes from an object `(T_j, Q_j)` over a stage, by the
  relative descent of objects of `Coh_{X/B}`
  (`AlgebraicGeometry.Space.CoherentSituation.exists_stage_module_of_stage`, the proof of Stacks
  08KD relative to `B`);
* the surjection `F_T ⟶ Q` comes from a map `F_{T_k} ⟶ Q_k` at a later stage, by the fullness
  clause of Stacks 07V7 for the system of base changes `X_{T_k}`, both modules being of finite
  presentation;
* that map is surjective at a yet later stage, because the locus of the test schemes over `T_k`
  on which it is surjective is an open subspace of `T_k` (Stacks 09TP) containing the image of
  `T`, and an open immersion is locally of finite presentation;
* the kernel of the map at that stage is the required quotient.

By Stacks 0CM6 this says that a model of the Quot presheaf which is an algebraic space has its
morphism to `B` locally of finite presentation: this is the second clause of Stacks 09TU, given
the first.

## Main results

* `AlgebraicGeometry.Space.exists_stage_lift_of_relativelyLimitPreserving`: a section over a
  cofiltered limit of affine schemes lifting a section over a stage through a relatively limit
  preserving morphism comes from a later stage.
* `AlgebraicGeometry.Space.exists_stage_mem_of_isOpenImmersion`: a morphism from a stage into a
  scheme which lands in an open subfunctor after restriction to the limit does so at a later stage.
* `AlgebraicGeometry.Space.QuotSituation.exists_stage_quotientPullback_eq`: the descent of
  quotients described above.
* `AlgebraicGeometry.Space.QuotSitePresheafModel.isLocallyOfFinitePresentation_toBase`: **the
  second clause of Stacks 09TU, given the first** — the morphism to `B` of a model of the Quot
  presheaf which is an algebraic space is locally of finite presentation when `F` is of finite
  presentation.

## References

* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 09TP](https://stacks.math.columbia.edu/tag/09TP)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
* [Stacks Project, Tag 06BC](https://stacks.math.columbia.edu/tag/06BC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry.Space.QuasiCoherentDescent (pullbackComparison
  pullbackComparison_trans_hom)

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local implicit_reducible] AlgebraicGeometry.Space.QuotSituation.toCoherentSituation

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Descending sections along relatively limit preserving morphisms -/

/-- **A section over a limit lifting a section over a stage comes from a later stage**, through a
relatively limit preserving morphism (Stacks 06BC). Let `T = lim T_j` be a cofiltered limit of
affine schemes of the site, taken in schemes, `a : F ⟶ G` relatively limit preserving, `x` a
section of `F` over `T` and `y` a section of `G` over a stage `T_i` with `a(x) = y|_T`. Then some
later stage `T_j` carries a section `z` of `F` with `a(z) = y|_{T_j}` and `z|_T = x`. -/
theorem exists_stage_lift_of_relativelyLimitPreserving
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : RelativelyLimitPreserving.{u, u, u, u} B S hS a)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigFppfOver B S hS) (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    (x : F.obj (op c.pt)) (i : I) (y : G.obj (op (D.obj i)))
    (hxy : a.app (op c.pt) x = G.map (c.π.app i).op y) :
    ∃ (j : I) (e : j ⟶ i) (z : F.obj (op (D.obj j))),
      a.app (op (D.obj j)) z = G.map (D.map e).op y ∧ F.map (c.π.app j).op z = x := by
  classical
  have hp := (relativelyLimitPreserving_iff_affineLimit_isPullback.{u, u, u, u} B S hS a).mp ha
    I D c hc hD hpt
  let U := uliftFunctor.{u, u}
  let F' := F ⋙ U
  let G' := G ⋙ U
  let α := Functor.whiskerLeft D.op (Functor.whiskerRight a U)
  let yc : colimit (D.op ⋙ G') := colimit.ι (D.op ⋙ G') (op i) ⟨y⟩
  have hw : U.map (a.app (op c.pt)) ⟨x⟩ = colimit.desc (D.op ⋙ G') (G'.mapCocone c.op) yc := by
    show ULift.up (a.app (op c.pt) x) = (colimit.ι (D.op ⋙ G') (op i) ≫
      colimit.desc (D.op ⋙ G') (G'.mapCocone c.op)) ⟨y⟩
    rw [colimit.ι_desc]
    exact congrArg ULift.up hxy
  obtain ⟨z, hz₁, hz₂⟩ := Types.exists_of_isPullback hp ⟨x⟩ yc hw
  obtain ⟨j', t', ht⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (D.op ⋙ F')) z
  have hcol : colimit.ι (D.op ⋙ G') j' (α.app j' t') = colimit.ι (D.op ⋙ G') (op i) ⟨y⟩ :=
    calc colimit.ι (D.op ⋙ G') j' (α.app j' t')
        = colimMap α (colimit.ι (D.op ⋙ F') j' t') := (colimit.ι_map_apply α j' t').symm
      _ = colimMap α z := congrArg (colimMap α) ht
      _ = yc := hz₂
  have hlimRep : colimit.desc (D.op ⋙ F') (F'.mapCocone c.op)
      (colimit.ι (D.op ⋙ F') j' t') = ⟨x⟩ :=
    (congrArg (colimit.desc (D.op ⋙ F') (F'.mapCocone c.op)) ht).trans hz₁
  change (colimit.ι (D.op ⋙ F') j' ≫
    colimit.desc (D.op ⋙ F') (F'.mapCocone c.op)) t' = ⟨x⟩ at hlimRep
  rw [colimit.ι_desc] at hlimRep
  change ULift.up (F.map (c.π.app j'.unop).op t'.down) = ULift.up x at hlimRep
  obtain ⟨k', fa, fa', heq⟩ := (Types.FilteredColimit.colimit_eq_iff (D.op ⋙ G')).mp hcol
  change ULift.up (G.map (D.map fa.unop).op (a.app _ t'.down)) =
    ULift.up (G.map (D.map fa'.unop).op y) at heq
  refine ⟨k'.unop, fa'.unop, F.map (D.map fa.unop).op t'.down, ?_, ?_⟩
  · rw [NatTrans.naturality_apply]
    exact congrArg ULift.down heq
  · rw [← Functor.map_comp_apply, ← op_comp, c.w fa.unop]
    exact congrArg ULift.down hlimRep

/-- **A morphism from a stage into a scheme which lands in an open subfunctor over the limit does
so at a later stage.** Let `T = lim T_j` be a cofiltered limit of affine schemes of the site, taken
in schemes, `U` a subfunctor of `h_V` whose inclusion is an open immersion and `t : T_i ⟶ V` a
morphism from a stage such that `T ⟶ T_i ⟶ V` lies in `U`. Then `T_j ⟶ T_i ⟶ V` lies in `U` for
some later stage `T_j`: an open immersion is locally of finite presentation, hence relatively
limit preserving. -/
theorem exists_stage_mem_of_isOpenImmersion {V : BigFppfOver B S hS}
    (U : Subfunctor (yoneda.obj V)) (hU : IsOpenImmersion B S hS U.ι)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigFppfOver B S hS) (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    (i : I) (t : D.obj i ⟶ V) (ht : c.π.app i ≫ t ∈ U.obj (op c.pt)) :
    ∃ (j : I) (e : j ⟶ i), D.map e ≫ t ∈ U.obj (op (D.obj j)) := by
  have hlfp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf U.ι :=
    MorphismProperty.relative_monotone (MorphismProperty.monotone_inverseImage _
      (fun _ _ f hf => by
        have : AlgebraicGeometry.IsOpenImmersion f := hf
        infer_instance)) _ hU
  obtain ⟨j, e, z, hz, -⟩ := exists_stage_lift_of_relativelyLimitPreserving U.ι
    (relativelyLimitPreserving_of_presheaf_locallyOfFinitePresentation B S hS hlfp) D c hc hD hpt
    ⟨_, ht⟩ i t rfl
  refine ⟨j, e, ?_⟩
  have hz' : z.1 = D.map e ≫ t := hz
  exact hz' ▸ z.2

/-- The restriction of a morphism of inverse images, written out. -/
theorem moduleHomRestrict_eq_comp {Z : AlgebraicSpaces B S hS}
    (M N : Modules.{u, u} B S hS Z.1 Z.2) {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P)
    (p : P ⟶ Z) (q : Q ⟶ Z) (h : g ≫ p = q)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    moduleHomRestrict M N g p q h x =
      (pullbackComparison B S hS g p q h M).hom ≫ (modulePullback B S hS g).map x ≫
        (pullbackComparison B S hS g p q h N).inv :=
  rfl

/-- The comparison `modulePullbackTriangle` at a module is the comparison `pullbackComparison` of
Stacks 03LU. -/
theorem modulePullbackTriangle_app_eq {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : X ⟶ Z} (hk : f ≫ g = k) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackTriangle B S hS hk).app M = pullbackComparison B S hS f g k hk M := by
  subst hk
  rw [QuasiCoherentDescent.pullbackComparison_rfl]
  ext
  simp [modulePullbackTriangle]

/-- `AlgebraicGeometry.Space.exists_stage_mem_of_isOpenImmersion` for the open subfunctors of a
stage: if the projection `T ⟶ T_i` lands in `U ⊆ h_{T_i}`, so does a transition `T_j ⟶ T_i`. -/
theorem exists_stage_map_mem_of_isOpenImmersion
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigFppfOver B S hS) (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)) (i : I)
    (U : Subfunctor (yoneda.obj (D.obj i))) (hU : IsOpenImmersion B S hS U.ι)
    (ht : c.π.app i ∈ U.obj (op c.pt)) :
    ∃ (j : I) (e : j ⟶ i), D.map e ∈ U.obj (op (D.obj j)) := by
  obtain ⟨j, e, he⟩ := exists_stage_mem_of_isOpenImmersion U hU D c hc hD hpt i (𝟙 _)
    (by rwa [Category.comp_id])
  exact ⟨j, e, by rwa [Category.comp_id] at he⟩

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-! ### The comparison of base changes, as a comparison of inverse images -/


/-- The identification `F_{T'} ≅ (X_{T'} ⟶ X_T)^* F_T` is the comparison of Stacks 03LU for the
triangle `X_{T'} ⟶ X_T ⟶ X`. -/
theorem baseChangeComparison_app {T' T : SchemesOver D.Y} (h : T' ⟶ T) :
    (D.baseChangeComparison h).app D.F = pullbackComparison B S hS (D.relativeMap h)
      (D.sourceProjection T) (D.sourceProjection T') (baseChangeMap_comp_projection D.f h) D.F :=
  _root_.AlgebraicGeometry.Space.modulePullbackTriangle_app_eq _ _

/-- `AlgebraicGeometry.Space.QuotSituation.baseChangeComparison_app` on forward morphisms. -/
theorem baseChangeComparison_hom_app {T' T : SchemesOver D.Y} (h : T' ⟶ T) :
    (D.baseChangeComparison h).hom.app D.F = (pullbackComparison B S hS (D.relativeMap h)
      (D.sourceProjection T) (D.sourceProjection T') (baseChangeMap_comp_projection D.f h)
        D.F).hom :=
  congrArg Iso.hom (D.baseChangeComparison_app h)

/-- **The situation of Stacks 083F attached to a map `F_T ⟶ G` of modules on a base change
`X_T`**, over the test scheme `T`. -/
abbrev stageMapSituation (T : SchemesOver D.Y)
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (hG : G.IsQuasicoherentOnSite)
    (v : D.baseChangeModule T ⟶ G) : ModuleMapSituation.{u, u} B S hS where
  X := D.space T
  Y := (schemeSpaceFunctor B S hS).obj T.left
  f := D.projection T
  F := D.baseChangeModule T
  G := G
  quasicoherent_F :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ D.F D.quasicoherent
  quasicoherent_G := hG
  u := v

/-- The test scheme over `T` of the situation attached to a map on `X_T`, for a morphism of test
schemes into `T`. -/
abbrev stageMapTest {T T' : SchemesOver D.Y}
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (hG : G.IsQuasicoherentOnSite)
    (v : D.baseChangeModule T ⟶ G) (g : T' ⟶ T) : (D.stageMapSituation T hG v).SchemesOver :=
  CostructuredArrow.mk (Y := T'.left) ((schemeSpaceFunctor B S hS).map g.left)

/-- The map of the situation attached to `v` is `v`, read in either spelling of the base
change. -/
theorem epi_map_stageMapSituation_u_iff {T : SchemesOver D.Y}
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (hG : G.IsQuasicoherentOnSite)
    (v : D.baseChangeModule T ⟶ G) {W : AlgebraicSpaces B S hS}
    (b : W ⟶ (D.stageMapSituation T hG v).X) :
    Epi ((modulePullback B S hS (Y := (D.stageMapSituation T hG v).X) b).map
        (D.stageMapSituation T hG v).u) ↔
      Epi ((modulePullback B S hS (Y := D.space T) b).map v) :=
  Iff.rfl

/-- **Surjectivity in the sense of Stacks 083F at a test scheme over `T` is surjectivity of the
inverse image along the morphism of base changes.** -/
theorem isSurjectiveAt_stageMapTest_iff {T T' : SchemesOver D.Y}
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (hG : G.IsQuasicoherentOnSite)
    (v : D.baseChangeModule T ⟶ G) (g : T' ⟶ T) :
    (D.stageMapSituation T hG v).IsSurjectiveAt (modulePullbackSystem B S hS)
        (D.stageMapTest hG v g) ↔
      Epi ((modulePullback B S hS (D.relativeMap g)).map v) := by
  have hpb₁ : IsPullback (D.relativeMap g) (D.projection T') (D.projection T)
      ((schemeSpaceFunctor B S hS).map g.left) := isPullback_baseChangeMap D.f g
  have hpb₂ : IsPullback
      ((D.stageMapSituation T hG v).baseChangeProjection (D.stageMapTest hG v g))
      ((D.stageMapSituation T hG v).baseChangeInclusion (D.stageMapTest hG v g))
      (D.stageMapSituation T hG v).f (D.stageMapTest hG v g).hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS
      (D.stageMapSituation T hG v).f (D.stageMapTest hG v g).hom
  let φ := hpb₁.isoIsPullback _ _ hpb₂
  have hφ : φ.hom ≫ (D.stageMapSituation T hG v).baseChangeProjection (D.stageMapTest hG v g) =
      D.relativeMap g :=
    hpb₁.isoIsPullback_hom_fst _ _ hpb₂
  show Epi ((modulePullback B S hS (Y := D.space T)
      ((D.stageMapSituation T hG v).baseChangeProjection (D.stageMapTest hG v g))).map v) ↔ _
  exact (epi_modulePullback_map_iff_of_iso (X := D.space T)
    (M := D.baseChangeModule T) (N := G) φ hφ v).symm

/-- **Stacks 09TP on a base change.** Let `v : F_T ⟶ G` be a map of modules on a base change
`X_T`, with `G` quasi-coherent of finite type and with support proper over `T`. Then there is an
open subspace `U` of `T` such that, for every morphism `g : T' ⟶ T` of test schemes over `B`, the
inverse image of `v` along `X_{T'} ⟶ X_T` is surjective exactly when `g` lands in `U`. -/
theorem exists_isOpenSubspace_epi_modulePullback_iff (T : SchemesOver D.Y)
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (hG : G.IsQuasicoherentOnSite)
    (hGft : SheafOfModules.IsFiniteTypeOnSite G)
    (hGp : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
      (hU : IsClosed (D.support T G)),
      IsProperOver B S hS (D.space T).2 ((schemeSpaceFunctor B S hS).obj T.left).2
        (D.projection T).hom hp (D.support T G) hU)
    (v : D.baseChangeModule T ⟶ G) :
    ∃ U : Subfunctor ((schemeSpaceFunctor B S hS).obj T.left).1, IsOpenSubspace B S hS U ∧
      ∀ {T' : SchemesOver D.Y} (g : T' ⟶ T),
        Epi ((modulePullback B S hS (D.relativeMap g)).map v) ↔ g.left ∈ U.obj (op T'.left) := by
  obtain ⟨_, hU, hP⟩ := hGp
  obtain ⟨U, hUo, hiff⟩ := (D.stageMapSituation T hG v).exists_isOpenSubspace_isSurjectiveAt_iff
    (Space.isLocallyOfFinitePresentation_projection D.toCoherentSituation T) hGft ⟨hU, hP⟩
  refine ⟨U, hUo, fun g => ?_⟩
  rw [← D.isSurjectiveAt_stageMapTest_iff hG v g, hiff]
  exact exists_comp_ι_eq_yoneda_map_iff U g.left

/-! ### Restricting a map of inverse images along a further morphism -/

/-- The pullback of a map along a morphism of test schemes, with the comparison of base changes
written as the comparison of Stacks 03LU. -/
theorem pullMapOf_eq {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {M : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj M ⟶ M')
    (v : D.baseChangeModule T ⟶ M) :
    D.pullMapOf h α v = (pullbackComparison B S hS (D.relativeMap h) (D.sourceProjection T)
        (D.sourceProjection T') (baseChangeMap_comp_projection D.f h) D.F).hom ≫
      (modulePullback B S hS (D.relativeMap h)).map v ≫ α := by
  rw [pullMapOf_def, D.baseChangeComparison_hom_app]


/-- **The comparisons of Stacks 03LU for base changes along a factorization `πₗ ≫ e = πⱼ`.** -/
theorem pullbackComparison_sourceProjection_trans {T₀ T₁ T : SchemesOver D.Y} (e : T₁ ⟶ T₀)
    (πₗ : T ⟶ T₁) (πⱼ : T ⟶ T₀)
    (hh : D.relativeMap πₗ ≫ D.relativeMap e = D.relativeMap πⱼ) :
    (pullbackComparison B S hS (D.relativeMap πₗ) (D.sourceProjection T₁) (D.sourceProjection T)
        (baseChangeMap_comp_projection D.f πₗ) D.F).hom ≫
      (modulePullback B S hS (D.relativeMap πₗ)).map (pullbackComparison B S hS (D.relativeMap e)
        (D.sourceProjection T₀) (D.sourceProjection T₁) (baseChangeMap_comp_projection D.f e)
          D.F).hom =
    (pullbackComparison B S hS (D.relativeMap πⱼ) (D.sourceProjection T₀) (D.sourceProjection T)
        (baseChangeMap_comp_projection D.f πⱼ) D.F).hom ≫
      (pullbackComparison B S hS (D.relativeMap πₗ) (D.relativeMap e) (D.relativeMap πⱼ) hh
        ((modulePullback B S hS (D.sourceProjection T₀)).obj D.F)).hom :=
  pullbackComparison_trans_hom B S hS (D.relativeMap πₗ) (D.relativeMap e)
    (D.sourceProjection T₀) (D.sourceProjection T₁) (baseChangeMap_comp_projection D.f e)
    (D.relativeMap πⱼ) hh (D.sourceProjection T)
    (baseChangeMap_comp_projection D.f πₗ) (baseChangeMap_comp_projection D.f πⱼ) D.F

/-- **A map descended by the fullness clause of Stacks 07V7, pulled back to the limit**, on
explicit composites. Let `ψ : (X_e)^* F_{T₀} ⟶ (X_e)^* Q` restrict, along `πₗ` with
`πₗ ≫ e = πⱼ`, to `χ`. Then `F_{T₁} ≅ (X_e)^* F_{T₀} ⟶ (X_e)^* Q`, pulled back along `πₗ`, is
`F_T ≅ (X_{πⱼ})^* F_{T₀} ⟶ (X_{πⱼ})^* Q` built from `χ`. -/
theorem comp_map_stageMap {T₀ T₁ T : SchemesOver D.Y} (e : T₁ ⟶ T₀)
    {Q : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    (ψ : (modulePullback B S hS (D.relativeMap e)).obj
        ((modulePullback B S hS (D.sourceProjection T₀)).obj D.F) ⟶
      (modulePullback B S hS (D.relativeMap e)).obj Q)
    (πₗ : T ⟶ T₁) (πⱼ : T ⟶ T₀)
    (hh : D.relativeMap πₗ ≫ D.relativeMap e = D.relativeMap πⱼ)
    (χ : (modulePullback B S hS (D.relativeMap πⱼ)).obj
        ((modulePullback B S hS (D.sourceProjection T₀)).obj D.F) ⟶
      (modulePullback B S hS (D.relativeMap πⱼ)).obj Q)
    (hψ : moduleHomRestrict _ Q (D.relativeMap πₗ) (D.relativeMap e) (D.relativeMap πⱼ) hh ψ = χ) :
    (pullbackComparison B S hS (D.relativeMap πₗ) (D.sourceProjection T₁) (D.sourceProjection T)
        (baseChangeMap_comp_projection D.f πₗ) D.F).hom ≫
      (modulePullback B S hS (D.relativeMap πₗ)).map
        ((pullbackComparison B S hS (D.relativeMap e) (D.sourceProjection T₀)
          (D.sourceProjection T₁) (baseChangeMap_comp_projection D.f e) D.F).hom ≫ ψ) ≫
      (pullbackComparison B S hS (D.relativeMap πₗ) (D.relativeMap e)
        (D.relativeMap πⱼ) hh Q).inv =
      (pullbackComparison B S hS (D.relativeMap πⱼ) (D.sourceProjection T₀) (D.sourceProjection T)
        (baseChangeMap_comp_projection D.f πⱼ) D.F).hom ≫ χ := by
  rw [← hψ, moduleHomRestrict_eq_comp, Functor.map_comp, Category.assoc,
    reassoc_of% (D.pullbackComparison_sourceProjection_trans e πₗ πⱼ hh)]

/-- `AlgebraicGeometry.Space.QuotSituation.comp_map_stageMap`, as a pullback of maps. -/
theorem pullMapOf_stageMap {T₀ T₁ T : SchemesOver D.Y} (e : T₁ ⟶ T₀)
    {Q : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    (ψ : (modulePullback B S hS (D.relativeMap e)).obj
        ((modulePullback B S hS (D.sourceProjection T₀)).obj D.F) ⟶
      (modulePullback B S hS (D.relativeMap e)).obj Q)
    (πₗ : T ⟶ T₁) (πⱼ : T ⟶ T₀)
    (hh : D.relativeMap πₗ ≫ D.relativeMap e = D.relativeMap πⱼ)
    (χ : (modulePullback B S hS (D.relativeMap πⱼ)).obj
        ((modulePullback B S hS (D.sourceProjection T₀)).obj D.F) ⟶
      (modulePullback B S hS (D.relativeMap πⱼ)).obj Q)
    (hψ : moduleHomRestrict _ Q (D.relativeMap πₗ) (D.relativeMap e) (D.relativeMap πⱼ) hh ψ = χ) :
    D.pullMapOf πₗ (pullbackComparison B S hS (D.relativeMap πₗ) (D.relativeMap e)
        (D.relativeMap πⱼ) hh Q).inv
        ((pullbackComparison B S hS (D.relativeMap e) (D.sourceProjection T₀)
          (D.sourceProjection T₁) (baseChangeMap_comp_projection D.f e) D.F).hom ≫ ψ) =
      (pullbackComparison B S hS (D.relativeMap πⱼ) (D.sourceProjection T₀) (D.sourceProjection T)
        (baseChangeMap_comp_projection D.f πⱼ) D.F).hom ≫ χ :=
  (D.pullMapOf_eq _ _ _).trans (D.comp_map_stageMap e ψ πₗ πⱼ hh χ hψ)

set_option synthInstance.maxHeartbeats 100000 in
/-- The pullback of a map along a morphism of test schemes, through an isomorphism, is surjective
exactly when the inverse image of the map is. -/
theorem epi_pullMapOf_iff {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {M : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj M ⟶ M') [IsIso α]
    (v : D.baseChangeModule T ⟶ M) :
    Epi (D.pullMapOf h α v) ↔ Epi ((modulePullback B S hS (D.relativeMap h)).map v) := by
  rw [pullMapOf_def]
  refine ⟨fun hv => ?_, fun hv => epi_comp'
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom ((D.baseChangeComparison h).app D.F)))
    (epi_comp' hv inferInstance)⟩
  have he : (modulePullback B S hS (D.relativeMap h)).map v =
      (D.baseChangeComparison h).inv.app D.F ≫
        ((D.baseChangeComparison h).hom.app D.F ≫
          (modulePullback B S hS (D.relativeMap h)).map v ≫ α) ≫ inv α := by
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_app_assoc]
  rw [he]
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv ((D.baseChangeComparison h).app D.F)))
    (epi_comp' hv inferInstance)

/-- The kernel of the projection `F_T ⟶ F_T / K` is `K`
(`AlgebraicGeometry.Space.QuotientSituation.mk_kernel_quotientProjection`, read with the
instances of this file). -/
theorem kernelSubobject_quotientProjection (T : SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) [HasKernel (D.quotientProjection T K)] :
    kernelSubobject (D.quotientProjection T K) = K := by
  refine (Subobject.mk_eq_mk_of_comm _ K.arrow
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel (cokernel.π K.arrow))
      (Abelian.monoIsKernelOfCokernel (Cofork.ofπ (cokernel.π K.arrow)
        ((cokernel.condition K.arrow).trans zero_comp.symm))
        (cokernelIsCokernel K.arrow))) ?_).trans
    (Subobject.mk_arrow K)
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- `AlgebraicGeometry.Space.QuotSituation.kernelSubobject_pullMapOf_of_epi` with instance
arguments. -/
theorem kernelSubobject_pullMapOf_eq_quotientPullback {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {M : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj M ⟶ M') [IsIso α]
    (v : D.baseChangeModule T ⟶ M) [Epi v] :
    kernelSubobject (D.pullMapOf h α v) = D.quotientPullback h (kernelSubobject v) :=
  D.kernelSubobject_pullMapOf_of_epi h α inferInstance v inferInstance

set_option synthInstance.maxHeartbeats 100000 in
/-- `AlgebraicGeometry.Space.QuotSituation.kernelSubobject_pullMapOf_eq_quotientPullback`, with
the pullback of the map written out as a composite. -/
theorem kernelSubobject_comp_map_of_epi {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {M : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj M ⟶ M') [IsIso α]
    (v : D.baseChangeModule T ⟶ M) [Epi v] :
    kernelSubobject ((pullbackComparison B S hS (D.relativeMap h) (D.sourceProjection T)
        (D.sourceProjection T') (baseChangeMap_comp_projection D.f h) D.F).hom ≫
      (modulePullback B S hS (D.relativeMap h)).map v ≫ α) =
      D.quotientPullback h (kernelSubobject v) :=
  (congrArg (fun f => kernelSubobject f) (D.pullMapOf_eq h α v).symm).trans
    (D.kernelSubobject_pullMapOf_eq_quotientPullback h α v)

/-- **The kernel of a descended map is the descended quotient.** If `ψ : (X_e)^* F_{T₀} ⟶
(X_e)^* Q` restricts along `πₗ` to the map `F_T ⟶ F_T/K ≅ (X_{πⱼ})^* Q` read through the
comparisons, and the map `F_{T₁} ≅ (X_e)^* F_{T₀} ⟶ (X_e)^* Q` is surjective, then the pullback of
its kernel along `πₗ` is `K`. -/
theorem quotientPullback_kernelSubobject_stageMap {T₀ T₁ T : SchemesOver D.Y} (e : T₁ ⟶ T₀)
    {Q : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    (ψ : (modulePullback B S hS (D.relativeMap e)).obj
        ((modulePullback B S hS (D.sourceProjection T₀)).obj D.F) ⟶
      (modulePullback B S hS (D.relativeMap e)).obj Q)
    (πₗ : T ⟶ T₁) (πⱼ : T ⟶ T₀)
    (hh : D.relativeMap πₗ ≫ D.relativeMap e = D.relativeMap πⱼ)
    (K : Subobject (D.baseChangeModule T))
    (α' : (modulePullback B S hS (D.relativeMap πⱼ)).obj Q ≅ D.quotientModule T K)
    (χ : (modulePullback B S hS (D.relativeMap πⱼ)).obj
        ((modulePullback B S hS (D.sourceProjection T₀)).obj D.F) ⟶
      (modulePullback B S hS (D.relativeMap πⱼ)).obj Q)
    (hχ : χ = (pullbackComparison B S hS (D.relativeMap πⱼ) (D.sourceProjection T₀)
        (D.sourceProjection T) (baseChangeMap_comp_projection D.f πⱼ) D.F).inv ≫
          D.quotientProjection T K ≫ α'.inv)
    (hψ : moduleHomRestrict _ Q (D.relativeMap πₗ) (D.relativeMap e) (D.relativeMap πⱼ) hh ψ = χ)
    [Epi ((pullbackComparison B S hS (D.relativeMap e) (D.sourceProjection T₀)
      (D.sourceProjection T₁) (baseChangeMap_comp_projection D.f e) D.F).hom ≫ ψ)] :
    D.quotientPullback πₗ (kernelSubobject ((pullbackComparison B S hS (D.relativeMap e)
      (D.sourceProjection T₀) (D.sourceProjection T₁) (baseChangeMap_comp_projection D.f e)
        D.F).hom ≫ ψ)) = K := by
  subst hχ
  have h₁ := D.comp_map_stageMap e ψ πₗ πⱼ hh _ hψ
  rw [Iso.hom_inv_id_assoc] at h₁
  refine (D.kernelSubobject_comp_map_of_epi πₗ ((pullbackComparison B S hS (D.relativeMap πₗ)
    (D.relativeMap e) (D.relativeMap πⱼ) hh Q).inv ≫ α'.hom) _).symm.trans ?_
  simp only [reassoc_of% h₁, Iso.inv_hom_id, Category.comp_id]
  exact D.kernelSubobject_quotientProjection T K

/-- **The kernel of a surjection from `F_T` onto a module of finite presentation, flat over `T`
with support proper over `T`, is a member of `Quot_{F/X/B}(T)`.** -/
theorem kernelSubobject_mem_of_isFlatWithProperSupport (T : SchemesOver D.Y)
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (hG : G.IsFinitePresentationOnSite)
    (hGf : D.toCoherentSituation.IsFlatWithProperSupport T G) (v : D.baseChangeModule T ⟶ G)
    (hv : Epi v) : kernelSubobject v ∈ D.properlySupportedQuotients T :=
  D.kernelSubobject_mem_properlySupportedQuotients
    { T := T
      F := G
      quasicoherent := by
        have := hG
        infer_instance
      finitePresentation := hG
      flat := hGf.1
      properSupport := hGf.2 } v hv

section Descent

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (E : I ⥤ BigAffineFppf B S hS)
  (c : Cone E) (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))

include hc in
/-- **Surjectivity over the limit descends to a stage** (Stacks 09TP and the local finite
presentation of an open immersion). Let `u : F_{T_l} ⟶ G` be a map of modules on a base change
`X_{T_l}` over a stage, with `G` of finite presentation, flat over `T_l` with support proper over
`T_l`. If the inverse image of `u` to `X_T` is surjective, so is its inverse image to `X_{T_m}`
for some later stage `T_m`. -/
theorem exists_stage_epi_of_epi_limit {i : I}
    (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y)
    (l : Over i)
    {G : Modules.{u, u} B S hS (D.space ((D.toCoherentSituation.stageTestSystem E g).obj l)).1
      (D.space ((D.toCoherentSituation.stageTestSystem E g).obj l)).2}
    (hG : G.IsFinitePresentationOnSite)
    (hGf : D.toCoherentSituation.IsFlatWithProperSupport
      ((D.toCoherentSituation.stageTestSystem E g).obj l) G)
    (u : D.baseChangeModule ((D.toCoherentSituation.stageTestSystem E g).obj l) ⟶ G)
    (hu : Epi ((modulePullback B S hS (D.relativeMap (T := (D.toCoherentSituation.stageTestCone E c
      g).pt) ((D.toCoherentSituation.stageTestCone E c g).π.app l))).map u)) :
    ∃ (m : Over i) (e : m ⟶ l),
      Epi ((modulePullback B S hS
        (D.relativeMap ((D.toCoherentSituation.stageTestSystem E g).map e))).map u) := by
  have hGq : G.IsQuasicoherentOnSite := by
    have := hG
    infer_instance
  obtain ⟨U, hU, hiff⟩ := D.exists_isOpenSubspace_epi_modulePullback_iff _ hGq
    (@SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ _ hG) hGf.2 u
  have hmem := (hiff (T' := (D.toCoherentSituation.stageTestCone E c g).pt)
    ((D.toCoherentSituation.stageTestCone E c g).π.app l)).1 hu
  obtain ⟨m, e, hm⟩ := exists_stage_map_mem_of_isOpenImmersion
    (Over.forget i ⋙ E ⋙ BigAffineFppf.inclusion B S hS)
    ((BigAffineFppf.inclusion B S hS).mapCone (c.whisker (Over.forget i)))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) _).symm hc)
    (fun m => (E.obj m.left).property) c.pt.property l U hU.2 hmem
  exact ⟨m, e, (hiff ((D.toCoherentSituation.stageTestSystem E g).map e)).2 hm⟩

include hc in
set_option synthInstance.maxHeartbeats 100000 in
/-- **A quotient over a limit of affine schemes, lying over a stage, comes from a later stage.**
Let `F` be of finite presentation, let `T = lim T_k` be a cofiltered limit of affine schemes of the
site, taken in schemes, `g : T_i ⟶ B` a morphism from a stage, and `K` a member of
`Quot_{F/X/B}(T)` over `T ⟶ T_i ⟶ B`. Then `K` is the pullback of a member of
`Quot_{F/X/B}(T_m)` over `T_m ⟶ T_i ⟶ B` for some later stage `T_m`. -/
theorem exists_stage_quotientPullback_eq (hF : D.F.IsFinitePresentationOnSite) {i : I}
    (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y)
    (K : Subobject (D.baseChangeModule (D.toCoherentSituation.stageTestCone E c g).pt))
    (hK : K ∈ D.properlySupportedQuotients (D.toCoherentSituation.stageTestCone E c g).pt) :
    ∃ (m : Over i)
      (K' : Subobject (D.baseChangeModule ((D.toCoherentSituation.stageTestSystem E g).obj m))),
      K' ∈ D.properlySupportedQuotients ((D.toCoherentSituation.stageTestSystem E g).obj m) ∧
        D.quotientPullback (T' := (D.toCoherentSituation.stageTestCone E c g).pt)
          ((D.toCoherentSituation.stageTestCone E c g).π.app m) K' = K := by
  have hZ := B.contains_terminal
  let hst := modulePullbackStabilityOfFinitePresentation B S hS
  -- the object of `Coh_{X/B}` of the quotient, and its descent to a stage `j`
  obtain ⟨j, Qj, hQj, hfpsj, ⟨α⟩⟩ :=
    D.toCoherentSituation.exists_stage_module_of_stage E c hc
      (D.cohObject (D.toCoherentSituation.stageTestCone E c g).pt K hK) rfl g (Iso.refl _) rfl
  have hext : ((D.toCoherentSituation.stageTestCone E c g).extend
      (Iso.refl (D.toCoherentSituation.stageTestCone E c g).pt).hom).π.app j =
        (D.toCoherentSituation.stageTestCone E c g).π.app j :=
    Category.id_comp _
  let α' : (modulePullback B S hS (X := D.space (D.toCoherentSituation.stageTestCone E c g).pt)
      (D.relativeMap (T := (D.toCoherentSituation.stageTestCone E c g).pt)
      ((D.toCoherentSituation.stageTestCone E c g).π.app j))).obj Qj ≅
      D.quotientModule (D.toCoherentSituation.stageTestCone E c g).pt K :=
    eqToIso (congrArg (fun t => (modulePullback B S hS (D.relativeMap t)).obj Qj) hext.symm) ≪≫ α
  have hFj : ((modulePullback B S hS
      (D.sourceProjection ((D.toCoherentSituation.stageTestSystem E g).obj j))).obj
      D.F).IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_modulePullback B S hS _ D.F hF
  let χ : (modulePullback B S hS (X := D.space (D.toCoherentSituation.stageTestCone E c g).pt)
      (D.relativeMap (T := (D.toCoherentSituation.stageTestCone E c g).pt)
      ((D.toCoherentSituation.stageTestCone E c g).π.app j))).obj
        ((modulePullback B S hS
          (D.sourceProjection ((D.toCoherentSituation.stageTestSystem E g).obj j))).obj D.F) ⟶
      (modulePullback B S hS (X := D.space (D.toCoherentSituation.stageTestCone E c g).pt)
        (D.relativeMap (T := (D.toCoherentSituation.stageTestCone E c g).pt)
        ((D.toCoherentSituation.stageTestCone E c g).π.app j))).obj Qj :=
    (pullbackComparison B S hS (T := D.space (D.toCoherentSituation.stageTestCone E c g).pt)
      (D.relativeMap (T := (D.toCoherentSituation.stageTestCone E c g).pt)
      ((D.toCoherentSituation.stageTestCone E c g).π.app j))
      (D.sourceProjection ((D.toCoherentSituation.stageTestSystem E g).obj j))
      (D.sourceProjection (D.toCoherentSituation.stageTestCone E c g).pt)
        (baseChangeMap_comp_projection D.f (U := (D.toCoherentSituation.stageTestCone E c g).pt)
        ((D.toCoherentSituation.stageTestCone E c g).π.app j)) D.F).inv ≫
      D.quotientProjection (D.toCoherentSituation.stageTestCone E c g).pt K ≫ α'.inv
  obtain ⟨-, hfull, -⟩ := D.toCoherentSituation.finitePresentationModule_isColimit_baseChange
      (D.toCoherentSituation.stageTestSystem E g) (D.toCoherentSituation.stageTestCone E c g) hZ
    (fun e => D.toCoherentSituation.isAffineHom_stageSpaceSystem_map E g e)
      (D.toCoherentSituation.isQuasiCompactSpace_stageSpaceSystem E g)
    (D.toCoherentSituation.isAbsolutelyQuasiSeparated_stageSpaceSystem E g hZ)
      (D.toCoherentSituation.isLimit_stageSpaceCone E c g hc)
    (D.toCoherentSituation.siteContainsBaseChangeLimits_stageSpaceSystem E c g hc)
  obtain ⟨l, e', ψ, hψ⟩ := hfull j _ Qj hFj hQj χ
  have hT₀ := D.pullMapOf_stageMap (T := (D.toCoherentSituation.stageTestCone E c g).pt)
      ((D.toCoherentSituation.stageTestSystem E g).map e') ψ
      ((D.toCoherentSituation.stageTestCone E c g).π.app l)
      ((D.toCoherentSituation.stageTestCone E c g).π.app j)
    (D.toCoherentSituation.relativeMap_cone_comp (D.toCoherentSituation.stageTestSystem E g)
      (D.toCoherentSituation.stageTestCone E c g) e') χ hψ
  generalize hu : (pullbackComparison B S hS
      (D.relativeMap ((D.toCoherentSituation.stageTestSystem E g).map e'))
    (D.sourceProjection ((D.toCoherentSituation.stageTestSystem E g).obj j))
      (D.sourceProjection ((D.toCoherentSituation.stageTestSystem E g).obj l))
    (baseChangeMap_comp_projection D.f
      ((D.toCoherentSituation.stageTestSystem E g).map e')) D.F).hom ≫ ψ = u_l at hT₀
  have hχ : (pullbackComparison B S hS (T := D.space (D.toCoherentSituation.stageTestCone E c g).pt)
      (D.relativeMap (T := (D.toCoherentSituation.stageTestCone E c g).pt)
      ((D.toCoherentSituation.stageTestCone E c g).π.app j))
      (D.sourceProjection ((D.toCoherentSituation.stageTestSystem E g).obj j))
        (D.sourceProjection (D.toCoherentSituation.stageTestCone E c g).pt)
      (baseChangeMap_comp_projection D.f (U := (D.toCoherentSituation.stageTestCone E c g).pt)
        ((D.toCoherentSituation.stageTestCone E c g).π.app j)) D.F).hom ≫ χ =
      D.quotientProjection (D.toCoherentSituation.stageTestCone E c g).pt K ≫ α'.inv :=
    Iso.hom_inv_id_assoc _ _
  have hTpull := (congrArg Epi hT₀).mpr
    (epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _))
      (epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _))
        (epi_comp' inferInstance (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv α')))))
  have hT := (D.epi_pullMapOf_iff _ _ _).1 hTpull
  -- surjectivity descends to a stage `T_m` (Stacks 09TP)
  have hGfps : ∀ {n : Over i} (e : n ⟶ j), D.toCoherentSituation.IsFlatWithProperSupport
      ((D.toCoherentSituation.stageTestSystem E g).obj n)
      ((modulePullback B S hS
        (D.relativeMap ((D.toCoherentSituation.stageTestSystem E g).map e))).obj Qj) := by
    intro n e
    obtain ⟨hp, hU, hproper⟩ := hfpsj.2
    have := hQj
    obtain ⟨hU', hproper'⟩ := hst.properSupport
      (isPullback_baseChangeMap D.f ((D.toCoherentSituation.stageTestSystem E g).map e))
      hp Qj inferInstance inferInstance hU hproper
    exact ⟨hst.flat (isPullback_baseChangeMap D.f
      ((D.toCoherentSituation.stageTestSystem E g).map e)) Qj hQj hfpsj.1, _, hU', hproper'⟩
  obtain ⟨m, e'', hEm⟩ := D.exists_stage_epi_of_epi_limit E c hc g l
    (isFinitePresentationOnSite_modulePullback B S hS _ Qj hQj) (hGfps e') u_l hT
  -- the map at the stage `T_m` is surjective, and its kernel is the required quotient
  have hψm := (moduleHomRestrict_homRestrict (M := (modulePullback B S hS
      (D.sourceProjection ((D.toCoherentSituation.stageTestSystem E g).obj j))).obj D.F) (N := Qj)
        (D.relativeMap ((D.toCoherentSituation.stageTestSystem E g).map e''))
      (D.relativeMap ((D.toCoherentSituation.stageTestCone E c g).π.app m))
        (D.relativeMap ((D.toCoherentSituation.stageTestSystem E g).map e'))
        (D.relativeMap ((D.toCoherentSituation.stageTestSystem E g).map (e'' ≫ e')))
      (D.relativeMap ((D.toCoherentSituation.stageTestCone E c g).π.app j))
        (D.toCoherentSituation.relativeMap_map_comp
        (D.toCoherentSituation.stageTestSystem E g) e'' e')
      (D.toCoherentSituation.relativeMap_cone_comp (D.toCoherentSituation.stageTestSystem E g)
        (D.toCoherentSituation.stageTestCone E c g) (e'' ≫ e')) ψ).trans
    ((moduleHomRestrict_congr
      (D.toCoherentSituation.relativeMap_cone_comp (D.toCoherentSituation.stageTestSystem E g)
      (D.toCoherentSituation.stageTestCone E c g) e'') _ _ _ ψ).trans hψ)
  have hlm := D.pullMapOf_stageMap ((D.toCoherentSituation.stageTestSystem E g).map e') ψ
      ((D.toCoherentSituation.stageTestSystem E g).map e'')
      ((D.toCoherentSituation.stageTestSystem E g).map (e'' ≫ e'))
    (D.toCoherentSituation.relativeMap_map_comp
      (D.toCoherentSituation.stageTestSystem E g) e'' e') _ rfl
  rw [hu] at hlm
  have hEpim := (congrArg Epi hlm).mp ((D.epi_pullMapOf_iff _ _ _).2 hEm)
  have hmemK := D.kernelSubobject_mem_of_isFlatWithProperSupport _
    (isFinitePresentationOnSite_modulePullback B S hS _ Qj hQj) (hGfps (e'' ≫ e')) _ hEpim
  refine ⟨m, _, hmemK, ?_⟩
  have := hEpim
  refine D.quotientPullback_kernelSubobject_stageMap
      (T := (D.toCoherentSituation.stageTestCone E c g).pt)
    ((D.toCoherentSituation.stageTestSystem E g).map (e'' ≫ e')) _
    ((D.toCoherentSituation.stageTestCone E c g).π.app m)
    ((D.toCoherentSituation.stageTestCone E c g).π.app j) ?_ K α' ?_ ?_ ?_
  · exact D.toCoherentSituation.relativeMap_cone_comp (D.toCoherentSituation.stageTestSystem E g)
      (D.toCoherentSituation.stageTestCone E c g) (e'' ≫ e')
  · exact χ
  · rfl
  · exact hψm

end Descent

end QuotSituation

namespace QuotSitePresheafModel

variable {D : QuotSituation B S hS}

/-- **The second clause of Stacks 09TU, given the first.** Let `f : X ⟶ B` be of finite
presentation and `F` a quasi-coherent `𝒪_X`-module of finite presentation. Then the morphism to `B`
of a model of `Quot_{F/X/B}` which is an algebraic space is locally of finite presentation.

By Stacks 0CM6 it suffices that a quotient over a cofiltered limit `T = lim T_i` of affine schemes
whose morphism to `B` comes from a stage comes itself from a later stage, which is
`AlgebraicGeometry.Space.QuotSituation.exists_stage_quotientPullback_eq`. -/
theorem isLocallyOfFinitePresentation_toBase (N : QuotSitePresheafModel D)
    (hN : IsAlgebraicSpace B S hS N.presheaf) (hF : D.F.IsFinitePresentationOnSite) :
    IsLocallyOfFinitePresentation B S hS N.toBase := by
  refine isLocallyOfFinitePresentation_of_affineLimit_surjective B S hS hN D.Y.2 N.toBase ?_
  intro I _ _ Dg c hc haff haffc x y hxy
  let E : I ⥤ BigAffineFppf B S hS := ObjectProperty.lift _ Dg haff
  let cE : Cone E :=
    { pt := ⟨c.pt, haffc⟩
      π :=
        { app := fun i => ObjectProperty.homMk (c.π.app i)
          naturality := fun _ _ f => ObjectProperty.hom_ext _ (c.π.naturality f) } }
  have hcE : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone cE) := hc
  obtain ⟨⟨i⟩, yi, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit _) y
  let g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶
      D.Y := ObjectProperty.homMk (yonedaEquiv.symm yi)
  generalize hq : N.iso.hom.app (op c.pt) (ULift.up x) = q
  obtain ⟨b, K, hK⟩ := q
  have hb : b = (schemeSpaceFunctor B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (cE.π.app i)) ≫ g := by
    apply ObjectProperty.hom_ext
    apply yonedaEquiv.injective
    have h₁ : N.toBase.app (op c.pt) x = yonedaEquiv b.hom := by
      show (D.quotSitePresheafToBase.app (op c.pt) (N.iso.hom.app (op c.pt) ⟨x⟩)).down = _
      rw [hq]
      rfl
    rw [← h₁, hxy]
    show (colimit.ι (Dg.op ⋙ D.Y.obj) (op i) ≫
      colimit.desc (Dg.op ⋙ D.Y.obj) (D.Y.obj.mapCocone c.op)) yi = _
    rw [colimit.ι_desc]
    show D.Y.1.map (c.π.app i).op yi = yonedaEquiv (yoneda.map (c.π.app i) ≫ yonedaEquiv.symm yi)
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  subst hb
  obtain ⟨m, K', hK', hpull⟩ := D.exists_stage_quotientPullback_eq E cE hcE hF g K hK
  let zm : QuotFamilyOver D (Dg.obj m.left) :=
    ⟨((D.toCoherentSituation.stageTestSystem E g).obj m).hom, K', hK'⟩
  have hzm : zm.baseChange (c.π.app m.left) = ⟨_, K, hK⟩ := by
    refine (QuotSituation.quotFamily_eq_baseChange_of D (c.π.app m.left) ⟨_, K, hK⟩ zm ?_
      ((D.toCoherentSituation.stageTestCone E cE g).π.app m) rfl hpull.symm).symm
    show (schemeSpaceFunctor B S hS).map (c.π.app i) ≫ g =
      (schemeSpaceFunctor B S hS).map (c.π.app m.left) ≫
        (schemeSpaceFunctor B S hS).map (Dg.map m.hom) ≫ g
    rw [← Functor.map_comp_assoc, c.w]
  refine ⟨colimit.ι (Dg.op ⋙ N.presheaf) (op m.left) (N.iso.inv.app (op (Dg.obj m.left)) zm).down,
    ?_, ?_⟩
  · show (colimit.ι (Dg.op ⋙ N.presheaf) (op m.left) ≫
      colimit.desc (Dg.op ⋙ N.presheaf) (N.presheaf.mapCocone c.op)) _ = x
    rw [colimit.ι_desc]
    show N.presheaf.map (c.π.app m.left).op (N.iso.inv.app (op (Dg.obj m.left)) zm).down = x
    have hnat := NatTrans.naturality_apply N.iso.inv (c.π.app m.left).op zm
    change N.iso.inv.app (op c.pt) (zm.baseChange (c.π.app m.left)) =
      ULift.up (N.presheaf.map (c.π.app m.left).op (N.iso.inv.app (op (Dg.obj m.left)) zm).down)
      at hnat
    rw [hzm, ← hq] at hnat
    have h₄ : N.iso.inv.app (op c.pt) (N.iso.hom.app (op c.pt) (ULift.up x)) = ULift.up x :=
      types_congr_hom (N.iso.hom_inv_id_app (op c.pt)) (ULift.up x)
    exact congrArg ULift.down (hnat.symm.trans h₄)
  · rw [colimit.ι_map_apply]
    have h₃ : N.toBase.app (op (Dg.obj m.left)) (N.iso.inv.app (op (Dg.obj m.left)) zm).down =
        yonedaEquiv zm.toBase.hom := by
      show (D.quotSitePresheafToBase.app _ (N.iso.hom.app _
        ⟨(N.iso.inv.app (op (Dg.obj m.left)) zm).down⟩)).down = _
      have h₅ : N.iso.hom.app (op (Dg.obj m.left)) (N.iso.inv.app (op (Dg.obj m.left)) zm) =
          zm := types_congr_hom (N.iso.inv_hom_id_app (op (Dg.obj m.left))) zm
      show (D.quotSitePresheafToBase.app _ (N.iso.hom.app _
        (N.iso.inv.app (op (Dg.obj m.left)) zm))).down = _
      rw [h₅]
      rfl
    show colimit.ι (Dg.op ⋙ D.Y.obj) (op m.left)
      (N.toBase.app (op (Dg.obj m.left)) (N.iso.inv.app (op (Dg.obj m.left)) zm).down) = _
    have h₆ : yonedaEquiv zm.toBase.hom = D.Y.1.map (Dg.map m.hom).op yi := by
      show yonedaEquiv ((yoneda (C := BigFppfOver B S hS)).map (Dg.map m.hom) ≫
        (yonedaEquiv (F := D.Y.1) (X := Dg.obj i)).symm yi) = _
      rw [← yonedaEquiv_naturality (F := D.Y.1), Equiv.apply_symm_apply]
    rw [h₃, h₆]
    exact colimit.w_apply (Dg.op ⋙ D.Y.obj) m.hom.op yi

end QuotSitePresheafModel

end AlgebraicGeometry.Space

end
