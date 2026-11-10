module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.AffineStageCharts
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.AffineStageCharts

/-!
# Descent of morphisms to a finite stage, under `LimitFacts`

Eventual étaleness over an affine chart, atlas models, eventual equality on a quasi-compact
source, and from these the fullness and faithfulness statements of Stacks 07SK (in their
private `LimitFacts` form), together with their consequences for isomorphisms, monomorphisms
and lifts of pairs of morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! The two projections of an explicit fibre product out of a lift into it are not `simp`
lemmas in Mathlib, where `pullback.hom_ext` is the preferred interface; the explicit cones
built below are compared projection by projection throughout. -/

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, Cardinal.mk (i ⟶ j) < B.cutoff.ord.cof)
variable (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))

/-- Surjective étale presheaf morphisms are stable under base change. -/
private theorem presheaf_surjective_etale_of_isPullback {W X Y Z : (AlgebraicGeometry.BigFppfOver
      B S hS)ᵒᵖ ⥤ Type u} {a : W ⟶ X} {b : W ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback a b c d)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf c)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf c) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf b ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf b := by
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  exact ⟨P.presheaf.of_isPullback h hs, Q.presheaf.of_isPullback h he⟩

/-- A surjective étale atlas `q` of `Y` pulls back along a chart square over `h` to a surjective
étale chart of `Y ×_Z X`, which is the pullback of `q` along the first projection. -/
private theorem exists_etale_chart_pullback {X V Y Z C : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤
      Type u} (r : Y ⟶ Z) (h : X ⟶ Z) (q : V ⟶ Y) (a : C ⟶ X) (b : C ⟶ V)
    (hC : IsPullback a b h (q ≫ r))
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q) :
    ∃ p : C ⟶ pullback r h, IsPullback b p q (pullback.fst r h) ∧ p ≫ pullback.snd r h = a ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p := by
  let p : C ⟶ pullback r h :=
    pullback.lift (b ≫ q) a (by simpa only [Category.assoc] using hC.w.symm)
  have hp : IsPullback b p q (pullback.fst r h) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback r h)
    simpa [p] using hC.flip
  obtain ⟨hps, hpe⟩ := presheaf_surjective_etale_of_isPullback B S hS hp hs he
  exact ⟨p, hp, by simp [p], hps, hpe⟩

/-- Two stages at which a pair of base-change equalities hold have a common later stage. -/
private theorem exists_common_stage_baseChange_eq {J : Type*} [Category J] [IsCofiltered J]
    {C : Type*} [Category C] [HasPullbacks C] (F : J ⥤ C) {j : J}
    {Y₁ Z₁ Y₂ Z₂ : Over (F.obj j)} {f₁ f₁' : Y₁ ⟶ Z₁} {f₂ f₂' : Y₂ ⟶ Z₂}
    (h₁ : ∃ (k : J) (e : k ⟶ j), (Over.pullback (F.map e)).map f₁ =
      (Over.pullback (F.map e)).map f₁')
    (h₂ : ∃ (k : J) (e : k ⟶ j), (Over.pullback (F.map e)).map f₂ =
      (Over.pullback (F.map e)).map f₂') :
    ∃ (k : J) (e : k ⟶ j), (Over.pullback (F.map e)).map f₁ = (Over.pullback (F.map e)).map f₁' ∧
      (Over.pullback (F.map e)).map f₂ = (Over.pullback (F.map e)).map f₂' := by
  obtain ⟨k₁, e₁, hk₁⟩ := h₁
  obtain ⟨k₂, e₂, hk₂⟩ := h₂
  let c₁ := IsCofiltered.minToLeft (Over.mk e₁) (Over.mk e₂)
  let c₂ := IsCofiltered.minToRight (Over.mk e₁) (Over.mk e₂)
  exact ⟨_, (IsCofiltered.min (Over.mk e₁) (Over.mk e₂)).hom,
    baseChange_eq_of_baseChange_eq (F.map e₁) (F.map c₁.left) _
      (by rw [← F.map_comp]; exact congrArg F.map c₁.w) _ _ hk₁,
    baseChange_eq_of_baseChange_eq (F.map e₂) (F.map c₂.left) _
      (by rw [← F.map_comp]; exact congrArg F.map c₂.w) _ _ hk₂⟩

/-- Naturality of the iterated base change isomorphisms, for isomorphisms characterised by their
first projection. -/
private theorem pullback_map_comp_iso_hom {C : Type*} [Category C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X) (h : q ≫ p = r) {Y Z : Over X}
    (f : Y ⟶ Z) (α : (Over.pullback q).obj ((Over.pullback p).obj Y) ≅ (Over.pullback r).obj Y)
    (β : (Over.pullback q).obj ((Over.pullback p).obj Z) ≅ (Over.pullback r).obj Z)
    (hα : α.hom.left ≫ pullback.fst Y.hom r =
      pullback.fst ((Over.pullback p).obj Y).hom q ≫ pullback.fst Y.hom p)
    (hβ : β.hom.left ≫ pullback.fst Z.hom r =
      pullback.fst ((Over.pullback p).obj Z).hom q ≫ pullback.fst Z.hom p) :
    (Over.pullback q).map ((Over.pullback p).map f) ≫ β.hom =
      α.hom ≫ (Over.pullback r).map f := by
  rw [iteratedBaseChangeIso_unique p q r h Y α hα, iteratedBaseChangeIso_unique p q r h Z β hβ]
  exact iteratedBaseChangeIso_naturality p q r h f

/-- The base change of a finite-presentation morphism of algebraic spaces is an algebraic space,
of finite presentation over the base-changed target. -/
private theorem isFinitePresentation_pullback_snd {X Y Z : (AlgebraicGeometry.BigFppfOver
      B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (hf : AlgebraicGeometry.Space.IsFinitePresentation B S hS f) :
    AlgebraicGeometry.IsAlgebraicSpace B S hS (pullback f g) ∧
      AlgebraicGeometry.Space.IsFinitePresentation B S hS (pullback.snd f g) :=
  have hP := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f g hX hY hZ'
  ⟨hP, isFinitePresentation_of_isPullback B S hS hP hX hY hZ'
    (IsPullback.of_hasPullback f g) hf⟩

include hD hAffine hQc hQs

omit hD hQc hQs in
private theorem eventually_etale_over_affine_chart_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (X : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀.obj))
    (hX : AlgebraicGeometry.FinitePresentation X.hom)
    [Etale ((Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)).obj X).hom] :
    ∃ j : Over i, Etale ((Over.pullback
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (affineStageChartOfLimitFacts B S hS D i U₀ p₀ hAffine j).toChart)).obj X).hom := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let E := affineStageChartOverDiagramOfLimitFacts B S hS D
    i U₀ p₀ hAffine
  let c := affineStageChartConeOfLimitFacts B S hS D
    i U₀ p₀ hAffine U.obj p q hp
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let F := E ⋙ Over.forget U₀.obj
  let E' := E ⋙ Over.post Q
  let sc := (Over.post Q).mapCone c
  have hF (j : Over i) : IsAffine (Q.obj (F.obj j)) :=
    (affineStageChartOfLimitFacts B S hS D i U₀ p₀ hAffine j).U.property
  have hsc : IsLimit ((Over.forget (Q.obj U₀.obj)).mapCone sc) :=
    hFacts.chartLim hAffine i U₀ p₀ _ p q hp
  let : ∀ j, IsAffine (E'.obj j).left := hF
  let : ∀ {j k : Over i} (a : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (E'.map a).left := by
    intro j k a
    infer_instance
  let : Etale ((Over.pullback sc.pt.hom).obj X).hom :=
    ‹Etale ((Over.pullback (Q.map q)).obj X).hom›
  exact scheme_eventually_etale_pullback E' sc hsc X hX

omit hD hQc hQs in
private theorem exists_finitePresentation_atlas_model_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (Y : Over (limit D)) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hf : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom) :
    let c := affineStageChartConeOfLimitFacts B S hS D
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (W : AlgebraicGeometry.BigAffineFppf B S hS) (w : yoneda.obj W.obj ⟶ Y.left)
      (g : W.obj ⟶ U.obj) (j : Over i)
      (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        (affineStageChartOfLimitFacts B S hS D i U₀ p₀ hAffine j).U.obj)),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w ∧
      yoneda.map g ≫ p = w ≫ Y.hom ∧ AlgebraicGeometry.FinitePresentation Wj.hom ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback
          ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (c.π.app j).left)).obj Wj) := by
  obtain ⟨W, w, g, hws, hwe, hw, hg⟩ := exists_affine_finitePresentation_chart B S hS
    (hFacts.limAlg) hY Y.hom hf U p hs he
  obtain ⟨j, Wj, hWj, hmodel⟩ := exists_model_over_affine_chart_of_limitFacts B S hS D hAffine
    hFacts i U₀ p₀ U p q hp W.obj g hg
  exact ⟨W, w, g, j, Wj, hws, hwe, hw, hWj, hmodel.2⟩

omit hQc hQs in
private theorem eventually_eq_on_quasiCompact_source_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i : I)
    {Y Z G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y)
    (r : Y ⟶ D.obj i) (a : Z ⟶ G) (b : D.obj i ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : Y ⟶ Z) (hf : f ≫ a = r ≫ b) (hg : g ≫ a = r ≫ b)
    (hfg : pullback.fst r (limit.π D i) ≫ f =
      pullback.fst r (limit.π D i) ≫ g) :
    ∃ (j : I) (e : j ⟶ i),
      pullback.fst r (D.map e) ≫ f = pullback.fst r (D.map e) ≫ g := by
  classical
  obtain ⟨U₀, q₀, hU₀, hsurj, het⟩ := exists_affine_etale_atlas B S hS Y hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hh : pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀ ≫ f =
      pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀ ≫ g := by
    let k : pullback (limit.π D i) (q₀ ≫ r) ⟶ pullback r (limit.π D i) :=
      pullback.lift (pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀)
      (pullback.fst (limit.π D i) (q₀ ≫ r))
      (by simp only [Category.assoc, pullback.condition])
    simpa [k] using congrArg (fun t => k ≫ t) hfg
  obtain ⟨j, hj⟩ := eventually_eq_on_affine_chart_over_of_limitFacts B S hS D hAffine
    hFacts i U (q₀ ≫ r) hG b hZalg a ha
    (q₀ ≫ f) (q₀ ≫ g) (by simp [hf]) (by simp [hg]) hh
  refine ⟨j.left, j.hom, ?_⟩
  let C := affineStageChartOfLimitFacts B S hS D i U (q₀ ≫ r) hAffine j
  obtain ⟨p, hp, hpsnd, hps, hpe⟩ := exists_etale_chart_pullback B S hS r (D.map j.hom) q₀
    C.toStage (yoneda.map C.toChart) C.isPullback hsurj
    (represented_etale_of_isEtale B S hS q₀ het)
  apply hom_ext_of_surjective_etale_atlas B S hS
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS r (D.map j.hom) hY (hD j.left) (hD i))
    hZalg.isSheaf p hps hpe
  rw [← hp.w_assoc, ← hp.w_assoc]
  exact hj

omit hQc hQs in
private theorem exists_stage_atlas_factorization_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i : I)
    (Y : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y.left)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : pullback Y.hom (limit.π D i) ⟶ Z)
    (hf : f ≫ a = pullback.fst Y.hom (limit.π D i) ≫ Y.hom) :
    ∃ (j : Over i) (U : AlgebraicGeometry.BigAffineFppf B S hS)
      (p : yoneda.obj U.obj ⟶ pullback Y.hom (D.map j.hom))
      (g : yoneda.obj U.obj ⟶ Z),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      g ≫ a = p ≫ pullback.snd Y.hom (D.map j.hom) ≫ D.map j.hom ∧
      pullback.fst (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ≫ g =
        pullback.lift
          (pullback.fst (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ≫ p)
          (pullback.snd (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left))
          (by simpa only [Over.pullback_obj_hom, Category.assoc] using
            (pullback.condition (f := p ≫ pullback.snd Y.hom (D.map j.hom))
              (g := limit.π D j.left))) ≫
        (iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
          (limit.w D j.hom) Y).hom.left ≫ f := by
  classical
  obtain ⟨U₀, q₀, hU₀, hs, he⟩ := exists_affine_etale_atlas B S hS Y.left hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  let k : pullback (limit.π D i) (q₀ ≫ Y.hom) ⟶ pullback Y.hom (limit.π D i) :=
    pullback.lift (pullback.snd _ _ ≫ q₀) (pullback.fst _ _)
      (by simp only [Category.assoc, pullback.condition])
  obtain ⟨j, g, hg, hgf⟩ := exists_hom_on_affine_chart_of_limitFacts B S hS D hD hAffine
    hFacts i U (q₀ ≫ Y.hom) hZalg a ha (k ≫ f) (by
      rw [Category.assoc, hf]
      simpa [k, Category.assoc] using (pullback.condition (f := limit.π D i)
        (g := q₀ ≫ Y.hom)).symm)
  let C := affineStageChartOfLimitFacts B S hS D i U (q₀ ≫ Y.hom) hAffine j
  obtain ⟨p, hp, hpsnd, hps, hpe⟩ := exists_etale_chart_pullback B S hS Y.hom (D.map j.hom) q₀
    C.toStage (yoneda.map C.toChart) C.isPullback hs (represented_etale_of_isEtale B S hS q₀ he)
  refine ⟨j, C.U, p, g, hps, hpe, by rw [reassoc_of% hpsnd]; exact hg, ?_⟩
  let v : pullback (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ⟶
      pullback (limit.π D i) (q₀ ≫ Y.hom) :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ yoneda.map C.toChart) (by
      simp only [Category.assoc]
      rw [← C.isPullback.w, ← limit.w D j.hom]
      simp only [← Category.assoc]
      congr 1
      rw [← hpsnd]
      exact pullback.condition.symm)
  let l := C.isPullback.lift
    (pullback.fst (limit.π D i) (q₀ ≫ Y.hom) ≫ limit.π D j.left)
    (pullback.snd (limit.π D i) (q₀ ≫ Y.hom))
    (by rw [Category.assoc, limit.w]; exact pullback.condition)
  have hv : v ≫ l = pullback.fst _ _ := by
    apply C.isPullback.hom_ext
    · simp only [Category.assoc, l, IsPullback.lift_fst, v, pullback.lift_fst_assoc]
      simpa [← hp.w, hpsnd, Category.assoc] using
        (pullback.condition (f := p ≫ pullback.snd Y.hom (D.map j.hom))
          (g := limit.π D j.left)).symm
    · simp [l, v]
  conv_lhs => rw [← hv, Category.assoc, hgf]
  simp only [← Category.assoc]
  apply congrArg (fun t => t ≫ f)
  apply pullback.hom_ext
  · simp [v, k, iteratedBaseChangeIso_hom_left, ← hp.w, Category.assoc]
  · simp [v, k, iteratedBaseChangeIso_hom_left, Category.assoc]

/-- A morphism between base changes of finite-presentation algebraic spaces
is defined at a sufficiently late stage. -/
theorem exists_morphism_after_baseChange_aux
    (hFacts : LimitFacts B S hS D)
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f : (Over.pullback (limit.π D i)).obj Yᵢ ⟶
      (Over.pullback (limit.π D i)).obj Zᵢ) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj Yᵢ ⟶
        (Over.pullback (D.map e)).obj Zᵢ)
      (α : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Yᵢ) ≅
        (Over.pullback (limit.π D i)).obj Yᵢ)
      (β : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Zᵢ) ≅
        (Over.pullback (limit.π D i)).obj Zᵢ),
      (α.hom.left ≫ pullback.fst Yᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Yᵢ).hom (limit.π D j) ≫
          pullback.fst Yᵢ.hom (D.map e)) ∧
      (β.hom.left ≫ pullback.fst Zᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Zᵢ).hom (limit.π D j) ≫
          pullback.fst Zᵢ.hom (D.map e)) ∧
      α.hom ≫ f = (Over.pullback (limit.π D j)).map g ≫ β.hom := by
  classical
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS Yᵢ.hom
    (hD i) (hQc i) hYfp
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hY (hQs i) hYfp.2.2
  let f₀ := f.left ≫ pullback.fst Zᵢ.hom (limit.π D i)
  have hf₀ : f₀ ≫ Zᵢ.hom = pullback.fst Yᵢ.hom (limit.π D i) ≫ Yᵢ.hom := by
    simp only [f₀, Category.assoc, pullback.condition]
    have hw : f.left ≫ pullback.snd Zᵢ.hom (limit.π D i) =
        pullback.snd Yᵢ.hom (limit.π D i) := f.w
    rw [← Category.assoc, hw]
  obtain ⟨j, U, p, g, hs, he, hg, hgf⟩ := exists_stage_atlas_factorization_of_limitFacts
    B S hS D hD hAffine hFacts i Yᵢ hY hYqc hZ' Zᵢ.hom hZfp.1 f₀ hf₀
  let Yj := (Over.pullback (D.map j.hom)).obj Yᵢ
  have hYj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom (D.map j.hom)
    hY (hD j.left) (hD i)
  have hYjqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_pullback
    B S hS hZ Yᵢ.hom (D.map j.hom) hY (hD j.left) (hD i) hYqs (hQs j.left)
  have hU := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U.obj
  have hUqc := isQuasiCompactSpace_yoneda_of_isAffine B S hS U.obj U.property
  have hR := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS p p hU hU hYj
  have hRqc := AlgebraicGeometry.Space.isQuasiCompactSpace_pullback
    B S hS hZ p p hU hYj hUqc hUqc hYjqs
  have hlim := equalizes_kernelPair_after_baseChange p Yj.hom (limit.π D j.left)
    ((iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
      (limit.w D j.hom) Yᵢ).hom.left ≫ f₀) g hgf
  obtain ⟨k, e, hkg⟩ := eventually_eq_on_quasiCompact_source_of_limitFacts B S hS D hD hAffine
    hFacts j.left hR hZ' (hD i) hRqc
    (pullback.fst p p ≫ p ≫ Yj.hom) Zᵢ.hom (D.map j.hom) hZfp.1
    (pullback.fst p p ≫ g) (pullback.snd p p ≫ g)
    (by simpa only [Yj, Over.pullback_obj_hom, Category.assoc] using
      congrArg (fun t => pullback.fst p p ≫ t) hg)
    (by simpa only [Yj, Over.pullback_obj_hom, Category.assoc, pullback.condition_assoc] using
      congrArg (fun t => pullback.snd p p ≫ t) hg) hlim
  let K := affineStageChartOfLimitFacts B S hS D j.left U (p ≫ Yj.hom) hAffine (Over.mk e)
  let Yk := (Over.pullback (D.map e)).obj Yj
  obtain ⟨pK, hpK, hpKsnd, hKs, hKe⟩ := exists_etale_chart_pullback B S hS Yj.hom (D.map e) p
    K.toStage (yoneda.map K.toChart) K.isPullback hs he
  have hYk := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom (D.map e)
    hYj (hD k) (hD j.left)
  obtain ⟨gK, hgK⟩ := exists_hom_of_equalizes_atlas B S hS hYk hZ'.isSheaf pK hKs hKe
    (yoneda.map K.toChart ≫ g)
    (equalizes_kernelPair_of_baseChange_eq p Yj.hom (D.map e)
      (pullback.fst Yj.hom (D.map e)) (pullback.snd Yj.hom (D.map e)) pullback.condition
      (yoneda.map K.toChart) pK hpK.w g hkg)
  have hgKa : gK ≫ Zᵢ.hom = Yk.hom ≫ D.map e ≫ D.map j.hom := by
    apply hom_ext_of_surjective_etale_atlas B S hS hYk (hD i).isSheaf pK hKs hKe
    rw [← Category.assoc, hgK, Category.assoc, hg]
    simp only [Yj, Over.pullback_obj_hom] at hpKsnd
    have hw := congrArg (fun t => t ≫ D.map j.hom) K.isPullback.w
    simpa only [Yj, Yk, Over.pullback_obj_hom, reassoc_of% hpKsnd,
      Over.mk_hom, Category.assoc] using hw.symm
  let d := e ≫ j.hom
  let η := iteratedBaseChangeIso (D.map j.hom) (D.map e) (D.map d)
    (D.map_comp e j.hom).symm Yᵢ
  let raw : pullback Yᵢ.hom (D.map d) ⟶ Zᵢ.left := η.inv.left ≫ gK
  have hrawa : raw ≫ Zᵢ.hom = pullback.snd Yᵢ.hom (D.map d) ≫ D.map d := by
    dsimp only [raw]
    rw [Category.assoc, hgKa]
    simpa only [d, Yk, Yj, Over.pullback_obj_hom, Functor.map_comp, Category.assoc] using
      congrArg (fun t => t ≫ D.map d) (Over.w η.inv)
  let g' : (Over.pullback (D.map d)).obj Yᵢ ⟶ (Over.pullback (D.map d)).obj Zᵢ :=
    Over.homMk (pullback.lift raw (pullback.snd Yᵢ.hom (D.map d)) hrawa) (by simp)
  let α := iteratedBaseChangeIso (D.map d) (limit.π D k) (limit.π D i) (limit.w D d) Yᵢ
  let β := iteratedBaseChangeIso (D.map d) (limit.π D k) (limit.π D i) (limit.w D d) Zᵢ
  let m : pullback Yᵢ.hom (limit.π D i) ⟶ pullback Yᵢ.hom (D.map d) :=
    pullback.lift (pullback.fst Yᵢ.hom (limit.π D i))
      (pullback.snd Yᵢ.hom (limit.π D i) ≫ limit.π D k)
      (by rw [Category.assoc, limit.w]; exact pullback.condition)
  have hraw : m ≫ raw = f₀ := by
    let A := iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
      (limit.w D j.hom) Yᵢ
    let q : pullback (p ≫ Yj.hom) (limit.π D j.left) ⟶ pullback Yj.hom (limit.π D j.left) :=
      pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _)
        (by simp only [Category.assoc, pullback.condition])
    have hq : IsPullback (pullback.fst (p ≫ Yj.hom) (limit.π D j.left)) q p
        (pullback.fst Yj.hom (limit.π D j.left)) := by
      apply IsPullback.of_bot _ (by simp [q]) (IsPullback.of_hasPullback Yj.hom (limit.π D j.left))
      simpa [q] using IsPullback.of_hasPullback (p ≫ Yj.hom) (limit.π D j.left)
    let l : pullback (p ≫ Yj.hom) (limit.π D j.left) ⟶ yoneda.obj K.U.obj :=
      K.isPullback.lift (pullback.snd _ _ ≫ limit.π D k) (pullback.fst _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition.symm)
    have hl : q ≫ A.hom.left ≫ m ≫ η.inv.left = l ≫ pK := by
      have e₁ := hpK.w.symm
      simp only [Yj, Over.pullback_obj_hom] at e₁ hpKsnd
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [Yj, q, A, m, η, l, e₁, iteratedBaseChangeIso_hom_left,
            iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc]
        · simp [Yj, q, A, m, η, l, e₁, iteratedBaseChangeIso_hom_left,
            iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc, limit.w,
            pullback.condition]
      · simp [Yj, q, A, m, η, l, hpKsnd, iteratedBaseChangeIso_hom_left,
          iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc]
    have hqse := presheaf_surjective_etale_of_isPullback B S hS hq hs he
    have hEq : q ≫ A.hom.left ≫ (m ≫ raw) = q ≫ A.hom.left ≫ f₀ := by
      change q ≫ A.hom.left ≫ m ≫ η.inv.left ≫ gK = _
      have hh := congrArg (fun t => t ≫ gK) hl
      simp only [Category.assoc, hgK] at hh
      rw [hh]
      simpa [l, Category.assoc, q, A, Yj] using hgf
    obtain ⟨V, v, w, hV⟩ := hFacts.piAff j.left U (p ≫ Yj.hom)
    let vq := hV.flip.isoPullback.hom ≫ q
    have hEq' : A.hom.left ≫ (m ≫ raw) = A.hom.left ≫ f₀ := by
      apply hom_ext_of_surjective_etale_atlas B S hS
        (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom (limit.π D j.left)
          hYj (hFacts.limAlg) (hD j.left))
        hZ'.isSheaf vq
        (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q hqse.1)
        (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q hqse.2)
      simpa only [vq, Category.assoc] using
        congrArg (fun t => hV.flip.isoPullback.hom ≫ t) hEq
    let : IsIso A.hom.left :=
      inferInstanceAs (IsIso ((Over.forget (limit D)).map A.hom))
    exact (cancel_epi A.hom.left).mp hEq'
  refine ⟨k, d, g', α, β, iteratedBaseChangeIso_hom_fst _ _ _ _ _,
    iteratedBaseChangeIso_hom_fst _ _ _ _ _, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hm :
        α.hom.left ≫ m = pullback.fst ((Over.pullback (D.map d)).obj Yᵢ).hom (limit.π D k) := by
      apply pullback.hom_ext <;>
        simp [α, m, iteratedBaseChangeIso_hom_left, Category.assoc, pullback.condition]
    have hh := congrArg (fun t => α.hom.left ≫ t) hraw
    rw [← Category.assoc α.hom.left m raw, hm] at hh
    simpa [g', f₀, Category.assoc, β, iteratedBaseChangeIso_hom_left,
      iteratedBaseChangeIso_inv_left, Over.pullback_map_left] using hh.symm
  · simpa only [Over.comp_left, Over.pullback_obj_hom] using
      (Over.w (α.hom ≫ f)).trans
        (Over.w ((Over.pullback (limit.π D k)).map g' ≫ β.hom)).symm

omit hQs in
/-- Two finite-stage morphisms that agree over the limit agree at a sufficiently
late stage. -/
theorem eventually_eq_of_baseChange_eq_aux
    (hFacts : LimitFacts B S hS D)
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f g : Yᵢ ⟶ Zᵢ)
    (hfg : (Over.pullback (limit.π D i)).map f =
      (Over.pullback (limit.π D i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map f =
        (Over.pullback (D.map e)).map g := by
  classical
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS Yᵢ.hom
    (hD i) (hQc i) hYfp
  obtain ⟨U₀, q₀, hU₀, hsurj, het⟩ := exists_affine_etale_atlas B S hS Yᵢ.left hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hf : (q₀ ≫ f.left) ≫ Zᵢ.hom = q₀ ≫ Yᵢ.hom := by simp
  have hg : (q₀ ≫ g.left) ≫ Zᵢ.hom = q₀ ≫ Yᵢ.hom := by simp
  obtain ⟨j, hj⟩ := eventually_eq_on_affine_chart_of_limitFacts B S hS D hD hAffine
    hFacts i U (q₀ ≫ Yᵢ.hom) hZ' Zᵢ.hom hZfp.1
    (q₀ ≫ f.left) (q₀ ≫ g.left) hf hg
    (precomp_eq_of_baseChange_eq (limit.π D i) Yᵢ Zᵢ f g hfg q₀)
  refine ⟨j.left, j.hom, ?_⟩
  let C := affineStageChartOfLimitFacts B S hS D i U (q₀ ≫ Yᵢ.hom) hAffine j
  obtain ⟨p, hp, -, hps, hpe⟩ := exists_etale_chart_pullback B S hS Yᵢ.hom (D.map j.hom) q₀
    C.toStage (yoneda.map C.toChart) C.isPullback hsurj
    (represented_etale_of_isEtale B S hS q₀ het)
  have heq : pullback.fst Yᵢ.hom (D.map j.hom) ≫ f.left =
      pullback.fst Yᵢ.hom (D.map j.hom) ≫ g.left := by
    apply hom_ext_of_surjective_etale_atlas B S hS
      (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom (D.map j.hom)
        hY (hD j.left) (hD i)) hZ'.isSheaf p hps hpe
    rw [← hp.w_assoc, ← hp.w_assoc]
    exact hj
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa [Over.pullback_map_left] using heq
  · simp [Over.pullback_map_left]

theorem exists_isIso_after_baseChange_of_limitFacts
    (hFacts : LimitFacts B S hS D)
    (i : I) (Y Z : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Z.hom)
    (f : Y ⟶ Z) [IsIso ((Over.pullback (limit.π D i)).map f)] :
    ∃ (j : I) (e : j ⟶ i), IsIso ((Over.pullback (D.map e)).map f) := by
  classical
  let f₀ := (Over.pullback (limit.π D i)).map f
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ := exists_morphism_after_baseChange_aux
    B S hS hZ D hD hAffine hQc hQs hFacts i Z Y hZ' hY hZfp hYfp (inv f₀)
  have hn := pullback_map_comp_iso_hom (D.map e) (limit.π D j) (limit.π D i) (limit.w D e) f β α
    hβ hα
  let Yj := (Over.pullback (D.map e)).obj Y
  let Zj := (Over.pullback (D.map e)).obj Z
  let fj := (Over.pullback (D.map e)).map f
  obtain ⟨hYj, hYjfp⟩ := isFinitePresentation_pullback_snd B S hS Y.hom (D.map e) hY (hD j)
    (hD i) hYfp
  obtain ⟨hZj, hZjfp⟩ := isFinitePresentation_pullback_snd B S hS Z.hom (D.map e) hZ' (hD j)
    (hD i) hZfp
  have hfg : (Over.pullback (limit.π D j)).map (fj ≫ g) =
      (Over.pullback (limit.π D j)).map (𝟙 Yj) := by
    apply (Iso.cancel_iso_hom_right _ _ β).mp
    simp only [Yj, Functor.map_comp]
    rw [Category.assoc, ← hg, ← Category.assoc, hn, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
    rw [(Over.pullback (limit.π D j)).map_id Yj, Category.id_comp]
  have hgf : (Over.pullback (limit.π D j)).map (g ≫ fj) =
      (Over.pullback (limit.π D j)).map (𝟙 Zj) := by
    apply (Iso.cancel_iso_hom_right _ _ α).mp
    simp only [Zj, Functor.map_comp]
    rw [Category.assoc, hn, ← Category.assoc, ← hg, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
    rw [(Over.pullback (limit.π D j)).map_id Zj, Category.id_comp]
  obtain ⟨k, e', hk₁, hk₂⟩ := exists_common_stage_baseChange_eq D
    (eventually_eq_of_baseChange_eq_aux B S hS D hD hAffine hQc hFacts j Yj Yj hYj hYj hYjfp
      hYjfp (fj ≫ g) (𝟙 Yj) hfg)
    (eventually_eq_of_baseChange_eq_aux B S hS D hD hAffine hQc hFacts j Zj Zj hZj hZj hZjfp
      hZjfp (g ≫ fj) (𝟙 Zj) hgf)
  let : IsIso ((Over.pullback (D.map e')).map fj) :=
    ⟨⟨(Over.pullback (D.map e')).map g,
      by simpa only [Functor.map_comp] using hk₁.trans ((Over.pullback (D.map e')).map_id Yj),
      by simpa only [Functor.map_comp] using hk₂.trans ((Over.pullback (D.map e')).map_id Zj)⟩⟩
  refine ⟨k, e' ≫ e, ?_⟩
  have h := iteratedBaseChangeIso_naturality (D.map e) (D.map e')
    (D.map (e' ≫ e)) (D.map_comp _ _).symm f
  have hf' : (Over.pullback (D.map (e' ≫ e))).map f =
      (iteratedBaseChangeIso (D.map e) (D.map e') (D.map (e' ≫ e))
        (D.map_comp _ _).symm Y).inv ≫
      (Over.pullback (D.map e')).map fj ≫
      (iteratedBaseChangeIso (D.map e) (D.map e') (D.map (e' ≫ e))
        (D.map_comp _ _).symm Z).hom := by
    rw [show fj = (Over.pullback (D.map e)).map f from rfl, h, Iso.inv_hom_id_assoc]
  rw [hf']
  infer_instance

theorem exists_mono_after_baseChange_of_limitFacts
    (hFacts : LimitFacts B S hS D)
    (i : I) (Y Z : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Z.hom)
    (f : Y ⟶ Z) [Mono ((Over.pullback (limit.π D i)).map f)] :
    ∃ (j : I) (e : j ⟶ i), Mono ((Over.pullback (D.map e)).map f) := by
  let c := overPullbackCone f f
  have hc := overPullbackCone_isPullback f f
  have hf := isFinitePresentation_overHom B S hS hZ (hD i) (hQc i) (hQs i)
    Y Z hY hZ' hYfp hZfp f
  have hR : AlgebraicGeometry.IsAlgebraicSpace B S hS c.pt.left :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f.left f.left hY hY hZ'
  have hRfst := isFinitePresentation_of_isPullback B S hS hR hY hY hZ'
    (IsPullback.of_hasPullback f.left f.left).flip hf
  have hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS c.pt.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hR hY (hD i)
      (pullback.fst f.left f.left) Y.hom hRfst hYfp
  have heq : (Over.pullback (limit.π D i)).map c.fst =
      (Over.pullback (limit.π D i)).map c.snd := by
    apply (cancel_mono ((Over.pullback (limit.π D i)).map f)).mp
    rw [← Functor.map_comp, ← Functor.map_comp, c.condition]
  obtain ⟨j, e, hj⟩ := eventually_eq_of_baseChange_eq_aux B S hS D hD hAffine hQc
    hFacts i c.pt Y hR hY hRfp hYfp c.fst c.snd heq
  exact ⟨j, e, IsKernelPair.mono_of_eq_fst_snd (hc.map (Over.pullback (D.map e))) hj⟩

theorem exists_lift_pair_after_baseChange_of_limitFacts
    (hFacts : LimitFacts B S hS D)
    (i : I) (A R W : Over (D.obj i))
    (hA : AlgebraicGeometry.IsAlgebraicSpace B S hS A.left)
    (hR : AlgebraicGeometry.IsAlgebraicSpace B S hS R.left)
    (hW : AlgebraicGeometry.IsAlgebraicSpace B S hS W.left)
    (hAfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS A.hom)
    (hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS R.hom)
    (hWfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS W.hom)
    (s t : R ⟶ W) (a b : A ⟶ W)
    (u : (Over.pullback (limit.π D i)).obj A ⟶ (Over.pullback (limit.π D i)).obj R)
    (hu₁ : u ≫ (Over.pullback (limit.π D i)).map s = (Over.pullback (limit.π D i)).map a)
    (hu₂ : u ≫ (Over.pullback (limit.π D i)).map t = (Over.pullback (limit.π D i)).map b) :
    ∃ (j : I) (e : j ⟶ i)
      (v : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj R),
      v ≫ (Over.pullback (D.map e)).map s = (Over.pullback (D.map e)).map a ∧
      v ≫ (Over.pullback (D.map e)).map t = (Over.pullback (D.map e)).map b := by
  classical
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ := exists_morphism_after_baseChange_aux
    B S hS hZ D hD hAffine hQc hQs hFacts i A R hA hR hAfp hRfp u
  let γ := iteratedBaseChangeIso (D.map e) (limit.π D j) (limit.π D i) (limit.w D e) W
  have heq (v : R ⟶ W) (z : A ⟶ W)
      (hz : u ≫ (Over.pullback (limit.π D i)).map v = (Over.pullback (limit.π D i)).map z) :
      (Over.pullback (limit.π D j)).map (g ≫ (Over.pullback (D.map e)).map v) =
        (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map z) := by
    have hv := pullback_map_comp_iso_hom (D.map e) (limit.π D j) (limit.π D i) (limit.w D e) v β γ
      hβ (iteratedBaseChangeIso_hom_fst _ _ _ _ _)
    have hz' := pullback_map_comp_iso_hom (D.map e) (limit.π D j) (limit.π D i) (limit.w D e) z α γ
      hα (iteratedBaseChangeIso_hom_fst _ _ _ _ _)
    apply (Iso.cancel_iso_hom_right _ _ γ).mp
    rw [Functor.map_comp, Category.assoc, hv, ← Category.assoc, ← hg,
      Category.assoc, hz, hz']
  let Aj := (Over.pullback (D.map e)).obj A
  let Wj := (Over.pullback (D.map e)).obj W
  obtain ⟨hAj, hAjfp⟩ := isFinitePresentation_pullback_snd B S hS A.hom (D.map e) hA (hD j)
    (hD i) hAfp
  obtain ⟨hWj, hWjfp⟩ := isFinitePresentation_pullback_snd B S hS W.hom (D.map e) hW (hD j)
    (hD i) hWfp
  obtain ⟨k, e', hk₁, hk₂⟩ := exists_common_stage_baseChange_eq D
    (eventually_eq_of_baseChange_eq_aux B S hS D hD hAffine hQc hFacts j Aj Wj hAj hWj hAjfp
      hWjfp (g ≫ (Over.pullback (D.map e)).map s) ((Over.pullback (D.map e)).map a) (heq s a hu₁))
    (eventually_eq_of_baseChange_eq_aux B S hS D hD hAffine hQc hFacts j Aj Wj hAj hWj hAjfp
      hWjfp (g ≫ (Over.pullback (D.map e)).map t) ((Over.pullback (D.map e)).map b) (heq t b hu₂))
  let δ (Z : Over (D.obj i)) := iteratedBaseChangeIso (D.map e) (D.map e')
    (D.map (e' ≫ e)) (D.map_comp _ _).symm Z
  let v := (δ A).inv ≫ (Over.pullback (D.map e')).map g ≫ (δ R).hom
  have hfinal (x : R ⟶ W) (z : A ⟶ W)
      (hx : (Over.pullback (D.map e')).map (g ≫ (Over.pullback (D.map e)).map x) =
        (Over.pullback (D.map e')).map ((Over.pullback (D.map e)).map z)) :
      v ≫ (Over.pullback (D.map (e' ≫ e))).map x =
        (Over.pullback (D.map (e' ≫ e))).map z := by
    have hn := iteratedBaseChangeIso_naturality (D.map e) (D.map e')
      (D.map (e' ≫ e)) (D.map_comp _ _).symm x
    have hz' := iteratedBaseChangeIso_naturality (D.map e) (D.map e')
      (D.map (e' ≫ e)) (D.map_comp _ _).symm z
    calc
      v ≫ (Over.pullback (D.map (e' ≫ e))).map x =
          (δ A).inv ≫ (Over.pullback (D.map e')).map g ≫
            (Over.pullback (D.map e')).map ((Over.pullback (D.map e)).map x) ≫
            (δ W).hom := by
        simp only [v, Category.assoc]
        rw [← hn]
      _ = (δ A).inv ≫ (Over.pullback (D.map e')).map
          ((Over.pullback (D.map e)).map z) ≫ (δ W).hom := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun z => (δ A).inv ≫ z ≫ (δ W).hom) hx
      _ = (Over.pullback (D.map (e' ≫ e))).map z := by
        rw [hz', Iso.inv_hom_id_assoc]
  exact ⟨k, e' ≫ e, v, hfinal s a hk₁, hfinal t b hk₂⟩

end AlgebraicGeometry.Space

end
