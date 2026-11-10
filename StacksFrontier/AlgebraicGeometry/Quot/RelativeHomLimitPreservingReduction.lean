module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreservingCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAffineGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability

/-!
# Stacks 08K4 reduced to an affine source over an affine base

The proof of Stacks 08K4 has three steps.  This file performs the first two, so that what is
left is the affine case, Algebra, Lemma 05LI.

* **Change of base to a stage** (Stacks 08JW).  Given a directed limit `T = lim T_i` of affine
  test schemes, pick an index `0`; the test schemes over `T_0` are the test schemes of the
  situation base changed to `T_0`, whose relative Hom functor is that of the given situation by
  `AlgebraicGeometry.Space.HomSituation.homFunctorBaseChange`.  So `Hom(F, G)` is limit
  preserving as soon as the relative Hom functor of every base change to an affine test scheme
  is: `AlgebraicGeometry.Space.HomSituation.limitPreserving_homFunctor_of_stages`.
* **Two affine charts** (Stacks 03H6 and 08K3).  Over an affine base the source `X` of a
  quasi-compact and quasi-separated morphism is quasi-compact and quasi-separated; choose an
  affine scheme `U` surjective and étale over `X` and an affine scheme `V` surjective and étale
  over `U ×_X U`, which is quasi-compact because `X` is quasi-separated.  Then `Hom(F, G)` is
  the equalizer of the two restrictions between the relative Hom functors of `U` and of `V`
  (`AlgebraicGeometry.Space.HomSituation.limitPreserving_homFunctor_of_charts`), both of which
  are relative Hom functors of a situation whose source and base are affine schemes:
  `AlgebraicGeometry.Space.HomSituation.limitPreserving_homFunctor_of_affineBase`.

## Main results

* `AlgebraicGeometry.nonempty_isColimit_mapCocone_of_overStage`: the formal transport of a
  colimit presentation along a change of indexing category to the stages over a chosen stage
  and a comparison of presheaves.
* `AlgebraicGeometry.Space.HomSituation.limitPreserving_homFunctor_of_stages`: the change of
  base to the stages.
* `AlgebraicGeometry.Space.HomSituation.limitPreserving_homFunctor_of_affineBase`: the chart
  step over an affine base.
* `AlgebraicGeometry.Space.HomSituation.limitPreserving_homFunctor_of_affineCase`: **Stacks
  08K4 reduced to the affine case**, the affine case being the hypothesis.

## References

* [Stacks Project, Tag 08K4](https://stacks.math.columbia.edu/tag/08K4)
* [Stacks Project, Tag 08JW](https://stacks.math.columbia.edu/tag/08JW)
* [Stacks Project, Tag 08K3](https://stacks.math.columbia.edu/tag/08K3)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w' z y

namespace AlgebraicGeometry

/-! ### Transport of a colimit presentation to the stages over a chosen stage -/

section Transport

variable {C : Type z} [Category.{y} C] {C' : Type z} [Category.{y} C']
  {P : Cᵒᵖ ⥤ Type v} {P' : C'ᵒᵖ ⥤ Type v} (Φ : C' ⥤ C) (e : P' ≅ Φ.op ⋙ P)
  {I : Type w} [Category.{w'} I] [IsCofiltered I] (E : I ⥤ C) (c : Cone E) (i₀ : I)
  (E' : Over i₀ ⥤ C') (c' : Cone E') (ψ : E' ⋙ Φ ≅ Over.forget i₀ ⋙ E)
  (φ : Φ.obj c'.pt ≅ c.pt)
  (hφ : ∀ A : Over i₀, Φ.map (c'.π.app A) ≫ ψ.hom.app A = φ.hom ≫ c.π.app A.left)

include e hφ in
/-- **A colimit presentation transports to the stages over a chosen stage.**  Let `P'` be
identified with `P` through a functor `Φ`, let `E'` be a diagram indexed by the stages over
`i₀` of a cofiltered diagram `E` whose image under `Φ` is identified with `E` there, and let
`c'` be a cone on `E'` whose image under `Φ` is identified with a cone `c` on `E`, compatibly.
If `P'` turns `c'` into a colimit cocone then `P` turns `c` into one. -/
theorem nonempty_isColimit_mapCocone_of_overStage (h : IsColimit (P'.mapCocone c'.op)) :
    Nonempty (IsColimit (P.mapCocone c.op)) := by
  have nat : ∀ {X Y : C'} (k : X ⟶ Y) (z : P'.obj (op Y)),
      e.hom.app (op X) (P'.map k.op z) = P.map (Φ.map k).op (e.hom.app (op Y) z) :=
    fun k z ↦ NatTrans.naturality_apply e.hom k.op z
  have comp : ∀ {X Y Z : C} (k : X ⟶ Y) (l : Y ⟶ Z) (z : P.obj (op Z)),
      P.map k.op (P.map l.op z) = P.map (k ≫ l).op z := fun k l z ↦ by
    rw [op_comp, Functor.map_comp_apply]
  have hinv : ∀ {X : C'} (z : P.obj (op (Φ.obj X))), e.hom.app (op X) (e.inv.app (op X) z) = z :=
    fun z ↦ Iso.inv_hom_id_apply (e.app _) z
  have hφ' : ∀ A : Over i₀, c.π.app A.left ≫ ψ.inv.app A = φ.inv ≫ Φ.map (c'.π.app A) := by
    intro A
    rw [← cancel_mono (ψ.hom.app A), Category.assoc, Category.assoc, hφ, Iso.inv_hom_id_app,
      Iso.inv_hom_id_assoc]
    exact Category.comp_id _
  refine nonempty_isColimit_mapCocone_of_exists_of_eventually_eq P E c ?_ ?_
  · intro x
    obtain ⟨A, y', hy'⟩ := exists_eq_map_of_isColimit_mapCocone P' E' c' h
      (e.inv.app (op c'.pt) (P.map φ.hom.op x))
    refine ⟨A.left, P.map (ψ.inv.app A).op (e.hom.app (op (E'.obj A)) y'), ?_⟩
    have h₁ : e.hom.app (op c'.pt) (P'.map (c'.π.app A).op y') = P.map φ.hom.op x := by
      rw [hy', hinv]
    rw [comp, hφ', ← comp, ← nat, h₁, comp, Iso.inv_hom_id]
    simp
  · intro i x y hxy
    let j₀ := IsCofiltered.min i i₀
    let f₁ : j₀ ⟶ i := IsCofiltered.minToLeft i i₀
    let A : Over i₀ := Over.mk (IsCofiltered.minToRight i i₀)
    let tr : P.obj (op (E.obj i)) → P'.obj (op (E'.obj A)) := fun z ↦
      e.inv.app (op (E'.obj A)) (P.map (ψ.hom.app A).op (P.map (E.map f₁).op z))
    have htr : ∀ z, e.hom.app (op c'.pt) (P'.map (c'.π.app A).op (tr z)) =
        P.map φ.hom.op (P.map (c.π.app i).op z) := by
      intro z
      rw [nat, hinv]
      simp only [comp]
      rw [reassoc_of% (hφ A)]
      exact congrArg (fun k ↦ P.map (φ.hom ≫ k).op z) (c.w f₁)
    have hinj : Function.Injective (e.hom.app (op c'.pt)) := (e.app (op c'.pt)).toEquiv.injective
    have hxy' : P'.map (c'.π.app A).op (tr x) = P'.map (c'.π.app A).op (tr y) :=
      hinj ((htr x).trans ((congrArg (P.map φ.hom.op) hxy).trans (htr y).symm))
    obtain ⟨A', g, hg⟩ := eventually_eq_of_isColimit_mapCocone P' E' c' h A (tr x) (tr y) hxy'
    refine ⟨A'.left, g.left ≫ f₁, ?_⟩
    have hn : Φ.map (E'.map g) ≫ ψ.hom.app A = ψ.hom.app A' ≫ E.map g.left :=
      ψ.hom.naturality g
    have key : ∀ z, e.hom.app (op (E'.obj A')) (P'.map (E'.map g).op (tr z)) =
        P.map (ψ.hom.app A').op (P.map (E.map (g.left ≫ f₁)).op z) := by
      intro z
      rw [nat, hinv]
      simp only [comp]
      rw [reassoc_of% hn, ← E.map_comp]
    have h₃ := (key x).symm.trans ((congrArg (e.hom.app (op (E'.obj A'))) hg).trans (key y))
    simpa only [comp, Iso.inv_hom_id_app_assoc] using congrArg (P.map (ψ.inv.app A').op) h₃

end Transport

namespace Space.HomSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The change of base to a stage -/

section Stages

variable (s : HomSituation B S hS)

/-- **A test scheme over a chosen test scheme `T₀`, read as a test scheme of the situation base
changed to `T₀`.**  The underlying object of the big fppf category is unchanged; the structure
morphism to the new base is the image of the morphism to `T₀`. -/
def overStageSection (T₀ : s.SchemesOver) :
    Over T₀ ⥤ (s.baseChangedSituation T₀.hom).SchemesOver where
  obj A := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map A.hom.left)
  map {A A'} k := CostructuredArrow.homMk k.left.left (by
    have h : k.left.left ≫ A'.hom.left = A.hom.left :=
      congrArg (fun g : A.left ⟶ T₀ => g.left) (Over.w k)
    change (schemeSpaceFunctor B S hS).map k.left.left ≫
      (schemeSpaceFunctor B S hS).map A'.hom.left =
        (schemeSpaceFunctor B S hS).map A.hom.left
    rw [← Functor.map_comp, h])
  map_id A := by apply CostructuredArrow.hom_ext; rfl
  map_comp k k' := by apply CostructuredArrow.hom_ext; rfl

/-- Reading a test scheme over `T₀` as a test scheme of the base change and then back over the
base returns it, up to the identity of its underlying object. -/
def overStageSectionIso (T₀ : s.SchemesOver) :
    s.overStageSection T₀ ⋙ CostructuredArrow.map T₀.hom ≅ Over.forget T₀ :=
  NatIso.ofComponents
    (fun A ↦ CostructuredArrow.isoMk (Iso.refl _) (by
      change (schemeSpaceFunctor B S hS).map (𝟙 _) ≫ A.left.hom =
        (schemeSpaceFunctor B S hS).map A.hom.left ≫ T₀.hom
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
      exact (CostructuredArrow.w A.hom).symm))
    (fun {A A'} k ↦ CostructuredArrow.hom_ext _ _ (by
      change k.left.left ≫ 𝟙 _ = 𝟙 _ ≫ k.left.left
      rw [Category.comp_id, Category.id_comp]))

/-- **The change of base to the stages, Stacks 08JW in the proof of Stacks 08K4.**  The
relative Hom functor is limit preserving as soon as the relative Hom functor of its base change
to every affine test scheme is. -/
theorem limitPreserving_homFunctor_of_stages
    (h : ∀ T₀ : s.SchemesOver, IsAffine ((BigFppfOver.toScheme B S hS).obj T₀.left) →
      LimitPreserving.{u, u + 1, u, u} (s.baseChangedSituation T₀.hom).testSchemeFunctor
        ((s.baseChangedSituation T₀.hom).homFunctor (modulePushforwardCoherence B S hS))) :
    LimitPreserving.{u, u + 1, u, u} s.testSchemeFunctor
      (s.homFunctor (modulePushforwardCoherence B S hS)) := by
  intro I _ _ E c hc hE hpt
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  set T₀ := E.obj i₀
  let K : Cone (Over.post E : Over i₀ ⥤ Over T₀) :=
    { pt := Over.mk (c.π.app i₀)
      π :=
        { app := fun A => Over.homMk (c.π.app A.left) (c.w A.hom)
          naturality := fun A A' k => by
            apply Over.OverMorphism.ext
            change 𝟙 c.pt ≫ c.π.app A'.left = c.π.app A.left ≫ E.map k.left
            rw [Category.id_comp, c.w k.left] } }
  let E' := Over.post E ⋙ s.overStageSection T₀
  let c' := (s.overStageSection T₀).mapCone K
  have hc' : IsLimit ((s.baseChangedSituation T₀.hom).testSchemeFunctor.mapCone c') :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) (s.testSchemeFunctor.mapCone c)).symm hc
  obtain ⟨hcol⟩ := h T₀ (hE i₀) (Over i₀) E' c' hc' (fun A => hE A.left) hpt
  refine nonempty_isColimit_mapCocone_of_overStage (CostructuredArrow.map T₀.hom)
    (s.homFunctorBaseChange T₀.hom) E c i₀ E' c'
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (Over.post E) (s.overStageSectionIso T₀))
    (CostructuredArrow.isoMk (Iso.refl _) ?_) ?_ hcol
  · change (schemeSpaceFunctor B S hS).map (𝟙 _) ≫ c.pt.hom =
      (schemeSpaceFunctor B S hS).map (c.π.app i₀).left ≫ T₀.hom
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact (CostructuredArrow.w (c.π.app i₀)).symm
  · intro A
    refine CostructuredArrow.hom_ext _ _ ?_
    change (c.π.app A.left).left ≫ 𝟙 _ = 𝟙 _ ≫ (c.π.app A.left).left
    rw [Category.comp_id, Category.id_comp]

end Stages

/-! ### The chart step over an affine base -/

section AffineBase

/-- A quasi-compact algebraic space has an affine étale surjective chart from the site. -/
private theorem exists_affine_etale_surjective_chart (X : AlgebraicSpaces B S hS)
    (h : IsQuasiCompactSpace B S hS X.1) :
    ∃ (U : BigFppfOver B S hS) (a : (schemeSpaceFunctor B S hS).obj U ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧ IsEtale B S hS a.hom ∧
        IsSurjective B S hS a.hom := by
  obtain ⟨U, p, hU, hpsurj, hpet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 h
  exact ⟨U, ObjectProperty.homMk p, hU, hpet,
    (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U p).1 hpsurj⟩

/-- **The chart step of Stacks 08K4 over an affine base.**  Let `f : X ⟶ T₀` be a quasi-compact
and quasi-separated morphism to the algebraic space of an affine scheme `T₀` of the site, and let
`F` be of finite presentation.  Then the relative Hom functor is limit preserving as soon as the
relative Hom functor of every situation whose source is an affine scheme over `T₀` and whose
source module is of finite presentation is. -/
theorem limitPreserving_homFunctor_of_affineBase {T₀ : BigFppfOver B S hS}
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (X : AlgebraicSpaces B S hS) (f : X ⟶ (schemeSpaceFunctor B S hS).obj T₀)
    (F G : Modules.{u, u} B S hS X.1 X.2) (hFq : F.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (hF : F.IsFinitePresentationOnSite)
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    (haff : ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ (fU : (schemeSpaceFunctor B S hS).obj U ⟶ (schemeSpaceFunctor B S hS).obj T₀)
        (F' G' : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
          ((schemeSpaceFunctor B S hS).obj U).2)
        (hF'q : F'.IsQuasicoherentOnSite) (hG'q : G'.IsQuasicoherentOnSite),
        F'.IsFinitePresentationOnSite →
          LimitPreserving.{u, u + 1, u, u}
            (HomSituation.mk _ _ fU F' G' hF'q hG'q).testSchemeFunctor
            ((HomSituation.mk _ _ fU F' G' hF'q hG'q).homFunctor
              (modulePushforwardCoherence B S hS))) :
    LimitPreserving.{u, u + 1, u, u}
      (HomSituation.mk X _ f F G hFq hGq).testSchemeFunctor
      ((HomSituation.mk X _ f F G hFq hGq).homFunctor (modulePushforwardCoherence B S hS)) := by
  set s : HomSituation B S hS := HomSituation.mk X _ f F G hFq hGq with hs
  have hT₀sp : IsAffineSpace B S hS (yoneda.obj T₀) := ⟨T₀, hT₀, ⟨Iso.refl _⟩⟩
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS f.hom hT₀sp hqc
  obtain ⟨U, a, hU, hpet, ha'⟩ := exists_affine_etale_surjective_chart X hXqc
  have hUqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS U hU
  have hpf : IsQuasiCompact B S hS (a.hom ≫ f.hom) :=
    isQuasiCompact_yoneda_of_isAffine B S hS (a.hom ≫ f.hom) hU hT₀
  have hRqc :=
    isQuasiCompactSpace_selfPullback B S hS a.hom f.hom (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS T₀) hUqc hqs hpf
  let R := overlapSpace (fun _ : PUnit.{1} ↦ a) PUnit.unit PUnit.unit
  obtain ⟨V, b, hV, hqet, hb'⟩ := exists_affine_etale_surjective_chart R hRqc
  refine s.limitPreserving_homFunctor_of_charts a b hpet ha' hqet hb' ?_ ?_
  · exact haff U hU (a ≫ f) _ _ _ _
      (isFinitePresentationOnSite_modulePullback B S hS a F hF)
  · exact haff V hV ((b ≫ overlapFst (fun _ : PUnit.{1} ↦ a) PUnit.unit PUnit.unit ≫ a) ≫ f)
      _ _ _ _ (isFinitePresentationOnSite_modulePullback B S hS _ F hF)

end AffineBase

/-! ### Stacks 08K4 reduced to the affine case -/

/-- **Stacks 08K4 reduced to its affine case.**  In the standing data of Stacks 08JT, if `F` is
of finite presentation and `f` is quasi-compact and quasi-separated, the relative Hom functor is
limit preserving as soon as the relative Hom functor of every situation whose source and base are
affine schemes of the site and whose source module is of finite presentation is. -/
theorem limitPreserving_homFunctor_of_affineCase (s : HomSituation B S hS)
    (hF : s.F.IsFinitePresentationOnSite) (hqc : IsQuasiCompact B S hS s.f.hom)
    (hqs : IsQuasiSeparated B S hS s.f.hom)
    (haff : ∀ (U T₀ : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) →
      ∀ (fU : (schemeSpaceFunctor B S hS).obj U ⟶ (schemeSpaceFunctor B S hS).obj T₀)
        (F' G' : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
          ((schemeSpaceFunctor B S hS).obj U).2)
        (hF'q : F'.IsQuasicoherentOnSite) (hG'q : G'.IsQuasicoherentOnSite),
        F'.IsFinitePresentationOnSite →
          LimitPreserving.{u, u + 1, u, u}
            (HomSituation.mk _ _ fU F' G' hF'q hG'q).testSchemeFunctor
            ((HomSituation.mk _ _ fU F' G' hF'q hG'q).homFunctor
              (modulePushforwardCoherence B S hS))) :
    LimitPreserving.{u, u + 1, u, u} s.testSchemeFunctor
      (s.homFunctor (modulePushforwardCoherence B S hS)) := by
  refine s.limitPreserving_homFunctor_of_stages fun T₀ hT₀ ↦ ?_
  exact limitPreserving_homFunctor_of_affineBase hT₀ (s.baseChangedSource T₀.hom)
    (s.baseChangedMorphism T₀.hom) _ _ _ _
    (isFinitePresentationOnSite_modulePullback B S hS _ s.F hF)
    (isQuasiCompact_pullback_snd_of_isQuasiCompact B S hS hqc T₀.left T₀.hom.hom)
    (isQuasiSeparated_pullback_snd B S hS s.f.hom T₀.hom.hom hqs)
    (fun U hU ↦ haff U T₀.left hU hT₀)

end Space.HomSituation

end AlgebraicGeometry

end
