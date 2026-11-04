module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.LimitEffective
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange

/-!
# Finite descent over an affine base reduces to a Noetherian base

An affine scheme is the limit of a directed inverse system of affine Noetherian schemes with
affine transition morphisms, namely the spectra of the finitely generated subalgebras of its ring
of global sections (`AlgebraicGeometry.exists_limitNoetherianSituation_of_isAffine`). A morphism
to it which is finite and of finite presentation comes from a stage of that system, and is finite
and surjective already at a slightly later stage; base changing that model along the transition
morphisms presents the given morphism as a limit of finite surjective morphisms to affine
Noetherian schemes. Feeding this into
`AlgebraicGeometry.LimitDatum.qcSepEtaleEffective_of_forall_stage` reduces the effectivity of
quasi-compact separated étale descent along a finite, finitely presented, surjective morphism
with affine base to the same statement over an affine *Noetherian* base.

## Main definitions

* `AlgebraicGeometry.baseChangeDiagramProjection`: the projection of the diagram of base changes
  of a scheme over a stage onto the inverse system itself.

## Main results

* `AlgebraicGeometry.qcSepEtaleEffective_of_baseChangeDiagram`: **a morphism identified with the
  base change to the limit of a scheme over a stage inherits effectivity of quasi-compact
  separated étale descent from its base changes to the later stages.**
* `AlgebraicGeometry.qcSepEtaleEffective_of_forall_isNoetherian`: **effectivity of quasi-compact
  separated étale descent along a finite, finitely presented, surjective morphism with affine
  base follows from effectivity along the finite surjective morphisms to affine Noetherian
  schemes.**

## References

* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZO](https://stacks.math.columbia.edu/tag/01ZO)
* [Stacks Project, Tag 07RR](https://stacks.math.columbia.edu/tag/07RR)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- **The projection of the diagram of base changes of a scheme over a stage onto the inverse
system.** At a later stage `a` it is the first projection
`D.obj a.left ×_{D.obj i} X ⟶ D.obj a.left`. -/
def baseChangeDiagramProjection {I : Type v} [Category.{w} I] (D : I ⥤ Scheme.{u}) (i : I)
    (X : Over (D.obj i)) : baseChangeDiagram D i X ⟶ Over.forget i ⋙ D where
  app a := pullback.fst (D.map a.hom) X.hom
  naturality a b g := by
    rw [baseChangeDiagram_map]
    exact baseChangeTransition_fst (D.map b.hom) (D.map a.hom) (D.map g.left)
      (by rw [← D.map_comp, g.w]) X

/-- The component of `AlgebraicGeometry.baseChangeDiagramProjection` at a later stage `a` is the
first projection `pullback.fst (D.map a.hom) X.hom`. -/
@[simp]
lemma baseChangeDiagramProjection_app {I : Type v} [Category.{w} I] (D : I ⥤ Scheme.{u}) (i : I)
    (X : Over (D.obj i)) (a : Over i) :
    (baseChangeDiagramProjection D i X).app a = pullback.fst (D.map a.hom) X.hom := rfl

/-- **A morphism identified with the base change to the limit of a scheme over a stage inherits
effectivity of quasi-compact separated étale descent from its base changes to the later
stages.** -/
theorem qcSepEtaleEffective_of_baseChangeDiagram {I : Type u} [Category.{u} I] [IsCofiltered I]
    [EssentiallySmall.{u} I] (𝒟 : I ⥤ Scheme.{u}) (c : Cone 𝒟) (hc : IsLimit c)
    [∀ a : I, IsAffine (𝒟.obj a)] (j : I) (Y : Over (𝒟.obj j)) [IsAffine Y.left]
    {X : Scheme.{u}} (f : X ⟶ c.pt) (ξ : X ≅ pullback (c.π.app j) Y.hom)
    (hξ : ξ.hom ≫ pullback.fst (c.π.app j) Y.hom = f)
    (H : ∀ a : Over j, QcSepEtaleEffective (pullback.fst (𝒟.map a.hom) Y.hom)) :
    QcSepEtaleEffective f := by
  have hTA {p q : I} (g : p ⟶ q) : IsAffineHom (𝒟.map g) := inferInstance
  have hAffX (a : Over j) : IsAffine ((baseChangeDiagram 𝒟 j Y).obj a) :=
    isAffine_baseChangeDiagram_obj 𝒟 j Y a
  have hAffS (a : Over j) : IsAffine ((Over.forget j ⋙ 𝒟).obj a) :=
    inferInstanceAs (IsAffine (𝒟.obj a.left))
  refine LimitDatum.qcSepEtaleEffective_of_forall_stage
    (cX := (baseChangeCone 𝒟 c j Y).extend ξ.hom) (cS := c.whisker (Over.forget j))
    (baseChangeDiagramProjection 𝒟 j Y) f ?_
    (IsLimit.ofIsoLimit (baseChangeConeIsLimit 𝒟 hc j Y)
      (Cone.extendIso (baseChangeCone 𝒟 c j Y) ξ.symm))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) c).symm hc) H
  intro a
  have h3 : (baseChangeCone 𝒟 c j Y).π.app a ≫ pullback.fst (𝒟.map a.hom) Y.hom =
      pullback.fst (c.π.app j) Y.hom ≫ c.π.app a.left := by
    rw [baseChangeCone_π_app]
    exact baseChangeTransition_fst (𝒟.map a.hom) (c.π.app j) (c.π.app a.left) (by simp) Y
  have h1 : ((baseChangeCone 𝒟 c j Y).extend ξ.hom).π.app a ≫
      (baseChangeDiagramProjection 𝒟 j Y).app a =
      ξ.hom ≫ pullback.fst (c.π.app j) Y.hom ≫ c.π.app a.left :=
    (Category.assoc _ _ _).trans (congrArg (fun k ↦ ξ.hom ≫ k) h3)
  rw [h1, ← Category.assoc, hξ]
  rfl

/-- **Effectivity of quasi-compact separated étale descent along a finite, finitely presented,
surjective morphism with affine base reduces to the case of an affine Noetherian base.** -/
theorem qcSepEtaleEffective_of_forall_isNoetherian {S X : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [Surjective f] [IsFinite f] (hfp : FinitePresentation f)
    (H : ∀ (S' X' : Scheme.{u}) (g : X' ⟶ S'), IsAffine S' → IsNoetherian S' → IsFinite g →
      Surjective g → QcSepEtaleEffective g) :
    QcSepEtaleEffective f := by
  have hRF : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hRS : MorphismProperty.RespectsIso (@Surjective : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨J, hJpre, hJne, hJdir, 𝒟, heq, haff, -⟩ :=
    exists_limitNoetherianSituation_of_isAffine S
  subst heq
  have hTA {a b : Jᵒᵖ} (g : a ⟶ b) : IsAffineHom (𝒟.system.map g) := 𝒟.transition_affine g
  have hAff (a : Jᵒᵖ) : IsAffine (𝒟.system.obj a) := haff a.unop
  have hNoe (a : Jᵒᵖ) : IsNoetherian (𝒟.system.obj a) := 𝒟.noetherian a.unop
  have key : ∃ (j : Jᵒᵖ) (Y : Over (𝒟.system.obj j)), IsFinite Y.hom ∧ Surjective Y.hom ∧
      Nonempty (Over.mk f ≅ (Over.pullback (𝒟.limitCone.π.app j)).obj Y) := by
    have step {j j' : Jᵒᵖ} (m : j' ⟶ j) (Z : Over (𝒟.system.obj j))
        (e : Over.mk f ≅ (Over.pullback (𝒟.limitCone.π.app j)).obj Z) :
        Over.mk f ≅ (Over.pullback (𝒟.limitCone.π.app j')).obj
          ((Over.pullback (𝒟.system.map m)).obj Z) :=
      e ≪≫ (overPullbackCompIso (𝒟.system.map m) (𝒟.limitCone.π.app j')
        (𝒟.limitCone.π.app j) (𝒟.limitCone.w m) Z).symm
    obtain ⟨j₀, Y₀, hY₀, ⟨e₀⟩⟩ :=
      LimitFPObjectDescent.exists_model_of_finitePresentation 𝒟.system 𝒟.limitCone 𝒟.isLimit
        (Over.mk f) hfp
    obtain ⟨j₁, m₁, hFin₁⟩ := exists_isFinite_overPullback_obj_of_isLimit 𝒟.system 𝒟.limitCone
      𝒟.isLimit j₀ Y₀ hY₀ (prop_of_overIso @IsFinite e₀ (show IsFinite (Over.mk f).hom from ‹_›))
    have hY₁ : FinitePresentation ((Over.pullback (𝒟.system.map m₁)).obj Y₀).hom :=
      LimitFPObjectDescent.finitePresentation_overPullback _ Y₀ hY₀
    have e₁ := step m₁ Y₀ e₀
    obtain ⟨j₂, m₂, hSurj₂⟩ := exists_surjective_overPullback_obj_of_isLimit 𝒟.system
      𝒟.limitCone 𝒟.isLimit j₁ ((Over.pullback (𝒟.system.map m₁)).obj Y₀) hY₁
      (prop_of_overIso @Surjective e₁ (show Surjective (Over.mk f).hom from ‹_›))
    refine ⟨j₂, (Over.pullback (𝒟.system.map m₂)).obj
        ((Over.pullback (𝒟.system.map m₁)).obj Y₀), ?_, hSurj₂,
      ⟨step m₂ _ e₁⟩⟩
    have := hFin₁
    show IsFinite (pullback.snd ((Over.pullback (𝒟.system.map m₁)).obj Y₀).hom
      (𝒟.system.map m₂))
    infer_instance
  obtain ⟨j, Y, hFinY, hSurjY, ⟨e⟩⟩ := key
  have := hFinY
  have hAffY : IsAffine Y.left := by
    have := hAff j
    exact isAffine_of_isAffineHom Y.hom
  refine qcSepEtaleEffective_of_baseChangeDiagram 𝒟.system 𝒟.limitCone 𝒟.isLimit j Y f
    ((Over.forget _).mapIso e ≪≫ pullbackSymmetry Y.hom (𝒟.limitCone.π.app j)) ?_ fun a ↦ ?_
  · rw [Iso.trans_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc,
      pullbackSymmetry_hom_comp_fst]
    exact Over.w e.hom
  · have := hSurjY
    exact H _ _ _ (hAff a.left) (hNoe a.left) inferInstance inferInstance

end AlgebraicGeometry

end
