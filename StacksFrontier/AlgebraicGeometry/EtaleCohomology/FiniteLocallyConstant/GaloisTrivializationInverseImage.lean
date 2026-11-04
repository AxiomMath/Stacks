module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology

/-!
# A sheaf trivialized over an étale `X`-scheme `W` has constant inverse image on `W`

Let `W` be an étale `X`-scheme. The slice `X_étale / W` of the small étale site is the small
étale site of the scheme `W` itself: an étale `X`-scheme over `W` is the same as an étale
`W`-scheme. A trivialization of a sheaf `F` of `Λ`-modules over `W` is stated on the slice, as an
isomorphism `M̲ ≅ F|_W` of sheaves on `X_étale / W`
(`AlgebraicGeometry.GaloisTrivialization`, `AlgebraicGeometry.exists_finiteEtale_trivialization`).
This file reads it on `W_étale`: the inverse image `w⁻¹F` along the structure morphism
`w : W ⟶ X` is then the constant sheaf `M̲` of `W_étale`.

## Main definitions

* `Stacks.EtaleCohomology.etaleLeftOverFunctor`: an étale `W`-scheme as an object of the slice.
* `Stacks.EtaleCohomology.etaleOverLeftEquivalence`: the slice `X_étale / W` is `W_étale`.
* `Stacks.EtaleCohomology.etaleModuleInverseImageIsoConstantOfOverPullback`: a trivialization over
  `W` gives `w⁻¹F ≅ M̲` on `W_étale`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}} (W : X.Etale)

/-- An object of the slice `X_étale / W` as an étale `W`-scheme. -/
def etaleOverLeftFunctor : Over W ⥤ W.left.Etale where
  obj V := MorphismProperty.Over.mk ⊤ V.hom.left inferInstance
  map g := MorphismProperty.Over.homMk g.left.left (by
    have := congrArg (fun morphism ↦ morphism.left) g.w
    exact this)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An étale `W`-scheme as an object of the slice `X_étale / W`. -/
def etaleLeftOverFunctor : W.left.Etale ⥤ Over W where
  obj V := Over.mk (MorphismProperty.Over.homMk
    (A := MorphismProperty.Over.mk (P := (@Etale : MorphismProperty Scheme.{u}))
      ⊤ (V.hom ≫ W.hom) inferInstance)
    (B := W) V.hom)
  map {V V'} g := Over.homMk (MorphismProperty.Over.homMk g.left (by
    change g.left ≫ (V'.hom ≫ W.hom) = V.hom ≫ W.hom
    have h : g.left ≫ V'.hom = V.hom := by simpa using g.w
    rw [← Category.assoc, h])) (by
      apply MorphismProperty.Comma.Hom.ext
      · exact g.w
      · apply Subsingleton.elim)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The slice `X_étale / W` of the small étale site is the small étale site of `W`.** -/
def etaleOverLeftEquivalence : Over W ≌ W.left.Etale where
  functor := etaleOverLeftFunctor W
  inverse := etaleLeftOverFunctor W
  unitIso := NatIso.ofComponents (fun V ↦ Over.isoMk
    (MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (V.hom.left ≫ W.hom) = V.left.hom
      simpa using V.hom.w)) (by
        apply MorphismProperty.Comma.Hom.ext
        · change 𝟙 _ ≫ V.hom.left = V.hom.left
          simp
        · apply Subsingleton.elim)) (by
          intro V V' g
          apply Over.OverMorphism.ext
          apply MorphismProperty.Comma.Hom.ext
          · change g.left.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left.left
            simp
          · apply Subsingleton.elim)
  counitIso := NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _)) (by
      intro V V' g
      apply MorphismProperty.Comma.Hom.ext
      · change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
        simp
      · apply Subsingleton.elim)

/-- The functor `X_étale / W ⥤ W_étale` sends coverings of the slice topology to étale
coverings. -/
lemma etaleOverLeftFunctor_coverPreserving :
    CoverPreserving ((smallEtaleTopology X).over W) (smallEtaleTopology W.left)
      (etaleOverLeftFunctor W) := by
  constructor
  intro V S hS
  obtain ⟨members, T, g, rfl⟩ := S.exists_eq_ofArrows
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hS
  rw [Sieve.functorPushforward_ofArrows]
  apply (ofArrows_mem_smallEtaleTopology_iff _).mpr
  exact (ofArrows_mem_smallEtaleTopology_iff (fun member ↦ (g member).left)).mp hS

/-- The functor `W_étale ⥤ X_étale / W` sends étale coverings to coverings of the slice
topology. -/
lemma etaleLeftOverFunctor_coverPreserving :
    CoverPreserving (smallEtaleTopology W.left) ((smallEtaleTopology X).over W)
      (etaleLeftOverFunctor W) := by
  constructor
  intro V S hS
  obtain ⟨members, T, g, rfl⟩ := S.exists_eq_ofArrows
  rw [Sieve.functorPushforward_ofArrows, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  apply (ofArrows_mem_smallEtaleTopology_iff _).mpr
  exact (ofArrows_mem_smallEtaleTopology_iff g).mp hS

/-- The identification `W_étale ≅ X_étale / W` is a dense subsite. -/
instance isDenseSubsite_etaleLeftOverFunctor :
    (etaleLeftOverFunctor W).IsDenseSubsite
      (smallEtaleTopology W.left) ((smallEtaleTopology X).over W) := by
  have : (etaleOverLeftEquivalence W).functor.IsCocontinuous
      ((smallEtaleTopology X).over W) (smallEtaleTopology W.left) :=
    ((etaleOverLeftEquivalence W).toAdjunction.isCocontinuous_iff_coverPreserving
      _ _).mpr (etaleLeftOverFunctor_coverPreserving W)
  have : (etaleOverLeftEquivalence W).inverse.IsCocontinuous
      (smallEtaleTopology W.left) ((smallEtaleTopology X).over W) :=
    ((etaleOverLeftEquivalence W).symm.toAdjunction.isCocontinuous_iff_coverPreserving
      _ _).mpr (etaleOverLeftFunctor_coverPreserving W)
  exact Equivalence.isDenseSubsite_inverse_of_isCocontinuous ((smallEtaleTopology X).over W)
    (smallEtaleTopology W.left) (etaleOverLeftEquivalence W)

/-- Composition with `w : W ⟶ X` is the identification `W_étale ≅ X_étale / W` followed by the
forgetful functor of the slice. -/
def smallEtaleComposeIsoEtaleLeftOverFunctor :
    Scheme.Etale.smallEtaleCompose W.hom ≅ etaleLeftOverFunctor W ⋙ Over.forget W :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

variable (Λ : Type r) [Ring Λ]
  [HasWeakSheafify ((smallEtaleTopology X).over W) (ModuleCat.{max (u + 1) r} Λ)]

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- **A trivialization of `F` over `W` on the slice gives `w⁻¹ F ≅ M̲` on `W_étale`**, for the
structure morphism `w : W ⟶ X` of an étale `X`-scheme. -/
def etaleModuleInverseImageIsoConstantOfOverPullback
    (F : EtaleModules.{u, r} Λ X) (M : ModuleCat.{max (u + 1) r} Λ)
    (e : (constantSheaf ((smallEtaleTopology X).over W) (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
      ((smallEtaleTopology X).overPullback _ W).obj F) :
    (etaleModuleInverseImage.{u, r} Λ W.hom).obj F ≅
      (constantSheaf W.left.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M :=
  letI : (Scheme.Etale.smallEtaleCompose W.hom).IsContinuous
      W.left.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.Etale.smallEtaleCompose_isContinuous _
  letI := Functor.isContinuous_comp (etaleLeftOverFunctor W) (Over.forget W)
    W.left.smallEtaleTopology ((smallEtaleTopology X).over W) X.smallEtaleTopology
  (etaleModuleInverseImageRestrictionIso.{u, r} Λ W.hom).app F ≪≫
    (Functor.sheafPushforwardContinuousIso (smallEtaleComposeIsoEtaleLeftOverFunctor W)
      (ModuleCat.{max (u + 1) r} Λ) W.left.smallEtaleTopology X.smallEtaleTopology).app F ≪≫
    ((etaleLeftOverFunctor W).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      W.left.smallEtaleTopology ((smallEtaleTopology X).over W)).mapIso e.symm ≪≫
    (Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
      W.left.smallEtaleTopology ((smallEtaleTopology X).over W) (etaleLeftOverFunctor W)
      (ModuleCat.{max (u + 1) r} Λ)).app M

end Stacks.EtaleCohomology

end
