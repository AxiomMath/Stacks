module

public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackStageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.DescendingProperties.SeparatedDescentConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionAlgebraicLimit

/-!
# Noetherian approximation of `Coh_{X/Y}` over an affine base

Over the base `Spec ℤ` (the terminal scheme), let `f : X ⟶ Y` be a separated morphism of finite
presentation of algebraic spaces whose target `Y` is an affine scheme `T` of the site. Write
`Γ(T) = colim ℤ[i]` as the filtered colimit of its finitely generated subrings. By Stacks 07SK
the morphism `f` descends to a morphism of finite presentation `f_i : X_i ⟶ Spec ℤ[i]` at some
stage, and by Stacks 0851 the descended morphism may be taken separated. Then `Coh_{X/Y}` is
the base change of `Coh_{X_i/Spec ℤ[i]}` along `T ⟶ Spec ℤ[i]` (Stacks 08LP), up to the
identification of `X` with `X_i ×_{Spec ℤ[i]} T`, and so it is algebraic as soon as
`Coh_{X_i/Spec ℤ[i]}` is (Stacks 05UM). This is the Noetherian-approximation step of the proof
of Stacks 09DS.

## Main definitions

* `AlgebraicGeometry.Space.finsetStage`: the stage `Spec ℤ[i]` as an affine object of the site.
* `AlgebraicGeometry.Space.finsetStageDiagram`: the inverse system of the stages.
* `AlgebraicGeometry.Space.finsetStageCone`: the cone with vertex `T` over it.

## Main results

* `AlgebraicGeometry.Space.isLimit_finsetStageCone`: `T` is the limit of the stages.

## References

* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### The inverse system of finitely generated subrings -/

section Stages

variable (R : Type u) [CommRing R]

/-- A finitely generated subring of a ring is countable. -/
theorem countable_adjoinFinset (i : Finset R) :
    Countable (Algebra.adjoin ℤ (i : Set R)) := by
  obtain ⟨n, g, hg⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (finiteType_adjoinFinset_int R i)
  exact hg.countable

/-- The spectrum of a finitely generated subring lies in every big fppf site. -/
theorem contains_specAdjoinFinsetDiagram_objSE (i : (Finset R)ᵒᵖ) :
    B.Contains ((specAdjoinFinsetDiagram R).obj i) := by
  have := countable_adjoinFinset R i.unop
  change (Spec (CommRingCat.of (Algebra.adjoin ℤ ((i.unop : Finset R) : Set R)))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff)

/-- **The stage `Spec ℤ[i]`**, as an affine object of the big fppf site of `Spec ℤ`. -/
def finsetStage (i : (Finset R)ᵒᵖ) : BigAffineFppf B (⊤_ Scheme.{u}) hZ :=
  ⟨siteObject B (⊤_ Scheme.{u}) hZ (contains_specAdjoinFinsetDiagram_objSE (B := B) R i)
    (terminal.from _), isAffine_specAdjoinFinsetDiagram_obj R i⟩

/-- **The inverse system of the stages `Spec ℤ[i]`.** -/
def finsetStageDiagram : (Finset R)ᵒᵖ ⥤ BigAffineFppf B (⊤_ Scheme.{u}) hZ where
  obj i := finsetStage hZ R i
  map {i j} f := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
    ((specAdjoinFinsetDiagram R).map f)) (ObjectProperty.hom_ext _ (terminal.hom_ext _ _)))
  map_id i := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (specAdjoinFinsetDiagram R).map_id i
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (specAdjoinFinsetDiagram R).map_comp f g

/-- The underlying system of schemes is the system of spectra of the finitely generated
subrings. -/
theorem finsetStageDiagram_comp_toScheme :
    finsetStageDiagram hZ R ⋙ BigAffineFppf.toScheme B (⊤_ Scheme.{u}) hZ =
      specAdjoinFinsetDiagram R :=
  rfl

end Stages

/-! ### An affine object of the site as the limit of the stages -/

section Cone

variable (T : BigAffineFppf B (⊤_ Scheme.{u}) hZ)

/-- The ring of global functions of the affine scheme underlying `T`. -/
abbrev affineRing : Type u := Γ((BigAffineFppf.toScheme B (⊤_ Scheme.{u}) hZ).obj T, ⊤)

/-- **The cone with vertex `T` over the stages of `Γ(T)`**: `T ≅ Spec Γ(T) ⟶ Spec ℤ[i]`, the cone
`AlgebraicGeometry.affineStageCone` read in the site. -/
def finsetStageCone : Cone (finsetStageDiagram hZ (affineRing hZ T)) where
  pt := T
  π :=
    { app i := ObjectProperty.homMk (Over.homMk
        (ObjectProperty.homMk ((affineStageCone
          ((BigAffineFppf.toScheme B (⊤_ Scheme.{u}) hZ).obj T)).π.app i))
        (ObjectProperty.hom_ext _ (terminal.hom_ext _ _)))
      naturality {i j} f := by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        exact (affineStageCone ((BigAffineFppf.toScheme B (⊤_ Scheme.{u}) hZ).obj T)).π.naturality
          f }

/-- **`T` is the limit of the stages of `Γ(T)`**, in schemes. -/
noncomputable def isLimit_finsetStageCone :
    IsLimit ((BigAffineFppf.toScheme B (⊤_ Scheme.{u}) hZ).mapCone (finsetStageCone hZ T)) :=
  isLimit_affineStageCone ((BigAffineFppf.toScheme B (⊤_ Scheme.{u}) hZ).obj T)

end Cone

/-! ### Two transport lemmas -/

section Transport

variable {S : Scheme.{u}} {hS : B.Contains S}

/-- Finite presentation is stable under base change along a cartesian square, read as a statement
about presheaves which are algebraic spaces. -/
theorem isFinitePresentation_of_isPullback' {P X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : P ⟶ X} {f' : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback g' f' f g)
    (hP : IsAlgebraicSpace B S hS P) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ' : IsAlgebraicSpace B S hS Z)
    (hf : IsFinitePresentation B S hS f) : IsFinitePresentation B S hS f' :=
  IsFinitePresentation.of_isPullback B S hS hP hX hY hZ' sq hf

/-- Separatedness of a morphism is unchanged by composing with an isomorphism on the target. -/
private theorem isSeparated_iff_of_comp_eq_of_isIso {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {m : X ⟶ Y} {g : Y ⟶ Z} {f : X ⟶ Z} [IsIso g] (hm : m ≫ g = f) :
    IsSeparated B S hS f ↔ IsSeparated B S hS m := by
  subst hm
  exact ⟨fun h => isSeparated_of_isPullback B S hS
      (IsPullback.of_horiz_isIso (CommSq.mk (show 𝟙 X ≫ m ≫ g = m ≫ g by simp))) h,
    fun h => isSeparated_of_isPullback B S hS
      (IsPullback.of_horiz_isIso (CommSq.mk (show 𝟙 X ≫ m = (m ≫ g) ≫ inv g by simp))) h⟩

end Transport

/-! ### The model at a stage -/

section Model

variable (T : BigAffineFppf B (⊤_ Scheme.{u}) hZ)

/-- The system of the stages `Spec ℤ[i]` of `Γ(T)`, as presheaves. -/
abbrev stageSystem :
    (Finset (affineRing hZ T))ᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u :=
  finsetStageDiagram hZ (affineRing hZ T) ⋙ affineYoneda B (⊤_ Scheme.{u}) hZ

/-- The limit of the stages is the presheaf represented by `T`. -/
noncomputable def stageLimitIso :
    limit (stageSystem hZ T) ≅ yoneda.obj ((BigAffineFppf.inclusion _ _ hZ).obj T) :=
  (limit.isLimit _).conePointUniqueUpToIso
    (isLimit_affineYoneda_mapCone_of_isLimit_toScheme _ (finsetStageCone hZ T)
      (isLimit_finsetStageCone hZ T))

/-- The inverse of `stageLimitIso` followed by the projection to the stage `j` is the map of
represented presheaves induced by the leg `T ⟶ Spec ℤ[j]` of `finsetStageCone`. -/
@[reassoc (attr := simp)]
theorem stageLimitIso_inv_π (j : (Finset (affineRing hZ T))ᵒᵖ) :
    (stageLimitIso hZ T).inv ≫ limit.π (stageSystem hZ T) j =
      yoneda.map ((BigAffineFppf.inclusion _ _ hZ).map ((finsetStageCone hZ T).π.app j)) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

/-- Each stage of `stageSystem` is an algebraic space. -/
theorem stageSystem_isAlgebraicSpace (j : (Finset (affineRing hZ T))ᵒᵖ) :
    IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ ((stageSystem hZ T).obj j) :=
  isAlgebraicSpace_yoneda B _ hZ _

/-- Each stage of `stageSystem` is affine as a scheme over `Spec ℤ`. -/
private theorem isAffine_toScheme_stage (j : (Finset (affineRing hZ T))ᵒᵖ) :
    IsAffine ((BigFppfOver.toScheme B _ hZ).obj
      ((BigAffineFppf.inclusion _ _ hZ).obj ((finsetStageDiagram hZ (affineRing hZ T)).obj j))) :=
  (finsetStage hZ (affineRing hZ T) j).property

/-- Each transition morphism of `stageSystem` is affine. -/
theorem stageSystem_isAffineHom {j k : (Finset (affineRing hZ T))ᵒᵖ} (m : j ⟶ k) :
    IsAffineHom B (⊤_ Scheme.{u}) hZ ((stageSystem hZ T).map m) := by
  have := isAffine_toScheme_stage hZ T j
  have := isAffine_toScheme_stage hZ T k
  exact isAffineHom_yoneda_map B _ hZ _

/-- Each stage of `stageSystem` is quasi-compact. -/
theorem stageSystem_isQuasiCompactSpace (j : (Finset (affineRing hZ T))ᵒᵖ) :
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ ((stageSystem hZ T).obj j) :=
  isQuasiCompactSpace_yoneda_of_isAffine B _ hZ _ (finsetStage hZ (affineRing hZ T) j).property

/-- Each stage of `stageSystem` is absolutely quasi-separated. -/
theorem stageSystem_isAbsolutelyQuasiSeparated (j : (Finset (affineRing hZ T))ᵒᵖ) :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ ((stageSystem hZ T).obj j) := by
  have := isAffine_toScheme_stage hZ T j
  exact (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B _ hZ hZ _).2 inferInstance

/-- The system `stageSystem` satisfies `SiteContainsBaseChangeLimits`: the limits of the base
changes of its stages to an affine object of the site lie in the site. -/
theorem stageSystem_siteContainsBaseChangeLimits :
    SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ (stageSystem hZ T) :=
  siteContainsBaseChangeLimits_affineYoneda _ (finsetStageCone hZ T)
    (isLimit_finsetStageCone hZ T)

/-- **Stacks 07SK and 0851 over an affine target.** Let `f : X ⟶ Y` be a separated morphism of
finite presentation of algebraic spaces over `Spec ℤ` whose target is identified with the presheaf
represented by an affine object `T` of the site. Then at some stage `Spec ℤ[j]` of `Γ(T)` there is
a separated morphism of finite presentation `f_j : X_j ⟶ Spec ℤ[j]` of which `f` is the base change
along `Y ≅ T ⟶ Spec ℤ[j]`. -/
theorem exists_stageModelSE (D : CoherentSituation B (⊤_ Scheme.{u}) hZ)
    (eY : D.Y.1 ≅ yoneda.obj ((BigAffineFppf.inclusion _ _ hZ).obj T))
    (hsep : IsSeparated B _ hZ D.f.hom) :
    ∃ (j : (Finset (affineRing hZ T))ᵒᵖ) (Xj : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
      (fj : Xj ⟶ (stageSystem hZ T).obj j) (k : D.X.1 ⟶ Xj),
      IsAlgebraicSpace B _ hZ Xj ∧ IsFinitePresentation B _ hZ fj ∧ IsSeparated B _ hZ fj ∧
      IsPullback k D.f.hom fj
        (eY.hom ≫ yoneda.map ((BigAffineFppf.inclusion _ _ hZ).map
          ((finsetStageCone hZ T).π.app j))) := by
  classical
  let D' := stageSystem hZ T
  let ι := stageLimitIso hZ T
  have hlimAlg : IsAlgebraicSpace B _ hZ (limit D') :=
    isAlgebraicSpace_of_iso B _ hZ ι.symm
      (isAlgebraicSpace_yoneda B _ hZ ((BigAffineFppf.inclusion _ _ hZ).obj T))
  let φ : D.Y.1 ⟶ limit D' := eY.hom ≫ ι.inv
  have : IsIso φ := by dsimp [φ]; infer_instance
  have hφfp : IsFinitePresentation B _ hZ (D.f.hom ≫ φ) := by
    refine isFinitePresentation_of_isPullback' (g' := 𝟙 _) (g := inv φ)
      (IsPullback.of_horiz_isIso (CommSq.mk (by simp))) D.X.2 D.X.2 hlimAlg D.Y.2
      D.finitePresentation
  obtain ⟨i, Yi, hYi, hYifp, ⟨e⟩⟩ :=
    exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits B _ hZ hZ D'
      (stageSystem_isAlgebraicSpace hZ T) (stageSystem_isAffineHom hZ T)
      (stageSystem_isQuasiCompactSpace hZ T) (stageSystem_isAbsolutelyQuasiSeparated hZ T)
      (stageSystem_siteContainsBaseChangeLimits hZ T) hlimAlg (Over.mk (D.f.hom ≫ φ)) D.X.2 hφfp
  -- the square at the stage `i`
  let a : D.X.1 ⟶ Yi.left := e.hom.left ≫ pullback.fst Yi.hom (limit.π D' i)
  have hw : e.hom.left ≫ pullback.snd Yi.hom (limit.π D' i) = D.f.hom ≫ φ := Over.w e.hom
  have hsqi : IsPullback a (D.f.hom ≫ φ) Yi.hom (limit.π D' i) := by
    refine IsPullback.of_iso_pullback (CommSq.mk ?_) ((Over.forget _).mapIso e) rfl hw
    rw [Category.assoc, pullback.condition, reassoc_of% hw]
    simp only [φ, Category.assoc]
  -- the descent situation of Stacks 084W at the stage `i`
  let M : MorphismDescentSituation B (⊤_ Scheme.{u}) hZ hZ (Finset (affineRing hZ T)) :=
    { base := D'
      base_isAlgebraicSpace := fun i => stageSystem_isAlgebraicSpace hZ T (op i)
      transition_affine := fun m => stageSystem_isAffineHom hZ T m
      limit_isAlgebraicSpace := hlimAlg
      initial := i.unop
      source₀ := Yi.left
      target₀ := D'.obj i
      sourceToBase := Yi.hom
      targetToBase := 𝟙 _
      map₀ := Yi.hom
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hYi
      target₀_isAlgebraicSpace := stageSystem_isAlgebraicSpace hZ T i
      base₀_quasiCompact := stageSystem_isQuasiCompactSpace hZ T i
      base₀_quasiSeparated := stageSystem_isAbsolutelyQuasiSeparated hZ T i
      source₀_quasiCompact := isQuasiCompactSpace_of_isFinitePresentation B _ hZ Yi.hom
        (stageSystem_isAlgebraicSpace hZ T i) (stageSystem_isQuasiCompactSpace hZ T i) hYifp
      source₀_quasiSeparated := isAbsolutelyQuasiSeparated_of_isFinitePresentation B _ hZ hZ hYi
        (stageSystem_isAbsolutelyQuasiSeparated hZ T i) hYifp
      target₀_quasiCompact := stageSystem_isQuasiCompactSpace hZ T i
      target₀_quasiSeparated := stageSystem_isAbsolutelyQuasiSeparated hZ T i }
  -- the base change to the limit is separated, being `f` up to isomorphism
  have hlimSep : IsSeparated B _ hZ M.mapLimit := by
    refine (isSeparated_iff_of_comp_eq_of_isIso (g := pullback.fst (limit.π D' i) (𝟙 (D'.obj i)))
      (pullback.lift_fst _ _ _)).1 ?_
    let eX := hsqi.flip.isoPullback
    have hcomm : eX.inv ≫ D.f.hom = pullback.fst (limit.π D' i) Yi.hom ≫ inv φ := by
      rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst_assoc, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    exact isSeparated_of_isPullback B _ hZ
      (IsPullback.of_horiz_isIso (fst := eX.inv) (CommSq.mk hcomm)) hsep
  obtain ⟨jj, hjj, hsepj⟩ :=
    M.exists_isSeparated_mapAt_of_siteContainsBaseChangeLimits
      (stageSystem_siteContainsBaseChangeLimits hZ T) hlimSep
  -- the model at the stage `j`
  let τ : D'.obj (op jj) ⟶ D'.obj i := D'.map (homOfLE hjj).op
  let Xj := pullback τ Yi.hom
  let fj : Xj ⟶ D'.obj (op jj) := pullback.fst τ Yi.hom
  have hXj : IsAlgebraicSpace B _ hZ Xj :=
    isAlgebraicSpace_pullback B _ hZ τ Yi.hom (stageSystem_isAlgebraicSpace hZ T (op jj))
      hYi (stageSystem_isAlgebraicSpace hZ T i)
  have hfjfp : IsFinitePresentation B _ hZ fj :=
    isFinitePresentation_of_isPullback' (IsPullback.of_hasPullback τ Yi.hom).flip hXj hYi
      (stageSystem_isAlgebraicSpace hZ T (op jj)) (stageSystem_isAlgebraicSpace hZ T i) hYifp
  have hfjsep : IsSeparated B _ hZ fj :=
    (isSeparated_iff_of_comp_eq_of_isIso (g := pullback.fst τ (𝟙 (D'.obj i)))
      (pullback.lift_fst _ _ _)).2 hsepj
  have hτ : limit.π D' (op jj) ≫ τ = limit.π D' i := limit.w D' (homOfLE hjj).op
  let k : D.X.1 ⟶ Xj := pullback.lift ((D.f.hom ≫ φ) ≫ limit.π D' (op jj)) a (by
    rw [Category.assoc, hτ, hsqi.w])
  have hsqj : IsPullback k (D.f.hom ≫ φ) fj (limit.π D' (op jj)) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd τ Yi.hom) ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback τ Yi.hom).flip
    rw [pullback.lift_snd, hτ]
    exact hsqi
  refine ⟨op jj, Xj, fj, k, hXj, hfjfp, hfjsep, ?_⟩
  have hb : eY.hom ≫ yoneda.map ((BigAffineFppf.inclusion _ _ hZ).map
      ((finsetStageCone hZ T).π.app (op jj))) = φ ≫ limit.π D' (op jj) := by
    change _ = (eY.hom ≫ (stageLimitIso hZ T).inv) ≫ limit.π (stageSystem hZ T) (op jj)
    rw [Category.assoc, stageLimitIso_inv_π]
    rfl
  rw [hb]
  exact IsPullback.of_iso hsqj (Iso.refl _) (Iso.refl _) (asIso φ).symm (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

end Model

/-! ### Algebraicity over an affine target from the stages -/

section Algebraicity

universe w

/-- **The Noetherian-approximation step of Stacks 09DS.** Over `Spec ℤ`, let `f : X ⟶ Y` be
separated and of finite presentation with `Y` the presheaf represented by an affine object `T` of
the site. If `Coh_{X₀/Y₀}` is an algebraic stack for every separated `f₀ : X₀ ⟶ Y₀` of finite
presentation whose target is (the algebraic space of) an affine object of finite type over `ℤ`,
then `Coh_{X/Y}` is an algebraic stack. -/
theorem isAlgebraicStack_of_affine (T : BigAffineFppf B (⊤_ Scheme.{u}) hZ)
    (D : CoherentSituation B (⊤_ Scheme.{u}) hZ)
    (eY : D.Y.1 ≅ yoneda.obj ((BigAffineFppf.inclusion _ _ hZ).obj T))
    (hsep : IsSeparated B _ hZ D.f.hom)
    (hbase : ∀ (T₀ : BigAffineFppf B (⊤_ Scheme.{u}) hZ),
      LocallyOfFiniteType (terminal.from ((BigAffineFppf.toScheme _ _ hZ).obj T₀)) →
      ∀ (D₀ : CoherentSituation B (⊤_ Scheme.{u}) hZ),
        D₀.Y = (schemeSpaceFunctor B _ hZ).obj ((BigAffineFppf.inclusion _ _ hZ).obj T₀) →
        IsSeparated B _ hZ D₀.f.hom →
        Stack.IsAlgebraicStack.{u, w} B _ hZ D₀.coherentCFG.val) :
    Stack.IsAlgebraicStack.{u, w} B _ hZ D.coherentCFG.val := by
  obtain ⟨j, Xj, fj, k, hXj, hfjfp, hfjsep, hP⟩ := exists_stageModelSE hZ T D eY hsep
  let D₀ : CoherentSituation B (⊤_ Scheme.{u}) hZ :=
    { X := ⟨Xj, hXj⟩
      Y := (schemeSpaceFunctor B _ hZ).obj
        ((BigAffineFppf.inclusion _ _ hZ).obj (finsetStage hZ (affineRing hZ T) j))
      f := ObjectProperty.homMk fj
      finitePresentation := hfjfp }
  have h₀ : Stack.IsAlgebraicStack.{u, w} B _ hZ D₀.coherentCFG.val :=
    hbase (finsetStage hZ (affineRing hZ T) j)
      (locallyOfFiniteType_terminalFrom_specAdjoinFinsetDiagram_obj _ j) D₀ rfl hfjsep
  let g : D.Y ⟶ D₀.Y := ObjectProperty.homMk (eY.hom ≫ yoneda.map
    ((BigAffineFppf.inclusion _ _ hZ).map ((finsetStageCone hZ T).π.app j)))
  have h₁ := D₀.isAlgebraicStack_baseChange.{u, w} g h₀
  let e : D.X ≅ (D₀.baseChange g).X := ObjectProperty.isoMk _ hP.isoPullback
  have he : e.hom ≫ (D₀.baseChange g).f = D.f :=
    ObjectProperty.hom_ext _ hP.isoPullback_hom_snd
  exact (CoherentSituation.isAlgebraicStack_isoSituation_iff (D := D₀.baseChange g) (f' := D.f)
    D.finitePresentation e he).mpr h₁

end Algebraicity

end AlgebraicGeometry.Space

end
