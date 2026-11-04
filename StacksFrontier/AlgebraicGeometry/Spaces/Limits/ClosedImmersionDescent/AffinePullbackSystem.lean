module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Immersion
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionDescent.PreimagesAndRepresentations

/-!
# The inverse system of affine base changes over an étale atlas

Let `X = lim Xᵢ` be a directed inverse limit of algebraic spaces over a base algebraic space,
with affine transition morphisms, and let `U₀ ⟶ Xᵢ₀` be a morphism from an affine object of the
site.  Affineness of the transition morphisms represents each base change `Xᵢ ×_{Xᵢ₀} U₀`, for
`i ≥ i₀`, by an affine object `Wᵢ` of the site; this file chooses those representing objects and
assembles the choices into an inverse system naturally isomorphic to the canonical system of base
changes, whose limit is the base change of `X ⟶ Xᵢ₀` along `U₀` by
`AlgebraicGeometry.Space.isLimitPullbackLimitOverPost`.  The limit of the `Wᵢ` is computed in
the slice of all schemes over `S`, where it is affine.

It then proves the eventual closed immersion over an affine étale atlas of one stage: the base
change of a closed immersion `f : Y ⟶ X` along `U₀ ⟶ X` is a closed immersion into the limit of
the `Wᵢ`, and because its target is affine it is representable by an affine object of the site
mapping to `U₀` by a closed immersion of schemes.  The scheme-level statement
`AlgebraicGeometry.EventualLimit.eventually_isClosedImmersion_comp_π_app` then gives a stage at
which the morphism of schemes is a closed immersion, and `AlgebraicGeometry.Space.presheaf_tfae`
at the closed immersions carries that back to the algebraic spaces.

It opens with `AlgebraicGeometry.Space.exists_over_limit_of_affine`, the limit of an inverse
system of affine objects of the site computed in the slice of all schemes and compared with the
limit of the represented functors, which the eventual immersion uses too. All other declarations
of this file are private auxiliaries for
`AlgebraicGeometry.Space.eventually_isClosedImmersion_comp_limitπ` and
`AlgebraicGeometry.Space.eventually_isImmersion_comp_limitπ`.

## References

* [Stacks Project, Tag 0828](https://stacks.math.columbia.edu/tag/0828)
* [Stacks Project, Tag 0827](https://stacks.math.columbia.edu/tag/0827)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter Opposite

universe u

namespace AlgebraicGeometry.Space

lemma exists_over_limit_of_affine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {J : Type u} [Category.{u} J] [IsConnected J]
    (A : J ⥤ BigFppfOver B S hS)
    (sc : Cone (A ⋙ BigFppfOver.toScheme B S hS))
    (hsc : IsLimit sc)
    (hA : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (A.obj j)))
    (pc : Cone (A ⋙ yoneda)) (hpc : IsLimit pc) :
    ∃ lc : Cone (A ⋙ Over.post B.inclusion),
      Nonempty (IsLimit lc) ∧ IsAffine lc.pt.left ∧
      ∃ e : (restrictedPoints (Over.post B.inclusion)).obj lc.pt ≅ pc.pt,
        ∀ j, e.hom ≫ pc.π.app j =
          (restrictedPoints (Over.post B.inclusion)).map (lc.π.app j) ≫
            (restrictedPointsIso (Over.post B.inclusion) (A.obj j)).hom := by
  let F := Over.post (X := B.obj hS) B.inclusion
  let R := restrictedPoints F
  let : HasLimit ((A ⋙ F) ⋙ Over.forget S) := ⟨⟨sc, hsc⟩⟩
  let : HasLimit (A ⋙ F) := hasLimit_of_created (A ⋙ F) (Over.forget S)
  let lc := limit.cone (A ⋙ F)
  have hlc := limit.isLimit (A ⋙ F)
  have : ∀ j, IsAffine (((A ⋙ F) ⋙ Over.forget S).obj j) := hA
  have ha : IsAffine lc.pt.left :=
    Scheme.isAffine_of_isLimit _ (isLimitOfPreserves (Over.forget S) hlc)
  let eA : (A ⋙ F) ⋙ R ≅ A ⋙ yoneda := NatIso.ofComponents
    (fun j => restrictedPointsIso F (A.obj j))
    (fun f => restrictedPointsIso_naturality F (A.map f))
  let rc := (Cone.postcompose eA.hom).obj (R.mapCone lc)
  have hrc : IsLimit rc :=
    (IsLimit.postcomposeHomEquiv eA _).symm (isLimitOfPreserves R hlc)
  refine ⟨lc, ⟨hlc⟩, ha, hrc.conePointUniqueUpToIso hpc, ?_⟩
  intro j
  exact hrc.conePointUniqueUpToIso_hom_comp hpc j

/-- Functoriality of `D.map (homOfLE _).op` for a composite of inequalities. -/
private lemma map_homOfLE_op_comp {I : Type u} [Preorder I] {C : Type*} [Category C]
    (D : Iᵒᵖ ⥤ C) {i j k : I} (h₁ : i ≤ j) (h₂ : j ≤ k) (h₃ : i ≤ k) :
    D.map (homOfLE h₃).op = D.map (homOfLE h₂).op ≫ D.map (homOfLE h₁).op := by
  rw [← Functor.map_comp]
  congr 1

private lemma exists_affine_pullback_stage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (i₀ i : I) (h : i₀ ≤ i)
    (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    ∃ (W : BigAffineFppf B S hS)
      (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶
        D.obj (op i))
      (q : (BigAffineFppf.inclusion B S hS).obj W ⟶ U₀),
    IsPullback p (yoneda.map q) (D.map (homOfLE h).op) p₀ := by
  let U₀' : BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  exact hAffine h U₀' p₀

private structure AffinePullbackStage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) (i : I) (h : i₀ ≤ i) where
  W : BigAffineFppf B S hS
  p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ D.obj (op i)
  q : (BigAffineFppf.inclusion B S hS).obj W ⟶ U₀
  isPullback : IsPullback p (yoneda.map q) (D.map (homOfLE h).op) p₀

private noncomputable def affinePullbackStageIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    {i : I} (h : i₀ ≤ i)
    (P : AffinePullbackStage B S hS D i₀ U₀ p₀ i h) :
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj P.W) ≅
      pullback (D.map (homOfLE h).op) p₀ :=
  P.isPullback.isoPullback

private lemma affinePullbackStageIso_hom_fst
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    {i : I} (h : i₀ ≤ i)
    (P : AffinePullbackStage B S hS D i₀ U₀ p₀ i h) :
    (affinePullbackStageIso B S hS D i₀ U₀ p₀ h P).hom ≫
      pullback.fst (D.map (homOfLE h).op) p₀ = P.p :=
  P.isPullback.isoPullback_hom_fst

private lemma affinePullbackStageIso_hom_snd
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    {i : I} (h : i₀ ≤ i)
    (P : AffinePullbackStage B S hS D i₀ U₀ p₀ i h) :
    (affinePullbackStageIso B S hS D i₀ U₀ p₀ h P).hom ≫
      pullback.snd (D.map (homOfLE h).op) p₀ = yoneda.map P.q :=
  P.isPullback.isoPullback_hom_snd

private noncomputable def chooseAffinePullbackStage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (i₀ i : I) (h : i₀ ≤ i)
    (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    AffinePullbackStage B S hS D i₀ U₀ p₀ i h := by
  apply Classical.choice
  obtain ⟨W, p, q, hp⟩ :=
    exists_affine_pullback_stage B S hS D hAffine i₀ i h U₀ hU₀ p₀
  exact ⟨⟨W, p, q, hp⟩⟩

private lemma affinePullbackStage_transition
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    {i j : I} (hi : i₀ ≤ i) (hj : i₀ ≤ j) (hij : i ≤ j)
    (Pi : AffinePullbackStage B S hS D i₀ U₀ p₀ i hi)
    (Pj : AffinePullbackStage B S hS D i₀ U₀ p₀ j hj) :
    ∃ (g : (BigAffineFppf.inclusion B S hS).obj Pj.W ⟶
        (BigAffineFppf.inclusion B S hS).obj Pi.W),
      yoneda.map g ≫ Pi.p = Pj.p ≫ D.map (homOfLE hij).op ∧
      yoneda.map g ≫ yoneda.map Pi.q = yoneda.map Pj.q := by
  let a := D.map (homOfLE hij).op
  have hsq : (Pj.p ≫ a) ≫ D.map (homOfLE hi).op = yoneda.map Pj.q ≫ p₀ := by
    rw [Category.assoc, ← map_homOfLE_op_comp D hi hij hj]
    exact Pj.isPullback.w
  let lift := Pi.isPullback.lift (Pj.p ≫ a) (yoneda.map Pj.q) hsq
  let g := yoneda.preimage lift
  refine ⟨g, ?_, ?_⟩
  · show yoneda.map g ≫ Pi.p = Pj.p ≫ a
    rw [show yoneda.map g = lift from yoneda.map_preimage lift]
    exact Pi.isPullback.lift_fst _ _ _
  · rw [show yoneda.map g = lift from yoneda.map_preimage lift]
    exact Pi.isPullback.lift_snd _ _ _

private abbrev AffinePullbackTail (I : Type u) [Preorder I] (i₀ : I) :=
  {i : I // i₀ ≤ i}

private lemma affinePullbackTail_nonempty
    {I : Type u} [Preorder I] (i₀ : I) : Nonempty (AffinePullbackTail I i₀) :=
  ⟨⟨i₀, le_rfl⟩⟩

private lemma affinePullbackTail_isDirected
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (i₀ : I) :
  IsDirected (AffinePullbackTail I i₀) (· ≤ ·) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨k, hak, hbk⟩ := IsDirected.directed (r := (· ≤ ·)) a.1 b.1
  exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩

attribute [local instance] affinePullbackTail_nonempty affinePullbackTail_isDirected

private noncomputable def affinePullbackStage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) (i : AffinePullbackTail I i₀) :
    AffinePullbackStage B S hS D i₀ U₀ p₀ i.1 i.2 :=
  chooseAffinePullbackStage B S hS D hAffine i₀ i.1 i.2 U₀ hU₀ p₀

private noncomputable def affinePullbackStageMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    {i j : AffinePullbackTail I i₀} (g : op i ⟶ op j)
    (Pi : AffinePullbackStage B S hS D i₀ U₀ p₀ j.1 j.2)
    (Pj : AffinePullbackStage B S hS D i₀ U₀ p₀ i.1 i.2) :
    (BigAffineFppf.inclusion B S hS).obj Pj.W ⟶
      (BigAffineFppf.inclusion B S hS).obj Pi.W := by
  let hij : j.1 ≤ i.1 := leOfHom g.unop
  exact Classical.choose (affinePullbackStage_transition B S hS D i₀ U₀ p₀
    j.2 i.2 hij Pi Pj)

private lemma affinePullbackStageMap_fst
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    {i j : AffinePullbackTail I i₀} (g : op i ⟶ op j)
    (Pi : AffinePullbackStage B S hS D i₀ U₀ p₀ j.1 j.2)
    (Pj : AffinePullbackStage B S hS D i₀ U₀ p₀ i.1 i.2) :
    yoneda.map (affinePullbackStageMap B S hS D i₀ U₀ p₀ g Pi Pj) ≫ Pi.p =
      Pj.p ≫ D.map (homOfLE (leOfHom g.unop)).op :=
  (Classical.choose_spec (affinePullbackStage_transition B S hS D i₀ U₀ p₀
    j.2 i.2 (leOfHom g.unop) Pi Pj)).1

private lemma affinePullbackStageMap_snd
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    {i j : AffinePullbackTail I i₀} (g : op i ⟶ op j)
    (Pi : AffinePullbackStage B S hS D i₀ U₀ p₀ j.1 j.2)
    (Pj : AffinePullbackStage B S hS D i₀ U₀ p₀ i.1 i.2) :
    yoneda.map (affinePullbackStageMap B S hS D i₀ U₀ p₀ g Pi Pj) ≫ yoneda.map Pi.q =
      yoneda.map Pj.q :=
  (Classical.choose_spec (affinePullbackStage_transition B S hS D i₀ U₀ p₀
    j.2 i.2 (leOfHom g.unop) Pi Pj)).2

private lemma affinePullbackStageMap_compatibility
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    {i j : AffinePullbackTail I i₀} (g : op i ⟶ op j) :
    (pullback.fst (D.map (homOfLE i.2).op) p₀ ≫
        D.map (homOfLE (leOfHom g.unop)).op) ≫ D.map (homOfLE j.2).op =
      pullback.snd (D.map (homOfLE i.2).op) p₀ ≫ p₀ := by
  rw [Category.assoc]
  exact (congrArg _ (map_homOfLE_op_comp D j.2 (leOfHom g.unop) i.2).symm).trans
    pullback.condition

private lemma affinePullbackStageIso_naturality
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    {i j : AffinePullbackTail I i₀} (g : op i ⟶ op j)
    (Pi : AffinePullbackStage B S hS D i₀ U₀ p₀ j.1 j.2)
    (Pj : AffinePullbackStage B S hS D i₀ U₀ p₀ i.1 i.2) :
    yoneda.map (affinePullbackStageMap B S hS D i₀ U₀ p₀ g Pi Pj) ≫
        (affinePullbackStageIso B S hS D i₀ U₀ p₀ j.2 Pi).hom =
      (affinePullbackStageIso B S hS D i₀ U₀ p₀ i.2 Pj).hom ≫
        pullback.lift
          (pullback.fst (D.map (homOfLE i.2).op) p₀ ≫
            D.map (homOfLE (leOfHom g.unop)).op)
          (pullback.snd (D.map (homOfLE i.2).op) p₀)
          (affinePullbackStageMap_compatibility B S hS D i₀ U₀ p₀ g) := by
  apply pullback.hom_ext
  · rw [Category.assoc, affinePullbackStageIso_hom_fst,
      affinePullbackStageMap_fst]
    rw [← affinePullbackStageIso_hom_fst]
    simp only [Category.assoc, pullback.lift_fst]
  · simp only [Category.assoc, pullback.lift_snd, affinePullbackStageIso_hom_snd,
      affinePullbackStageMap_snd]

private abbrev AffinePullbackTailOver
    (I : Type u) [Preorder I] (i₀ : I) := (AffinePullbackTail I i₀)ᵒᵖ

private noncomputable def affinePullbackTailToOver
    {I : Type u} [Preorder I] (i₀ : I) :
    AffinePullbackTailOver I i₀ ⥤ Over (op i₀) where
  obj i := Over.mk (homOfLE i.unop.2).op
  map {i j} g := Over.homMk (homOfLE (leOfHom g.unop)).op
  map_id := by
    intro i
    apply CommaMorphism.ext <;> apply Subsingleton.elim
  map_comp := by
    intro i j k f g
    apply CommaMorphism.ext <;> apply Subsingleton.elim

private noncomputable def affinePullbackOverToTail
    {I : Type u} [Preorder I] (i₀ : I) :
    Over (op i₀) ⥤ AffinePullbackTailOver I i₀ where
  obj j := op ⟨j.left.unop, leOfHom j.hom.unop⟩
  map {j k} g := op (homOfLE (leOfHom g.left.unop))
  map_id := by
    intro j
    apply Subsingleton.elim
  map_comp := by
    intro j k l f g
    apply Subsingleton.elim

private noncomputable def affinePullbackTailOverEquivalence
    {I : Type u} [Preorder I] (i₀ : I) :
    AffinePullbackTailOver I i₀ ≌ Over (op i₀) := by
  let F := affinePullbackTailToOver i₀
  let G := affinePullbackOverToTail i₀
  refine CategoryTheory.Equivalence.mk F G ?_ ?_
  · refine NatIso.ofComponents (fun i => Iso.refl _) ?_
    intro i j f
    apply Subsingleton.elim
  · refine NatIso.ofComponents (fun j => Iso.refl _) ?_
    intro j k f
    apply CommaMorphism.ext <;> apply Subsingleton.elim

private noncomputable def affinePullbackCanonicalDiagram
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    AffinePullbackTailOver I i₀ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (affinePullbackTailOverEquivalence i₀).functor ⋙
    (Over.post (X := op i₀) D) ⋙ Over.pullback p₀ ⋙ Over.forget (yoneda.obj U₀)

private noncomputable def affinePullbackCanonicalLimitCone
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    Cone (affinePullbackCanonicalDiagram B S hS D i₀ U₀ p₀) :=
  Cone.whisker (affinePullbackTailOverEquivalence i₀).functor
    ((Over.forget (yoneda.obj U₀)).mapCone
      ((Over.pullback p₀).mapCone ((limit.cone D).overPost (op i₀))))

private noncomputable def affinePullbackCanonicalLimitCone_isLimit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    IsLimit (affinePullbackCanonicalLimitCone B S hS D i₀ U₀ p₀) :=
  (isLimitPullbackLimitOverPost B S hS D (op i₀) p₀).whiskerEquivalence
    (affinePullbackTailOverEquivalence i₀)

private noncomputable def affinePullbackSiteDiagram
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    (AffinePullbackTail I i₀)ᵒᵖ ⥤ BigFppfOver B S hS where
  obj i := (BigAffineFppf.inclusion B S hS).obj
    (affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ i.unop).W
  map {i j} g := affinePullbackStageMap B S hS D i₀ U₀ p₀ g
    (affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ j.unop)
    (affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ i.unop)
  map_id := by
    intro i
    let P := affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ i.unop
    have hid : affinePullbackStageMap B S hS D i₀ U₀ p₀ (𝟙 i) P P = 𝟙 _ := by
      apply yoneda.map_injective
      apply P.isPullback.hom_ext
      · have hId : (homOfLE (leOfHom (𝟙 i).unop)).op = 𝟙 (op i.unop) := by
          apply Subsingleton.elim
        have hfst := affinePullbackStageMap_fst B S hS D i₀ U₀ p₀ (𝟙 i) P P
        rw [hId] at hfst
        calc
          _ = P.p ≫ D.map (𝟙 (op i.unop)) := hfst
          _ = P.p := by
            have hD : D.map (𝟙 (op i.unop)) = 𝟙 (D.obj (op i.unop)) := D.map_id _
            rw [hD]
            simp
          _ = yoneda.map (𝟙 _) ≫ P.p := by simp
      · simpa using affinePullbackStageMap_snd B S hS D i₀ U₀ p₀ (𝟙 i) P P
    exact hid
  map_comp := by
    intro i j k f g
    let Pi := affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ i.unop
    let Pj := affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ j.unop
    let Pk := affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ k.unop
    have hcomp : affinePullbackStageMap B S hS D i₀ U₀ p₀ (f ≫ g) Pk Pi =
        affinePullbackStageMap B S hS D i₀ U₀ p₀ f Pj Pi ≫
          affinePullbackStageMap B S hS D i₀ U₀ p₀ g Pk Pj := by
      apply yoneda.map_injective
      apply Pk.isPullback.hom_ext
      · rw [Functor.map_comp, Category.assoc, affinePullbackStageMap_fst,
          affinePullbackStageMap_fst, ← Category.assoc, affinePullbackStageMap_fst,
          Category.assoc]
        exact congrArg (Pi.p ≫ ·)
          (map_homOfLE_op_comp D (leOfHom g.unop) (leOfHom f.unop) (leOfHom (f ≫ g).unop))
      · simp only [Functor.map_comp, Category.assoc, affinePullbackStageMap_snd]
    exact hcomp

private noncomputable def affinePullbackChosenPresheafDiagram
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    (AffinePullbackTail I i₀)ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  affinePullbackSiteDiagram B S hS D hAffine i₀ U₀ hU₀ p₀ ⋙ yoneda

private noncomputable def affinePullbackChosenPresheafDiagramIsoCanonical
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    affinePullbackChosenPresheafDiagram B S hS D hAffine i₀ U₀ hU₀ p₀ ≅
      affinePullbackCanonicalDiagram B S hS D i₀ U₀ p₀ := by
  refine NatIso.ofComponents (fun i => ?_) ?_
  · exact affinePullbackStageIso B S hS D i₀ U₀ p₀ i.unop.2
      (affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ i.unop)
  · intro i j g
    exact affinePullbackStageIso_naturality B S hS D i₀ U₀ p₀ g
      (affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ j.unop)
      (affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ i.unop)

private noncomputable def affinePullbackSchemeDiagram
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    (AffinePullbackTail I i₀)ᵒᵖ ⥤ Scheme :=
  affinePullbackSiteDiagram B S hS D hAffine i₀ U₀ hU₀ p₀ ⋙
    BigFppfOver.toScheme B S hS

private lemma affinePullbackSchemeDiagram_obj_isAffine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    (i : (AffinePullbackTail I i₀)ᵒᵖ) :
    IsAffine ((affinePullbackSchemeDiagram B S hS D hAffine i₀ U₀ hU₀ p₀).obj i) := by
  show IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj
      (affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ i.unop).W))
  exact BigAffineFppf.isAffine_toScheme_obj B S hS
    (affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ i.unop).W

private noncomputable def affinePullbackAffineDiagram
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    (AffinePullbackTail I i₀)ᵒᵖ ⥤ AlgebraicGeometry.AffineScheme where
  obj i := AlgebraicGeometry.AffineScheme.mk
    ((affinePullbackSchemeDiagram B S hS D hAffine i₀ U₀ hU₀ p₀).obj i)
    (affinePullbackSchemeDiagram_obj_isAffine B S hS D hAffine i₀ U₀ hU₀ p₀ i)
  map {i j} g := by
    letI := affinePullbackSchemeDiagram_obj_isAffine B S hS D hAffine i₀ U₀ hU₀ p₀ i
    letI := affinePullbackSchemeDiagram_obj_isAffine B S hS D hAffine i₀ U₀ hU₀ p₀ j
    exact AlgebraicGeometry.AffineScheme.ofHom
      ((affinePullbackSchemeDiagram B S hS D hAffine i₀ U₀ hU₀ p₀).map g)
  map_id := by
    intro i
    apply InducedCategory.hom_ext
    exact (affinePullbackSchemeDiagram B S hS D hAffine i₀ U₀ hU₀ p₀).map_id i
  map_comp := by
    intro i j k f g
    apply InducedCategory.hom_ext
    exact (affinePullbackSchemeDiagram B S hS D hAffine i₀ U₀ hU₀ p₀).map_comp f g

private noncomputable def affinePullbackSchemeLimitCone
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    Cone (affinePullbackSchemeDiagram B S hS D hAffine i₀ U₀ hU₀ p₀) :=
  (AlgebraicGeometry.AffineScheme.forgetToScheme).mapCone
    (limit.cone (affinePullbackAffineDiagram B S hS D hAffine i₀ U₀ hU₀ p₀))

private noncomputable def affinePullbackSchemeLimitCone_isLimit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    IsLimit (affinePullbackSchemeLimitCone B S hS D hAffine i₀ U₀ hU₀ p₀) := by
  let A := affinePullbackAffineDiagram B S hS D hAffine i₀ U₀ hU₀ p₀
  have hlim := isLimitOfPreserves AlgebraicGeometry.AffineScheme.forgetToScheme
    (limit.isLimit A)
  change IsLimit ((AlgebraicGeometry.AffineScheme.forgetToScheme).mapCone
    (limit.cone A))
  exact hlim

private lemma eventually_isClosedImmersion_of_affine_atlas
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}))
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ limit D)
    (hClosed : Space.IsClosedImmersion B S hS f)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    (hpS : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p₀)
    (hpE : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p₀)
    (hFinite : Space.IsLocallyOfFiniteType B S hS (f ≫ limit.π D (op i₀))) :
    ∀ᶠ i in atTop, Space.IsClosedImmersion B S hS (f ≫ limit.π D (op i)) := by
  classical
  let F := Over.post (X := B.obj hS) B.inclusion
  let T := BigFppfOver.toScheme B S hS
  let R := restrictedPoints F
  let E := (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf
  let C := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) T).presheaf
  let J := AffinePullbackTail I i₀
  let : IsConnected Jᵒᵖ := IsCofiltered.isConnected _
  let A := affinePullbackSiteDiagram B S hS D hAffine i₀ U₀ hU₀ p₀
  let P := affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀
  let eA := affinePullbackChosenPresheafDiagramIsoCanonical
    B S hS D hAffine i₀ U₀ hU₀ p₀
  let cc := affinePullbackCanonicalLimitCone B S hS D i₀ U₀ p₀
  let pc : Cone (A ⋙ yoneda) :=
    { pt := pullback (limit.π D (op i₀)) p₀
      π := ((Cone.postcompose eA.inv).obj cc).π }
  have hpc : IsLimit pc := (IsLimit.postcomposeHomEquiv eA.symm cc).symm
    (affinePullbackCanonicalLimitCone_isLimit B S hS D i₀ U₀ p₀)
  have hAs (j) : IsAffine (T.obj (A.obj j)) :=
    affinePullbackSchemeDiagram_obj_isAffine B S hS D hAffine i₀ U₀ hU₀ p₀ j
  obtain ⟨lc, ⟨hlc⟩, hla, e, he⟩ := exists_over_limit_of_affine B S hS A
    (affinePullbackSchemeLimitCone B S hS D hAffine i₀ U₀ hU₀ p₀)
    (affinePullbackSchemeLimitCone_isLimit B S hS D hAffine i₀ U₀ hU₀ p₀)
    hAs pc hpc
  have : IsAffine lc.pt.left := hla
  let shA : Jᵒᵖ ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u) := {
    obj j := ⟨yoneda.obj (A.obj j),
      (isAlgebraicSpace_yoneda B S hS (A.obj j)).isSheaf⟩
    map g := ⟨yoneda.map (A.map g)⟩ }
  have hps : Presheaf.IsSheaf _ pc.pt := Sheaf.isSheaf_of_isLimit shA pc hpc
  have hls : Presheaf.IsSheaf _ (R.obj lc.pt) :=
    (Presheaf.isSheaf_of_iso_iff e).mpr hps
  let G := pullback (f ≫ limit.π D (op i₀)) p₀
  let a : G ⟶ Y := pullback.fst _ _
  let b : G ⟶ yoneda.obj U₀ := pullback.snd _ _
  have hG := _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS
    (f ≫ limit.π D (op i₀)) p₀ hY
    (isAlgebraicSpace_yoneda B S hS U₀) (hD i₀)
  have hcond : (a ≫ f) ≫ limit.π D (op i₀) = b ≫ p₀ := by
    simpa only [Category.assoc, a, b] using
      pullback.condition (f := f ≫ limit.π D (op i₀)) (g := p₀)
  let d : G ⟶ pullback (limit.π D (op i₀)) p₀ := pullback.lift (a ≫ f) b hcond
  have hdfst : d ≫ pullback.fst (limit.π D (op i₀)) p₀ = a ≫ f := pullback.lift_fst _ _ _
  have hdsnd : d ≫ pullback.snd (limit.π D (op i₀)) p₀ = b := pullback.lift_snd _ _ _
  have hd : IsPullback d a (pullback.fst (limit.π D (op i₀)) p₀) f := by
    have ho : IsPullback (d ≫ pullback.snd (limit.π D (op i₀)) p₀) a
        p₀ (f ≫ limit.π D (op i₀)) := by
      rw [hdsnd]
      exact (IsPullback.of_hasPullback (f ≫ limit.π D (op i₀)) p₀).flip
    exact ho.of_right hdfst (IsPullback.of_hasPullback _ _).flip
  have hdC : C d :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hd.flip hClosed
  have hde : C (d ≫ e.inv) := MorphismProperty.RespectsIso.postcomp C e.inv d hdC
  obtain ⟨V, eV, v, hv, hev⟩ := exists_representation_of_presheaf B S hS
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    (fun q m hq hm => by have := hq; have := hm; exact inferInstanceAs
      (_root_.AlgebraicGeometry.IsClosedImmersion (q ≫ m)))
    lc.pt hG hls (d ≫ e.inv) hde
  have hvci : _root_.AlgebraicGeometry.IsClosedImmersion v.left := hv
  have : IsAffine (T.obj V) :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine v.left).1
  let k (j : Jᵒᵖ) : V ⟶ A.obj j := F.preimage (v ≫ lc.π.app j)
  have hk (j : Jᵒᵖ) : yoneda.map (k j) = eV.hom ≫ d ≫ pc.π.app j := by
    have he' := he j
    have hv' := congrArg
      (· ≫ R.map (lc.π.app j) ≫ (restrictedPointsIso F (A.obj j)).hom) hev
    dsimp only [k]
    simp only [Category.assoc] at hv'
    rw [← he', Iso.inv_hom_id_assoc] at hv'
    rw [he'] at hv'
    calc
      yoneda.map (F.preimage (v ≫ lc.π.app j)) =
          (restrictedPointsIso F V).inv ≫ R.map (F.map (F.preimage
            (v ≫ lc.π.app j))) ≫ (restrictedPointsIso F (A.obj j)).hom := by
        rw [restrictedPointsIso_naturality]
        simp
      _ = (restrictedPointsIso F V).inv ≫ R.map v ≫
          R.map (lc.π.app j) ≫ (restrictedPointsIso F (A.obj j)).hom := by
        rw [F.map_preimage, R.map_comp]
        simp only [Category.assoc]
      _ = eV.hom ≫ d ≫ pc.π.app j := hv'.symm
  have hpcP (j : Jᵒᵖ) : pc.π.app j ≫ (P j.unop).p =
      pullback.fst (limit.π D (op i₀)) p₀ ≫ limit.π D (op j.unop.1) := by
    have h2 : (P j.unop).isPullback.isoPullback.inv ≫ (P j.unop).p =
        pullback.fst (D.map (homOfLE j.unop.2).op) p₀ := IsPullback.isoPullback_inv_fst _
    exact (congrArg (fun x => cc.π.app j ≫ x) h2).trans (pullback.lift_fst _ _ _)
  have hpcQ (j : Jᵒᵖ) : pc.π.app j ≫ yoneda.map (P j.unop).q =
      pullback.snd (limit.π D (op i₀)) p₀ := by
    have h2 : (P j.unop).isPullback.isoPullback.inv ≫ yoneda.map (P j.unop).q =
        pullback.snd (D.map (homOfLE j.unop.2).op) p₀ := IsPullback.isoPullback_inv_snd _
    exact (congrArg (fun x => cc.π.app j ≫ x) h2).trans (pullback.lift_snd _ _ _)
  have hkP (j : Jᵒᵖ) : yoneda.map (k j) ≫ (P j.unop).p =
      eV.hom ≫ a ≫ f ≫ limit.π D (op j.unop.1) := by
    rw [hk]
    refine (Category.assoc _ _ _).trans <|
      (congrArg _ ((Category.assoc _ _ _).trans (congrArg _ (hpcP j)))).trans ?_
    rw [← Category.assoc d, hdfst, Category.assoc]
  have hkQ (j : Jᵒᵖ) : yoneda.map (k j) ≫ yoneda.map (P j.unop).q = eV.hom ≫ b := by
    rw [hk]
    refine (Category.assoc _ _ _).trans <|
      (congrArg _ ((Category.assoc _ _ _).trans (congrArg _ (hpcQ j)))).trans ?_
    rw [hdsnd]
  let j₀ : J := ⟨i₀, le_rfl⟩
  have haE : E a := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_hasPullback (f ≫ limit.π D (op i₀)) p₀).flip hpE
  have hVE : E (eV.hom ≫ a) := MorphismProperty.RespectsIso.precomp E eV.hom a haE
  have hPE (j : Jᵒᵖ) : E (P j.unop).p :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (P j.unop).isPullback.flip hpE
  have hft : LocallyOfFiniteType (T.map (k (op j₀))) :=
    hFinite V (A.obj (op j₀)) (eV.hom ≫ a) (P j₀).p (k (op j₀))
      hVE (hPE (op j₀)) (by simpa only [Category.assoc] using hkP (op j₀))
  let sc := (Over.forget S).mapCone lc
  have hsc : IsLimit sc := isLimitOfPreserves (Over.forget S) hlc
  let τ : A ⋙ T ⟶ (Functor.const Jᵒᵖ).obj (T.obj (A.obj (op j₀))) := {
    app j := (A ⋙ T).map (homOfLE (show j₀ ≤ j.unop from j.unop.2)).op
    naturality := by
      intro j l g
      dsimp
      rw [Category.comp_id, ← Functor.map_comp, ← Functor.map_comp]
      congr 2 }
  have hτ : sc.π ≫ τ = (Functor.const Jᵒᵖ).map (sc.π.app (op j₀)) := by
    ext j
    exact sc.w (homOfLE (show j₀ ≤ j.unop from j.unop.2)).op
  have hks (j : Jᵒᵖ) : T.map (k j) = v.left ≫ sc.π.app j :=
    congrArg (fun z => z.left) (F.map_preimage (v ≫ lc.π.app j))
  let vl : T.obj V ⟶ sc.pt := v.left
  let s₀ : sc.pt ⟶ T.obj (A.obj (op j₀)) := sc.π.app (op j₀)
  have hlft : LocallyOfFiniteType (vl ≫ s₀) := by
    have h : LocallyOfFiniteType (T.map (k (op j₀))) := hft
    rw [hks (op j₀)] at h
    exact h
  have := hlft
  have hvcl : _root_.AlgebraicGeometry.IsClosedImmersion vl := hvci
  let (j : Jᵒᵖ) : IsAffine ((A ⋙ T).obj j) := hAs j
  have (j : J) : CompactSpace ((A ⋙ T).obj (op j)) := by
    rw [compactSpace_iff_quasiCompact]
    infer_instance
  have {j l : J} (h : j ≤ l) :
      _root_.AlgebraicGeometry.IsAffineHom ((A ⋙ T).map (homOfLE h).op) :=
    isAffineHom_of_isAffine _
  have hEventually :=
    _root_.AlgebraicGeometry.EventualLimit.eventually_isClosedImmersion_comp_π_app
      (A ⋙ T) τ sc hsc s₀ vl hτ
  obtain ⟨j, hj⟩ := eventually_atTop.1 hEventually
  refine eventually_atTop.2 ⟨j.1, fun i hi => ?_⟩
  let l : J := ⟨i, j.2.trans hi⟩
  have : _root_.AlgebraicGeometry.IsClosedImmersion (T.map (k (op l))) := by
    rw [hks]
    exact hj l hi
  have hKC : C (yoneda.map (k (op l))) := by
    let : PreservesLimitsOfShape WalkingCospan T := by apply comp_preservesLimitsOfShape
    let : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) T).IsStableUnderBaseChange := {
      of_isPullback := fun h hf =>
        _root_.AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange.of_isPullback
          (h.map T) hf }
    apply MorphismProperty.relative_map
    show _root_.AlgebraicGeometry.IsClosedImmersion (T.map (k (op l)))
    infer_instance
  have hOuter : IsPullback (eV.hom ≫ b) (eV.hom ≫ a) p₀
      (f ≫ limit.π D (op i₀)) :=
    (IsPullback.of_hasPullback (f ≫ limit.π D (op i₀)) p₀).flip.of_iso'
      eV (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [b]) (by simp [a]) (by simp) (by simp)
  have hOuter' : IsPullback (yoneda.map (k (op l)) ≫ yoneda.map (P l).q)
      (eV.hom ≫ a) p₀
      ((f ≫ limit.π D (op i)) ≫ D.map (homOfLE l.2).op) := by
    rw [hkQ]
    simpa only [Category.assoc, limit.w] using hOuter
  have hSquare := hOuter'.of_right (hkP (op l)) (P l).isPullback.flip
  have hpS' := (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@Surjective.{u}) T)).of_isPullback
        (P l).isPullback.flip hpS
  apply ((presheaf_tfae B S hS _
    _root_.AlgebraicGeometry.IsClosedImmersion.isZariskiLocalAtTarget hdesc hY (hD i)
    (f ≫ limit.π D (op i))).out 4 1).mp
  refine ⟨A.obj (op l), (P l).p, hpS', hPE (op l), ?_⟩
  have heq : hSquare.flip.isoPullback.inv ≫ yoneda.map (k (op l)) =
      pullback.snd (f ≫ limit.π D (op i)) (P l).p := IsPullback.isoPullback_inv_snd _
  show C (pullback.snd (f ≫ limit.π D (op i)) (P l).p)
  rw [← heq]
  exact MorphismProperty.RespectsIso.precomp C hSquare.flip.isoPullback.inv
    (yoneda.map (k (op l))) hKC

end AlgebraicGeometry.Space
