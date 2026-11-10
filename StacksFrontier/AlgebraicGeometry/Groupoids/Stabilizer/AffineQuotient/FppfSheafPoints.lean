module

public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.AffineQuotientPoints
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineIntegral
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineInvariantFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.FiniteFreeResidueExtension
public import StacksFrontier.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Module.Free.Basis
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Functors of points on a big fppf site

Auxiliary facts about a big fppf site `B` (Tag 021S), used to represent the fppf quotient of a
finite flat equivalence relation on an affine scheme (Tag 03BM): the category of schemes of `B`
has a terminal object and pullbacks, every covering sieve of `B` is refined by a covering family,
the inclusion of `B` into all schemes is cover-preserving for the fpqc topology, the restricted
functor of points of a scheme over `S` is a sheaf on the localized site, and a flat, surjective
morphism locally of finite presentation induces a locally surjective map of functors of points.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

open Stacks.Groupoids Stacks.Morphisms AlgebraicGeometry.GroupoidScheme

private theorem relationMap_mono {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source] :
    Mono (prod.lift G.target G.source) := by
  let j : Stacks.Groupoids.PreRelation G.arrows G.objects := prod.lift G.target G.source
  have hj : IsEquivalenceRelation j.target j.source := by
    simpa [j, Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source] using
      (show IsEquivalenceRelation G.target G.source from inferInstance)
  exact ((Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp hj).1

private theorem schemeCutoff_terminal_size_lt (B : AlgebraicGeometry.BigFppfSite.{u}) :
    (⊤_ Scheme.{u}).size < B.cutoff := by
  have e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    IsTerminal.uniqueUpToIso terminalIsTerminal specULiftZIsTerminal
  have hsize : (⊤_ Scheme.{u}).size = Cardinal.aleph0 := by
    calc
      (⊤_ Scheme.{u}).size = (Spec (CommRingCat.of (ULift.{u} ℤ))).size := Scheme.size_congr e
      _ = max Cardinal.aleph0 (Cardinal.mk (ULift.{u} ℤ)) :=
        Scheme.size_Spec (CommRingCat.of (ULift.{u} ℤ))
      _ = Cardinal.aleph0 := by simp
  exact hsize ▸ B.aleph0_lt_cutoff

private theorem schemeCutoff_isClosedUnderLimitsOfShape_empty
    (B : AlgebraicGeometry.BigFppfSite.{u}) {J : Type*} [Category J] [IsEmpty J] :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme.{u} ↦ X.size < B.cutoff) J := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  have hterm : IsTerminal (limit F) :=
    (isLimitEquivIsTerminalOfIsEmpty Scheme (J := J) (F := F) (limit.cone F))
      (limit.isLimit F)
  rw [Scheme.size_congr (hterm.uniqueUpToIso terminalIsTerminal)]
  exact schemeCutoff_terminal_size_lt B

attribute [local instance] schemeCutoff_isClosedUnderLimitsOfShape_empty

private theorem schemeCutoff_hasTerminal (B : AlgebraicGeometry.BigFppfSite.{u}) :
    HasTerminal B.Schemes := inferInstance

attribute [local instance] schemeCutoff_hasTerminal

private theorem schemeCutoff_hasPullbacks (B : AlgebraicGeometry.BigFppfSite.{u}) :
    HasPullbacks B.Schemes := inferInstance

attribute [local instance] schemeCutoff_hasPullbacks

/-- Every covering sieve `R` of an object `X` of a big fppf site `B` contains the presieve of a
family over `X` which is a covering of `B`. -/
public theorem exists_covering_refining_sieve (B : AlgebraicGeometry.BigFppfSite.{u})
    {X : B.Schemes} {R : Sieve X} (hR : R ∈ B.topology X) :
    ∃ E : PreZeroHypercover X, B.IsCovering ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [AlgebraicGeometry.BigFppfSite.topology, Precoverage.mem_toGrothendieck_iff] at hR
  induction hR with
  | of X P hP =>
      obtain ⟨E, hEq, hE⟩ := hP
      exact ⟨E, hE, hEq ▸ Sieve.le_generate _⟩
  | top X =>
      exact ⟨PreZeroHypercover.singleton (𝟙 X), B.coverings_isSite.1 (𝟙 X), fun _ _ _ ↦ trivial⟩
  | pullback X R hR Y f ih =>
      obtain ⟨E, hE, hle⟩ := ih
      obtain ⟨P, p₁, p₂, hpb, hP⟩ := B.coverings_isSite.2.2 ⟨X, E⟩ hE Y f
      let F : PreZeroHypercover Y := ⟨E.I₀, P, p₂⟩
      refine ⟨F, hP, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      intro i
      rw [Sieve.pullback_apply, ← (hpb i).w]
      exact R.downward_closed (hle _ _ ⟨i⟩) (p₁ i)
  | transitive X R Q hR hRQ ihR ihRQ =>
      obtain ⟨E, hE, hle⟩ := ihR
      have hlocal (i : E.I₀) := ihRQ (hle _ _ ⟨i⟩)
      choose G hG hGle using hlocal
      refine ⟨E.bind G,
        B.coverings_isSite.2.1 ⟨X, E⟩ hE (fun i ↦ ⟨E.X i, G i⟩) hG (fun _ ↦ rfl), ?_⟩
      rw [Presieve.ofArrows_le_iff]
      rintro ⟨i, j⟩
      change Q ((G i).f j ≫ E.f i)
      exact hGle i _ _ ⟨j⟩

private theorem inclusion_coverPreserving_fpqc (B : AlgebraicGeometry.BigFppfSite.{u}) :
    CoverPreserving B.topology Scheme.fpqcTopology B.inclusion := by
  refine ⟨?_⟩
  intro X R hR
  obtain ⟨E, hE, hER⟩ := exists_covering_refining_sieve B hR
  have hEfp : AlgebraicGeometry.IsFppfCovering ⟨X, E⟩ := B.isFppfCovering_of_isCovering hE
  have hEfp' : (E.map B.inclusion).presieve₀ ∈
      Scheme.fpqcPrecoverage (B.inclusion.obj X) := by
    apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
    simpa [AlgebraicGeometry.IsFppfCovering, Scheme.fppfPrecoverage,
      PreZeroHypercover.presieve₀_map] using hEfp
  have hgen : Sieve.generate ((E.map B.inclusion).presieve₀) ∈
      Scheme.fpqcTopology (B.inclusion.obj X) :=
    Precoverage.generate_mem_toGrothendieck hEfp'
  have hle : Sieve.generate ((E.map B.inclusion).presieve₀) ≤
      R.functorPushforward B.inclusion := by
    rw [PreZeroHypercover.presieve₀_map, Sieve.generate_map_eq_functorPushforward]
    exact Sieve.functorPushforward_monotone B.inclusion X
      ((Sieve.generate_le_iff E.presieve₀ R).2 hER)
  exact Scheme.fpqcTopology.superset_covering hle hgen

theorem bigFppfOver_points_isSheaf (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (M : Over S) :
    Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (Over.post B.inclusion) M) := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let F : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  have : HasPullbacks B.Schemes := schemeCutoff_hasPullbacks B
  let : HasFiniteLimits B.Schemes := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesLimitsOfShape WalkingCospan B.inclusion := by infer_instance
  let : PreservesLimitsOfShape (Discrete.{0} PEmpty) B.inclusion := by infer_instance
  let : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  let : RepresentablyFlat B.inclusion := flat_of_preservesFiniteLimits B.inclusion
  let hbase := inclusion_coverPreserving_fpqc B
  let : B.inclusion.IsContinuous B.topology Scheme.fpqcTopology :=
    (Functor.isContinuous_iff_coverPreserving (F := B.inclusion)
      (J := B.topology) (K := Scheme.fpqcTopology)).2 hbase
  let : HasFiniteLimits (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance
  let : PreservesFiniteLimits F :=
    PreservesFiniteLimits.overPost (F := B.inclusion) (X := B.obj hS)
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  have hFcover : CoverPreserving J (Scheme.fpqcTopology.over S) F :=
    CoverPreserving.overPost (X := B.obj hS) hbase
  let : F.IsContinuous J (Scheme.fpqcTopology.over S) :=
    (Functor.isContinuous_iff_coverPreserving (F := F)
      (J := J) (K := Scheme.fpqcTopology.over S)).2 hFcover
  have hYon : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj M) :=
    (isSheaf_iff_isSheaf_of_type (J := Scheme.fpqcTopology.over S) (yoneda.obj M)).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := Scheme.fpqcTopology.over S) (yoneda.obj M))
  simpa [Stacks.Groupoids.points, F] using
    (F.op_comp_isSheaf_of_isSheaf J (Scheme.fpqcTopology.over S)
      (yoneda.obj M) hYon)

theorem points_map_isLocallySurjective_of_fppf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U M : Over S} (f : U ⟶ M)
    [Flat f.left] [LocallyOfFinitePresentation f.left] [Surjective f.left] :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS)
      ((Over.post B.inclusion).op.whiskerLeft (yoneda.map f)) := by
  classical
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let F : C ⥤ Over S := Over.post B.inclusion
  refine ⟨?_⟩
  intro X s
  let Q := pullback f.left s.left
  let P : Over S := Over.mk
    (pullback.snd f.left s.left ≫ ((Over.post B.inclusion).obj X).hom)
  let p₁ : P ⟶ U := Over.homMk (pullback.fst f.left s.left) (by
    calc
      pullback.fst f.left s.left ≫ U.hom =
          pullback.fst f.left s.left ≫ f.left ≫ M.hom := by rw [← Over.w f]
      _ = pullback.snd f.left s.left ≫ s.left ≫ M.hom :=
        congrArg (fun g => g ≫ M.hom) pullback.condition
      _ = pullback.snd f.left s.left ≫ ((Over.post B.inclusion).obj X).hom :=
        congrArg (fun g => pullback.snd f.left s.left ≫ g) (Over.w s))
  let p₂ : P ⟶ (Over.post B.inclusion).obj X :=
    Over.homMk (pullback.snd f.left s.left) rfl
  let E : PreZeroHypercover.{u + 1} (B.inclusion.obj X.left) :=
    PreZeroHypercover.singleton p₂.left
  have hPflat : Flat (pullback.snd f.left s.left) := inferInstance
  have hPlfp : LocallyOfFinitePresentation (pullback.snd f.left s.left) := inferInstance
  have hPsurj : Surjective (pullback.snd f.left s.left) := inferInstance
  have hE : E.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj X.left) := by
    change E.presieve₀ ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)
      (B.inclusion.obj X.left)
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun y ↦ ⟨PUnit.unit, hPsurj.surj y⟩, fun _ ↦ ⟨hPflat, hPlfp⟩⟩
  obtain ⟨V, hV, href⟩ :=
    AlgebraicGeometry.exists_isCovering_refining_fppfCovering B X.left E hE
  rcases href with ⟨ref⟩
  have hRcov : (Sieve.overEquiv X).symm V.sieve₀ ∈ J X := by
    rw [GrothendieckTopology.mem_over_iff]
    simpa [PreZeroHypercover.sieve₀, Sieve.ofArrows] using
      (Precoverage.generate_mem_toGrothendieck
        (show V.presieve₀ ∈ B.precoverage X.left from ⟨V, rfl, hV⟩))
  have hle : (Sieve.overEquiv X).symm V.sieve₀ ≤
      Presheaf.imageSieve
        (F.op.whiskerLeft (yoneda.map f)) s := by
    rw [← ((Sieve.overEquiv X).symm).apply_symm_apply
      (Presheaf.imageSieve (F.op.whiskerLeft (yoneda.map f)) s)]
    rw [((Sieve.overEquiv X).symm).map_rel_iff]
    simp only [OrderIso.symm_symm]
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
      Presieve.ofArrows_le_iff]
    intro i
    let i' : (PreZeroHypercover.map B.inclusion V).I₀ := i
    let W : C := Over.mk (V.f i ≫ X.hom)
    let α : W ⟶ X := Over.homMk (V.f i) (by simp [W])
    let b := ref.h₀ i'
    have href0 : ref.h₀ i' ≫ p₂.left = (V.f i').hom := by
      simpa [E, F, Over.post, PreZeroHypercover.singleton,
        PreZeroHypercover.map] using ref.w₀ i'
    have hbp : b ≫ p₂.left = B.inclusion.map (V.f i') := by
      simpa [b, AlgebraicGeometry.BigFppfSite.inclusion,
        AlgebraicGeometry.schemeBelowInclusion] using href0
    have hbOver : b ≫ P.hom = (F.obj W).hom := by
      change b ≫ (pullback.snd f.left s.left ≫ B.inclusion.map X.hom) =
        B.inclusion.map (V.f i) ≫ B.inclusion.map X.hom
      exact congrArg (fun g => g ≫ B.inclusion.map X.hom) hbp
    let β : F.obj W ⟶ P := Over.homMk b hbOver
    have hlift : (F.op.whiskerLeft (yoneda.map f)).app (Opposite.op W) (β ≫ p₁) =
        F.map α ≫ s := by
      apply Over.OverMorphism.ext
      change b ≫ (p₁.left ≫ f.left) =
        B.inclusion.map (V.f i') ≫ s.left
      exact (congrArg (fun g => b ≫ g) pullback.condition).trans
        ((Category.assoc b p₂.left s.left).symm.trans (congrArg (fun g => g ≫ s.left) hbp))
    have hgen : (Sieve.overEquiv X
        (Presheaf.imageSieve (F.op.whiskerLeft (yoneda.map f)) s)) (V.f i) := by
      rw [Sieve.overEquiv_iff, Presheaf.imageSieve_apply]
      exact ⟨β ≫ p₁, hlift⟩
    exact hgen
  exact J.superset_covering hle hRcov

end AlgebraicGeometry

end

end
