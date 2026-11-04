module
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Recovery21.FiniteCoveringsWithIntersections
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SectionsOnALocallySmallSite
public import StacksCore.Tactic.StacksAttribute

/-!
# FilteredColimitsOfEtaleCohomologyUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology`, stated as
separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

noncomputable section

variable {X : Scheme.{u}}

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
  Stacks.EtaleCohomology.etaleContainsIdentities etale_respectsIso

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- An object of the small étale site with affine underlying scheme has quasi-compact and
quasi-separated underlying scheme. -/
theorem mem_qcqsObjects_of_isAffine (V : X.Etale) [IsAffine V.left] :
    V ∈ _root_.Stacks.EtaleCohomology.qcqsEtaleObjects X :=
  ⟨inferInstance, inferInstance⟩

/-- The objects with quasi-compact and quasi-separated underlying scheme contain the vertex of a
fibre product of any two of their members over a third: a morphism between quasi-compact and
quasi-separated schemes is quasi-compact and quasi-separated, the first projection is a base change
of such a morphism, and its source is therefore quasi-compact and quasi-separated over the
quasi-compact and quasi-separated first factor. -/
theorem exists_pullbackCone_mem_qcqsObjects {V₁ V₂ W : X.Etale} (f : V₁ ⟶ W) (g : V₂ ⟶ W)
    (h₁ : V₁ ∈ _root_.Stacks.EtaleCohomology.qcqsEtaleObjects X)
    (h₂ : V₂ ∈ _root_.Stacks.EtaleCohomology.qcqsEtaleObjects X)
    (hW : W ∈ _root_.Stacks.EtaleCohomology.qcqsEtaleObjects X) :
    ∃ t : PullbackCone f g, Nonempty (IsLimit t) ∧
      t.pt ∈ _root_.Stacks.EtaleCohomology.qcqsEtaleObjects X := by
  obtain ⟨_, _⟩ := h₁
  obtain ⟨_, _⟩ := h₂
  obtain ⟨_, _⟩ := hW
  have hsq : IsPullback (pullback.snd f g).left (pullback.fst f g).left g.left f.left :=
    ((IsPullback.of_hasPullback f g).map
      (Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X)).flip
  have hq : QuasiCompact (pullback.fst f g).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have hs : QuasiSeparated (pullback.fst f g).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have hc : CompactSpace (pullback f g).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f g).left
  have hqs : QuasiSeparatedSpace (pullback f g).left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst f g).left
  exact ⟨PullbackCone.mk (pullback.fst f g) (pullback.snd f g) pullback.condition,
    ⟨pullbackIsPullback f g⟩, hc, hqs⟩

/-- The finite covering families of an object of the small étale site with quasi-compact and
quasi-separated underlying scheme by objects of the same kind.  This is
`Stacks.EtaleCohomology.qcqsEtaleCovering`. -/
alias qcqsCovering := qcqsEtaleCovering

/-- **Cofinal finite refinement, no hypothesis on the base.** Every covering sieve of an object of
the small étale site with quasi-compact and quasi-separated underlying scheme contains a finite
covering family by objects with affine, hence quasi-compact and quasi-separated, underlying
scheme. -/
theorem exists_qcqsCovering_le_unconditional (U : X.Etale)
    (hU : U ∈ _root_.Stacks.EtaleCohomology.qcqsEtaleObjects X) (R : Sieve U)
    (hR : R ∈ X.smallEtaleTopology U) : ∃ E ∈ qcqsCovering X U, E.sieve₀ ≤ R := by
  have := hU.1
  obtain ⟨E, hfin, haff, hcov, hle⟩ :=
    _root_.Stacks.EtaleCohomology.exists_finite_isAffine_covering_le U R hR
  refine ⟨E, ⟨hfin, hU, fun i ↦ ?_, hcov⟩, hle⟩
  have := haff i
  exact mem_qcqsObjects_of_isAffine _

/-- A finite covering family by objects with quasi-compact and quasi-separated underlying scheme
has all its iterated fibre products of the same kind, by induction on the family from the binary
case. -/
theorem hasIntersectionsIn_qcqsObjects (U : X.Etale) (E : PreZeroHypercover.{u} U)
    (hE : E ∈ qcqsCovering X U) :
    Stacks.Cohomology.HasIntersectionsIn (_root_.Stacks.EtaleCohomology.qcqsEtaleObjects X) E := by
  refine ⟨hE.1, hE.2.1, hE.2.2.1, fun n A ↦ ?_⟩
  exact Stacks.Cohomology.exists_widePullback_in (_root_.Stacks.EtaleCohomology.qcqsEtaleObjects X)
    (fun f g hu hv hw ↦ exists_pullbackCone_mem_qcqsObjects f g hu hv hw)
    hE.2.1 (n + 1) (fun i ↦ E.X (A i)) (fun i ↦ E.f (A i)) (fun i ↦ hE.2.2.1 (A i))

/-- **Étale cohomology over a quasi-compact and quasi-separated object commutes with filtered
colimits.** For every scheme `X`, every object `U` of the small étale site of `X` whose underlying
scheme is quasi-compact and quasi-separated, every degree `p` and every filtered system `F` of
abelian sheaves, the canonical map from the filtered colimit of the cohomology groups over `U` to
the cohomology of the filtered colimit is an isomorphism. No hypothesis on `X` is needed.

This is Stacks 0739 on the small étale site with `B` the objects with quasi-compact and
quasi-separated underlying scheme: the finite coverings by such objects are cofinal among the
coverings of a member of `B`, and their iterated fibre products are again in `B`. -/
@[sga "4 VII 3.3" "more general"]
theorem isIso_colimit_post_rightDerived_sheafSections_smallEtale_of_qcqs (p : ℕ) (U : X.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    {I : Type (max (u + 1) v)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso (colimit.post F (((sheafSections X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).obj (op U)).rightDerived p)) :=
  Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections_largeCoefficients.{v, u, u, u + 1}
    X.smallEtaleTopology (_root_.Stacks.EtaleCohomology.qcqsEtaleObjects X) (qcqsEtaleCovering X)
    (fun _ _ hE ↦ hE.2.2.2) (fun U E hE ↦ hasIntersectionsIn_qcqsObjects U E hE)
    (fun U hU R hR ↦ exists_qcqsCovering_le_unconditional U hU R hR) p U
    ⟨inferInstance, inferInstance⟩ F

end

end Stacks.EtaleCohomology

end
