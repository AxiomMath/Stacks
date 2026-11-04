module

public import StacksFrontier.AlgebraicGeometry.Topologies.H.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.StandardCoverings
public import StacksFrontier.CategoryTheory.Sites.Pretopology.EquivalenceComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Representing standard h coverings inside a big h site

A big h site chooses a set-sized collection of h covering families on a size-bounded full
subcategory of schemes.  A standard h covering of one of its objects need not be among the
chosen families, since neither its index type nor its source schemes need belong to the
site.  This file shows that nothing is lost: every standard h covering of an affine object
of the site is tautologically equivalent to one of the chosen families.

## Main results

* `AlgebraicGeometry.exists_isCovering_tautologicallyEquivalent_standardHCovering`: a
  standard h covering of an affine object of a big h site is tautologically equivalent to a
  covering belonging to the site.

## Implementation notes

The index type of a standard h covering is finite, hence equivalent to a type in the site's
index universe, and its sources are of finite presentation over an object of the site, hence
small enough to be objects of the site themselves.  The given family is therefore first
reindexed and then transported into the site, where the site's own representability axiom
replaces it by a chosen covering combinatorially equivalent to it.  Each of these three
steps only changes the family within its tautological equivalence class, and the comparison
is stated after applying the site's inclusion functor because the sources of the given
family are arbitrary schemes.

## References

* [Stacks Project, Tag 0EU0](https://stacks.math.columbia.edu/tag/0EU0)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- **Stacks 0EU0, part (2).** A standard h covering of an affine object of a big h site is
tautologically equivalent to a covering belonging to that site.

Parts (1) and (3) are `AlgebraicGeometry.exists_isCovering_refinement_of_isHCovering` and
`AlgebraicGeometry.BigHSite.exists_isCovering_tautologicallyEquivalent_openCover`. -/
@[stacks 0EU0 "part (2)"]
public theorem exists_isCovering_tautologicallyEquivalent_standardHCovering
    (B : BigHSite.{u}) (T : B.Schemes) [IsAffine (B.inclusion.obj T)]
    (𝒰 : PreZeroHypercover.{v} (B.inclusion.obj T))
    (hstandard : IsStandardHCovering 𝒰.f) :
    ∃ 𝒱 : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, 𝒱⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent 𝒰 (𝒱.map B.inclusion) := by
  classical
  have : Finite 𝒰.I₀ := hstandard.1
  have : Fintype 𝒰.I₀ := Fintype.ofFinite 𝒰.I₀
  let e : ULift.{u + 1, 0} (Fin (Fintype.card 𝒰.I₀)) ≃ 𝒰.I₀ :=
    Equiv.ulift.trans (Fintype.equivFin 𝒰.I₀).symm
  set E : PreZeroHypercover.{u + 1} (B.inclusion.obj T) := 𝒰.reindex e
  have hE : IsStandardHCovering E.f := hstandard.reindex e
  have hfpE : ∀ i, FinitePresentation (E.f i) := hE.2.2.1
  have hsmall : ∀ i, (E.X i).size < B.cutoff := by
    intro i
    have : LocallyOfFinitePresentation (E.f i) := (hfpE i).1
    have : QuasiCompact (E.f i) := (hfpE i).2.1
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (E.f i) T.2
  let W : PreZeroHypercover.{u + 1} T :=
    { I₀ := E.I₀
      X i := B.obj (E.X i) (hsmall i)
      f i := ObjectProperty.homMk (E.f i) }
  have hW : IsHCoveringInCutoff (κ := B.cutoff) ⟨T, W⟩ := hE.isHCovering
  obtain ⟨⟨T', V⟩, hV, hT, hcomb⟩ := B.covering_representative ⟨T, W⟩ hW
  cases hT
  refine ⟨V, hV, ?_⟩
  refine PreZeroHypercover.tautologicallyEquivalent_trans 𝒰 (W.map B.inclusion)
    (V.map B.inclusion) ?_ ?_
  · exact PreZeroHypercover.tautologicallyEquivalent_of_combinatoriallyEquivalent _ _
      (PreZeroHypercover.combinatoriallyEquivalent_reindex 𝒰 e)
  · apply PreZeroHypercover.tautologicallyEquivalent_of_combinatoriallyEquivalent
    obtain ⟨⟨α, hX, hf⟩, ⟨β, hY, hg⟩⟩ :
      PreZeroHypercover.CombinatoriallyEquivalent W V := hcomb
    refine ⟨⟨α, fun i ↦ congrArg B.inclusion.obj (hX i), fun i ↦ ?_⟩,
      ⟨β, fun j ↦ congrArg B.inclusion.obj (hY j), fun j ↦ ?_⟩⟩
    · simpa [PreZeroHypercover.map] using congrArg B.inclusion.map (hf i)
    · simpa [PreZeroHypercover.map] using congrArg B.inclusion.map (hg j)

end AlgebraicGeometry
