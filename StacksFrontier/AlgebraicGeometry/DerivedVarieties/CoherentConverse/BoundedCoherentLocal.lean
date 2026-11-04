module

public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.Modules.OpenCoverAcyclic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage

/-!
# Bounded coherent complexes are local

Let `X` be a quasi-compact scheme and `K` an object of `D(𝒪_X)`. If every point of `X` has an
open neighbourhood `U` such that `K|_U` lies in `D^b_Coh(𝒪_U)`, then `K` lies in `D^b_Coh(𝒪_X)`:
coherence of the cohomology sheaves is local, and finitely many of the neighbourhoods cover `X`,
so the cohomological bounds can be taken uniform. Conversely the restriction of an object of
`D^b_Coh(𝒪_X)` to an open lies in `D^b_Coh`.

The restriction is the derived functor of the exact restriction functor
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, at arbitrary models of the derived
categories.

## Main results

* `Stacks.AlgebraicGeometry.BoundedCoherentLocal.derivedCategoryBBounded_of_forall_restrict`.
* `Stacks.AlgebraicGeometry.BoundedCoherentLocal.derivedCategoryBBounded_restrict`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe w w' u

namespace Stacks.AlgebraicGeometry.BoundedCoherentLocal

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

/-- Restriction along an open immersion commutes with the cohomology sheaves. -/
abbrev restrictHomologyIso {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    [HasDerivedCategory.{w'} Y.Modules] (n : ℤ) :
    (Scheme.Modules.restrictFunctor f).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor Y.Modules n ≅
      DerivedCategory.homologyFunctor X.Modules n ⋙ Scheme.Modules.restrictFunctor f :=
  (Scheme.Modules.restrictFunctor f).mapDerivedCategoryHomologyIso n

/-- **The restriction of an object of `D^b_Coh` to an open is in `D^b_Coh`.** -/
theorem derivedCategoryBBounded_restrict (U : X.Opens) [HasDerivedCategory.{w'} U.toScheme.Modules]
    (K : DerivedCategory X.Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded (fun M : X.Modules => M.IsCoherent) K) :
    DerivedCategoryB.derivedCategoryBBounded (fun M : U.toScheme.Modules => M.IsCoherent)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  refine ⟨⟨⟨a, fun i hi => ?_⟩, ⟨b, fun i hi => ?_⟩⟩, fun i => ?_⟩
  · exact ((Scheme.Modules.restrictFunctor U.ι).map_isZero (ha i hi)).of_iso
      ((restrictHomologyIso U.ι i).app K)
  · exact ((Scheme.Modules.restrictFunctor U.ι).map_isZero (hb i hi)).of_iso
      ((restrictHomologyIso U.ι i).app K)
  · have : ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent := hc i
    exact (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre
      U.toScheme).isClosedUnderIsomorphisms.of_iso ((restrictHomologyIso U.ι i).app K).symm
      (AlgebraicGeometry.Modules.isCoherent_restrict _ U)

/-- **`D^b_Coh` is local.** On a quasi-compact scheme, an object whose restrictions to the members
of an open cover lie in `D^b_Coh` lies in `D^b_Coh`. -/
theorem derivedCategoryBBounded_of_forall_restrict [CompactSpace X]
    [∀ U : X.Opens, HasDerivedCategory.{w'} U.toScheme.Modules] (K : DerivedCategory X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      DerivedCategoryB.derivedCategoryBBounded (fun M : U.toScheme.Modules => M.IsCoherent)
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K)) :
    DerivedCategoryB.derivedCategoryBBounded (fun M : X.Modules => M.IsCoherent) K := by
  choose U hxU hU using h
  have hcov : iSup U = ⊤ := eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  have hcovs : IsOpenCover (fun x : s => U x.1) := by
    refine IsOpenCover.mk (eq_top_iff.2 fun y _ => ?_)
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy⟩
  choose a ha using fun x => (hU x).1.1
  choose b hb using fun x => (hU x).1.2
  have hz : ∀ i : ℤ, (∀ x : s, IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Scheme.Modules.restrictFunctor (U x.1).ι).mapDerivedCategory.obj K))) →
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K) := fun i hi =>
    Stacks.AlgebraicGeometry.Modules.isZero_of_isZero_restrictFunctor _ hcovs fun x =>
      (hi x).of_iso ((restrictHomologyIso (U x.1).ι i).app K).symm
  have hcoh : ∀ i, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent := fun i =>
    AlgebraicGeometry.Modules.isCoherent_of_restrict _ U hcov fun x =>
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre
        (U x).toScheme).isClosedUnderIsomorphisms.of_iso ((restrictHomologyIso (U x).ι i).app K)
        ((hU x).2 i)
  rcases s.eq_empty_or_nonempty with hs0 | hne
  · have h0 : ∀ i, IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K) := fun i =>
      hz i fun x => absurd x.2 (by simp [hs0])
    exact ⟨⟨⟨0, fun i _ => h0 i⟩, ⟨0, fun i _ => h0 i⟩⟩, hcoh⟩
  refine ⟨⟨⟨s.inf' hne fun x => a x, fun i hi => hz i fun x => ha x.1 i ?_⟩,
    ⟨s.sup' hne fun x => b x, fun i hi => hz i fun x => hb x.1 i ?_⟩⟩, hcoh⟩
  · exact lt_of_lt_of_le hi (Finset.inf'_le _ x.2)
  · exact lt_of_le_of_lt (Finset.le_sup' _ x.2) hi

end Stacks.AlgebraicGeometry.BoundedCoherentLocal

end
