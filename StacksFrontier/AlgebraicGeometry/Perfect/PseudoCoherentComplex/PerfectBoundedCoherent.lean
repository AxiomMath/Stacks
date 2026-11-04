module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.LocallyFiniteCohomology

/-!
# Perfect complexes have bounded coherent cohomology

On a Noetherian scheme every perfect object of the derived category of modules has bounded and
coherent cohomology. This is [Stacks, Tag 0FXU].

## Main results

* `Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect`: a perfect object
  of the derived category lies in `DerivedCategoryB.derivedCategoryBBounded` for the coherence
  property.

## Implementation notes

Coherence in every degree is [Stacks, Tag 0FEP], namely
`Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology`. Boundedness is the
compactness argument: [Stacks, Tag 0FEP] also gives, around each point, a neighbourhood on which
only finitely many cohomology modules have support, a Noetherian scheme is quasi-compact, so
finitely many such neighbourhoods cover it, and the union of the corresponding finite sets of
degrees is finite. Outside that finite set every stalk of the cohomology vanishes, hence so
does the cohomology, because `SheafOfModules.toSheaf` is faithful and a sheaf with vanishing
stalks is zero.

## References

* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SheafOfModules

universe u d

namespace Stacks.AlgebraicGeometry.PerfectCohomology

/-- **A perfect derived object on a Noetherian scheme has bounded coherent cohomology.** -/
@[stacks 0FXU "perfect_bounded_coherent"]
theorem isBoundedCoherent_of_isPerfect
    (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent) K := by
  classical
  let C := StrictlyPerfect.OXMod.{u, u} X.toRingedSpace
  let H : ℤ → C := fun n => (DerivedCategory.homologyFunctor C n).obj K
  let S : Set ℤ := {n | ∃ x : X, x ∈ SheafOfModules.supp (H n)}
  have hlocal (x : X) : ∃ U : X.Opens, x ∈ U ∧
      {n : ℤ | ∃ y : X, y ∈ U ∧ y ∈ SheafOfModules.supp (H n)}.Finite := by
    simpa [H, C] using locally_finite_homology X K hK x
  let U : X → X.Opens := fun x => (hlocal x).choose
  obtain ⟨t : Finset (X : Type u), ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (X : Type u))).elim_finite_subcover
    (ι := (X : Type u)) (fun x : (X : Type u) => (U x : Set (X : Type u)))
    (fun x => (U x).isOpen) fun x _ => Set.mem_iUnion.mpr ⟨x, (hlocal x).choose_spec.1⟩
  have hUnion : (⋃ x ∈ (t : Set X),
      {n : ℤ | ∃ y : X, y ∈ U x ∧ y ∈ SheafOfModules.supp (H n)}).Finite :=
    t.finite_toSet.biUnion fun x _ => (hlocal x).choose_spec.2
  have hS : S.Finite := hUnion.subset <| by
    rintro n ⟨x, hx⟩
    obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion₂.mpr ⟨i, hit, x, hxi, hx⟩
  have hzero (n : ℤ) (hn : n ∉ S) : IsZero (H n) := by
    apply isZero_of_faithful (SheafOfModules.toSheaf X.ringCatSheaf)
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).2
    intro x
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr <|
      not_nontrivial_iff_subsingleton.mp (fun hx =>
        hn ⟨x, (SheafOfModules.mem_supp_iff_nontrivial_stalk (H n) x).2 hx⟩)
  refine ⟨⟨?_, ?_⟩, fun n => isCoherent_homology X K hK n⟩
  · obtain ⟨a, ha⟩ := hS.bddBelow
    exact ⟨a, fun n hna => hzero n (fun hn => (not_le_of_gt hna) (ha hn))⟩
  · obtain ⟨b, hb⟩ := hS.bddAbove
    exact ⟨b, fun n hbn => hzero n (fun hn => (not_le_of_gt hbn) (hb hn))⟩

end Stacks.AlgebraicGeometry.PerfectCohomology

end
