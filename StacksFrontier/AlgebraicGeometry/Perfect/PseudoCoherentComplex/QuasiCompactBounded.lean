module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.LocallyFiniteCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs

/-!
# A perfect object on a quasi-compact scheme is bounded

On a quasi-compact scheme every perfect object of the derived category of `𝒪_X`-modules has only
finitely many nonzero cohomology sheaves, hence lies in `D^b(𝒪_X)`.

## Main results

* `Stacks.AlgebraicGeometry.PerfectCohomology.exists_isGE_isLE_of_isPerfect`: a perfect object on
  a quasi-compact scheme is bounded below and above.
* `Stacks.AlgebraicGeometry.PerfectCohomology.exists_isLE_of_isPerfect`: the upper bound alone.

## Implementation notes

This is the quasi-compactness patch from the local statement [Stacks, Tag 0FEP], namely
`Stacks.AlgebraicGeometry.PerfectCohomology.locally_finite_homology`, to a global bound. The
local statement needs no finiteness hypothesis on `X` at all: on a member of the covering
carrying a strictly perfect model the cohomology of the object is that of a bounded complex, so
only finitely many degrees have support meeting that member. Quasi-compactness lets finitely many
such members cover `X`, and the union of the corresponding finite sets of degrees is finite;
outside it every stalk of the cohomology vanishes, hence so does the cohomology, because
`SheafOfModules.toSheaf` is faithful and a sheaf with vanishing stalks is zero.

The boundedness half of [Stacks, Tag 0FXU],
`Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect`, runs exactly this
argument, but is stated with `[IsNoetherian X]` because it also concludes coherence of the
cohomology sheaves — and coherence is where the Noetherian hypothesis is really needed. Nothing
below mentions coherence, so `[CompactSpace X]` suffices.

Perfectness is spelled `Stacks.Cohomology.PerfectComplexes.IsPerfect`, the spelling the
scheme-level consumers use; `AlgebraicGeometry.RingedSpace.IsPerfect`, at which
[Stacks, Tag 0FEP] is stated, is the same predicate by `rfl`.

## References

* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SheafOfModules

universe u d

namespace Stacks.AlgebraicGeometry.PerfectCohomology

/-- **A perfect object on a quasi-compact scheme is bounded.** There are integers `a ≤ b` outside
which the cohomology sheaves of the object vanish.

Near every point only finitely many cohomology sheaves have support meeting a neighbourhood
([Stacks, Tag 0FEP]); quasi-compactness reduces to finitely many such neighbourhoods, and a
cohomology sheaf whose support is empty is zero. -/
theorem exists_isGE_isLE_of_isPerfect (X : Scheme.{u}) [CompactSpace X]
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b := by
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
  have hS : S.Finite := hUnion.subset (by
    rintro n ⟨x, hx⟩
    obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion₂.mpr ⟨i, hit, x, hxi, hx⟩)
  have hzero (n : ℤ) (hn : n ∉ S) : IsZero (H n) := by
    apply isZero_of_faithful (SheafOfModules.toSheaf X.ringCatSheaf)
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).2
    intro x
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr <|
      not_nontrivial_iff_subsingleton.mp (fun hx =>
        hn ⟨x, (SheafOfModules.mem_supp_iff_nontrivial_stalk (H n) x).2 hx⟩)
  obtain ⟨a, ha⟩ := hS.bddBelow
  obtain ⟨b, hb⟩ := hS.bddAbove
  exact ⟨a, b,
    (DerivedCategory.isGE_iff K a).2 fun n hna => hzero n fun hn => not_le_of_gt hna (ha hn),
    (DerivedCategory.isLE_iff K b).2 fun n hbn => hzero n fun hn => not_le_of_gt hbn (hb hn)⟩

/-- **A perfect object on a quasi-compact scheme is bounded above.** This is the upper half of
`Stacks.AlgebraicGeometry.PerfectCohomology.exists_isGE_isLE_of_isPerfect`, the form in which the
bound is consumed by the vanishing-window argument of [Stacks, Tag 09M4]. -/
theorem exists_isLE_of_isPerfect (X : Scheme.{u}) [CompactSpace X]
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) :
    ∃ b : ℤ, K.IsLE b :=
  let ⟨_, b, _, hb⟩ := exists_isGE_isLE_of_isPerfect X K hK
  ⟨b, hb⟩

end Stacks.AlgebraicGeometry.PerfectCohomology

end
