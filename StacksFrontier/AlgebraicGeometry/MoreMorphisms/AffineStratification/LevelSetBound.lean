module

public import Mathlib.Topology.Semicontinuity.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.AffineDiagonalTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.ReducedInduced

/-!
# Stratifying a scheme by the level sets of a lower semicontinuous function

A lower semicontinuous integer-valued function `F` on a scheme `Y` has locally closed level
sets, and when `F` takes only finitely many values these level sets, ordered by the value, form
a locally finite stratification of `Y`: the closure of `{F = d}` is contained in `{F ≤ d}`,
which is the union of the strata at values `≤ d`.

If moreover each level set carries an affine reduced induced scheme structure and `Y` is
separated — so that every morphism out of an affine scheme is affine — the stratification is an
affine stratification, and the affine stratification number of `Y` is bounded by the number of
values of `F`.

## Main results

* `AlgebraicGeometry.isLocallyClosed_levelSet_of_lowerSemicontinuous`: level sets of a lower
  semicontinuous integer-valued function are locally closed.
* `AlgebraicGeometry.affineStratificationNumber_le_ncard_of_isAffine_levelSet`: the bound on the
  affine stratification number.

## Implementation notes

The strata are indexed by `Fin (n + 1)` with `n` the number of values of `F`, the zeroth stratum
being empty and the remaining ones being the level sets listed in increasing order of value. The
extra empty stratum is what makes the index type `Fin (n + 1)` rather than `Fin n`, so the bound
reads `≤ n` rather than `≤ n - 1`.

## References

* [Stacks Project, Tag 0F2S](https://stacks.math.columbia.edu/tag/0F2S)
* [Stacks Project, Tag 0F2V](https://stacks.math.columbia.edu/tag/0F2V)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

namespace AlgebraicGeometry

/-- A level set of a lower semicontinuous integer-valued function is locally closed: it is the
intersection of the open set where the function exceeds `d - 1` with the closed set where it is
at most `d`. -/
theorem isLocallyClosed_levelSet_of_lowerSemicontinuous {T : Type*} [TopologicalSpace T]
    {F : T → ℤ} (hF : LowerSemicontinuous F) (d : ℤ) :
    IsLocallyClosed {y | F y = d} := by
  have heq : {y | F y = d} = F ⁻¹' Set.Ioi (d - 1) ∩ F ⁻¹' Set.Iic d := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_Iic]
    omega
  rw [heq]
  exact (hF.isOpen_preimage _).isLocallyClosed.inter (hF.isClosed_preimage _).isLocallyClosed

/-- The reduced induced scheme on the empty subset of a scheme is affine, being empty. -/
theorem isAffine_reducedInduced_empty (Y : Scheme.{u})
    (h : IsLocallyClosed (∅ : Set Y)) :
    IsAffine (reducedInducedScheme (∅ : Set Y) h) := by
  have : IsEmpty (reducedInducedScheme (∅ : Set Y) h) :=
    ⟨fun x ↦ (range_reducedInducedInclusion (∅ : Set Y) h).subset ⟨x, rfl⟩⟩
  infer_instance

/-- **The affine stratification number is bounded by the number of values of a lower
semicontinuous function with affine level sets.** If an integer-valued function on a separated
scheme `Y` is lower semicontinuous, takes finitely many values, and each of its level sets
carries an affine reduced induced scheme structure, then the affine stratification number of `Y`
is at most the number of values.

See [Stacks, Tag 0F2V]. -/
theorem affineStratificationNumber_le_ncard_of_isAffine_levelSet
    {Y : Scheme.{u}} [Y.IsSeparated] (F : Y → ℤ)
    (hfinite : (Set.range F).Finite) (hF : LowerSemicontinuous F)
    (haffine : ∀ d, IsAffine (reducedInducedScheme {y | F y = d}
      (isLocallyClosed_levelSet_of_lowerSemicontinuous hF d))) :
    affineStratificationNumber Y ≤ (Set.range F).ncard := by
  classical
  set s := hfinite.toFinset with hs
  set e := s.orderIsoOfFin (rfl : s.card = s.card) with he
  set strata : Fin (s.card + 1) → Set Y :=
    Fin.cases ∅ (fun i ↦ {y | F y = (e i).1}) with hstrata
  have hLC : ∀ i, IsLocallyClosed (strata i) := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact isOpen_empty.isLocallyClosed
    · exact isLocallyClosed_levelSet_of_lowerSemicontinuous hF _
  have hex : ∀ y : Y, ∃ k, (e k).1 = F y := fun y ↦
    (e.surjective ⟨F y, hfinite.mem_toFinset.mpr ⟨y, rfl⟩⟩).imp fun _ h ↦ congrArg Subtype.val h
  have hcover : ⋃ i, strata i = Set.univ := by
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨i, hi⟩ := hex y
    exact Set.mem_iUnion.mpr ⟨i.succ, hi.symm⟩
  have hstrat : IsLocallyFiniteStratification strata := by
    refine ⟨⟨⟨hLC, ?_, hcover⟩, ?_⟩, locallyFinite_of_finite _⟩
    · intro i j
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · exact fun _ ↦ disjoint_bot_left
      · refine Fin.cases ?_ (fun j' ↦ ?_) j
        · exact fun _ ↦ disjoint_bot_right
        · exact fun hij ↦ Set.disjoint_left.mpr fun y hyi hyj ↦ hij <|
            congrArg Fin.succ (e.injective (Subtype.ext (hyi.symm.trans hyj)))
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [hstrata]
      · intro y hy
        obtain ⟨k, hk⟩ := hex y
        have hkj : k ≤ j := e.le_iff_le.mp (show (e k).1 ≤ (e j).1 from hk ▸
          (hF.isClosed_preimage (e j).1).closure_subset_iff.mpr (fun _ h ↦ h.le) hy)
        exact Set.mem_iUnion.mpr ⟨k.succ,
          Set.mem_iUnion.mpr ⟨Fin.succ_le_succ_iff.mpr hkj, hk.symm⟩⟩
  have haffine' : ∀ i, IsAffine (reducedInducedScheme (strata i) (hLC i)) := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact isAffine_reducedInduced_empty Y _
    · exact haffine (e j).1
  let A : AffineStratification Y (Fin (s.card + 1)) :=
    { strata := strata
      isLocallyFiniteStratification := hstrat
      isAffine := haffine'
      isAffineHom := fun i ↦ by
        have := haffine' i
        exact isAffineHom_of_isAffine_of_isSeparated (reducedInducedInclusion _ _) }
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact Nat.sInf_le ⟨A⟩

end AlgebraicGeometry

end
