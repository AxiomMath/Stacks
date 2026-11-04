module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.IndependenceKTheory
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.PowerSumShortExact
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackLocallySplit

/-!
# The Whitney sum formula in the ring of total Chow cohomology classes

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project. The total
Chern class `c(ℰ)` of a finite locally free `𝒪_Y`-module of constant rank is a total Chow
cohomology class (`Stacks.Chow.totalChern`), and the ring `Stacks.Chow.TotalChowClass` it lives
in is not claimed to be commutative. This file states [Stacks, Tag 02UA] and [Stacks, Tag 02UI]
on total classes: two total Chern classes commute, their homogeneous components commute, and the
total Chern class of the middle term of a short exact sequence is the product of the total Chern
classes of the outer two. It also shows that translating the sorted list of an interval of `ℤ` by
one gives the sorted list of the translated interval.

## Main results

* `Stacks.Chow.commute_totalChern`: total Chern classes commute in the ring of total classes.
* `Stacks.Chow.commute_homComponent_totalChern`: the homogeneous components of two total Chern
  classes commute, the displayed identity of [Stacks, Tag 02UA] read on total classes.
* `Stacks.Chow.totalChern_shortExact`: the Whitney sum formula `c(ℰ) = c(ℰ₁) c(ℰ₂)` of
  [Stacks, Tag 02UI] for an arbitrary short exact sequence `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0`, on total
  classes.
* `Stacks.Chow.totalChern_biprod`: its case of a direct sum, `c(ℰ ⊕ ℱ) = c(ℰ) c(ℱ)`.
* `Stacks.Chow.map_sort_Icc_add_one`: the sorted list of `Icc a b` translated by `1` is the
  sorted list of `Icc (a + 1) (b + 1)`.

## References

* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Commutation and the Whitney sum formula for total classes -/

section TotalChern

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **Total Chern classes commute**: `c(ℰ) c(ℱ) = c(ℱ) c(ℰ)` in the ring of total Chow
cohomology classes, which is not claimed to be commutative. -/
theorem commute_totalChern (F G : Y.Modules) (r s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G s] :
    Commute (totalChern C sY F r) (totalChern C sY G s) := by
  refine TotalChowClass.ext_op fun g _ ↦ ?_
  let _ := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
  let _ := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank G s g
  rw [TotalChowClass.op_mul, TotalChowClass.op_mul, op_totalChern, op_totalChern]
  exact GenuineChern.chernFamily_commute C (g ≫ sY) _ _ r s

/-- The degree-`i` component of `c(ℰ)` and the degree-`j` component of `c(ℱ)` commute in the
ring of total Chow cohomology classes. -/
theorem commute_homComponent_totalChern (F G : Y.Modules) (r s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G s] (i j : ℕ) :
    Commute (TotalChowClass.homComponent i (totalChern C sY F r))
      (TotalChowClass.homComponent j (totalChern C sY G s)) := by
  refine TotalChowClass.ext_op fun g _ ↦ ?_
  let _ := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
  let _ := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank G s g
  rw [TotalChowClass.op_mul, TotalChowClass.op_mul, TotalChowClass.op_homComponent,
    TotalChowClass.op_homComponent, op_totalChern, op_totalChern]
  exact GenuineChern.commute_homComponent_chernFamily C (g ≫ sY) _ r _ s i j

/-- **The Whitney sum formula for a short exact sequence, on total classes**: for
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` with `ℰ₁`, `ℰ₂` finite locally free of ranks `r`, `s`,

  `c(ℰ) = c(ℰ₁) c(ℰ₂)`

in the ring of total Chow cohomology classes. -/
theorem totalChern_shortExact (S : ShortComplex Y.Modules) (hS : S.ShortExact) (r s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ s] :
    have _ := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact S hS r s ‹_› ‹_›
    totalChern C sY S.X₂ (r + s) = totalChern C sY S.X₁ r * totalChern C sY S.X₃ s := by
  have _ := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact S hS r s ‹_› ‹_›
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Y.ringCatSheaf) S.X₃ :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree S.X₃ s
  refine TotalChowClass.ext_op fun g _ ↦ ?_
  let _ := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank S.X₂ (r + s) g
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (S.map (Scheme.Modules.pullback g)).X₁ r :=
    pullbackPreservesRank_of_isFiniteLocallyFreeOfRank S.X₁ r g
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (S.map (Scheme.Modules.pullback g)).X₃ s :=
    pullbackPreservesRank_of_isFiniteLocallyFreeOfRank S.X₃ s g
  rw [TotalChowClass.op_mul, op_totalChern, op_totalChern, op_totalChern]
  exact GenuineChern.chernFamily_eq_mul_of_shortExact C (g ≫ sY)
    (S.map (Scheme.Modules.pullback g))
    (Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree g S hS) r s

/-- **The Whitney sum formula for a direct sum, on total classes**: `c(ℰ ⊕ ℱ) = c(ℰ) c(ℱ)`. -/
theorem totalChern_biprod (M N : Y.Modules) (r s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N s] :
    have _ := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
      (ShortComplex.mk (biprod.inl : M ⟶ M ⊞ N) (biprod.snd : M ⊞ N ⟶ N) (by simp))
      (ShortComplex.Splitting.ofHasBinaryBiproduct M N).shortExact r s ‹_› ‹_›
    totalChern C sY (M ⊞ N) (r + s) = totalChern C sY M r * totalChern C sY N s :=
  totalChern_shortExact C sY
    (ShortComplex.mk (biprod.inl : M ⟶ M ⊞ N) (biprod.snd : M ⊞ N ⟶ N) (by simp))
    (ShortComplex.Splitting.ofHasBinaryBiproduct M N).shortExact r s

end TotalChern

/-! ### Translating a sorted interval of integers -/

section SortedInterval

/-- Adding one to the members of the sorted list of an interval of `ℤ` gives the sorted list of
the translated interval. -/
theorem map_sort_Icc_add_one (a b : ℤ) :
    ((Finset.Icc a b).sort (· ≤ ·)).map (· + 1) = (Finset.Icc (a + 1) (b + 1)).sort (· ≤ ·) := by
  have hinj : Function.Injective (fun n : ℤ ↦ n + 1) := fun m n h ↦ by simpa using h
  refine List.Perm.eq_of_pairwise'
    (List.pairwise_map.2 (((Finset.Icc a b).pairwise_sort _).imp fun h ↦ by omega))
    ((Finset.Icc (a + 1) (b + 1)).pairwise_sort _) ?_
  refine (List.perm_ext_iff_of_nodup (((Finset.Icc a b).sort_nodup _).map hinj)
    ((Finset.Icc (a + 1) (b + 1)).sort_nodup _)).2 fun n ↦ ?_
  simp only [List.mem_map, Finset.mem_sort, Finset.mem_Icc]
  exact ⟨fun ⟨m, hm, hmn⟩ ↦ ⟨by omega, by omega⟩, fun hn ↦ ⟨n - 1, ⟨by omega, by omega⟩, by omega⟩⟩

end SortedInterval

end Stacks.Chow

end
