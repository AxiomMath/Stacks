module

public import StacksFrontier.AlgebraicGeometry.SectionExtensionAffineCover.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite set inside an affine nonvanishing locus of an ample sheaf

Let `X` be a scheme and `L` an ample invertible `𝒪_X`-module. Given a finite set of points `E`
inside an open `W ⊆ X`, there are an `n ≥ 1` and a global section `s` of `L^{⊗ n}` whose
nonvanishing locus `X_s` is affine and satisfies `E ⊆ X_s ⊆ W`.

## Main results

* `Stacks.SheafOfModules.Invertible.exists_sections_finite_subset_nonvanishingOpen_le_of_isAmple`:
  a finite subset of an open `W` lies in an affine nonvanishing locus, contained in `W`, of a
  global section of a positive tensor power of an ample invertible module.
* `Stacks.SheafOfModules.nonvanishingLocus_sectionsOfTop_finsetSum_le` and
  `Stacks.SheafOfModules.mem_nonvanishingLocus_sectionsOfTop_finsetSum`: the nonvanishing locus
  of a finite sum of global sections is contained in the union of the summands' loci, and
  contains every point at which exactly one summand is nonvanishing.
* `AlgebraicGeometry.Scheme.Modules.isAffineOpen_nonvanishingOpen_finsetSum`: the nonvanishing
  locus of a finite sum of global sections is affine as soon as the summands' loci are.
* `Stacks.SheafOfModules.nonvanishingLocus_sectionsOfTop_zero`: the zero section vanishes
  everywhere.

## Implementation notes

Global sections are elements of `Γ(X, L^{⊗ n}) = (L^{⊗ n}).val.obj (op ⊤)`, converted to
`PresheafOfModules.sections` by `Stacks.SheafOfModules.sectionsOfTop`, because
`PresheafOfModules.sections` carries no additive structure of its own.

## References

* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

universe u

namespace Stacks.SheafOfModules

section RingedSpace

variable {X : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureSheafRing X))
  [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- The zero global section vanishes everywhere. -/
theorem nonvanishingLocus_sectionsOfTop_zero :
    nonvanishingLocus M (sectionsOfTop M 0) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  rw [mem_nonvanishingLocus_sectionsOfTop_iff, map_zero] at hx
  exact hx (Submodule.zero_mem _)

/-- The nonvanishing locus of a finite sum of global sections is contained in the union of the
nonvanishing loci of the summands. -/
theorem nonvanishingLocus_sectionsOfTop_finsetSum_le {ι : Type*} (t : Finset ι)
    (u : ι → M.val.obj (op (⊤ : Opens X.carrier))) :
    nonvanishingLocus M (sectionsOfTop M (∑ i ∈ t, u i)) ⊆
      ⋃ i ∈ t, nonvanishingLocus M (sectionsOfTop M (u i)) := by
  classical
  induction t using Finset.induction with
  | empty => rw [Finset.sum_empty, nonvanishingLocus_sectionsOfTop_zero]; exact Set.empty_subset _
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine (nonvanishingLocus_sectionsOfTop_add_le M (u a) (∑ i ∈ t, u i)).trans ?_
      refine Set.union_subset
        (fun z hz => Set.mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a t, hz⟩) ?_
      exact ih.trans (Set.iUnion₂_subset fun i hi z hz =>
        Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hz⟩)

/-- A finite sum of global sections is nonvanishing at a point at which exactly one summand is
nonvanishing. -/
theorem mem_nonvanishingLocus_sectionsOfTop_finsetSum {ι : Type*} (t : Finset ι)
    (u : ι → M.val.obj (op (⊤ : Opens X.carrier))) {x : X.carrier} {j : ι} (hj : j ∈ t)
    (hxj : x ∈ nonvanishingLocus M (sectionsOfTop M (u j)))
    (hother : ∀ i ∈ t, i ≠ j → x ∉ nonvanishingLocus M (sectionsOfTop M (u i))) :
    x ∈ nonvanishingLocus M (sectionsOfTop M (∑ i ∈ t, u i)) := by
  classical
  rw [← Finset.add_sum_erase t u hj]
  refine mem_nonvanishingLocus_sectionsOfTop_add M _ _ hxj fun hmem => ?_
  obtain ⟨i, hi, hxi⟩ :=
    Set.mem_iUnion₂.mp (nonvanishingLocus_sectionsOfTop_finsetSum_le M (t.erase j) u hmem)
  exact hother i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi) hxi

end RingedSpace

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules

variable {X : Scheme.{u}} (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property M]

/-- The nonvanishing locus of a finite sum of global sections of an invertible module is affine
as soon as the nonvanishing loci of the summands are. -/
theorem isAffineOpen_nonvanishingOpen_finsetSum {ι : Type*} (t : Finset ι)
    (u : ι → M.val.obj (op (⊤ : _root_.TopologicalSpace.Opens X.carrier)))
    (hu : ∀ i ∈ t,
      IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M (u i)))) :
    IsAffineOpen
      (nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M (∑ i ∈ t, u i))) := by
  classical
  induction t using Finset.induction with
  | empty =>
      have hb : nonvanishingOpen (X := X.toRingedSpace) M
          (sectionsOfTop M (∑ i ∈ (∅ : Finset ι), u i)) = ⊥ := by
        refine _root_.TopologicalSpace.Opens.ext ?_
        rw [Finset.sum_empty]
        exact nonvanishingLocus_sectionsOfTop_zero M
      rw [hb]
      exact AlgebraicGeometry.isAffineOpen_bot X
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact isAffineOpen_nonvanishingOpen_add M (u a) (∑ i ∈ t, u i)
        (hu a (Finset.mem_insert_self a t))
        (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.SheafOfModules.Invertible

variable {Y : Scheme.{u}} (M : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property M]

local notation "Mpow[" n "]" => tensorPowerModule' M ((n : ℕ) : ℤ)

local notation "NV[" n ", " s "]" =>
  Stacks.SheafOfModules.nonvanishingOpen (X := Y.toRingedSpace)
    (tensorPowerModule' M ((n : ℕ) : ℤ)) s

/-- Let `L` be an ample invertible module on a scheme `Y`, and let `E ⊆ W ⊆ Y` with `E` finite
and `W` open. Then there are an `n ≥ 1` and a global section `s` of `L^{⊗ n}` whose nonvanishing
locus is affine and satisfies `E ⊆ Y_s ⊆ W`. -/
@[stacks 09NV, ega "II 4.5.4"]
theorem exists_sections_finite_subset_nonvanishingOpen_le_of_isAmple
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple Y M)
    {E : Set Y} (hE : E.Finite) (W : Y.Opens) (hEW : E ⊆ W) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (s : Mpow[m].sections),
      IsAffineOpen NV[m, s] ∧ E ⊆ (NV[m, s] : Set Y) ∧ (NV[m, s] : Set Y) ⊆ W := by
  classical
  have hE'fin : {y | y ∈ E ∧ ∀ z ∈ E, y ⤳ z → z = y}.Finite := hE.subset fun _ hy => hy.1
  set T : Finset Y := hE'fin.toFinset
  have hmemT : ∀ y : Y, y ∈ T ↔ (y ∈ E ∧ ∀ z ∈ E, y ⤳ z → z = y) := fun _ =>
    hE'fin.mem_toFinset
  have hpt : ∀ y : Y, ∃ (m : ℕ), 1 ≤ m ∧ ∃ s : Mpow[m].sections,
      y ∈ T → (y ∈ NV[m, s] ∧ (∀ z ∈ T, z ≠ y → z ∉ NV[m, s]) ∧
        NV[m, s] ≤ W ∧ IsAffineOpen NV[m, s]) := by
    intro y
    by_cases hy : y ∈ T
    · have hyW : y ∈ W := hEW ((hmemT y).mp hy).1
      have hZ : IsClosed (⋃ z ∈ T.erase y, closure ({z} : Set Y)) :=
        isClosed_biUnion_finset fun z _ => isClosed_closure
      have hyV : y ∈ (⟨(W : Set Y) ∩ (⋃ z ∈ T.erase y, closure ({z} : Set Y))ᶜ,
          W.isOpen.inter hZ.isOpen_compl⟩ : Y.Opens) := by
        refine ⟨hyW, fun hmem => ?_⟩
        obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hmem
        exact (Finset.ne_of_mem_erase hz)
          (((hmemT z).mp (Finset.mem_of_mem_erase hz)).2 y ((hmemT y).mp hy).1
            (specializes_iff_mem_closure.mpr hyz)).symm
      obtain ⟨m, hm, s, h1, h2, h3⟩ :=
        exists_sections_mem_nonvanishingOpen_le_of_isAmple M hL _ y hyV
      refine ⟨m, hm, s, fun _ => ⟨h1, fun z hz hzy hzs => ?_, fun z hzs => (h2 hzs).1, h3⟩⟩
      exact (h2 hzs).2
        (Set.mem_iUnion₂.mpr ⟨z, Finset.mem_erase.mpr ⟨hzy, hz⟩, subset_closure rfl⟩)
    · exact ⟨1, le_rfl, Stacks.SheafOfModules.sectionsOfTop Mpow[1] 0, fun h => absurd h hy⟩
  choose mm hmm ss hss using hpt
  have hNpos : 0 < ∏ y ∈ T, mm y := Finset.prod_pos fun y _ => hmm y
  have hdvd : ∀ i : {y : Y // y ∈ T}, mm i.1 ∣ ∏ y ∈ T, mm y := fun i =>
    Finset.dvd_prod_of_mem _ i.2
  have hq : ∀ i : {y : Y // y ∈ T}, 1 ≤ (∏ y ∈ T, mm y) / mm i.1 := fun i =>
    (Nat.one_le_div_iff (hmm i.1)).2 (Nat.le_of_dvd hNpos (hdvd i))
  set uu : {y : Y // y ∈ T} → Mpow[∏ y ∈ T, mm y].sections := fun i =>
    sectionsCongr Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property M
      (Nat.mul_div_cancel' (hdvd i)) (sectionPow' M (ss i.1) ((∏ y ∈ T, mm y) / mm i.1))
    with huudef
  set u : {y : Y // y ∈ T} →
      Mpow[∏ y ∈ T, mm y].val.obj (op (⊤ : _root_.TopologicalSpace.Opens Y.carrier)) :=
    fun i => (uu i).eval (op ⊤) with hudef
  have hus : ∀ i : {y : Y // y ∈ T},
      Stacks.SheafOfModules.sectionsOfTop Mpow[∏ y ∈ T, mm y] (u i) = uu i := fun i =>
    sectionsOfTop_eval_top_self Mpow[∏ y ∈ T, mm y] (uu i)
  have hlocu : ∀ i : {y : Y // y ∈ T},
      Stacks.SheafOfModules.nonvanishingLocus Mpow[∏ y ∈ T, mm y]
        (Stacks.SheafOfModules.sectionsOfTop Mpow[∏ y ∈ T, mm y] (u i)) =
        Stacks.SheafOfModules.nonvanishingLocus Mpow[mm i.1] (ss i.1) := fun i => by
    rw [hus i]
    exact (nonvanishingLocus_sectionsCongr M _ _).trans
      (nonvanishingLocus_sectionPow' M (ss i.1) _ (hq i))
  refine ⟨∏ y ∈ T, mm y, hNpos,
    Stacks.SheafOfModules.sectionsOfTop Mpow[∏ y ∈ T, mm y]
      (∑ i ∈ (Finset.univ : Finset {y : Y // y ∈ T}), u i), ?_, ?_, ?_⟩
  · refine AlgebraicGeometry.Scheme.Modules.isAffineOpen_nonvanishingOpen_finsetSum
      Mpow[∏ y ∈ T, mm y] Finset.univ u fun i _ => ?_
    convert (hss i.1 i.2).2.2.2 using 1
    exact _root_.TopologicalSpace.Opens.ext (hlocu i)
  · intro x hx
    obtain ⟨y, hyE, hxy, hymax⟩ := Topology.exists_maximal_specializes hE hx
    have hyT : y ∈ T := (hmemT y).mpr ⟨hyE, hymax⟩
    refine hxy.mem_open
      (Stacks.SheafOfModules.isOpen_nonvanishingLocus Mpow[∏ y ∈ T, mm y] _) ?_
    refine Stacks.SheafOfModules.mem_nonvanishingLocus_sectionsOfTop_finsetSum
      Mpow[∏ y ∈ T, mm y] Finset.univ u (Finset.mem_univ (⟨y, hyT⟩ : {y : Y // y ∈ T})) ?_ ?_
    · rw [hlocu ⟨y, hyT⟩]
      exact (hss y hyT).1
    · intro i _ hij
      rw [hlocu i]
      exact (hss i.1 i.2).2.1 y hyT fun h => hij (Subtype.ext h.symm)
  · intro x hx
    obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp
      (Stacks.SheafOfModules.nonvanishingLocus_sectionsOfTop_finsetSum_le
        Mpow[∏ y ∈ T, mm y] Finset.univ u hx)
    rw [hlocu i] at hxi
    exact (hss i.1 i.2).2.2.1 hxi

end Stacks.SheafOfModules.Invertible

end
