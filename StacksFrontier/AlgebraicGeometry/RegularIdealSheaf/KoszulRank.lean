module

public import StacksFrontier.AlgebraicGeometry.QuasiRegular.Germs
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Independence
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Regular
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulQuotientIdentification
public import StacksFrontier.RingTheory.Koszul.LengthLeGenerators

/-!
# The local number of generators of a Koszul-regular sheaf of ideals

Let `Y` be a ringed space and `𝓘 ⊆ O_Y` a sheaf of ideals. [Stacks, Tag 0BQZ] writes
`r : Y → {1, 2, 3, …}` for the function sending `y` to the minimal number of generators of `𝓘`
needed in a neighbourhood of `y`. This file defines that function, `localGeneratorCount`, and
proves that at a point of the support of `O_Y/𝓘` it is the length of any Koszul-regular sequence
generating `𝓘` near the point. In particular two Koszul-regular generating sequences of
different lengths can only overlap away from the support.

## Main definitions

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.localGeneratorCount`: the function `r` of the tag.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.rankLocus`: the largest open on which every point
  of the support of `O_Y/𝓘` has `r = n`.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.localGeneratorCount_eq`: at a point of the support,
  `r` is the length of a Koszul-regular sequence generating `𝓘` nearby.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.notMem_idealQuotientSupport_of_ne`: a point where
  two Koszul-regular generating sequences of different lengths are both defined is off the
  support.

## Implementation notes

The value of `r` off the support plays no role in the tag: there `O_Y/𝓘` vanishes and so do both
sides of its formula. The function is defined by `sInf`, which gives it a value everywhere without
a hypothesis; at a point of the support of a Koszul-regular sheaf of ideals the infimum is
attained by the Koszul-regular generating sequence, and no shorter family generates, by
`Koszul.length_le_of_span_eq` applied to the germs.

## References

* [Stacks Project, Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ)
* [Stacks Project, Definition 31.21.2 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasiRegular Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {Y : RingedSpace.{u}} (J : (structureSheafModule Y).Submodule)

/-- **The function `r` of [Stacks, Tag 0BQZ]**: the minimal number of generators of `𝓘` needed in
a neighbourhood of `y`. -/
def localGeneratorCount (y : Y) : ℕ :=
  sInf {m | ∃ (U : Opens Y) (_ : y ∈ U) (f : Fin m → Y.presheaf.obj (op U)),
    IsGeneratedByOn Y J U f}

/-- **The rank-`n` locus**: the largest open on which every point of the support of `O_Y/𝓘` has
`r = n`. -/
def rankLocus (n : ℤ) : Opens Y :=
  sSup {U : Opens Y | ∀ y ∈ U, y ∈ idealQuotientSupport Y J → (localGeneratorCount J y : ℤ) = n}

variable {J}

/-- The germs at `y` of a family generating `𝓘` near `y` generate the germs at `y` of any other
family of sections of `𝓘`. -/
theorem jid_germFamily_le {U U' : Opens Y} {r s : ℕ} {f : Fin r → Y.presheaf.obj (op U)}
    (hf : ∀ i, f i ∈ J.obj (op U)) {g : Fin s → Y.presheaf.obj (op U')}
    (hg : IsGeneratedByOn Y J U' g) (y : Y) (hy : y ∈ U) (hy' : y ∈ U') :
    Ideal.span (Set.range (germFamily Y U f y hy)) ≤
      Ideal.span (Set.range (germFamily Y U' g y hy')) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have hres : Y.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (f i) ∈
      (generatedIdealOn Y U' g).obj (op (U ⊓ U')) := by
    rw [← hg (U ⊓ U') inf_le_right]
    exact J.toSubmodule.map_mem _ (hf i)
  have h := (mem_generatedIdealOn_iff U' g (U ⊓ U') inf_le_right _).mp hres y ⟨hy, hy'⟩
  rwa [TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (inf_le_left : U ⊓ U' ≤ U)) y
    ⟨hy, hy'⟩ (f i)] at h

/-- **At a point of the support the germs of a generating family generate a proper ideal.** If
they generated the unit ideal, `1` would be a combination of the generators on a neighbourhood,
hence a section of `𝓘` there. -/
theorem jid_germFamily_ne_top {U : Opens Y} {r : ℕ} {f : Fin r → Y.presheaf.obj (op U)}
    (hf : IsGeneratedByOn Y J U f) (y : Y) (hy : y ∈ U)
    (hyS : y ∈ idealQuotientSupport Y J) :
    Ideal.span (Set.range (germFamily Y U f y hy)) ≠ ⊤ := by
  classical
  intro htop
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
    ((Ideal.eq_top_iff_one _).mp htop)
  obtain ⟨W₀, hyW₀, σ, hσ⟩ := exists_common_germ_presheaf Y.presheaf y c Finset.univ
  set W₁ : Opens Y := W₀ ⊓ U
  have hyW₁ : y ∈ W₁ := ⟨hyW₀, hy⟩
  let a : Y.presheaf.obj (op W₁) :=
    ∑ i, Y.presheaf.map (homOfLE (inf_le_left : W₁ ≤ W₀)).op (σ i) *
      Y.presheaf.map (homOfLE (inf_le_right : W₁ ≤ U)).op (f i) - 1
  have ha : Y.presheaf.germ W₁ y hyW₁ a = 0 := by
    simp only [a, map_sub, map_sum, map_mul, map_one, TopCat.Presheaf.germ_res_apply]
    rw [sub_eq_zero, ← hc]
    exact Finset.sum_congr rfl fun i _ => by rw [hσ i (Finset.mem_univ i), smul_eq_mul]; rfl
  obtain ⟨W, hyW, hWW₁, hW⟩ := exists_nhds_eq_zero_of_germ_eq_zero W₁ a y hyW₁ ha
  refine (notMem_idealQuotientSupport_of_one_mem J y W hyW ?_) hyS
  have hfW : ∀ i, Y.presheaf.map (homOfLE (hWW₁.trans inf_le_right)).op (f i) ∈ J.obj (op W) :=
    fun i => J.toSubmodule.map_mem _ (mem_of_isGeneratedByOn Y J U f hf i)
  have h1 : (1 : Y.presheaf.obj (op W)) =
      ∑ i, Y.presheaf.map (homOfLE hWW₁).op
        (Y.presheaf.map (homOfLE (inf_le_left : W₁ ≤ W₀)).op (σ i)) *
          Y.presheaf.map (homOfLE (hWW₁.trans inf_le_right)).op (f i) := by
    simp only [a, map_sub, map_sum, map_mul, map_one, sub_eq_zero] at hW
    rw [← hW]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [h1]
  exact Submodule.sum_mem _ fun i _ => J.toSubmodule.obj (op W) |>.smul_mem _ (hfW i)

/-- **At a point of the support, `r` is the length of a Koszul-regular generating sequence.** -/
theorem localGeneratorCount_eq {U : Opens Y} {n : ℕ} {f : Fin n → Y.presheaf.obj (op U)}
    (hK : IsKoszulSequenceExactOn Y U f (fun j => 0 < j)) (hf : IsGeneratedByOn Y J U f)
    (y : Y) (hy : y ∈ U) (hyS : y ∈ idealQuotientSupport Y J) :
    localGeneratorCount J y = n := by
  have hmem : n ∈ {m | ∃ (U : Opens Y) (_ : y ∈ U) (f : Fin m → Y.presheaf.obj (op U)),
      IsGeneratedByOn Y J U f} := ⟨U, hy, f, hf⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  obtain ⟨U', hy', g, hg⟩ := Nat.sInf_mem ⟨n, hmem⟩
  exact Koszul.length_le_of_span_eq (germFamily Y U f y hy) (germFamily Y U' g y hy')
    ((isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular Y U f).mp hK y hy)
    (jid_germFamily_ne_top hf y hy hyS)
    (le_antisymm (jid_germFamily_le (mem_of_isGeneratedByOn Y J U f hf) hg y hy hy')
      (jid_germFamily_le (mem_of_isGeneratedByOn Y J U' g hg) hf y hy' hy))

/-- **Koszul-regular generating sequences of different lengths only overlap off the support.** -/
theorem notMem_idealQuotientSupport_of_ne {U U' : Opens Y} {n n' : ℕ}
    {f : Fin n → Y.presheaf.obj (op U)} {f' : Fin n' → Y.presheaf.obj (op U')}
    (hK : IsKoszulSequenceExactOn Y U f (fun j => 0 < j)) (hf : IsGeneratedByOn Y J U f)
    (hK' : IsKoszulSequenceExactOn Y U' f' (fun j => 0 < j)) (hf' : IsGeneratedByOn Y J U' f')
    (hnn' : n ≠ n') (y : Y) (hy : y ∈ U) (hy' : y ∈ U') :
    y ∉ idealQuotientSupport Y J := fun hyS =>
  hnn' ((localGeneratorCount_eq hK hf y hy hyS).symm.trans
    (localGeneratorCount_eq hK' hf' y hy' hyS))

/-- The open of a Koszul-regular generating sequence of length `n` lies in the rank-`n` locus. -/
theorem le_rankLocus {U : Opens Y} {n : ℕ} {f : Fin n → Y.presheaf.obj (op U)}
    (hK : IsKoszulSequenceExactOn Y U f (fun j => 0 < j)) (hf : IsGeneratedByOn Y J U f) :
    U ≤ rankLocus J n :=
  le_sSup fun y hy hyS => by rw [localGeneratorCount_eq hK hf y hy hyS]

/-- At a point of the support in the rank-`n` locus, `r = n`. -/
theorem localGeneratorCount_eq_of_mem_rankLocus {n : ℤ} {y : Y} (hy : y ∈ rankLocus J n)
    (hyS : y ∈ idealQuotientSupport Y J) : (localGeneratorCount J y : ℤ) = n := by
  obtain ⟨U, hU, hyU⟩ := Opens.mem_sSup.mp hy
  exact hU y hyU hyS

end Stacks.AlgebraicGeometry.RegularIdealSheaf
