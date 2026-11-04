module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseCoherentFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.GradedActionTruncation
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.Truncation

/-!
# Finiteness of a graded truncation from finiteness of its residue classes

Let `S = ⨁_{i ≥ 0} 𝒮 i` be a graded ring acting on a `ℤ`-graded direct sum `⨁_{n ∈ ℤ} V n` by a
degree-raising action, and let `d ≥ 1`. The Veronese reduction of [Stacks, Tag 0B5R] produces, for
each residue `q < d`, a *finite* generating family over the Veronese subring `S⁽ᵈ⁾` for the part
of the truncation `⨁_{n ≥ k} V n` supported in the degrees congruent to `q` modulo `d`. This file
turns those `d` families into finiteness of the whole truncation over `S` itself.

Nothing here is about `Proj`: the only input is the degree-raising formula `hsmul`, and the two
instances of interest are the twisted global sections of a sheaf and the shifted global sections
of a graded module.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistedSections.span_subring_subset_span`: a span over a subring
  is contained in the span over the ring.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.coe_decompose_rangeGrading`: the degree-`i`
  homogeneous component of `x` for the tautological grading of a direct sum is the degree-`i`
  summand of `x`, read back in the sum.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.gradedActionGradedSMul`: a degree-raising action
  makes the tautological grading a graded module over `𝒮`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.gradedActionTruncation_eq_truncationAbove`: the
  truncation of the action is the truncation of the graded module.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_gradedActionTruncation_of_residues`:
  if every residue class of the truncation lies in the `S⁽ᵈ⁾`-span of a finite subset of the
  truncation, the truncation is a finite `S`-module.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public noncomputable section

open DirectSum
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjTwistedSections

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- A span over a subring is contained in the span over the ring: the elements of the subring act
by restriction of the ring's action, so a subring-linear combination is a ring-linear combination
of the same set. -/
public theorem span_subring_subset_span (R : Type*) [CommRing R] (R' : Subring R)
    {M : Type*} [AddCommGroup M] [Module R M] (T : Set M) :
    (Submodule.span R' T : Set M) ⊆ (Submodule.span R T : Set M) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ (c : R) ha

variable {V : ℤ → Type u} [∀ n, AddCommGroup (V n)]

/-- The homogeneous components of the tautological grading are the summands: for the grading of
`⨁_{n ∈ ℤ} V n` by the ranges of the inclusions of the summands, the degree-`i` component of `x`
is the degree-`i` summand of `x`, put back into the sum. -/
public theorem coe_decompose_rangeGrading (x : ⨁ n : ℤ, V n) (i : ℤ) :
    letI := DirectSum.rangeGradingDecomposition ℤ V
    ((DirectSum.decompose (DirectSum.rangeGrading ℤ V) x i :
        DirectSum.rangeGrading ℤ V i) : ⨁ n : ℤ, V n) = DirectSum.of V i (x i) := by
  classical
  let := DirectSum.rangeGradingDecomposition ℤ V
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j s =>
      have hmem : (DirectSum.of V j s : ⨁ n : ℤ, V n) ∈ DirectSum.rangeGrading ℤ V j :=
        (DirectSum.mem_rangeGrading ℤ V j _).mpr ⟨s, rfl⟩
      rw [DirectSum.decompose_of_mem (DirectSum.rangeGrading ℤ V) hmem]
      rcases eq_or_ne i j with rfl | hij
      · rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
      · have h1 : (DirectSum.of (fun k : ℤ => (DirectSum.rangeGrading ℤ V k : Type u)) j
            ⟨DirectSum.of V j s, hmem⟩) i = 0 :=
          DirectSum.of_eq_of_ne _ _ _ hij
        have h2 : (DirectSum.of V j s) i = 0 := DirectSum.of_eq_of_ne _ _ _ hij
        rw [h1, h2, ZeroMemClass.coe_zero, map_zero]
  | add y z hy hz =>
      rw [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add, hy, hz,
        DirectSum.add_apply, map_add]

/-- The degree-`i` homogeneous component of `x` for the tautological grading vanishes exactly when
the degree-`i` summand of `x` does. -/
private theorem coe_decompose_rangeGrading_eq_zero_iff (x : ⨁ n : ℤ, V n) (i : ℤ) :
    letI := DirectSum.rangeGradingDecomposition ℤ V
    ((DirectSum.decompose (DirectSum.rangeGrading ℤ V) x i :
        DirectSum.rangeGrading ℤ V i) : ⨁ n : ℤ, V n) = 0 ↔
      DirectSum.component ℤ ℤ V i x = 0 := by
  rw [coe_decompose_rangeGrading, ← DirectSum.apply_eq_component]
  exact ⟨fun h => DirectSum.of_injective (β := V) i (h.trans (map_zero _).symm),
    fun h => by rw [h, map_zero]⟩

/-- A degree-raising action makes the tautological grading a graded module: a homogeneous scalar
of degree `i` carries the degree-`n` summand into the degree-`i + n` summand, which is exactly
the compatibility `SetLike.GradedSMul` asks for. -/
@[instance_reducible] public def gradedActionGradedSMul [Module S (⨁ n : ℤ, V n)]
    (act : ∀ (i : ℕ) (n : ℤ), 𝒮 i → V n → V ((i : ℤ) + n))
    (hsmul : ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : V n),
      (a : S) • (DirectSum.of V n s : ⨁ m : ℤ, V m) =
        DirectSum.of V ((i : ℤ) + n) (act i n a s)) :
    SetLike.GradedSMul 𝒮 (DirectSum.rangeGrading ℤ V) where
  smul_mem {i n a b} ha hb := by
    obtain ⟨s, rfl⟩ := (DirectSum.mem_rangeGrading ℤ V n b).mp hb
    exact (DirectSum.mem_rangeGrading ℤ V ((i : ℤ) + n) _).mpr
      ⟨act i n ⟨a, ha⟩ s, hsmul i n ⟨a, ha⟩ s⟩

variable [Module S (⨁ n : ℤ, V n)]
  (act : ∀ (i : ℕ) (n : ℤ), 𝒮 i → V n → V ((i : ℤ) + n))
  (hsmul : ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : V n),
    (a : S) • (DirectSum.of V n s : ⨁ m : ℤ, V m) =
      DirectSum.of V ((i : ℤ) + n) (act i n a s))

include hsmul in
/-- The truncation of a graded action is the truncation of the graded module: both are cut out by
the vanishing of the components in degrees `< k`, the first reading those components as summands
and the second through the decomposition of the tautological grading. -/
public theorem gradedActionTruncation_eq_truncationAbove (k : ℤ) :
    letI := DirectSum.rangeGradingDecomposition ℤ V
    letI := gradedActionGradedSMul 𝒮 act hsmul
    (gradedActionTruncation 𝒮 act hsmul k : Set (⨁ n : ℤ, V n)) =
      (Stacks.GradedModule.truncationAbove 𝒮 (DirectSum.rangeGrading ℤ V) k :
        Set (⨁ n : ℤ, V n)) := by
  let := DirectSum.rangeGradingDecomposition ℤ V
  let := gradedActionGradedSMul 𝒮 act hsmul
  ext x
  constructor
  · exact fun hx i hi => (coe_decompose_rangeGrading_eq_zero_iff x i).mpr (hx i hi)
  · exact fun hx n hn => (coe_decompose_rangeGrading_eq_zero_iff x n).mp (hx n hn)

include hsmul in
/-- A graded truncation whose residue classes are finitely generated over the Veronese subring is
a finite module over the ring.

For each residue `q < d`, `h` supplies a finite subset `G` of the truncation such that every
element of the truncation supported in the degrees congruent to `q` modulo `d` lies in the
`S⁽ᵈ⁾`-span of `G`. The `d` sets together then span the truncation over `S⁽ᵈ⁾`, hence over `S`,
and they are finitely many finite sets. -/
public theorem moduleFinite_gradedActionTruncation_of_residues {d : ℕ} (hd : 0 < d) (k : ℤ)
    (h : ∀ q < d, ∃ G : Set (⨁ n : ℤ, V n), G.Finite ∧
      G ⊆ (gradedActionTruncation 𝒮 act hsmul k : Set (⨁ n : ℤ, V n)) ∧
      ∀ y ∈ gradedActionTruncation 𝒮 act hsmul k,
        (∀ n : ℤ, Stacks.Veronese.degreeResidue d n ≠ q →
          DirectSum.component ℤ ℤ V n y = 0) →
        y ∈ Submodule.span (Stacks.Veronese.veroneseSubring 𝒮 d) G) :
    Module.Finite S (gradedActionTruncation 𝒮 act hsmul k) := by
  classical
  let := DirectSum.rangeGradingDecomposition ℤ V
  let := gradedActionGradedSMul 𝒮 act hsmul
  choose! G hGfin hGsub hGspan using h
  have hcoe := Set.ext_iff.mp <| gradedActionTruncation_eq_truncationAbove 𝒮 act hsmul k
  -- the union of the `d` families
  set T : Set (⨁ n : ℤ, V n) := ⋃ q ∈ Finset.range d, G q
  have hTfin : T.Finite :=
    Set.Finite.biUnion (Finset.range d).finite_toSet fun q hq => hGfin q (Finset.mem_range.mp hq)
  have hTsub : T ⊆ (gradedActionTruncation 𝒮 act hsmul k : Set (⨁ n : ℤ, V n)) := by
    intro z hz
    obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.mp hz
    exact hGsub q (Finset.mem_range.mp hq) hzq
  -- the truncation is the `S`-span of `T`
  have hspan : gradedActionTruncation 𝒮 act hsmul k = Submodule.span S T := by
    refine le_antisymm (fun x hx => ?_) (Submodule.span_le.mpr hTsub)
    have hmem : x ∈ Submodule.span (Stacks.Veronese.veroneseSubring 𝒮 d) T := by
      refine Stacks.Veronese.mem_span_of_mem_truncationAbove 𝒮 (DirectSum.rangeGrading ℤ V) hd k
        G (fun q hq y hy hres => ?_) ((hcoe x).mp hx)
      refine hGspan q (Finset.mem_range.mp hq) y ?_ (fun n hn => ?_)
      · exact (hcoe y).mpr hy
      · exact (coe_decompose_rangeGrading_eq_zero_iff y n).mp (hres n hn)
    exact span_subring_subset_span S (Stacks.Veronese.veroneseSubring 𝒮 d) T hmem
  rw [hspan]
  exact Module.Finite.iff_fg.mpr ⟨hTfin.toFinset, by rw [Set.Finite.coe_toFinset]⟩

end Stacks.AlgebraicGeometry.ProjTwistedSections

end
