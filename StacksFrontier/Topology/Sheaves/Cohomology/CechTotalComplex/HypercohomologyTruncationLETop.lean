module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalDuality
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# Hypercohomology of the quotient brutal truncations in a fixed degree

Let `K` be a bounded below complex of `𝒪_X`-modules concentrated in degrees `≥ 0`. If the
hypercohomology in degree `N` of every term `Kᵉ[-e]`, `e ≤ p`, vanishes, so does that of the
quotient brutal truncation `σ^{≤p}K`: it is filtered with these graded pieces. Consequently the
inclusion `Kᵖ[-p] ⟶ σ^{≤p}K` of the top term is bijective on `H^N` as soon as `H^N(X, σ^{≤p-1}K)`
vanishes and the boundary map `H^{N-1}(X, σ^{≤p-1}K) ⟶ H^N(X, Kᵖ[-p])` is zero.

## Main results

* `Stacks.Cech.Hypercohomology.isZero_hypercohomology_truncLEPlus`: the vanishing.
* `Stacks.Cech.Hypercohomology.bijective_hypercohomologyMap_truncLEι`: the bijectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open StacksDraft.StupidTruncation
open Stacks.Cohomology.RightDerivedBoundary (toSC)

universe u

namespace Stacks.Cech.Hypercohomology

open scoped Stacks.StandardDerivedModel

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- **The middle term of a short exact sequence has vanishing hypercohomology in degree `n`** when
the two outer terms do. -/
theorem isZero_hypercohomology_X₂
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) (h₁ : IsZero (hypercohomology O S.X₁ n))
    (h₃ : IsZero (hypercohomology O S.X₃ n)) : IsZero (hypercohomology O S.X₂ n) := by
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun b b' => ?_⟩
  have hz : ∀ b : hypercohomology O S.X₂ n, b = 0 := fun b => by
    obtain ⟨a, rfl⟩ := (exact_f_g O S hS n b).1 ((ModuleCat.subsingleton_of_isZero h₃).elim _ _)
    rw [(ModuleCat.subsingleton_of_isZero h₁).elim a 0, map_zero]
  rw [hz b, hz b']

variable (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))

/-- The quotient brutal truncation `σ^{≤p}K`, `p < 0`, of a complex concentrated in nonnegative
degrees has no hypercohomology. -/
theorem isZero_hypercohomology_truncLEPlus_of_neg (h0 : ∀ n, n < 0 → IsZero (K.obj.X n))
    (p : ℤ) (hp : p < 0) (N : ℤ) : IsZero (hypercohomology O (truncLEPlus O K p) N) := by
  have : (truncLEPlus O K p).obj.IsStrictlyGE (N + 1) := by
    refine (CochainComplex.isStrictlyGE_iff _ _).2 fun j _ => ?_
    by_cases hj : j ≤ p
    · exact (h0 j (by omega)).of_iso (stupidTruncLEXIso K.obj p j hj)
    · exact isZero_truncLEPlus_X O K (by omega)
  exact isZero_hypercohomology O _ (N + 1) N (by omega)

/-- **The hypercohomology of `σ^{≤p}K` in degree `N` vanishes** when that of every term `Kᵉ[-e]`,
`e ≤ p`, does, for a complex concentrated in nonnegative degrees. -/
theorem isZero_hypercohomology_truncLEPlus (h0 : ∀ n, n < 0 → IsZero (K.obj.X n)) (N : ℤ)
    (p : ℤ) (hvan : ∀ e, e ≤ p → IsZero (hypercohomology O (singlePlus O (K.obj.X e) e) N)) :
    IsZero (hypercohomology O (truncLEPlus O K p) N) := by
  rcases lt_or_ge p (-1) with hp | hp
  · exact isZero_hypercohomology_truncLEPlus_of_neg K h0 p (by omega) N
  induction p, hp using Int.leInduction with
  | base => exact isZero_hypercohomology_truncLEPlus_of_neg K h0 (-1) (by omega) N
  | succ p _ ih =>
    exact isZero_hypercohomology_X₂ (truncLESC O K (p + 1) p rfl)
      (truncLESC_shortExact O K (p + 1) p rfl) N (hvan _ le_rfl)
      (ih fun e he => hvan e (by omega))

/-- **The inclusion of the top term `Kᵖ[-p] ⟶ σ^{≤p}K` is bijective on `H^N`** when
`H^N(X, σ^{≤p'}K)` vanishes, `p' + 1 = p`, and the boundary map
`H^M(X, σ^{≤p'}K) ⟶ H^N(X, Kᵖ[-p])`, `M + 1 = N`, is zero. -/
theorem bijective_hypercohomologyMap_truncLEι (p p' : ℤ) (hp : p' + 1 = p) (M N : ℤ)
    (hM : M + 1 = N) (h₃ : IsZero (hypercohomology O (truncLEPlus O K p') N))
    (hδ : ∀ y, boundary O (truncLESC O K p p' hp) (truncLESC_shortExact O K p p' hp) M N hM y = 0) :
    Function.Bijective (hypercohomologyMap O (truncLEι O K p) N) := by
  refine ⟨fun a a' haa' => ?_, fun b => ?_⟩
  · have hker : ∀ c, hypercohomologyMap O (truncLEι O K p) N c = 0 → c = 0 := fun c hc => by
      obtain ⟨y, rfl⟩ := (exact_boundary_f O (truncLESC O K p p' hp)
        (truncLESC_shortExact O K p p' hp) M N hM c).1 hc
      exact hδ y
    exact sub_eq_zero.1 (hker _ (by rw [map_sub, haa', sub_self]))
  · exact (exact_f_g O (truncLESC O K p p' hp) (truncLESC_shortExact O K p p' hp) N b).1
      ((ModuleCat.subsingleton_of_isZero h₃).elim _ _)

end Stacks.Cech.Hypercohomology

end
