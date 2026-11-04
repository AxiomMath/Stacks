module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.FiniteTateTower

/-! # Exactness of a stage of the degreewise finite tower below its index

The stage `N` of the degreewise finite tower has, for every `i + 2 ≤ N`, adjoined variables of
degree `i + 2` killing a spanning family of the degree-`i + 1` cycles of the stage `i + 1`, and
every later step adjoins variables of degree greater than `i + 2`. So the stage `N` is already
exact in degree `i + 1`: a cycle there comes from the stage `i + 1`, where it is a combination of
the prescribed family with coefficients of degree zero, and such a combination is a boundary one
step up.

`DividedPowers.TateResolution.exists_finiteTateColimit_boundary_of_cycle` is the same argument for
the colimit. Running it at a finite stage is what the finiteness criteria for complexes need: the
augmented complex of a stage is a complex of finite free modules over the coefficient algebra,
which the colimit's is not in any single degree range that sees all of it.

## Main results

* `DividedPowers.TateResolution.finiteTateChainMap_differential` — the structure morphisms of the
  tower commute with the differentials of their two stages.
* `DividedPowers.TateResolution.exists_finiteTateStage_boundary_of_cycle` — the stage `N` of the
  tower is exact in every degree `i + 1` with `i + 2 ≤ N`.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0BZ9](https://stacks.math.columbia.edu/tag/0BZ9)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] TateDatum.dga TateDatum.compatible

variable {R : Type u} [CommRing R] (A₀ : TateStageData.{u, v} R 0)

/-- **The structure morphisms of the tower commute with the differentials** of their two stages,
each step doing so by `DividedPowers.TateResolution.finiteTateStep_differential`. -/
public theorem finiteTateChainMap_differential {m k : ℕ} (h : m ≤ k)
    (a : (finiteTateAlgebra A₀ m).carrier) :
    finiteTateDifferential A₀ k
        ((chainMap (finiteTateAlgebra A₀) (finiteTateStep A₀) h).hom a) =
      (chainMap (finiteTateAlgebra A₀) (finiteTateStep A₀) h).hom
        (finiteTateDifferential A₀ m a) := by
  induction h with
  | refl => rw [chainMap_hom_self, chainMap_hom_self]
  | @step l hl ih =>
      rw [chainMap_succ (finiteTateAlgebra A₀) (finiteTateStep A₀) hl]
      change finiteTateDifferential A₀ (l + 1)
          ((finiteTateStep A₀ l).hom
            ((chainMap (finiteTateAlgebra A₀) (finiteTateStep A₀) hl).hom a)) =
        (finiteTateStep A₀ l).hom
          ((chainMap (finiteTateAlgebra A₀) (finiteTateStep A₀) hl).hom
            (finiteTateDifferential A₀ m a))
      rw [finiteTateStep_differential A₀ l, ih]

/-- **A combination with coefficients of degree zero of the cycles prescribed at the stage
`n` is a boundary already at the stage `n + 1`**, the boundary of the corresponding combination
of the variables adjoined there. -/
public theorem exists_finiteTateStage_boundary_of_combination (n : ℕ)
    (s : Finset (finiteTateIndex A₀ n))
    (c : finiteTateIndex A₀ n → (finiteTateAlgebra A₀ n).carrier)
    (hc : ∀ j : finiteTateIndex A₀ n, c j ∈ (finiteTateAlgebra A₀ n).grade 0) :
    ∃ b : (finiteTateAlgebra A₀ (n + 1)).carrier,
      b ∈ (finiteTateAlgebra A₀ (n + 1)).grade (n + 1) ∧
      finiteTateDifferential A₀ (n + 1) b =
        (finiteTateStep A₀ n).hom (∑ j ∈ s, c j * finiteTateCycle A₀ n j) := by
  have hdga : IsDifferentialGradedAlgebra (finiteTateAlgebra A₀ (n + 1)).grade
      (finiteTateDifferential A₀ (n + 1)) := finiteTateDga A₀ (n + 1)
  obtain ⟨b, hb, hdb⟩ := exists_boundary_of_gradeZero_combination
    (finiteTateAlgebra A₀ (n + 1)).grade (finiteTateDifferential A₀ (n + 1))
    (fun j => (finiteTateStep A₀ n).hom (finiteTateCycle A₀ n j))
    (finiteTateGenerator A₀ n) n (finiteTateGenerator_mem A₀ n)
    (finiteTateGenerator_differential A₀ n) s
    (fun j => (finiteTateStep A₀ n).hom (c j))
    (fun j => (finiteTateStep A₀ n).map_grade 0 _ (hc j))
  refine ⟨b, hb, hdb.trans ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => (map_mul (finiteTateStep A₀ n).hom _ _).symm

/-- **The stage `N` of the degreewise finite tower is exact in every degree `i + 1` with
`i + 2 ≤ N`**, provided the stage `i + 1` has a finite spanning family of its degree-`i + 1`
cycles.

The cycle comes from the stage `i + 1`, by
`DividedPowers.TateResolution.exists_chainMap_eq_of_mem_grade`, and is still a cycle there because
the structure morphisms are injective and commute with the differentials. There it is a
combination of the prescribed family with coefficients of degree zero, hence a boundary at the
stage `i + 2`, and boundaries are carried to boundaries. -/
public theorem exists_finiteTateStage_boundary_of_cycle {N i : ℕ} (hi : i + 2 ≤ N)
    (hspan : HasFiniteSpanningCycles (finiteTateStage A₀ (i + 1)).datum (i + 1))
    {a : (finiteTateAlgebra A₀ N).carrier} (ha : a ∈ (finiteTateAlgebra A₀ N).grade (i + 1))
    (hda : finiteTateDifferential A₀ N a = 0) :
    ∃ b : (finiteTateAlgebra A₀ N).carrier, b ∈ (finiteTateAlgebra A₀ N).grade (i + 2) ∧
      finiteTateDifferential A₀ N b = a := by
  have h1 : i + 1 ≤ N := by omega
  obtain ⟨y, hy, hya⟩ := exists_chainMap_eq_of_mem_grade (finiteTateAlgebra A₀)
    (finiteTateStep A₀) (finiteTateGenerator A₀)
    (finiteTateStage_isSetVariableExtension A₀) h1 ha
  have hdy : finiteTateDifferential A₀ (i + 1) y = 0 := by
    refine chainMap_injective (finiteTateAlgebra A₀) (finiteTateStep A₀)
      (finiteTateStep_injective A₀) h1 ?_
    rw [← finiteTateChainMap_differential A₀ h1 y, hya, hda, map_zero]
  obtain ⟨c, hc, hcy⟩ := exists_gradeZero_combination_of_chosenCycleFinset hspan hy hdy
  have hsum : ∑ j ∈ (chosenCycleFinset (finiteTateStage A₀ (i + 1)).datum (i + 1)).attach,
      c (finiteTateCycle A₀ (i + 1) j) * finiteTateCycle A₀ (i + 1) j = y :=
    (Finset.sum_attach _ fun z => c z * z).trans hcy
  obtain ⟨b, hb, hdb⟩ := exists_finiteTateStage_boundary_of_combination A₀ (i + 1)
    (chosenCycleFinset (finiteTateStage A₀ (i + 1)).datum (i + 1)).attach
    (fun j => c (finiteTateCycle A₀ (i + 1) j)) (fun j => hc _)
  refine ⟨(chainMap (finiteTateAlgebra A₀) (finiteTateStep A₀) hi).hom b,
    (chainMap (finiteTateAlgebra A₀) (finiteTateStep A₀) hi).map_grade (i + 2) b hb, ?_⟩
  have hdb' : finiteTateDifferential A₀ (i + 1 + 1) b = (finiteTateStep A₀ (i + 1)).hom y :=
    hdb.trans (congrArg (finiteTateStep A₀ (i + 1)).hom hsum)
  rw [finiteTateChainMap_differential A₀ hi b, hdb']
  rw [← chainMap_hom_le_succ (finiteTateAlgebra A₀) (finiteTateStep A₀) (i + 1) y,
    chainMap_hom_trans (finiteTateAlgebra A₀) (finiteTateStep A₀) (Nat.le_succ (i + 1)) hi y]
  exact hya

end DividedPowers.TateResolution

end
