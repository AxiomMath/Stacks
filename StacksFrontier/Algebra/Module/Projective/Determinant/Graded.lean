module

public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The determinant line is a graded submodule of the exterior algebra

Let `R` be a commutative ring and `M` a finite projective `R`-module. Stacks 0FJA
(`ProjectiveDeterminant.determinant_submodule_eq_annihilator`) identifies the determinant line
`det(M) ⊆ ⋀_R(M)` with the annihilator of the degree-one elements. That identification is
ungraded. This file refines it to one degree at a time:

```
component R M n = ⋀ⁿ_R M ⊓ (annihilator of the degree-one elements)
```

The determinant line is by construction the supremum over `n` of the rank-stratum summands
`ProjectiveDeterminant.component R M n`, and the `n`-th of those lies in `⋀ⁿ_R M`. Since the
exterior powers are an internal grading of the exterior algebra, intersecting the supremum with
`⋀ⁿ_R M` therefore picks out exactly the `n`-th summand.

The degreewise form is what a *sheaf-level* local description of the determinant needs: the
determinant of a sheaf of modules is the direct sum over the degrees of the degreewise
annihilators, so its comparison with the determinant of a module has to be built degree by
degree.

## Main results

* `ProjectiveDeterminant.iSup_inf_le_of_le_of_iSupIndep`: the order-theoretic step, in a modular
  lattice — a supremum whose members lie inside the corresponding members of an independent
  family meets one member of that family in the one summand.
* `ProjectiveDeterminant.component_eq_exteriorPower_inf_submodule`: the `n`-th rank-stratum
  summand is the degree-`n` part of the determinant line.
* `ProjectiveDeterminant.component_eq_exteriorPower_inf_annihilator`: **the degreewise form of
  Stacks 0FJA.**
* `ProjectiveDeterminant.map_annihilatorPart_eq_component`: the same, with the left-hand side
  written as a submodule of `⋀ⁿ_R M` pushed into the exterior algebra. This is the spelling
  `Stacks.ExteriorAnnihilator.part` is defined at, so it applies to that submodule directly.

## Implementation notes

Deliberately untagged. Stacks 0FJA states the ungraded identification, which
`ProjectiveDeterminant.determinant_submodule_eq_annihilator` already carries; the gradedness is
not part of that tag's statement.

## References

* [Stacks Project, Tag 0FJA](https://stacks.math.columbia.edu/tag/0FJA)
-/

@[expose] public section

namespace ProjectiveDeterminant

universe u v

/-! ### The order-theoretic step -/

variable {α : Type*} [CompleteLattice α] [IsModularLattice α]

/-- **A supremum, each member of which lies inside the corresponding member of an independent
family, meets one member of that family in the single summand sitting inside it.**

Splitting the supremum at the index `n` and applying the modular law, which is legitimate
because `p n ≤ q n`, leaves the meet of `q n` with the supremum of the other `p i`; that meet is
bottom because the other `p i` lie in the other `q i`, which are disjoint from `q n`. The
lattice of submodules of a module is modular but not distributive, so the modular law is the
step that has to be used here. -/
theorem iSup_inf_le_of_le_of_iSupIndep {ι : Type*} {p q : ι → α} (hpq : ∀ i, p i ≤ q i)
    (hq : iSupIndep q) (n : ι) : (⨆ i, p i) ⊓ q n ≤ p n := by
  classical
  have hsplit : (⨆ i, p i) = p n ⊔ ⨆ (i) (_ : i ≠ n), p i := by
    refine le_antisymm (iSup_le fun i => ?_)
      (sup_le (le_iSup _ n) (iSup_le fun i => iSup_le fun _ => le_iSup _ i))
    by_cases h : i = n
    · subst h
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup_of_le i (le_iSup_of_le h le_rfl))
  have hrest : (⨆ (i) (_ : i ≠ n), p i) ≤ ⨆ (i) (_ : i ≠ n), q i :=
    iSup_mono fun i => iSup_mono fun _ => hpq i
  have hdisj : (⨆ (i) (_ : i ≠ n), p i) ⊓ q n = ⊥ :=
    disjoint_iff.mp (Disjoint.mono_right hrest (hq n)).symm
  exact le_of_eq (by rw [hsplit, sup_inf_assoc_of_le _ (hpq n), hdisj, sup_bot_eq])

/-! ### The degreewise identification -/

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The `n`-th rank-stratum summand of the determinant line lies in the degree-`n` exterior
power, being the image of that exterior power under multiplication by a scalar. -/
theorem component_le_exteriorPower [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    component (R := R) (M := M) n ≤ ⋀[R]^n M := by
  unfold component
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  simpa only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    using Submodule.smul_mem _ (rankIdempotent (R := R) (M := M) n) hx

/-- **The `n`-th rank-stratum summand is the degree-`n` part of the determinant line.** The
determinant line is the supremum of the summands, the `n`-th summand lies in `⋀ⁿ_R M`, and the
exterior powers are an internal grading of the exterior algebra. -/
theorem component_eq_exteriorPower_inf_submodule [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) :
    component (R := R) (M := M) n = ⋀[R]^n M ⊓ submodule (R := R) (M := M) := by
  refine le_antisymm (le_inf (component_le_exteriorPower n) (component_le_submodule n)) ?_
  rw [submodule, inf_comm]
  exact iSup_inf_le_of_le_of_iSupIndep (fun k => component_le_exteriorPower k)
    ((DirectSum.Decomposition.isInternal fun i : ℕ => ⋀[R]^i M).submodule_iSupIndep) n

/-- **The degreewise form of Stacks 0FJA.** The `n`-th rank-stratum summand of the determinant
line is the set of elements of the degree-`n` exterior power annihilated by every degree-one
element of the exterior algebra. -/
theorem component_eq_exteriorPower_inf_annihilator [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) :
    component (R := R) (M := M) n =
      ⋀[R]^n M ⊓ ⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m)) := by
  rw [component_eq_exteriorPower_inf_submodule n, determinant_submodule_eq_annihilator R M]

/-- **The degree-`n` part of the annihilator of the degree-one elements, taken as a submodule of
`⋀ⁿ_R M` and pushed into the exterior algebra, is the `n`-th rank-stratum summand of the
determinant line.**

This is `ProjectiveDeterminant.component_eq_exteriorPower_inf_annihilator` written at the
spelling `Stacks.ExteriorAnnihilator.part`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorAnnihilatorStalk.lean`) is defined at,
namely as the comap of the annihilator along the inclusion of the degree-`n` exterior power, so
it applies to `part R M n` with no transport. It is stated here rather than there because the
content is module-level and that file is in the sheaf tree. -/
theorem map_annihilatorPart_eq_component [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    Submodule.map (⋀[R]^n M).subtype
        ((⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))).comap
          (⋀[R]^n M).subtype) =
      component (R := R) (M := M) n := by
  rw [Submodule.map_comap_subtype, component_eq_exteriorPower_inf_annihilator n]

/-! ### The rank idempotent above its own degree -/

/-- The rank-`n` idempotent annihilates `⋀^(n + 1 + j)_R M` for every `j`, by induction on `j`.
The degree `n + 1` case is the content: `⋀^(n+1)_R M` is spanned by the products `ι m * b` with
`b ∈ ⋀ⁿ_R M`, the rank-`n` idempotent carries such a `b` into `component R M n`, and that
summand is annihilated by every degree-one element by the graded form of Tag 0FJA. Each further
degree is one more factor of `ι m`, which commutes past the scalar. -/
private theorem rankIdempotent_smul_eq_zero_aux [Module.Finite R M] [Module.Projective R M]
    (n j : ℕ) : ∀ x ∈ ⋀[R]^(n + 1 + j) M, rankIdempotent (R := R) (M := M) n • x = 0 := by
  have step : ∀ k, (∀ b ∈ ⋀[R]^k M, ∀ m : M, rankIdempotent (R := R) (M := M) n •
      (ExteriorAlgebra.ι R m * b) = 0) → ∀ x ∈ ⋀[R]^(k + 1) M,
      rankIdempotent (R := R) (M := M) n • x = 0 := by
    intro k h x hx
    rw [show (⋀[R]^(k + 1) M) =
      LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) * (⋀[R]^k M) from
      pow_succ' _ _] at hx
    refine Submodule.mul_induction_on hx ?_ fun y z hy hz => by rw [smul_add, hy, hz, add_zero]
    rintro _ ⟨m, rfl⟩ b hb
    exact h b hb m
  induction j with
  | zero =>
      refine step n fun b hb m => ?_
      have hcomp : rankIdempotent (R := R) (M := M) n • b ∈ component (R := R) (M := M) n :=
        Submodule.mem_map.mpr ⟨b, hb, rfl⟩
      rw [component_eq_exteriorPower_inf_annihilator n] at hcomp
      rw [← mul_smul_comm]
      exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hcomp.2 m)
  | succ j ih =>
      exact step (n + 1 + j) fun b hb m => by rw [← mul_smul_comm, ih b hb, mul_zero]

/-- **The rank-`n` idempotent of a finite projective module annihilates every exterior power of
degree greater than `n`.**

Over the rank-`n` stratum the module has rank `n`, so the exterior powers above degree `n`
vanish there; the statement here is that global form of the same fact, with the idempotent
cutting out the stratum in place of a localization. The proof uses no localization: the
degree-`(n+1)` case is exactly the statement that multiplication by the idempotent carries
`⋀ⁿ_R M` into the annihilator of the degree-one elements, which is
`ProjectiveDeterminant.component_eq_exteriorPower_inf_annihilator`, and the higher degrees
follow by splitting off one degree-one factor at a time.

The special case of a module free of rank `n`, where the idempotent is `1` and the exterior
powers above degree `n` are themselves zero, is used inside the proof of
`ProjectiveDeterminant.determinant_submodule_eq_annihilator`. -/
@[sga "6 VII 4.1" "affine case"]
theorem rankIdempotent_smul_eq_zero_of_mem_exteriorPower [Module.Finite R M]
    [Module.Projective R M] {n k : ℕ} (hnk : n < k) {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^k M) : rankIdempotent (R := R) (M := M) n • x = 0 :=
  rankIdempotent_smul_eq_zero_aux n (k - (n + 1)) x
    (by rwa [show n + 1 + (k - (n + 1)) = k from by omega])

end ProjectiveDeterminant

end
