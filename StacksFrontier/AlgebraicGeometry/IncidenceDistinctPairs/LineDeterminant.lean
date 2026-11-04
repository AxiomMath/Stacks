module

public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.LineEquations

/-!
# Three functionals killing a common corank-two subspace have vanishing determinants

`StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.LineEquations` reads the collinearity
determinants of Tag 0B1R forwards: if every `3 × 3` determinant `det (fᵢ (wⱼ))` vanishes then the
third point lies on the line joining the first two. This file is the converse, which is what
putting a triple of collinear points *into* the collinearity locus needs: if the three
functionals all vanish on the common kernel of the first two, then every one of those
determinants is zero.

The functionals here are not `k`-valued. At a point of the triple product the chart coordinates
take values in the residue field there, and they are `k`-linear only in the semilinear sense that
a scalar of `k` comes out through a fixed ring homomorphism `ρ : k → K`. So the statement is made
for a family of `ρ`-semilinear maps `V → K`, with additivity and semihomogeneity as explicit
hypotheses rather than through a `LinearMap`, which keeps the module instances on a residue field
out of the statement.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_spanning_pair_of_ker_ne_ker`: two nonzero
  functionals with different kernels admit two vectors spanning `V` modulo their common kernel.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.det_eq_zero_of_forall_mem_ker_inf_ker`: **the
  converse collinearity determinant.** Three `ρ`-semilinear maps vanishing on the common kernel
  of two nonzero functionals with different kernels have every `3 × 3` determinant zero.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.det_eq_zero_of_forall_apply_eq_zero`: the same for
  `k`-linear maps, where semihomogeneity is `map_smul`.

## Implementation notes

The common kernel of two nonzero functionals with different kernels has corank exactly two
(`AlgebraicGeometry.ProjectiveSpaceOfModule.finrank_quotient_inf_ker_eq_two`), but the proof
does not go through that count: it produces two explicit vectors `a` and `b` and, for each
`v`, the two
scalars expressing `v` modulo the common kernel, by solving the two linear equations
`f v' = g v' = 0` one after the other. That is cheaper than choosing a basis of the quotient and
it is also what the determinant argument consumes, since the scalars appear as the entries of the
`3 × 2` factor.

With that decomposition each matrix entry is `ρ αⱼ * φᵢ a + ρ βⱼ * φᵢ b`, so the matrix is a
product of a `3 × 2` and a `2 × 3` matrix and its determinant vanishes identically. For `Fin 3`
that is one `Matrix.det_fin_three` expansion closed by `ring`, which avoids introducing the
Cauchy–Binet formula or a rank argument.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u v

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- A `3 × 3` matrix whose entries factor through two columns has vanishing determinant: it is a
product of a `3 × 2` and a `2 × 3` matrix. -/
public theorem det_eq_zero_of_entries_eq_add {K : Type v} [CommRing K]
    (M : Matrix (Fin 3) (Fin 3) K) (s t : Fin 3 → K) (x y : Fin 3 → K)
    (hM : ∀ i j, M i j = x j * s i + y j * t i) : M.det = 0 := by
  rw [Matrix.det_fin_three, hM, hM, hM, hM, hM, hM, hM, hM, hM]
  ring

/-- **Two nonzero functionals with different kernels admit a pair of vectors spanning `V` modulo
their common kernel.** For each vector the two coefficients are read off by solving the two
linear equations in turn. -/
public theorem exists_spanning_pair_of_ker_ne_ker {f g : Module.Dual k V} (hf : f ≠ 0)
    (hg : g ≠ 0) (hne : LinearMap.ker f ≠ LinearMap.ker g) :
    ∃ a b : V, ∀ w : V, ∃ α β : k,
      w - α • a - β • b ∈ LinearMap.ker f ⊓ LinearMap.ker g := by
  -- `a` is killed by one of the two and not by the other, `b` is not killed by the first
  have key : ∀ {f g : Module.Dual k V}, f ≠ 0 → ¬ LinearMap.ker f ≤ LinearMap.ker g →
      ∃ a b : V, ∀ w : V, ∃ α β : k,
        w - α • a - β • b ∈ LinearMap.ker f ⊓ LinearMap.ker g := by
    intro f g hf hnle
    -- subtracting the right multiple of `x` kills any functional not vanishing on `x`
    have hkill : ∀ (h : Module.Dual k V) (w x : V), h x ≠ 0 → h (w - (h w / h x) • x) = 0 := by
      intro h w x hx
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx, sub_self]
    obtain ⟨a, ha0, ha1⟩ : ∃ a, f a = 0 ∧ g a ≠ 0 := by
      obtain ⟨a, ha, ha'⟩ := Set.not_subset.mp hnle
      exact ⟨a, ha, ha'⟩
    obtain ⟨b, hb0⟩ : ∃ b, f b ≠ 0 := by
      contrapose! hf
      exact LinearMap.ext hf
    refine ⟨a, b, fun w => ⟨g (w - (f w / f b) • b) / g a, f w / f b, ?_⟩⟩
    rw [sub_right_comm]
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr ?_, LinearMap.mem_ker.mpr ?_⟩
    · rw [map_sub, map_smul, ha0, smul_eq_mul, mul_zero, sub_zero, hkill f w b hb0]
    · exact hkill g _ a ha1
  by_cases hle : LinearMap.ker f ≤ LinearMap.ker g
  · have hnle : ¬ LinearMap.ker g ≤ LinearMap.ker f := fun h => hne (le_antisymm hle h)
    rw [inf_comm]
    exact key hg hnle
  · exact key hf hle

/-- **The converse collinearity determinant.** Let `f` and `g` be two nonzero functionals on `V`
with different kernels, and let `φ₀, φ₁, φ₂ : V → K` be additive and `ρ`-semihomogeneous for a
ring homomorphism `ρ : k → K`. If all three vanish on the common kernel of `f` and `g`, then
every `3 × 3` determinant `det (φᵢ (wⱼ))` vanishes.

This is the shape in which a triple of collinear points is put into the collinearity locus: the
three chart coordinates at a point of the triple product are semilinear in that sense, and
collinearity of the three points is exactly that the third kills the common kernel of the first
two. -/
public theorem det_eq_zero_of_forall_mem_ker_inf_ker {K : Type v} [CommRing K] (ρ : k →+* K)
    (φ : Fin 3 → V → K)
    (hadd : ∀ i (v w : V), φ i (v + w) = φ i v + φ i w)
    (hsmul : ∀ i (c : k) (v : V), φ i (c • v) = ρ c * φ i v)
    {f g : Module.Dual k V} (hf : f ≠ 0) (hg : g ≠ 0)
    (hne : LinearMap.ker f ≠ LinearMap.ker g)
    (hker : ∀ i, ∀ v ∈ LinearMap.ker f ⊓ LinearMap.ker g, φ i v = 0)
    (w : Fin 3 → V) :
    (Matrix.of fun i j => φ i (w j)).det = 0 := by
  obtain ⟨a, b, hab⟩ := exists_spanning_pair_of_ker_ne_ker k V hf hg hne
  choose α β hαβ using hab
  -- every value is a combination of the values at `a` and at `b`
  have hval : ∀ (i : Fin 3) (x : V),
      φ i x = ρ (α x) * φ i a + ρ (β x) * φ i b := by
    intro i x
    calc φ i x = φ i (α x • a + (β x • b + (x - α x • a - β x • b))) := by
          rw [show α x • a + (β x • b + (x - α x • a - β x • b)) = x by abel]
      _ = ρ (α x) * φ i a + ρ (β x) * φ i b := by
          rw [hadd, hadd, hsmul, hsmul, hker i _ (hαβ x), add_zero]
  exact det_eq_zero_of_entries_eq_add _ (fun i => φ i a) (fun i => φ i b)
    (fun j => ρ (α (w j))) (fun j => ρ (β (w j))) fun i j => hval i (w j)

/-- **The converse collinearity determinant for `k`-linear maps.** The semihomogeneity of
`AlgebraicGeometry.ProjectiveSpaceOfModule.det_eq_zero_of_forall_mem_ker_inf_ker` is `map_smul`
when the three maps are honest `k`-linear maps into a `k`-algebra. -/
public theorem det_eq_zero_of_forall_apply_eq_zero {K : Type v} [CommRing K] [Algebra k K]
    (lam : Fin 3 → (V →ₗ[k] K)) {f g : Module.Dual k V} (hf : f ≠ 0) (hg : g ≠ 0)
    (hne : LinearMap.ker f ≠ LinearMap.ker g)
    (hker : ∀ i, LinearMap.ker f ⊓ LinearMap.ker g ≤ LinearMap.ker (lam i))
    (w : Fin 3 → V) :
    (Matrix.of fun i j => lam i (w j)).det = 0 :=
  det_eq_zero_of_forall_mem_ker_inf_ker k V (algebraMap k K) (fun i x => lam i x)
    (fun i v w => map_add (lam i) v w)
    (fun i c v => by rw [map_smul, Algebra.smul_def]) hf hg hne
    (fun i v hv => LinearMap.mem_ker.mp (hker i hv)) w

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
