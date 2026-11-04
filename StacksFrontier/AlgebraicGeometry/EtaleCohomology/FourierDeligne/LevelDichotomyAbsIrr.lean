module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.SpanLatticeBound

/-!
# The level dichotomy of an absolutely irreducible integral representation

Let `O` be a domain with fraction field `E` and `ℓ ∈ O` an element such that every nonzero
element of `O` divides a power of `ℓ` (a discrete valuation ring with `ℓ` in its maximal ideal).
Let `S₀ ⊆ M_ι(O)` be closed under products and contain `1`, and absolutely irreducible: over an
algebraically closed field `K ⊇ E` its image stabilizes no subspace of `K^ι` other than `0` and
`K^ι`. Then there is a single exponent `c₀` such that at every level, for every commutative
`O`-algebra `R` and `N` with `ℓ^N r ≠ 0 ⇒ r ∣ ℓ` in `R` (as for `R = O/ℓ^{N+1}`), every
`S₀`-stable submodule `S ⊆ R^ι` with `ℓ^N S ≠ 0` contains `ℓ^{c₀} R^ι`.

Indeed by Burnside's theorem the `E`-span of `S₀` is `M_ι(E)`, so the `O`-span of `S₀` contains
`d • M_ι(O)` for a nonzero `d` dividing some `ℓ^c`; a vector `x ∈ S` with `ℓ^N x ≠ 0` has a
coordinate `x_j` dividing `ℓ`, and `S ⊇ d x_j R^ι ⊇ ℓ^{c+1} R^ι`.

This is the level dichotomy (Dich) of the single-level argument for the irreducibility of the
Fourier transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.exists_ne_zero_smul_mem_span_of_span_map_eq_top`.
* `Stacks.EtaleCohomology.exists_levelDichotomy_of_absIrr`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {O : Type*} (E : Type*) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
  [IsFractionRing O E] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A set of integral matrices whose images span `M_ι(E)` contains, in its `O`-span, a nonzero
multiple of each matrix unit. -/
theorem exists_ne_zero_smul_single_mem_span_of_span_map_eq_top (S₀ : Set (Matrix ι ι O))
    (h : Submodule.span E (Set.range fun a : S₀ => a.1.map (algebraMap O E)) = ⊤) (i j : ι) :
    ∃ d : O, d ≠ 0 ∧ d • Matrix.single i j (1 : O) ∈ Submodule.span O S₀ := by
  classical
  let φ : Matrix ι ι O →ₗ[O] Matrix ι ι E := (Algebra.linearMap O E).mapMatrix
  have hφ : Function.Injective φ := fun M N hMN => by
    ext a b
    exact IsFractionRing.injective O E (congrFun (congrFun hMN a) b)
  have hset : (Set.range fun a : S₀ => a.1.map (algebraMap O E)) = φ '' S₀ := by
    ext M
    simp [φ, Algebra.coe_linearMap]
  have hmem' : Matrix.single i j (1 : E) ∈ Submodule.span E (φ '' S₀) := by
    rw [← hset, h]
    exact Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hmem'
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    c.support (fun v => c v)
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  choose a ha using hint
  have : φ (b • Matrix.single i j (1 : O)) =
      φ (∑ v ∈ c.support.attach, a v.1 v.2 • v.1) := by
    rw [map_smul, map_sum]
    have h1 : φ (Matrix.single i j 1) = Matrix.single i j (1 : E) := by
      ext k l
      simp only [φ, LinearMap.mapMatrix_apply, Matrix.map_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [h1, ← hsum, Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum,
      ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hav := ha v.1 v.2
    simp only [Algebra.smul_def] at hav
    ext k l
    have hφv : φ v.1 k l = algebraMap O E (v.1 k l) := rfl
    rw [Matrix.smul_apply, Matrix.smul_apply, LinearMap.map_smul, Matrix.smul_apply, hφv,
      smul_eq_mul, Algebra.smul_def, Algebra.smul_def, hav]
    ring
  rw [hφ this]
  exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (Submodule.subset_span (hc v.2))

omit [Fintype ι] [DecidableEq ι] in
/-- **A set of integral matrices whose images span `M_ι(E)` spans `d • M_ι(O)` over `O`** for a
nonzero `d ∈ O`: write each matrix unit as an `E`-combination of the images and clear
denominators. -/
theorem exists_ne_zero_smul_mem_span_of_span_map_eq_top [Finite ι] (S₀ : Set (Matrix ι ι O))
    (h : Submodule.span E (Set.range fun a : S₀ => a.1.map (algebraMap O E)) = ⊤) :
    ∃ d : O, d ≠ 0 ∧ ∀ M : Matrix ι ι O, d • M ∈ Submodule.span O S₀ := by
  classical
  have := Fintype.ofFinite ι
  choose d hd hdN using fun p : ι × ι =>
    exists_ne_zero_smul_single_mem_span_of_span_map_eq_top E S₀ h p.1 p.2
  refine ⟨∏ p, d p, Finset.prod_ne_zero_iff.2 fun p _ => hd p, fun M => ?_⟩
  rw [Matrix.matrix_eq_sum_single M, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have : (∏ p, d p) • Matrix.single i j (M i j) =
      (M i j * ∏ p ∈ Finset.univ.erase (i, j), d p) • (d (i, j) • Matrix.single i j (1 : O)) := by
    rw [smul_smul, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ (i, j))]
    ext k l
    simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [this]
  exact Submodule.smul_mem _ _ (hdN (i, j))

/-- **The level dichotomy of an absolutely irreducible integral representation.** Let `S₀ ⊆
M_ι(O)` contain `1`, be closed under products, and stabilize no subspace of `K^ι` other than `0`
and `K^ι` over an algebraically closed `K ⊇ E`; let every nonzero element of `O` divide a power of
`ℓ`. There is `c₀` such that for every commutative `O`-algebra `R` and every `N` with
`ℓ^N r ≠ 0 ⇒ r ∣ ℓ` in `R`, an `S₀`-stable submodule `S ⊆ R^ι` with `ℓ^N S ≠ 0` contains
`ℓ^{c₀} R^ι`. -/
theorem exists_levelDichotomy_of_absIrr (K : Type*) [Field K] [IsAlgClosed K] [Algebra E K]
    {ℓ : O} (hℓ : ∀ d : O, d ≠ 0 → ∃ c : ℕ, d ∣ ℓ ^ c) (S₀ : Set (Matrix ι ι O))
    (hmul : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b ∈ S₀) (hone : (1 : Matrix ι ι O) ∈ S₀)
    (hirr : ∀ W : Submodule K (ι → K),
      (∀ a ∈ S₀, ∀ v ∈ W, (a.map (algebraMap O E)).map (algebraMap E K) *ᵥ v ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    ∃ c₀ : ℕ, ∀ (R : Type) [CommRing R] [Algebra O R] (N : ℕ),
      (∀ r : R, ℓ ^ N • r ≠ 0 → ∃ t : R, algebraMap O R ℓ = r * t) →
      ∀ S : Submodule R (ι → R), (∀ a ∈ S₀, ∀ v ∈ S, a.map (algebraMap O R) *ᵥ v ∈ S) →
        (∃ x ∈ S, ℓ ^ N • x ≠ 0) → ∀ w : ι → R, ℓ ^ c₀ • w ∈ S := by
  have hspan : Submodule.span E (Set.range fun a : S₀ => a.1.map (algebraMap O E)) = ⊤ :=
    span_range_eq_top_of_forall_mulVec_map_mem (K := K) (fun a : S₀ => a.1.map (algebraMap O E))
      (fun a b => ⟨⟨a.1 * b.1, hmul a.1 a.2 b.1 b.2⟩, (Matrix.map_mul).symm⟩)
      ⟨⟨1, hone⟩, Matrix.map_one _ (map_zero _) (map_one _)⟩
      (fun W hW => hirr W fun a ha v hv => hW ⟨a, ha⟩ v hv)
  obtain ⟨d, hd, hdS⟩ := exists_ne_zero_smul_mem_span_of_span_map_eq_top E S₀ hspan
  obtain ⟨c, e, he⟩ := hℓ d hd
  refine ⟨c + 1, fun R _ _ N hdiv S hS ⟨x, hx, hxN⟩ w => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, ℓ ^ N • x j ≠ 0 := Function.ne_iff.1 hxN
  obtain ⟨t, ht⟩ := hdiv (x j) hj
  have hw : ℓ ^ (c + 1) • w = (algebraMap O R d * x j) • (algebraMap O R e * t) • w := by
    rw [smul_smul, algebra_compatible_smul R (ℓ ^ (c + 1)) w, pow_succ, he, map_mul, map_mul, ht]
    congr 1
    ring
  rw [hw]
  exact smul_mem_of_forall_matrix_mem S₀ d hdS S hS hx j _

end Stacks.EtaleCohomology

end
