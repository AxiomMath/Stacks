module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.MonomialRankReduction
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodMultiplicative

/-!
# The graded pieces of the projection-kernel filtration

Let `D` be an ideal sheaf on a scheme `X`, let `A` be the ring of compatible global functions on
the infinitesimal thickenings `Eₙ₊₁ = (D ^ (n + 1)).subscheme` and let `Iₙ` be the projection
kernels. This file identifies the graded piece `Iₘ₊₁ / Iₘ₊₂` with the kernel of the restriction
`Γ(Eₘ₊₁, 𝒪) ⟶ Γ(Eₘ, 𝒪)`, and proves that `I₁ · (Iₘ₊₁ / Iₘ₊₂) = 0`, so that the graded piece
is a module over the residue ring `A / I₁`. It then specialises
`AlgebraicGeometry.SemistableReduction.le_span_pow_sup_iff_coeff_mem_ideal_one` to the
projection-kernel filtration.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningRestriction_projection_eq_zero` and
  `exists_projection_eq_of_thickeningRestriction_eq_zero`: the graded piece `Iₘ₊₁ / Iₘ₊₂` is the
  kernel of the restriction `Γ(Eₘ₊₁, 𝒪) ⟶ Γ(Eₘ, 𝒪)`, the second direction using surjectivity of
  the projections.
* `AlgebraicGeometry.Scheme.IdealSheafData`
  `.projection_mul_eq_of_sub_mem_formalNeighborhoodFiltration_one`: the action on a graded piece
  factors through the residue ring.
* `AlgebraicGeometry.Scheme.IdealSheafData.le_span_pow_sup_iff_coeff_mem_one_of_gradedPiece`:
  spanning and independence of the degree-`(m + 1)` monomials are one condition, given an
  elementwise comparison of the graded piece with a `k`-space that has a basis indexed by
  `Fin (m + 1 + 1)`.

## Implementation notes

The hypotheses on the comparison `ρ` in `le_span_pow_sup_iff_coeff_mem_one_of_gradedPiece` are
all required only on the kernel of the thickening restriction, additivity included. A comparison
built from the kernel description of the graded piece is additive only there, and an additive
extension to all of `Γ(Eₘ₊₁, 𝒪)` need not exist: in characteristic `p` the target `W` is an
`𝔽_p`-space, hence not divisible.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry.SemistableReduction

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-! ### The graded piece is the kernel of the thickening restriction -/

/-- The projection to the `(m + 1)`-st thickening sends the `(m + 1)`-st step of the filtration
into the kernel of the restriction to the `m`-th: a compatible function vanishing on `Eₘ` has its
`(m + 1)`-st component in that kernel. -/
public theorem thickeningRestriction_projection_eq_zero (m : ℕ)
    {a : formalNeighborhoodRing D} (ha : a ∈ formalNeighborhoodFiltration D (m + 1)) :
    thickeningRestriction D m (formalNeighborhoodProjection D (m + 1) a) = 0 := by
  rw [thickeningRestriction_formalNeighborhoodProjection]
  exact (mem_formalNeighborhoodFiltration_succ_iff D m a).1 ha

/-- **Every element of the kernel of the thickening restriction comes from the `(m + 1)`-st step
of the filtration**, when the projections are surjective. -/
public theorem exists_projection_eq_of_thickeningRestriction_eq_zero (m : ℕ)
    (hsurj : ∀ j, Function.Surjective (thickeningRestriction D j))
    {z : Γ(thickening D (m + 1), ⊤)} (hz : thickeningRestriction D m z = 0) :
    ∃ a ∈ formalNeighborhoodFiltration D (m + 1),
      formalNeighborhoodProjection D (m + 1) a = z := by
  obtain ⟨a, ha⟩ := surjective_formalNeighborhoodProjection D hsurj (m + 1) z
  refine ⟨a, (mem_formalNeighborhoodFiltration_succ_iff D m a).2 ?_, ha⟩
  show formalNeighborhoodProjection D m a = 0
  rwa [← thickeningRestriction_formalNeighborhoodProjection D m a, ha]

/-! ### The action on a graded piece factors through the residue ring -/

/-- **The action of the ring of compatible functions on a graded piece factors through the residue
ring `A / I₁`.**

If two compatible functions `a` and `b` agree modulo `I₁` — that is, their difference vanishes on
`E` itself — then they act the same way on the kernel of the restriction
`Γ(Eₘ₊₁, 𝒪) ⟶ Γ(Eₘ, 𝒪)`, which is the graded piece `Iₘ₊₁ / Iₘ₊₂`. Equivalently `I₁` annihilates
that piece, so the piece is a module over `A / I₁`. -/
public theorem projection_mul_eq_of_sub_mem_formalNeighborhoodFiltration_one (m : ℕ)
    {a b : formalNeighborhoodRing D}
    (hab : a - b ∈ formalNeighborhoodFiltration D 1)
    {z : Γ(thickening D (m + 1), ⊤)} (hz : thickeningRestriction D m z = 0) :
    formalNeighborhoodProjection D (m + 1) a * z =
      formalNeighborhoodProjection D (m + 1) b * z := by
  refine eq_of_sub_eq_zero ?_
  rw [← sub_mul, ← map_sub]
  refine mul_eq_zero_of_appTop_inclusion_eq_zero (D ^ 1) (D ^ (m + 1)) (D ^ (m + 2))
    (pow_succ_le_pow_succ D (show 0 ≤ m + 1 by omega))
    (pow_succ_le_pow_succ D (Nat.le_succ m)) (fun U => ?_) ?_ hz
  · simp only [ideal_pow, Pi.pow_apply]
    rw [← pow_add]
    exact le_of_eq (congrArg _ (by omega))
  · exact (thickeningRestrictionLE_formalNeighborhoodProjection D
      (show 0 ≤ m + 1 by omega) (a - b)).trans
      ((mem_formalNeighborhoodFiltration_succ_iff D 0 (a - b)).1 hab)

/-! ### Spanning and independence of the monomials in a graded piece -/

/-- **Spanning and independence of the degree-`(m + 1)` monomials are one condition for the
projection-kernel filtration**, given an elementwise comparison of the graded piece with a
`k`-space `W` that has a basis indexed by `Fin (m + 1 + 1)`: an additive, `φ`-semilinear
bijection `ρ` from the kernel of the thickening restriction onto `W`, each of these properties
being asked for only on that kernel. -/
public theorem le_span_pow_sup_iff_coeff_mem_one_of_gradedPiece
    (hsurj : ∀ j, Function.Surjective (thickeningRestriction D j))
    {k : Type u} [Field k] (φ : formalNeighborhoodRing D →+* k)
    (hφ : Function.Surjective φ)
    (hkerφ : RingHom.ker φ = formalNeighborhoodFiltration D 1)
    {x y : formalNeighborhoodRing D} (hx : x ∈ formalNeighborhoodFiltration D 1)
    (hy : y ∈ formalNeighborhoodFiltration D 1) (m : ℕ)
    {W : Type u} [AddCommGroup W] [Module k W]
    (ρ : Γ(thickening D (m + 1), ⊤) → W)
    (hρadd : ∀ {u v : Γ(thickening D (m + 1), ⊤)}, thickeningRestriction D m u = 0 →
      thickeningRestriction D m v = 0 → ρ (u + v) = ρ u + ρ v)
    (hρsmul : ∀ (a : formalNeighborhoodRing D) {z : Γ(thickening D (m + 1), ⊤)},
      thickeningRestriction D m z = 0 →
      ρ (formalNeighborhoodProjection D (m + 1) a * z) = φ a • ρ z)
    (hρker : ∀ {z : Γ(thickening D (m + 1), ⊤)}, thickeningRestriction D m z = 0 →
      (ρ z = 0 ↔ z = 0))
    (hρsurj : ∀ w : W, ∃ z, thickeningRestriction D m z = 0 ∧ ρ z = w)
    (b : Module.Basis (Fin (m + 1 + 1)) k W) :
    formalNeighborhoodFiltration D (m + 1) ≤
        Ideal.span {x, y} ^ (m + 1) ⊔ formalNeighborhoodFiltration D (m + 1 + 1) ↔
      ∀ c : ℕ → formalNeighborhoodRing D,
        (∑ j ∈ Finset.range (m + 1 + 1), c j * genMonomial x y (m + 1) j) ∈
          formalNeighborhoodFiltration D (m + 1 + 1) →
        ∀ j ≤ m + 1, c j ∈ formalNeighborhoodFiltration D 1 := by
  refine le_span_pow_sup_iff_coeff_mem_ideal_one (formalNeighborhoodFiltration D) φ
    (fun a => ρ (formalNeighborhoodProjection D (m + 1) a))
    (formalNeighborhoodFiltration_zero D) (formalNeighborhoodFiltration_mul_le D)
    (formalNeighborhoodFiltration_succ_le D) hφ hkerφ hx hy ?_ ?_ ?_ ?_ b
  · intro u v hu hv
    rw [map_add]
    exact hρadd (thickeningRestriction_projection_eq_zero D m hu)
      (thickeningRestriction_projection_eq_zero D m hv)
  · intro a z hz
    rw [map_mul]
    exact hρsmul a (thickeningRestriction_projection_eq_zero D m hz)
  · intro a ha
    rw [hρker (thickeningRestriction_projection_eq_zero D m ha)]
    exact mem_formalNeighborhoodFiltration_succ_iff D (m + 1) a |>.symm
  · intro w
    obtain ⟨z, hzker, hzw⟩ := hρsurj w
    obtain ⟨a, ha, haz⟩ := exists_projection_eq_of_thickeningRestriction_eq_zero D m hsurj hzker
    exact ⟨a, ha, by rw [haz, hzw]⟩

end AlgebraicGeometry.Scheme.IdealSheafData

end
