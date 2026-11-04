module

public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodRing
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ExceptionalFiltration

/-!
# The projection-kernel filtration on the ring of compatible functions

Let `D` be an ideal sheaf on a scheme `X` and let
`A = AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing D` be the ring of
compatible global functions on the infinitesimal thickenings `Eₙ₊₁ = (D ^ (n + 1)).subscheme`.
Projection to the `(n + 1)`-st thickening has a kernel, and those kernels define a decreasing
filtration

`A = I₀ ⊇ I₁ ⊇ I₂ ⊇ ⋯`,  `I₀ = A`,  `Iₙ₊₁ = ker (A ⟶ Γ(Eₙ₊₁, 𝒪))`.

This file proves everything about that filtration that holds for an arbitrary ideal sheaf on an
arbitrary scheme, with no hypothesis on `D` and no input from the cohomology of the
thickenings. Three of the eleven axioms of
`AlgebraicGeometry.SemistableReduction.MonomialFiltration` are of that kind: the filtration
starts at `⊤`, it decreases, and it is *separated*. The fourth and least obvious one is
*completeness*: a series `∑ cₑ` whose `n`-th term lies in `Iₙ` converges in `A`.

Completeness here is a formal property of an inverse limit and needs no cohomology. A term
`cₑ` lying in `Iₑ` has vanishing `m`-th component for every `m ≤ e - 1`, so for each fixed `m`
the sequence of `m`-th components `(cₑ)ₘ` is zero as soon as `e ≥ m + 2`. The componentwise
sum is therefore a *finite* sum in each component, and the element it defines is already
compatible, hence already in `A`. No surjectivity of the transition maps
`Γ(Eₙ₊₂, 𝒪) ⟶ Γ(Eₙ₊₁, 𝒪)` is used, and so no vanishing of `H¹(𝐏¹_k, 𝒪(n))`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodFiltration` — the filtration by
  the projection kernels, with `0`-th step the whole ring.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.mem_formalNeighborhoodFiltration_succ_iff` — a
  compatible function lies in `Iₙ₊₁` exactly when its `(n + 1)`-st component vanishes, and then
  all earlier components vanish too.
* `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodFiltration_succ_le` — the
  filtration decreases.
* `AlgebraicGeometry.Scheme.IdealSheafData.iInf_formalNeighborhoodFiltration` — the filtration
  is separated.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_sum_formalNeighborhoodFiltration` — the
  filtration is complete, unconditionally.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The filtration of the ring of compatible functions on the infinitesimal thickenings of `D`
by the kernels of the projections: the `0`-th step is the whole ring and the `(n + 1)`-st step
is the kernel of the projection to the `(n + 1)`-st thickening. -/
public def formalNeighborhoodFiltration : ℕ → Ideal (formalNeighborhoodRing D)
  | 0 => ⊤
  | n + 1 => RingHom.ker (formalNeighborhoodProjection D n)

/-- The `0`-th step of the filtration is the whole ring. -/
@[simp]
public theorem formalNeighborhoodFiltration_zero :
    formalNeighborhoodFiltration D 0 = ⊤ := rfl

/-- The `(n + 1)`-st step of the filtration is the kernel of the projection to the
`(n + 1)`-st thickening. -/
@[simp]
public theorem formalNeighborhoodFiltration_succ (n : ℕ) :
    formalNeighborhoodFiltration D (n + 1) =
      RingHom.ker (formalNeighborhoodProjection D n) := rfl

/-- A compatible function lies in the `(n + 1)`-st step of the filtration exactly when its
`(n + 1)`-st component vanishes. -/
public theorem mem_formalNeighborhoodFiltration_succ_iff (n : ℕ)
    (a : formalNeighborhoodRing D) :
    a ∈ formalNeighborhoodFiltration D (n + 1) ↔
      (a : ∀ n, Γ(thickening D n, ⊤)) n = 0 :=
  RingHom.mem_ker

/-- A compatible function in the `(n + 1)`-st step of the filtration has all its components up
to the `(n + 1)`-st equal to zero, not just the last one. -/
public theorem apply_eq_zero_of_mem_formalNeighborhoodFiltration_succ {n : ℕ}
    {a : formalNeighborhoodRing D} (ha : a ∈ formalNeighborhoodFiltration D (n + 1))
    {j : ℕ} (hj : j ≤ n) :
    (a : ∀ n, Γ(thickening D n, ⊤)) j = 0 :=
  RingHom.mem_ker.mp (ker_formalNeighborhoodProjection_le_of_le D hj ha)

/-- The filtration decreases. -/
public theorem formalNeighborhoodFiltration_succ_le (n : ℕ) :
    formalNeighborhoodFiltration D (n + 1) ≤ formalNeighborhoodFiltration D n := by
  cases n with
  | zero => exact le_top
  | succ m => exact ker_formalNeighborhoodProjection_antitone D m

/-- The filtration is separated: a compatible function in every step is zero. -/
public theorem iInf_formalNeighborhoodFiltration :
    (⨅ n, formalNeighborhoodFiltration D n) = ⊥ := by
  refine le_antisymm (le_of_le_of_eq ?_ (iInf_ker_formalNeighborhoodProjection D)) bot_le
  exact le_iInf fun n ↦ (iInf_le _ (n + 1)).trans_eq (formalNeighborhoodFiltration_succ D n)

/-- **Completeness of the projection-kernel filtration, unconditionally.**

Given a series `∑ cₑ` whose `n`-th term lies in the `n`-th step of the filtration, its
componentwise sum is a finite sum in each component, defines a compatible function, and is the
limit of the partial sums. This is the `exists_sum` axiom of
`AlgebraicGeometry.SemistableReduction.MonomialFiltration` for this filtration, and it holds
for every ideal sheaf on every scheme: no cohomology of the thickenings enters. -/
public theorem exists_sum_formalNeighborhoodFiltration (c : ℕ → formalNeighborhoodRing D)
    (hc : ∀ n, c n ∈ formalNeighborhoodFiltration D n) :
    ∃ s, ∀ n, s - ∑ e ∈ Finset.range n, c e ∈ formalNeighborhoodFiltration D n := by
  -- A term `c e` with `e ≥ m + 1` has vanishing `m`-th component.
  have hzero : ∀ m e : ℕ, m + 1 ≤ e → (c e : ∀ n, Γ(thickening D n, ⊤)) m = 0 := by
    intro m e he
    obtain ⟨t, rfl⟩ : ∃ t, e = t + 1 := ⟨e - 1, by omega⟩
    exact apply_eq_zero_of_mem_formalNeighborhoodFiltration_succ D (hc (t + 1)) (by omega)
  -- The candidate limit: in each component, the finite sum of the components of the terms.
  set f : ∀ n, Γ(thickening D n, ⊤) :=
    fun m ↦ ∑ e ∈ Finset.range (m + 1), (c e : ∀ n, Γ(thickening D n, ⊤)) m with hf
  have hmem : f ∈ formalNeighborhoodRing D := by
    intro m
    show thickeningRestriction D m (f (m + 1)) = f m
    rw [hf]
    simp only
    rw [map_sum, Finset.sum_range_succ]
    have hcompat : ∀ e ∈ Finset.range (m + 1),
        thickeningRestriction D m ((c e : ∀ n, Γ(thickening D n, ⊤)) (m + 1)) =
          (c e : ∀ n, Γ(thickening D n, ⊤)) m := fun e _ ↦ (c e).2 m
    rw [Finset.sum_congr rfl hcompat, (c (m + 1)).2 m, hzero m (m + 1) le_rfl, add_zero]
  refine ⟨⟨f, hmem⟩, fun n ↦ ?_⟩
  cases n with
  | zero => exact Submodule.mem_top
  | succ N =>
    rw [mem_formalNeighborhoodFiltration_succ_iff]
    push_cast
    simp [Finset.sum_apply, hf]

end AlgebraicGeometry.Scheme.IdealSheafData
