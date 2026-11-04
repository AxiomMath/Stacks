module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# The ring of compatible functions on the infinitesimal thickenings of a divisor

Let `D` be an ideal sheaf on a scheme `X`. Its positive powers `D ^ (n + 1)` cut out an
increasing chain of closed subschemes `E₁ ⊆ E₂ ⊆ ⋯`, the *infinitesimal thickenings* of
the subscheme cut out by `D`, and restriction of global functions turns the rings
`Γ(Eₙ₊₁, ⊤)` into an inverse system. The ring of compatible sequences

`A = {a : ∀ n, Γ(Eₙ₊₁, ⊤) // ∀ n, restriction (a (n + 1)) = a n}`

is the subring of `∀ n, Γ(Eₙ₊₁, ⊤)` realising `lim Γ(Eₙ, 𝒪_{Eₙ})`. When `E` is an
exceptional curve of the first kind on a Noetherian scheme, Stacks 0C2K identifies `A` as
a two-dimensional regular complete local Noetherian ring whose `n`-th projection has
kernel the `n`-th power of the maximal ideal.

This file provides the ring `A` together with its projections and the two elementary
structural facts about the filtration by projection kernels that the Stacks proof of
0C2K uses: the kernels decrease, and they intersect in zero, i.e. `A` is *separated*
for the linear topology they define. The substantive content of 0C2K — completeness,
Noetherianity, regularity, dimension two, and the identification of the kernels with
powers of the maximal ideal — is not proved here; it needs the cohomology of the
twists `𝒪_{𝐏¹}(d)` and the normal sheaf of an exceptional curve, neither of which is in
the library yet (see the module docstring of the Stacks 0C2K proof: it runs through
Stacks 01R2, 01WX and 0B3P).

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.thickening` — the `(n + 1)`-st infinitesimal
  thickening `(D ^ (n + 1)).subscheme`.
* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningRestriction` — restriction of global
  functions from the `(n + 2)`-nd thickening to the `(n + 1)`-st.
* `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing` — the subring of
  compatible global functions on all the positive thickenings.
* `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodProjection` — projection to
  the `(n + 1)`-st thickening.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningRestriction_formalNeighborhoodProjection`
  — the projections are compatible with restriction.
* `AlgebraicGeometry.Scheme.IdealSheafData.ker_formalNeighborhoodProjection_antitone` — the
  projection kernels decrease.
* `AlgebraicGeometry.Scheme.IdealSheafData.iInf_ker_formalNeighborhoodProjection` — the
  projection kernels intersect in zero.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The `(n + 1)`-st infinitesimal thickening of the closed subscheme cut out by an ideal
sheaf, namely the subscheme cut out by the `(n + 1)`-st power of the ideal sheaf. -/
@[sga "2 VI 2.2" "partial",
  sga "2 XI 3.18",
  sga "2 XII 2.1",
  sga "3 III 0.1.7" "(1), special case",
  sga "3 XI 6.9"]
public abbrev thickening (n : ℕ) : Scheme.{u} := (D ^ (n + 1)).subscheme

/-- Restriction of global functions from the `(n + 2)`-nd infinitesimal thickening to the
`(n + 1)`-st, induced by the inclusion `D ^ (n + 2) ≤ D ^ (n + 1)` of ideal sheaves. -/
public def thickeningRestriction (n : ℕ) :
    Γ(thickening D (n + 1), ⊤) →+* Γ(thickening D n, ⊤) :=
  (inclusion
    (show D ^ (n + 2) ≤ D ^ (n + 1) from
      le_def.mpr (fun U ↦ by
        simp only [ideal_pow]
        exact Ideal.pow_le_pow_right (by omega)))).appTop.hom

/-- The ring of compatible global functions on all the positive infinitesimal thickenings
of an ideal sheaf: the inverse limit `lim Γ(Eₙ, 𝒪_{Eₙ})`, realised as the subring of
compatible sequences inside the product. -/
@[ega "IV 16.1.11"]
public def formalNeighborhoodRing : Subring (∀ n, Γ(thickening D n, ⊤)) where
  carrier := {a | ∀ n, thickeningRestriction D n (a (n + 1)) = a n}
  zero_mem' n := map_zero _
  one_mem' n := map_one _
  add_mem' ha hb n := by simp [map_add, ha n, hb n]
  mul_mem' ha hb n := by simp [map_mul, ha n, hb n]
  neg_mem' ha n := by simp [map_neg, ha n]

/-- Projection from the ring of compatible functions to the global functions on the
`(n + 1)`-st infinitesimal thickening. -/
public def formalNeighborhoodProjection (n : ℕ) :
    formalNeighborhoodRing D →+* Γ(thickening D n, ⊤) :=
  (Pi.evalRingHom (fun n ↦ Γ(thickening D n, ⊤)) n).comp
    (formalNeighborhoodRing D).subtype

/-- The projection to the `(n + 1)`-st thickening evaluates a compatible sequence at its
`n`-th term. -/
@[simp]
public theorem formalNeighborhoodProjection_apply (n : ℕ) (a : formalNeighborhoodRing D) :
    formalNeighborhoodProjection D n a = (a : ∀ n, Γ(thickening D n, ⊤)) n :=
  rfl

/-- The projections out of the ring of compatible functions are compatible with
restriction between successive thickenings. -/
public theorem thickeningRestriction_formalNeighborhoodProjection (n : ℕ)
    (a : formalNeighborhoodRing D) :
    thickeningRestriction D n (formalNeighborhoodProjection D (n + 1) a) =
      formalNeighborhoodProjection D n a :=
  a.2 n

/-- Restriction followed by projection to the `(n + 2)`-nd thickening is projection to the
`(n + 1)`-st. -/
public theorem thickeningRestriction_comp_formalNeighborhoodProjection (n : ℕ) :
    (thickeningRestriction D n).comp (formalNeighborhoodProjection D (n + 1)) =
      formalNeighborhoodProjection D n :=
  RingHom.ext (thickeningRestriction_formalNeighborhoodProjection D n)

/-- The kernels of the projections decrease: a compatible function vanishing on the
`(n + 2)`-nd thickening vanishes on the `(n + 1)`-st. -/
public theorem ker_formalNeighborhoodProjection_antitone (n : ℕ) :
    RingHom.ker (formalNeighborhoodProjection D (n + 1)) ≤
      RingHom.ker (formalNeighborhoodProjection D n) := fun a ha ↦ by
  rw [RingHom.mem_ker] at ha ⊢
  rw [← thickeningRestriction_formalNeighborhoodProjection D n a, ha, map_zero]

/-- The kernels of the projections are antitone in the index. -/
public theorem ker_formalNeighborhoodProjection_le_of_le {m n : ℕ} (h : m ≤ n) :
    RingHom.ker (formalNeighborhoodProjection D n) ≤
      RingHom.ker (formalNeighborhoodProjection D m) := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k hmk ih =>
    exact (ker_formalNeighborhoodProjection_antitone D k).trans ih

/-- The ring of compatible functions is separated for the linear topology defined by the
projection kernels: a compatible function vanishing on every thickening is zero. -/
public theorem iInf_ker_formalNeighborhoodProjection :
    (⨅ n, RingHom.ker (formalNeighborhoodProjection D n)) = ⊥ := by
  refine le_antisymm (fun a ha ↦ ?_) bot_le
  have h : ∀ n, (a : ∀ n, Γ(thickening D n, ⊤)) n = 0 := fun n ↦
    RingHom.mem_ker.mp (Ideal.mem_iInf.mp ha n)
  exact (Submodule.mem_bot _).mpr (Subtype.ext (funext h))

end AlgebraicGeometry.Scheme.IdealSheafData
