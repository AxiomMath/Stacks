module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension

/-!
# The dimension of affine space, and subsets that cannot be dense in it

Affine `n`-space over a field `k` has Krull dimension `n`. Consequently a subset of `𝔸(n; k)`
whose closure has dimension `< n` is not dense: its closure is a *proper* closed subset. Put
together with the image dimension bound of
`StacksFrontier.AlgebraicGeometry.Variety.ImageDimension`, this says that the image of a closed
subset of dimension `< n` under a morphism to `𝔸(n; k)` lies in a proper closed subset, which
is the form in which a dimension count is turned into a nonempty open complement.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_affineSpace_of_finite`: `dim 𝔸(n; Spec k) = #n`, and
  `AlgebraicGeometry.topologicalKrullDim_affineSpace_fin` the same for `n = Fin r`.
* `not_dense_of_topologicalKrullDim_closure_lt` and
  `closure_ne_univ_of_topologicalKrullDim_closure_lt`: in any space, a subset whose closure has
  dimension strictly below that of the ambient space is not dense. On affine `n`-space the
  ambient dimension is `n`, by `AlgebraicGeometry.topologicalKrullDim_affineSpace_of_finite`.
* `AlgebraicGeometry.AffineSpace.closure_image_ne_univ_of_topologicalKrullDim_lt`: for a
  morphism `f : X ⟶ 𝔸(n; Spec k)` of schemes over `k` with `X` a Noetherian space and a closed
  `A ⊆ X` with `dim A < n`, the closure of `f '' A` is a proper closed subset of `𝔸(n; Spec k)`.
* `AlgebraicGeometry.AffineSpace.closure_range_ne_univ_of_topologicalKrullDim_lt`: the same for
  the whole image of a scheme of dimension `< n`.

## Implementation notes

The dimension of `𝔸(n; Spec k)` is read off from the isomorphism `AffineSpace.SpecIso` with
`Spec k[n]`, the identification `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` of the
topological and ring-theoretic Krull dimensions, and
`MvPolynomial.ringKrullDim_of_isNoetherianRing`, which gives `dim k[n] = dim k + #n = #n`.

The non-density statements are phrased with the dimension of the *closure* on the left: for a
constructible or merely arbitrary subset `S` this is no stronger than a bound on `dim S` when
`S` is closed, and it is what the image dimension bound produces directly.
-/

@[expose] public section

open CategoryTheory Set TopologicalSpace

universe u

/-- A subset whose closure has dimension strictly smaller than the dimension of the ambient
space is not dense. -/
theorem not_dense_of_topologicalKrullDim_closure_lt {T : Type*} [TopologicalSpace T]
    {S : Set T} (h : topologicalKrullDim (closure S) < topologicalKrullDim T) : ¬ Dense S := by
  intro hd
  rw [hd.closure_eq, topologicalKrullDim_univ] at h
  exact h.false

/-- A subset whose closure has dimension strictly smaller than the dimension of the ambient
space has a *proper* closed subset as its closure. -/
theorem closure_ne_univ_of_topologicalKrullDim_closure_lt {T : Type*} [TopologicalSpace T]
    {S : Set T} (h : topologicalKrullDim (closure S) < topologicalKrullDim T) :
    closure S ≠ Set.univ :=
  fun he ↦ not_dense_of_topologicalKrullDim_closure_lt h (dense_iff_closure_eq.mpr he)

namespace AlgebraicGeometry

/-- **The Krull dimension of affine `n`-space over a field is `n`.** -/
theorem topologicalKrullDim_affineSpace_of_finite (k : Type u) [Field k] (n : Type u) [Finite n] :
    topologicalKrullDim (AffineSpace n (Spec (.of k))) = (Nat.card n : WithBot ℕ∞) :=
  calc topologicalKrullDim (AffineSpace n (Spec (.of k)))
      = topologicalKrullDim (PrimeSpectrum (MvPolynomial n k)) :=
        IsHomeomorph.topologicalKrullDim_eq _
          (TopCat.homeoOfIso
            (Scheme.forgetToTop.mapIso (AffineSpace.SpecIso n (.of k)))).isHomeomorph
    _ = ringKrullDim (MvPolynomial n k) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ = ringKrullDim k + Nat.card n := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ENat.card_eq_coe_natCard]; rfl
    _ = (Nat.card n : WithBot ℕ∞) := by simp

/-- **The Krull dimension of affine `r`-space over a field is `r`.** -/
theorem topologicalKrullDim_affineSpace_fin (k : Type u) [Field k] (r : ℕ) :
    topologicalKrullDim (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k))) = (r : WithBot ℕ∞) := by
  rw [topologicalKrullDim_affineSpace_of_finite]
  simp

namespace AffineSpace

variable (k : Type u) [Field k] (n : Type u) [Finite n]

/-- A subset of `𝔸(n; k)` whose closure has dimension at most `d < n` has proper closure. -/
private theorem closure_ne_univ_of_le_of_lt_card {S : Set (AffineSpace n (Spec (.of k)))}
    {d : WithBot ℕ∞} (hle : topologicalKrullDim (closure S) ≤ d)
    (h : d < (Nat.card n : WithBot ℕ∞)) : closure S ≠ Set.univ :=
  closure_ne_univ_of_topologicalKrullDim_closure_lt
    (hle.trans_lt (by rwa [topologicalKrullDim_affineSpace_of_finite]))

/-- **A closed subset of dimension `< n` has image in a proper closed subset of `𝔸(n; k)`.**
Let `f : X ⟶ 𝔸(n; Spec k)` be a morphism of schemes over `k` with `X` locally of finite type
over `k` and a Noetherian space, and let `A ⊆ X` be closed of dimension `< n`. Then the closure
of `f '' A` is a proper closed subset. -/
theorem closure_image_ne_univ_of_topologicalKrullDim_lt {X : Scheme.{u}}
    (f : X ⟶ AffineSpace n (Spec (.of k))) (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [NoetherianSpace X]
    (hf : f ≫ (AffineSpace n (Spec (.of k)) ↘ Spec (.of k)) = sX)
    {A : Set X} (hA : IsClosed A)
    (h : topologicalKrullDim A < (Nat.card n : WithBot ℕ∞)) :
    closure (f.base '' A) ≠ Set.univ :=
  closure_ne_univ_of_le_of_lt_card k n (topologicalKrullDim_closure_image_le k f sX _ hf hA) h

/-- **A scheme of dimension `< n` has image in a proper closed subset of `𝔸(n; k)`.** -/
theorem closure_range_ne_univ_of_topologicalKrullDim_lt {X : Scheme.{u}}
    (f : X ⟶ AffineSpace n (Spec (.of k))) (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [NoetherianSpace X]
    (hf : f ≫ (AffineSpace n (Spec (.of k)) ↘ Spec (.of k)) = sX)
    (h : topologicalKrullDim X < (Nat.card n : WithBot ℕ∞)) :
    closure (Set.range f.base) ≠ Set.univ :=
  closure_ne_univ_of_le_of_lt_card k n (topologicalKrullDim_closure_range_le k f sX _ hf) h

end AffineSpace

end AlgebraicGeometry

end
