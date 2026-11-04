module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.NonSmoothLocusDimension
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimensionTotal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The non-smooth locus of a family is small when its fibres over the base are small

Let `q : A ⟶ 𝔸(ι; Spec k)` be a morphism locally of finite presentation and let
`Σ` be its non-smooth locus with the reduced induced structure. Suppose `Σ` carries a second
morphism `p : Σ ⟶ X` to a scheme `X` of dimension at most `n` over `k`, and that each fibre of
`p` has dimension at most `r - (n + 1)`, where `r = #ι`. Then

`dim Σ ≤ (r - (n + 1)) + n = r - 1 < r`,

which is exactly the hypothesis of
`AlgebraicGeometry.exists_nonempty_opens_preimage_subset_smoothLocus`, so `q` is smooth over a
nonempty open of `𝔸(ι; Spec k)`.

This is the dimension count of the proof of [Stacks, Tag 0FD6]. There `A = H_univ` is the
universal divisor, `X` is the ambient smooth variety of dimension `n`, `p` is the projection
`Σ ⊆ H_univ ⊆ 𝔸^r_X → X`, and the fibre of `p` over a closed point `x` of `X` is the kernel of
the evaluation map `ev_x : V → L_x / 𝔪_x² L_x`; when `ev_x` is surjective that kernel has
codimension `n + 1` in the `r`-dimensional space `V`, which is the fibre bound assumed here.

## Main results

* `LinearMap.finrank_ker_add_finrank_eq_of_surjective` and
  `LinearMap.finrank_ker_eq_sub_of_surjective`: the kernel of a surjective linear map out of a
  finite dimensional space has dimension `dim V - dim W`. This is the computation producing the
  number `r - (n + 1)` from the surjectivity of `ev_x`.
* `AlgebraicGeometry.topologicalKrullDim_lt_of_fiber_le_of_target_le`: `dim S < r` for a scheme
  `S` over a base of dimension `≤ n` with fibres of dimension `≤ r - (n + 1)`, when
  `n + 1 ≤ r`.
* `AlgebraicGeometry.topologicalKrullDim_nonSmoothSubscheme_lt_of_fiber_le`: the same with `S`
  the non-smooth subscheme of a morphism.
* `AlgebraicGeometry.exists_nonempty_opens_preimage_subset_smoothLocus_of_fiber_le`: the
  resulting nonempty open of `𝔸(ι; Spec k)` over which `q` is smooth.
* `AlgebraicGeometry.topologicalKrullDim_nonSmoothSubscheme_lt_of_closedPoints` and
  `AlgebraicGeometry.exists_nonempty_opens_preimage_subset_smoothLocus_of_closedPoints`: the same
  two conclusions from a bound on the **sum** of the local fibre dimension and the local
  dimension of `X`, taken at the closed points of `Σ` only. Neither the fibres nor `X` carry a
  bound of their own, so the fibre dimension may vary from point to point; that is the form the
  count takes when `X` is not equidimensional.

## Implementation notes

The fibre bound is a *hypothesis* of every statement here, not a claim: identifying the fibre of
`p` over a point of `X` with the kernel of `ev_x` requires a chart for the family over that
point, which is not part of this file. The two linear-algebra results are the other half of that
identification — the dimension of the kernel once `ev_x` is known to be surjective — and are
stated separately so that the two halves can be composed when the chart is available. The
hypothesis `n + 1 ≤ r` is likewise a parameter; in the application it is the inequality
`finrank W ≤ finrank V` that surjectivity of `ev_x` forces, and it is what makes `r - 1` a
genuine subtraction in `ℕ`.

Dimensions live in `WithBot ℕ∞`, which has no subtraction, so the subtraction `r - (n + 1)` is
performed in `ℕ` and only then cast; `n + 1 ≤ r` is what makes that cast say what it looks like.

No `@[stacks]` attribute is attached to anything in this file: these are general lemmas with the
fibre dimension as a parameter, not the registration of a tag.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- **Rank-nullity for a surjection.** The kernel of a surjective linear map `ev : V → W` out of
a finite dimensional space satisfies `dim (ker ev) + dim W = dim V`. -/
theorem LinearMap.finrank_ker_add_finrank_eq_of_surjective {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    {ev : V →ₗ[k] W} (hev : Function.Surjective ev) :
    Module.finrank k (LinearMap.ker ev) + Module.finrank k W = Module.finrank k V := by
  have h := LinearMap.finrank_range_add_finrank_ker ev
  rw [LinearMap.range_eq_top.mpr hev, finrank_top] at h
  omega

/-- **The kernel of a surjection has codimension the dimension of the target.** The form in
which the fibre dimension `r - (n + 1)` of the family is produced: for `ev_x : V → L_x/𝔪_x²L_x`
surjective with `dim V = r` and `dim L_x/𝔪_x²L_x = n + 1`, the kernel has dimension
`r - (n + 1)`. -/
theorem LinearMap.finrank_ker_eq_sub_of_surjective {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    {ev : V →ₗ[k] W} (hev : Function.Surjective ev) :
    Module.finrank k (LinearMap.ker ev) = Module.finrank k V - Module.finrank k W := by
  have h := LinearMap.finrank_ker_add_finrank_eq_of_surjective hev
  omega

namespace AlgebraicGeometry

/-- **A scheme fibred in dimension `r - (n + 1)` over a base of dimension `n` has dimension
`< r`.** Let `p : S ⟶ X` be a morphism of schemes locally of finite type over a field `k`, with
`dim X ≤ n` and every fibre of `p` of local dimension at most `r - (n + 1)`. If `n + 1 ≤ r`
then `dim S < r`.

Both the fibre bound and `n + 1 ≤ r` are parameters: this is the general shape of the count, and
what supplies the two is particular to each application. -/
@[ega "IV 10.6.1" "(iii), special case", sga "6 X 3.3" "special case"]
theorem topologicalKrullDim_lt_of_fiber_le_of_target_le
    (k : Type u) [Field k] {S X : Scheme.{u}}
    (pS : S ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType pS] [LocallyOfFiniteType pX]
    (p : S ⟶ X) (hp : p ≫ pX = pS) {n r : ℕ} (hnr : n + 1 ≤ r)
    (hX : topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (hfib : ∀ z : S, topologicalKrullDimAt (p.fiber (p z)) (p.asFiber z) ≤
      ((r - (n + 1) : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim S < (r : WithBot ℕ∞) :=
  topologicalKrullDim_lt_of_topologicalKrullDimAt_fiber_le k pS pX p hp hfib hX
    (by rw [← Nat.cast_add]; exact_mod_cast (by omega : r - (n + 1) + n < r))

/-- **The non-smooth locus of `q` has dimension `< r`** when it admits a morphism to a scheme
`X` of dimension `≤ n` over `k` all of whose fibres have dimension `≤ r - (n + 1)`, and
`n + 1 ≤ r`.

This is `AlgebraicGeometry.topologicalKrullDim_lt_of_fiber_le_of_target_le` for
`S = Σ`, the non-smooth subscheme of `q`; its structure morphism over `k` is the closed
immersion into the source followed by the source's own structure morphism, hence locally of
finite type. -/
theorem topologicalKrullDim_nonSmoothSubscheme_lt_of_fiber_le
    (k : Type u) [Field k] {A B X : Scheme.{u}} (q : A ⟶ B) [LocallyOfFinitePresentation q]
    (sA : A ⟶ Spec (.of k)) [LocallyOfFiniteType sA]
    (pX : X ⟶ Spec (.of k)) [LocallyOfFiniteType pX]
    (p : q.nonSmoothSubscheme ⟶ X) (hp : p ≫ pX = q.nonSmoothSubschemeι ≫ sA)
    {n r : ℕ} (hnr : n + 1 ≤ r)
    (hX : topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (hfib : ∀ z : q.nonSmoothSubscheme,
      topologicalKrullDimAt (p.fiber (p z)) (p.asFiber z) ≤ ((r - (n + 1) : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim q.nonSmoothSubscheme < (r : WithBot ℕ∞) :=
  topologicalKrullDim_lt_of_fiber_le_of_target_le k (q.nonSmoothSubschemeι ≫ sA) pX p hp hnr
    hX hfib

/-- **A family whose non-smooth locus is fibred in small dimension over a small base is smooth
over a nonempty open of the parameter space.** With `r = #ι`, if the non-smooth locus `Σ` of
`q : A ⟶ 𝔸(ι; Spec k)` admits a morphism to a scheme `X` of dimension `≤ n` over `k` whose
fibres have dimension `≤ r - (n + 1)`, and `n + 1 ≤ r`, then there is a nonempty open `U` of
`𝔸(ι; Spec k)` with `q ⁻¹ᵁ U` inside the smooth locus of `q`.

This is the composite of `AlgebraicGeometry.topologicalKrullDim_nonSmoothSubscheme_lt_of_fiber_le`
with `AlgebraicGeometry.exists_nonempty_opens_preimage_subset_smoothLocus`; the conclusion is the
`hsing` hypothesis of
`Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral`. -/
theorem exists_nonempty_opens_preimage_subset_smoothLocus_of_fiber_le
    (k : Type u) [Field k] {A X : Scheme.{u}} (ι : Type u) [Finite ι]
    (q : A ⟶ AffineSpace ι (Spec (.of k))) [LocallyOfFinitePresentation q]
    (sA : A ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [NoetherianSpace A]
    (hq : q ≫ (AffineSpace ι (Spec (.of k)) ↘ Spec (.of k)) = sA)
    (pX : X ⟶ Spec (.of k)) [LocallyOfFiniteType pX]
    (p : q.nonSmoothSubscheme ⟶ X) (hp : p ≫ pX = q.nonSmoothSubschemeι ≫ sA)
    {n : ℕ} (hnr : n + 1 ≤ Nat.card ι)
    (hX : topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (hfib : ∀ z : q.nonSmoothSubscheme, topologicalKrullDimAt (p.fiber (p z)) (p.asFiber z) ≤
      ((Nat.card ι - (n + 1) : ℕ) : WithBot ℕ∞)) :
    ∃ U : (AffineSpace ι (Spec (.of k))).Opens,
      (U : Set (AffineSpace ι (Spec (.of k)))).Nonempty ∧
        ((q ⁻¹ᵁ U : A.Opens) : Set A) ⊆ (q.smoothLocus : Set A) :=
  exists_nonempty_opens_preimage_subset_smoothLocus k ι q sA hq
    (topologicalKrullDim_nonSmoothSubscheme_lt_of_fiber_le k q sA pX p hp hnr hX hfib)

/-- **The non-smooth locus of `q` has dimension `< r`** when it admits a morphism `p` to a scheme
`X` over `k` such that at every closed point `z` of the locus the local dimension of the fibre of
`p` through `z` and the local dimension of `X` at `p z` add up to at most `r - 1`.

This is `AlgebraicGeometry.topologicalKrullDim_le_of_isClosed_singleton_fiber_add_target` read on
the non-smooth subscheme, whose structure morphism over `k` is the closed immersion into the
source followed by the source's own. Relative to
`AlgebraicGeometry.topologicalKrullDim_nonSmoothSubscheme_lt_of_fiber_le` neither the fibres nor
the target carry a bound of their own: only their sum is bounded, and only over the closed
points. That is what the dimension count of [Stacks, Tag 0FD6] needs when `X` is not
equidimensional. -/
theorem topologicalKrullDim_nonSmoothSubscheme_lt_of_closedPoints
    (k : Type u) [Field k] {A B X : Scheme.{u}} (q : A ⟶ B) [LocallyOfFinitePresentation q]
    (sA : A ⟶ Spec (.of k)) [LocallyOfFiniteType sA]
    (pX : X ⟶ Spec (.of k)) [LocallyOfFiniteType pX]
    (p : q.nonSmoothSubscheme ⟶ X) (hp : p ≫ pX = q.nonSmoothSubschemeι ≫ sA)
    {r : ℕ} (hr : 1 ≤ r)
    (hfib : ∀ z : q.nonSmoothSubscheme, IsClosed ({z} : Set q.nonSmoothSubscheme) →
      topologicalKrullDimAt (p.fiber (p z)) (p.asFiber z) + topologicalKrullDimAt X (p z) ≤
        ((r - 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim q.nonSmoothSubscheme < (r : WithBot ℕ∞) :=
  lt_of_le_of_lt (topologicalKrullDim_le_of_isClosed_singleton_fiber_add_target k
    (q.nonSmoothSubschemeι ≫ sA) pX p hp hfib) (by exact_mod_cast (by omega : r - 1 < r))

/-- **A family whose non-smooth locus has small fibre-plus-target dimension at its closed points
is smooth over a nonempty open of the parameter space.** With `r = #ι`, if the non-smooth locus
`Σ` of `q : A ⟶ 𝔸(ι; Spec k)` admits a morphism `p` to a scheme `X` over `k` such that at every
closed point `z` of `Σ` the local dimension of the fibre of `p` through `z` and the local
dimension of `X` at `p z` add up to at most `r - 1`, and `1 ≤ r`, then there is a nonempty open
`U` of `𝔸(ι; Spec k)` with `q ⁻¹ᵁ U` inside the smooth locus of `q`.

This is the composite of
`AlgebraicGeometry.topologicalKrullDim_nonSmoothSubscheme_lt_of_closedPoints`
with `AlgebraicGeometry.exists_nonempty_opens_preimage_subset_smoothLocus`; the conclusion is the
`hsing` hypothesis of `Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral`. -/
theorem exists_nonempty_opens_preimage_subset_smoothLocus_of_closedPoints
    (k : Type u) [Field k] {A X : Scheme.{u}} (ι : Type u) [Finite ι]
    (q : A ⟶ AffineSpace ι (Spec (.of k))) [LocallyOfFinitePresentation q]
    (sA : A ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [NoetherianSpace A]
    (hq : q ≫ (AffineSpace ι (Spec (.of k)) ↘ Spec (.of k)) = sA)
    (pX : X ⟶ Spec (.of k)) [LocallyOfFiniteType pX]
    (p : q.nonSmoothSubscheme ⟶ X) (hp : p ≫ pX = q.nonSmoothSubschemeι ≫ sA)
    (hr : 1 ≤ Nat.card ι)
    (hfib : ∀ z : q.nonSmoothSubscheme, IsClosed ({z} : Set q.nonSmoothSubscheme) →
      topologicalKrullDimAt (p.fiber (p z)) (p.asFiber z) + topologicalKrullDimAt X (p z) ≤
        ((Nat.card ι - 1 : ℕ) : WithBot ℕ∞)) :
    ∃ U : (AffineSpace ι (Spec (.of k))).Opens,
      (U : Set (AffineSpace ι (Spec (.of k)))).Nonempty ∧
        ((q ⁻¹ᵁ U : A.Opens) : Set A) ⊆ (q.smoothLocus : Set A) :=
  exists_nonempty_opens_preimage_subset_smoothLocus k ι q sA hq
    (topologicalKrullDim_nonSmoothSubscheme_lt_of_closedPoints k q sA pX p hp
      hr hfib)

end AlgebraicGeometry

end
