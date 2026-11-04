module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BidegreeFiltration

/-!
# The basic perturbation lemma for a nilpotent perturbation

Let `C^*` be a graded abelian group with two degree-`+1` additive maps `d₀` and `t`, with
`d = d₀ + t`, and suppose `d₀` is contracted onto a retract: there are a degree-`-1` map `h` and a
degree-`0` map `q` with

`h (d₀ x) + q x = x`  in degree `0`,    `d₀ (h x) + h (d₀ x) + q x = x`  in positive degrees.

The **basic perturbation lemma** says that if the composite `t ∘ h` is nilpotent then `d` is
contracted onto the *same* `q`, perturbed, with the perturbed homotopy

`H = h ∘ (1 + t h)⁻¹ = (1 + h t)⁻¹ ∘ h`,   `Q = (1 + h t)⁻¹ ∘ q ∘ (1 + t h)⁻¹`.

This module proves it.  Besides the contraction of `d₀` the only hypothesis is

`t (d x) + d₀ (t x) = 0`,

which is what `d² = 0` and `d₀² = 0` leave: it is the cross-term identity `d₀ t + t d₀ + t² = 0`
of the two differentials, written so that neither square appears.

## Why the perturbation is nilpotent and not merely locally nilpotent

In the application — the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] — `C^n` is
`M ⊗̂_D Ω^n_{D'}`, `d₀` is the relative part of the de Rham differential, `t` the base part and `h`
the relative divided power Poincaré homotopy.  The composite `t ∘ h` raises the number of
coefficient differentials of a form by one and lowers the number of variable differentials by one,
and in exterior degree `n` there are only `n + 1` bidegrees; so `(t h)^{n+1} = 0` *in each
degree*, with a bound depending on the degree and on nothing else.  That is what replaces the
source's spectral sequence of a filtered complex: the perturbation series terminates in each
degree, and no limit is taken.
`Crystalline.DividedPowerPolynomial.iterate_eq_zero_of_raisesProjectionDegree` is the form in
which that nilpotence is read off a bidegree decomposition.

Accordingly the nilpotence hypothesis below is `(t ∘ h)^[m i] = 0` on `C^{i+1}` for a *function*
`m : ℕ → ℕ`, not for one uniform exponent.

## The inverses are carried as variables with their equations

`Crystalline.FinitePerturbation.perturbedContraction` takes `S` and `T` as additive maps together
with the equations saying that they invert `1 + t h` and `1 + h t`, rather than spelling them as
`(1 + t h)⁻¹`.  That is the technique used throughout this chapter for completed maps: at the
application site every object is a completed tensor product and nothing may be allowed to unfold.
`Crystalline.FinitePerturbation.exists_inverse_one_add` produces such an `S` from nilpotence and
`Crystalline.FinitePerturbation.exists_perturbedContraction` packages the two.

## What is and is not claimed

The contraction identity `d H + H d + Q = 1` is proved with **no** side condition on `h`, which
is why it is stated on its own, before any retract is mentioned.  Given in addition the side
conditions

`h ∘ h = 0`,   `h ∘ ι = 0`,   `π ∘ h = 0`,   `π ∘ ι = 1`

of a *special* deformation retract, `Q` is shown to factor as `ι' ∘ π'` with `π' ∘ ι' = 1`, for
`ι' = T ∘ ι` and `π' = π ∘ S`; so the identity of `(C^*, d)` is homotopic to an idempotent through
the retract.

Given in addition that `d` squares to zero, `ι'` and `π'` are then shown to be **maps of
complexes** for the differential `d_L = π' ∘ d ∘ ι'` of the retract, which itself squares to zero;
so `ι' : (L^*, d_L) → (C^*, d)` is a homotopy equivalence, with `π' ι' = 1` on the nose and
`ι' π' = Q` homotopic to the identity.  That is the statement
`Crystalline.FinitePerturbation.exists_perturbedHomotopyEquiv`, and it is what the completed
clause of [Stacks, Lemma 60.21.2, Tag 07LD] asks for: a homotopy equivalence is in particular a
quasi-isomorphism.

The three chain-map statements come out of the contraction identity and the side conditions with
no further input, by the three vanishings

`H ∘ ι' = 0`,   `π' ∘ H = 0`,   `H ∘ d ∘ ι' = 0`,

the last of which is the contraction identity read at `ι' x` once the first two are known.

## Main definitions

* `Crystalline.FinitePerturbation.perturbedHomotopy` — **`H = h ∘ S`**, the perturbed homotopy.
* `Crystalline.FinitePerturbation.perturbedProjection` — **`Q = T ∘ q ∘ S`**, the perturbed
  projection in positive degrees, and `..._perturbedProjectionZero` in degree `0`.
* `Crystalline.FinitePerturbation.perturbedInclusion` and
  `Crystalline.FinitePerturbation.perturbedRetraction` — **`ι' = T ∘ ι` and `π' = π ∘ S`**, the
  perturbed comparison maps with the retract.
* `Crystalline.FinitePerturbation.perturbedRetractionFull` — `π'` in every degree, which is
  `π ∘ S` in a positive degree and `π` in degree `0`, nothing of negative degree being present.
* `Crystalline.FinitePerturbation.retractDifferential` — **`d_L = π' ∘ d ∘ ι'`**, the differential
  the retract inherits.

## Main results

* `Crystalline.FinitePerturbation.exists_inverse_one_add` — for a nilpotent additive
  endomorphism `v`, the map `1 + v` is invertible, with the inverse presented by its two
  equations.
* `Crystalline.FinitePerturbation.iterate_comp_swap` — `(h t)^{k+1} = h (t h)^k t`, so the
  nilpotence of `t h` gives that of `h t` and only one of the two has to be checked.
* `Crystalline.FinitePerturbation.perturbedContraction_zero` and
  `Crystalline.FinitePerturbation.perturbedContraction` — **the contraction identity for the
  perturbed differential**, in degree `0` and in positive degrees.
* `Crystalline.FinitePerturbation.exists_perturbedContraction` — **the basic perturbation
  lemma**: from the contraction of `d₀`, the cross-term identity and the nilpotence of `t ∘ h`,
  the identity of `C^*` is chain homotopic, for the differential `d`, to a perturbation of `q`.
* `Crystalline.FinitePerturbation.perturbedProjection_eq` and `..._perturbedProjectionZero_eq` —
  **`Q = ι' ∘ π'`** as soon as `q = ι ∘ π`.
* `Crystalline.FinitePerturbation.perturbedRetraction_perturbedInclusion` and
  `..._perturbedRetraction_perturbedInclusion_zero` — **`π' ∘ ι' = 1`**, under the side conditions
  of a special deformation retract.
* `Crystalline.FinitePerturbation.differential_inclusion` and
  `..._retraction_differential` — **the two comparison maps of a contracted complex are maps of
  complexes** for `d_L = π ∘ d ∘ ι`, stated over an abstract contraction with the three vanishings
  as hypotheses, so that the perturbed case is one application.
* `Crystalline.FinitePerturbation.retractDifferential_retractDifferential` — `d_L² = 0`, from
  `d² = 0` and the injectivity of `ι`.
* `Crystalline.FinitePerturbation.exists_perturbedHomotopyEquiv` — **the perturbation lemma as a
  homotopy equivalence**: from a special deformation retract of `d₀`, the cross-term identity,
  `d² = 0` and the nilpotence of `t ∘ h`, the retract carries a differential `d_L` for which `ι'`
  and `π'` are maps of complexes, `π' ι' = 1`, and `ι' π'` is chain homotopic to the identity.
* `Crystalline.FinitePerturbation.perturbedInclusion_eq_self` and
  `..._exists_homotopyEquivOfInclusion` — **the same conclusion with `ι` itself as the
  equivalence**, under the extra hypothesis `h (t (ι x)) = 0`, which makes the perturbation of
  `ι` trivial.  This is the form whose conclusion names the comparison map, as
  [Stacks, Lemma 60.20.2, Tag 07LD] does.
* `Crystalline.FinitePerturbation.exists_homotopyEquivOfInclusion_of_chainMap` — **and with the
  differential of the retract named too**, pinned by `ι` being a map of complexes for it.  Then
  the only existentially quantified data are the homotopy inverse and the homotopy.

## References

* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

universe u v

namespace Crystalline

namespace FinitePerturbation

/-! ### Inverting `1 + v` for a nilpotent `v` -/

section Inverse

variable {C : Type u} [AddCommGroup C]

/-- **`1 + v` is invertible for a nilpotent additive endomorphism `v`**, with the inverse
presented by the two equations `S x + v (S x) = x` and `S (x + v x) = x` rather than as a term.

An additive endomorphism of an abelian group is a `ℤ`-linear endomorphism, so this is the
invertibility of `1 + v` in the ring `Module.End ℤ C`, where it is
`IsNilpotent.isUnit_one_add`. -/
public theorem exists_inverse_one_add (v : C →+ C) (m : ℕ)
    (hv : ∀ x : C, (fun y ↦ v y)^[m] x = 0) :
    ∃ S : C →+ C, (∀ x : C, S x + v (S x) = x) ∧ (∀ x : C, S (x + v x) = x) := by
  have hpow : ∀ (k : ℕ) (x : C),
      ((v.toIntLinearMap : Module.End ℤ C) ^ k) x = (fun y ↦ v y)^[k] x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ l hl =>
      intro x
      have hmul : ((v.toIntLinearMap : Module.End ℤ C) ^ (l + 1)) x =
          ((v.toIntLinearMap : Module.End ℤ C) ^ l) (v x) := by
        rw [pow_succ]; rfl
      rw [hmul, hl (v x), Function.iterate_succ_apply]
  have hnil : IsNilpotent (v.toIntLinearMap : Module.End ℤ C) :=
    ⟨m, LinearMap.ext fun x ↦ (hpow m x).trans (hv x)⟩
  obtain ⟨u, hu⟩ := hnil.isUnit_one_add
  have h1 : ((1 : Module.End ℤ C) + v.toIntLinearMap) * (↑u⁻¹ : Module.End ℤ C) = 1 := by
    rw [← hu]; exact u.mul_inv
  have h2 : (↑u⁻¹ : Module.End ℤ C) * ((1 : Module.End ℤ C) + v.toIntLinearMap) = 1 := by
    rw [← hu]; exact u.inv_mul
  exact ⟨(↑u⁻¹ : Module.End ℤ C).toAddMonoidHom, fun x ↦ LinearMap.congr_fun h1 x,
    fun x ↦ LinearMap.congr_fun h2 x⟩

end Inverse

/-! ### Swapping the two composites -/

section Swap

variable {X : Type u} {Y : Type v} [AddCommGroup X] [AddCommGroup Y]

/-- **`(h t)^{k+1} = h (t h)^k t`.**  So if `t ∘ h` is nilpotent then so is `h ∘ t`, and only one
of the two composites has to be shown nilpotent. -/
public theorem iterate_comp_swap (t : X →+ Y) (h : Y →+ X) (k : ℕ) (x : X) :
    (fun y ↦ h (t y))^[k + 1] x = h ((fun y ↦ t (h y))^[k] (t x)) := by
  induction k generalizing x with
  | zero => rfl
  | succ l hl =>
    have h1 : (fun y ↦ h (t y))^[l + 1 + 1] x = (fun y ↦ h (t y))^[l + 1] (h (t x)) :=
      Function.iterate_succ_apply _ _ _
    have h2 : (fun y ↦ t (h y))^[l + 1] (t x) = (fun y ↦ t (h y))^[l] (t (h (t x))) :=
      Function.iterate_succ_apply _ _ _
    rw [h1, hl (h (t x)), h2]

/-- The nilpotence of `h ∘ t` from that of `t ∘ h`. -/
public theorem iterate_comp_eq_zero_of_swap (t : X →+ Y) (h : Y →+ X) (m : ℕ)
    (hv : ∀ y : Y, (fun y ↦ t (h y))^[m] y = 0) (x : X) :
    (fun y ↦ h (t y))^[m + 1] x = 0 := by
  rw [iterate_comp_swap t h m x, hv (t x), map_zero]

end Swap

/-! ### The shuffling lemma -/

section Aux

/-- The one piece of abelian group arithmetic the perturbed contraction identity comes down to,
isolated so that the shapes in the proof are not guessed: with `dk + a + qq = yy` the contraction
of `d₀` and `c₁ + c₂ + e = 0` the cross-term identity, the two sides agree. -/
private theorem shuffle {G : Type u} [AddCommGroup G] (a b c₁ c₂ e qq yy dk : G)
    (h1 : dk + a + qq = yy) (h2 : c₁ + c₂ + e = 0) :
    a + b + (c₁ + c₂) + qq = yy - dk + (b - e) := by
  have hy : yy - dk = a + qq := by rw [← h1]; abel
  have hce : c₁ + c₂ = -e := eq_neg_iff_add_eq_zero.mpr h2
  rw [hy, hce]
  abel

end Aux

/-! ### The perturbed contraction -/

section Perturbation

variable {C : ℕ → Type u} [∀ i, AddCommGroup (C i)] (d0 : ∀ i, C i →+ C (i + 1))
  (t : ∀ i, C i →+ C (i + 1)) (d : ∀ i, C i →+ C (i + 1)) (h : ∀ i, C (i + 1) →+ C i)
  (q : ∀ i, C i →+ C i) (S : ∀ i, C (i + 1) →+ C (i + 1)) (T : ∀ i, C i →+ C i)

/-- **The perturbed homotopy `H = h ∘ S`**, `S` being the inverse of `1 + t h`. -/
public def perturbedHomotopy (i : ℕ) : C (i + 1) →+ C i := (h i).comp (S i)

/-- **The perturbed projection `Q = T ∘ q ∘ S` in a positive degree.** -/
public def perturbedProjection (n : ℕ) : C (n + 1) →+ C (n + 1) :=
  (T (n + 1)).comp ((q (n + 1)).comp (S n))

/-- **The perturbed projection in degree `0`**, where there is no `S` to insert: nothing of
negative degree being present, the inverse of `1 + t h` is the identity there. -/
public def perturbedProjectionZero : C 0 →+ C 0 := (T 0).comp (q 0)

/-- **`h ∘ S = T ∘ h`**, the two readings of the perturbed homotopy.  The identity
`h (1 + t h) = (1 + h t) h` holds with no hypothesis, and inverting both factors turns it into
this. -/
public theorem perturbedHomotopy_eq
    (hS : ∀ (i : ℕ) (x : C (i + 1)), S i x + t i (h i (S i x)) = x)
    (hT' : ∀ (i : ℕ) (x : C i), T i (x + h i (t i x)) = x) (i : ℕ) (x : C (i + 1)) :
    perturbedHomotopy h S i x = T i (h i x) := by
  calc perturbedHomotopy h S i x = h i (S i x) := rfl
    _ = T i (h i (S i x) + h i (t i (h i (S i x)))) := (hT' i _).symm
    _ = T i (h i x) := by rw [← map_add, hS i x]

/-- **The contraction identity for the perturbed differential in degree `0`**:
`H (d x) + Q x = x` on `C⁰`.

In degree `0` no perturbation series is needed on the right: `h (d x) + q x` is already
`x + h (t x)`, which `T` sends back to `x`. -/
public theorem perturbedContraction_zero
    (hd : ∀ (i : ℕ) (x : C i), d i x = d0 i x + t i x)
    (hS : ∀ (i : ℕ) (x : C (i + 1)), S i x + t i (h i (S i x)) = x)
    (hT' : ∀ (i : ℕ) (x : C i), T i (x + h i (t i x)) = x)
    (hcon0 : ∀ x : C 0, h 0 (d0 0 x) + q 0 x = x) (x : C 0) :
    perturbedHomotopy h S 0 (d 0 x) + perturbedProjectionZero q T x = x := by
  have hinner : h 0 (d 0 x) + q 0 x = x + h 0 (t 0 x) := by
    rw [hd 0 x, map_add,
      show h 0 (d0 0 x) + h 0 (t 0 x) + q 0 x = h 0 (d0 0 x) + q 0 x + h 0 (t 0 x) from by abel,
      hcon0 x]
  calc perturbedHomotopy h S 0 (d 0 x) + perturbedProjectionZero q T x
      = T 0 (h 0 (d 0 x)) + T 0 (q 0 x) := by
        rw [perturbedHomotopy_eq t h S T hS hT' 0 (d 0 x)]; rfl
    _ = T 0 (h 0 (d 0 x) + q 0 x) := (map_add _ _ _).symm
    _ = T 0 (x + h 0 (t 0 x)) := by rw [hinner]
    _ = x := hT' 0 x

/-- **The computation the perturbed contraction identity rests on.**  For any `y` of degree
`n + 1`, with `k = h y`,

`h (d (y + t k)) + q y = (y - d₀ k) + h (t (y - d₀ k))`,

so that applying the inverse of `1 + h t` to the left-hand side returns `y - d₀ k`.  The only
input beyond the contraction of `d₀` is one application of the cross-term identity, which makes a
three-term expression vanish under `h`. -/
public theorem perturbedContraction_key
    (hd : ∀ (i : ℕ) (x : C i), d i x = d0 i x + t i x)
    (hcon : ∀ (n : ℕ) (x : C (n + 1)),
      d0 n (h n x) + h (n + 1) (d0 (n + 1) x) + q (n + 1) x = x)
    (hcross : ∀ (i : ℕ) (x : C i), t (i + 1) (d i x) + d0 (i + 1) (t i x) = 0) (n : ℕ)
    (y : C (n + 1)) :
    h (n + 1) (d (n + 1) (y + t n (h n y))) + q (n + 1) y =
      y - d0 n (h n y) + h (n + 1) (t (n + 1) (y - d0 n (h n y))) := by
  obtain ⟨k, hk⟩ : ∃ k : C n, h n y = k := ⟨_, rfl⟩
  have hcn : d0 n k + h (n + 1) (d0 (n + 1) y) + q (n + 1) y = y := by
    rw [← hk]; exact hcon n y
  have hc : t (n + 1) (d0 n k) + t (n + 1) (t n k) + d0 (n + 1) (t n k) = 0 := by
    have hx := hcross n k
    rwa [hd n k, map_add] at hx
  have he2 : h (n + 1) (d0 (n + 1) (t n k)) + h (n + 1) (t (n + 1) (t n k)) +
      h (n + 1) (t (n + 1) (d0 n k)) = 0 := by
    have h0 : h (n + 1) (t (n + 1) (d0 n k) + t (n + 1) (t n k) + d0 (n + 1) (t n k)) = 0 := by
      rw [hc, map_zero]
    simp only [map_add] at h0
    rw [show h (n + 1) (d0 (n + 1) (t n k)) + h (n + 1) (t (n + 1) (t n k)) +
        h (n + 1) (t (n + 1) (d0 n k)) =
      h (n + 1) (t (n + 1) (d0 n k)) + h (n + 1) (t (n + 1) (t n k)) +
        h (n + 1) (d0 (n + 1) (t n k)) from by abel]
    exact h0
  have hdx : d (n + 1) (y + t n k) =
      d0 (n + 1) y + t (n + 1) y + (d0 (n + 1) (t n k) + t (n + 1) (t n k)) := by
    rw [hd (n + 1) (y + t n k)]
    simp only [map_add]
    abel
  rw [hk, hdx]
  simp only [map_add, map_sub]
  exact shuffle _ _ _ _ _ _ _ _ hcn he2

/-- **The contraction identity for the perturbed differential in a positive degree**:
`d (H x) + H (d x) + Q x = x` on `C^{n+1}`.

With `y = S x` one has `x = y + t (h y)`, so
`Crystalline.FinitePerturbation.perturbedContraction_key` computes
`H (d x) + Q x = y - d₀ (h y)`, and `d (H x) = d₀ (h y) + t (h y)` returns `x`. -/
public theorem perturbedContraction
    (hd : ∀ (i : ℕ) (x : C i), d i x = d0 i x + t i x)
    (hS : ∀ (i : ℕ) (x : C (i + 1)), S i x + t i (h i (S i x)) = x)
    (hT' : ∀ (i : ℕ) (x : C i), T i (x + h i (t i x)) = x)
    (hcon : ∀ (n : ℕ) (x : C (n + 1)),
      d0 n (h n x) + h (n + 1) (d0 (n + 1) x) + q (n + 1) x = x)
    (hcross : ∀ (i : ℕ) (x : C i), t (i + 1) (d i x) + d0 (i + 1) (t i x) = 0) (n : ℕ)
    (x : C (n + 1)) :
    d n (perturbedHomotopy h S n x) + perturbedHomotopy h S (n + 1) (d (n + 1) x) +
        perturbedProjection q S T n x = x := by
  have hxy : x = S n x + t n (h n (S n x)) := (hS n x).symm
  have hkey := perturbedContraction_key d0 t d h q hd hcon hcross n (S n x)
  rw [← hxy] at hkey
  have hsum : perturbedHomotopy h S (n + 1) (d (n + 1) x) + perturbedProjection q S T n x =
      S n x - d0 n (h n (S n x)) := by
    rw [perturbedHomotopy_eq t h S T hS hT' (n + 1) (d (n + 1) x),
      show perturbedProjection q S T n x = T (n + 1) (q (n + 1) (S n x)) from rfl, ← map_add,
      hkey, hT' (n + 1) (S n x - d0 n (h n (S n x)))]
  calc d n (perturbedHomotopy h S n x) + perturbedHomotopy h S (n + 1) (d (n + 1) x) +
        perturbedProjection q S T n x
      = d n (perturbedHomotopy h S n x) +
        (perturbedHomotopy h S (n + 1) (d (n + 1) x) + perturbedProjection q S T n x) := by abel
    _ = d0 n (h n (S n x)) + t n (h n (S n x)) + (S n x - d0 n (h n (S n x))) := by
        rw [hsum, show d n (perturbedHomotopy h S n x) = d n (h n (S n x)) from rfl,
          hd n (h n (S n x))]
    _ = S n x + t n (h n (S n x)) := by abel
    _ = x := hxy.symm

end Perturbation

/-! ### The basic perturbation lemma -/

section Package

variable {C : ℕ → Type u} [∀ i, AddCommGroup (C i)]

/-- The inverses `S` of `1 + t h` and `T` of `1 + h t` in every degree, from the nilpotence of
`t ∘ h`. -/
private theorem exists_inverses_of_nilpotent (t : ∀ i, C i →+ C (i + 1))
    (h : ∀ i, C (i + 1) →+ C i) (m : ℕ → ℕ)
    (hnil : ∀ (i : ℕ) (x : C (i + 1)), (fun y ↦ t i (h i y))^[m i] x = 0) :
    ∃ (S : ∀ i, C (i + 1) →+ C (i + 1)) (T : ∀ i, C i →+ C i),
      (∀ (i : ℕ) (x : C (i + 1)), S i x + t i (h i (S i x)) = x) ∧
        (∀ (i : ℕ) (x : C i), T i x + h i (t i (T i x)) = x) ∧
          ∀ (i : ℕ) (x : C i), T i (x + h i (t i x)) = x := by
  choose S hS _ using fun i ↦ exists_inverse_one_add ((t i).comp (h i)) (m i) (hnil i)
  choose T hT hT' using fun i ↦
    exists_inverse_one_add ((h i).comp (t i)) (m i + 1)
      (iterate_comp_eq_zero_of_swap (t i) (h i) (m i) (hnil i))
  exact ⟨S, T, hS, hT, hT'⟩

/-- **The basic perturbation lemma.**  Let `d₀` and `t` be degree-`+1` additive maps on a graded
abelian group, let `d = d₀ + t`, let `d₀` be contracted onto a retract by `h` and `q`, let the
cross-term identity `t (d x) + d₀ (t x) = 0` hold — which is what `d² = 0` and `d₀² = 0` leave —
and let `t ∘ h` be nilpotent in each degree, with a bound `m i` allowed to depend on the degree.
Then the same `q`, perturbed, contracts `d`: there are `H` and `Q` with

`H (d x) + Q x = x` in degree `0`,    `d (H x) + H (d x) + Q x = x` in positive degrees,

so the identity of the complex `(C^*, d)` is chain homotopic to `Q`.

`H` is `h ∘ (1 + t h)⁻¹` and `Q` is `(1 + h t)⁻¹ ∘ q ∘ (1 + t h)⁻¹`, both finite sums in each
degree by the nilpotence; see `Crystalline.FinitePerturbation.perturbedHomotopy` and
`Crystalline.FinitePerturbation.perturbedProjection`.  No side condition on `h` is used. -/
public theorem exists_perturbedContraction (d0 t d : ∀ i, C i →+ C (i + 1))
    (h : ∀ i, C (i + 1) →+ C i) (q : ∀ i, C i →+ C i)
    (hd : ∀ (i : ℕ) (x : C i), d i x = d0 i x + t i x)
    (hcon0 : ∀ x : C 0, h 0 (d0 0 x) + q 0 x = x)
    (hcon : ∀ (n : ℕ) (x : C (n + 1)),
      d0 n (h n x) + h (n + 1) (d0 (n + 1) x) + q (n + 1) x = x)
    (hcross : ∀ (i : ℕ) (x : C i), t (i + 1) (d i x) + d0 (i + 1) (t i x) = 0) (m : ℕ → ℕ)
    (hnil : ∀ (i : ℕ) (x : C (i + 1)), (fun y ↦ t i (h i y))^[m i] x = 0) :
    ∃ (H : ∀ i, C (i + 1) →+ C i) (Q : ∀ i, C i →+ C i),
      (∀ x : C 0, H 0 (d 0 x) + Q 0 x = x) ∧
        ∀ (n : ℕ) (x : C (n + 1)), d n (H n x) + H (n + 1) (d (n + 1) x) + Q (n + 1) x = x := by
  obtain ⟨S, T, hS, -, hT'⟩ := exists_inverses_of_nilpotent t h m hnil
  exact ⟨perturbedHomotopy h S,
    fun i ↦ Nat.casesOn i (perturbedProjectionZero q T) (fun n ↦ perturbedProjection q S T n),
    perturbedContraction_zero d0 t d h q S T hd hS hT' hcon0,
    perturbedContraction d0 t d h q S T hd hS hT' hcon hcross⟩

end Package

/-! ### The perturbed retract -/

section Retract

variable {C : ℕ → Type u} {L : ℕ → Type v} [∀ i, AddCommGroup (C i)] [∀ i, AddCommGroup (L i)]
  (t : ∀ i, C i →+ C (i + 1)) (h : ∀ i, C (i + 1) →+ C i) (q : ∀ i, C i →+ C i)
  (iota : ∀ i, L i →+ C i) (pi : ∀ i, C i →+ L i) (S : ∀ i, C (i + 1) →+ C (i + 1))
  (T : ∀ i, C i →+ C i)

/-- **The perturbed inclusion `ι' = T ∘ ι`** of the retract. -/
public def perturbedInclusion (i : ℕ) : L i →+ C i := (T i).comp (iota i)

/-- **The perturbed projection onto the retract, `π' = π ∘ S`**, in a positive degree. -/
public def perturbedRetraction (n : ℕ) : C (n + 1) →+ L (n + 1) := (pi (n + 1)).comp (S n)

/-- **The perturbed projection onto the retract in every degree.**  In a positive degree it is
`Crystalline.FinitePerturbation.perturbedRetraction`, and in degree `0` it is `π` itself: nothing
of negative degree being present, the inverse of `1 + t h` is the identity there, exactly as in
`Crystalline.FinitePerturbation.perturbedProjectionZero`. -/
public def perturbedRetractionFull (i : ℕ) : C i →+ L i :=
  Nat.casesOn (motive := fun i ↦ C i →+ L i) i (pi 0) fun n ↦ perturbedRetraction pi S n

@[simp] public theorem perturbedRetractionFull_zero : perturbedRetractionFull pi S 0 = pi 0 := rfl

@[simp] public theorem perturbedRetractionFull_succ (n : ℕ) :
    perturbedRetractionFull pi S (n + 1) = perturbedRetraction pi S n := rfl

/-- **The perturbation of the inclusion is the inclusion itself**, as soon as `h` kills `t (ι x)`.

`T` inverts `1 + h t`, so `T (ι x + h (t (ι x))) = ι x`; the correction term is the hypothesis and
vanishes.  This is what makes the conclusion of
`Crystalline.FinitePerturbation.exists_homotopyEquivOfInclusion` a statement about the given
comparison map rather than about an unspecified perturbation of it. -/
public theorem perturbedInclusion_eq_self
    (hT' : ∀ (i : ℕ) (x : C i), T i (x + h i (t i x)) = x)
    (hhtiota : ∀ (i : ℕ) (x : L i), h i (t i (iota i x)) = 0) (i : ℕ) (x : L i) :
    perturbedInclusion iota T i x = iota i x := by
  have hz := hT' i (iota i x)
  rwa [hhtiota i x, add_zero] at hz

/-- **`Q = ι' ∘ π'` in a positive degree**, as soon as `q = ι ∘ π`: both sides are
`T ∘ ι ∘ π ∘ S`, so nothing is to be proved beyond the factorisation of `q` itself.  This is why
the contraction identity of
`Crystalline.FinitePerturbation.exists_perturbedContraction` is a statement about a *retract* once
the side conditions below are available. -/
public theorem perturbedProjection_eq (hq : ∀ (i : ℕ) (y : C i), q i y = iota i (pi i y)) (n : ℕ)
    (x : C (n + 1)) :
    perturbedProjection q S T n x =
      perturbedInclusion iota T (n + 1) (perturbedRetraction pi S n x) := by
  show T (n + 1) (q (n + 1) (S n x)) = T (n + 1) (iota (n + 1) (pi (n + 1) (S n x)))
  rw [hq]

/-- `Q = ι' ∘ π` in degree `0`, where `π' = π`. -/
public theorem perturbedProjectionZero_eq (hq : ∀ (i : ℕ) (y : C i), q i y = iota i (pi i y))
    (x : C 0) :
    perturbedProjectionZero q T x = perturbedInclusion iota T 0 (pi 0 x) := by
  show T 0 (q 0 x) = T 0 (iota 0 (pi 0 x))
  rw [hq]

/-- **`π' ∘ ι' = 1` in degree `0`**: the perturbed projection is still a retraction of the
perturbed inclusion.  `T ι` differs from `ι` by `h (t (T ι))`, which `π` kills. -/
public theorem perturbedRetraction_perturbedInclusion_zero
    (hT : ∀ (i : ℕ) (x : C i), T i x + h i (t i (T i x)) = x)
    (hpih : ∀ (i : ℕ) (y : C (i + 1)), pi i (h i y) = 0)
    (hpiiota : ∀ (i : ℕ) (x : L i), pi i (iota i x) = x) (x : L 0) :
    pi 0 (perturbedInclusion iota T 0 x) = x := by
  have hw : T 0 (iota 0 x) + h 0 (t 0 (T 0 (iota 0 x))) = iota 0 x := hT 0 _
  calc pi 0 (perturbedInclusion iota T 0 x)
      = pi 0 (T 0 (iota 0 x)) := rfl
    _ = pi 0 (T 0 (iota 0 x)) + pi 0 (h 0 (t 0 (T 0 (iota 0 x)))) := by
        rw [hpih 0 _, add_zero]
    _ = pi 0 (iota 0 x) := by rw [← map_add, hw]
    _ = x := hpiiota 0 x

/-- **`S` fixes whatever `h` kills.**  From `h x = 0` the identity `S x + t (h (S x)) = x` gives
`h (S x) + h (t (h (S x))) = 0`, and the inverse of `1 + h t` sends that to `h (S x)`; so
`h (S x) = 0` and the identity collapses to `S x = x`. -/
public theorem perturbedInverse_eq_self_of_homotopy_eq_zero
    (hS : ∀ (i : ℕ) (x : C (i + 1)), S i x + t i (h i (S i x)) = x)
    (hT' : ∀ (i : ℕ) (x : C i), T i (x + h i (t i x)) = x) (n : ℕ) (w : C (n + 1))
    (hw : h n w = 0) : S n w = w := by
  have hhSw : h n (S n w) = 0 := by
    have h1 : h n (S n w) + h n (t n (h n (S n w))) = 0 := by rw [← map_add, hS n w, hw]
    have h2 := hT' n (h n (S n w))
    rw [h1, map_zero] at h2
    exact h2.symm
  have h3 := hS n w
  rwa [hhSw, map_zero, add_zero] at h3

/-- **`ĥ` kills the perturbed inclusion**: `h (T (ι x)) = 0`.

`T (ι x)` differs from `ι x` by `h (t (T (ι x)))`, which `h` kills by `ĥ² = 0`, and `h` kills the
image of `ι` outright; so it kills `T (ι x)`.  Both of the two side conditions on `h` that mention
nothing of `π` are used here and nowhere else. -/
public theorem homotopy_perturbedInclusion_eq_zero
    (hT : ∀ (i : ℕ) (x : C i), T i x + h i (t i (T i x)) = x)
    (hhh : ∀ (i : ℕ) (y : C (i + 2)), h i (h (i + 1) y) = 0)
    (hhiota : ∀ (i : ℕ) (x : L (i + 1)), h i (iota (i + 1) x) = 0) (n : ℕ) (x : L (n + 1)) :
    h n (perturbedInclusion iota T (n + 1) x) = 0 := by
  have hw : T (n + 1) (iota (n + 1) x) +
      h (n + 1) (t (n + 1) (T (n + 1) (iota (n + 1) x))) = iota (n + 1) x := hT (n + 1) _
  have hz : h n (T (n + 1) (iota (n + 1) x)) +
      h n (h (n + 1) (t (n + 1) (T (n + 1) (iota (n + 1) x)))) = h n (iota (n + 1) x) := by
    rw [← map_add, hw]
  rwa [hhh n _, add_zero, hhiota n x] at hz

/-- `H` kills the perturbed inclusion, `H = h ∘ S` being `T ∘ h`. -/
private theorem perturbedHomotopy_perturbedInclusion_eq_zero
    (hS : ∀ (i : ℕ) (x : C (i + 1)), S i x + t i (h i (S i x)) = x)
    (hT : ∀ (i : ℕ) (x : C i), T i x + h i (t i (T i x)) = x)
    (hT' : ∀ (i : ℕ) (x : C i), T i (x + h i (t i x)) = x)
    (hhh : ∀ (i : ℕ) (y : C (i + 2)), h i (h (i + 1) y) = 0)
    (hhiota : ∀ (i : ℕ) (x : L (i + 1)), h i (iota (i + 1) x) = 0) (i : ℕ) (x : L (i + 1)) :
    perturbedHomotopy h S i (perturbedInclusion iota T (i + 1) x) = 0 := by
  rw [perturbedHomotopy_eq t h S T hS hT' i _,
    homotopy_perturbedInclusion_eq_zero t h iota T hT hhh hhiota i x, map_zero]

/-- **`π' ∘ ι' = 1` in a positive degree.**

The side conditions of a *special* deformation retract are all used, and each exactly once: `h`
kills `T (ι x)` by `Crystalline.FinitePerturbation.homotopy_perturbedInclusion_eq_zero`, so `S`
fixes it; and `π` kills the image of `h`, which is the whole difference between `T (ι x)` and
`ι x`. -/
public theorem perturbedRetraction_perturbedInclusion
    (hS : ∀ (i : ℕ) (x : C (i + 1)), S i x + t i (h i (S i x)) = x)
    (hT : ∀ (i : ℕ) (x : C i), T i x + h i (t i (T i x)) = x)
    (hT' : ∀ (i : ℕ) (x : C i), T i (x + h i (t i x)) = x)
    (hhh : ∀ (i : ℕ) (y : C (i + 2)), h i (h (i + 1) y) = 0)
    (hhiota : ∀ (i : ℕ) (x : L (i + 1)), h i (iota (i + 1) x) = 0)
    (hpih : ∀ (i : ℕ) (y : C (i + 1)), pi i (h i y) = 0)
    (hpiiota : ∀ (i : ℕ) (x : L i), pi i (iota i x) = x) (n : ℕ) (x : L (n + 1)) :
    perturbedRetraction pi S n (perturbedInclusion iota T (n + 1) x) = x := by
  obtain ⟨W, hWdef⟩ : ∃ W : C (n + 1), T (n + 1) (iota (n + 1) x) = W := ⟨_, rfl⟩
  have hw : W + h (n + 1) (t (n + 1) W) = iota (n + 1) x := by
    rw [← hWdef]; exact hT (n + 1) _
  have hhw : h n W = 0 := by
    rw [← hWdef]
    exact homotopy_perturbedInclusion_eq_zero t h iota T hT hhh hhiota n x
  calc perturbedRetraction pi S n (perturbedInclusion iota T (n + 1) x)
      = pi (n + 1) (S n W) := by rw [show perturbedInclusion iota T (n + 1) x = W from hWdef]; rfl
    _ = pi (n + 1) W := by
        rw [perturbedInverse_eq_self_of_homotopy_eq_zero t h S T hS hT' n W hhw]
    _ = pi (n + 1) W + pi (n + 1) (h (n + 1) (t (n + 1) W)) := by rw [hpih (n + 1) _, add_zero]
    _ = pi (n + 1) (iota (n + 1) x) := by rw [← map_add, hw]
    _ = x := hpiiota (n + 1) x

/-- **`π' ∘ ι' = 1` in every degree**, the two cases of
`Crystalline.FinitePerturbation.perturbedRetraction_perturbedInclusion` and
`..._perturbedRetraction_perturbedInclusion_zero` read off
`Crystalline.FinitePerturbation.perturbedRetractionFull`. -/
public theorem perturbedRetractionFull_perturbedInclusion
    (hS : ∀ (i : ℕ) (x : C (i + 1)), S i x + t i (h i (S i x)) = x)
    (hT : ∀ (i : ℕ) (x : C i), T i x + h i (t i (T i x)) = x)
    (hT' : ∀ (i : ℕ) (x : C i), T i (x + h i (t i x)) = x)
    (hhh : ∀ (i : ℕ) (y : C (i + 2)), h i (h (i + 1) y) = 0)
    (hhiota : ∀ (i : ℕ) (x : L (i + 1)), h i (iota (i + 1) x) = 0)
    (hpih : ∀ (i : ℕ) (y : C (i + 1)), pi i (h i y) = 0)
    (hpiiota : ∀ (i : ℕ) (x : L i), pi i (iota i x) = x) (i : ℕ) (x : L i) :
    perturbedRetractionFull pi S i (perturbedInclusion iota T i x) = x := by
  cases i with
  | zero => exact perturbedRetraction_perturbedInclusion_zero t h iota pi T hT hpih hpiiota x
  | succ n =>
    exact perturbedRetraction_perturbedInclusion t h iota pi S T hS hT hT' hhh hhiota hpih
      hpiiota n x

/-- **`π' ∘ H = 0` in every degree.**

In degree `0` there is no `S` on the left and this is the side condition `π ĥ = 0` itself.  In a
positive degree `h (S y)` is killed by `h`, by `ĥ² = 0`, so `S` fixes it and the left `S`
disappears, leaving the same side condition. -/
public theorem perturbedRetractionFull_perturbedHomotopy_eq_zero
    (hS : ∀ (i : ℕ) (x : C (i + 1)), S i x + t i (h i (S i x)) = x)
    (hT' : ∀ (i : ℕ) (x : C i), T i (x + h i (t i x)) = x)
    (hhh : ∀ (i : ℕ) (y : C (i + 2)), h i (h (i + 1) y) = 0)
    (hpih : ∀ (i : ℕ) (y : C (i + 1)), pi i (h i y) = 0) (i : ℕ) (y : C (i + 1)) :
    perturbedRetractionFull pi S i (perturbedHomotopy h S i y) = 0 := by
  cases i with
  | zero => exact hpih 0 (S 0 y)
  | succ n =>
    have hfix : S n (h (n + 1) (S (n + 1) y)) = h (n + 1) (S (n + 1) y) :=
      perturbedInverse_eq_self_of_homotopy_eq_zero t h S T hS hT' n _ (hhh n (S (n + 1) y))
    show pi (n + 1) (S n (h (n + 1) (S (n + 1) y))) = 0
    rw [hfix]
    exact hpih (n + 1) (S (n + 1) y)

end Retract

/-! ### The comparison maps of a contracted complex are maps of complexes -/

section ChainMap

variable {C : ℕ → Type u} {L : ℕ → Type v} [∀ i, AddCommGroup (C i)] [∀ i, AddCommGroup (L i)]
  (d : ∀ i, C i →+ C (i + 1)) (H : ∀ i, C (i + 1) →+ C i) (iota : ∀ i, L i →+ C i)
  (pi : ∀ i, C i →+ L i)

/-- **The differential the retract inherits**, `d_L = π ∘ d ∘ ι`.  This is the differential of the
full perturbation lemma: nothing else can be meant, since `ι` and `π` are the only maps between
the two graded groups. -/
public def retractDifferential (i : ℕ) : L i →+ L (i + 1) :=
  (pi (i + 1)).comp ((d i).comp (iota i))

public theorem retractDifferential_apply (i : ℕ) (x : L i) :
    retractDifferential d iota pi i x = pi (i + 1) (d i (iota i x)) :=
  rfl

/-- **`H (d (ι x)) = 0`.**

This is the contraction identity read at `ι x`: the projection term is `ι (π (ι x)) = ι x`, which
cancels the right-hand side, and in a positive degree the remaining term `d (H (ι x))` vanishes
because `H` kills the image of `ι`.  In degree `0` there is no such term and only `π ι = 1` is
used. -/
public theorem homotopy_differential_inclusion_eq_zero
    (hcon0 : ∀ x : C 0, H 0 (d 0 x) + iota 0 (pi 0 x) = x)
    (hcon : ∀ (n : ℕ) (x : C (n + 1)),
      d n (H n x) + H (n + 1) (d (n + 1) x) + iota (n + 1) (pi (n + 1) x) = x)
    (hpiiota : ∀ (i : ℕ) (x : L i), pi i (iota i x) = x)
    (hHiota : ∀ (i : ℕ) (x : L (i + 1)), H i (iota (i + 1) x) = 0) (i : ℕ) (x : L i) :
    H i (d i (iota i x)) = 0 := by
  cases i with
  | zero =>
    have hz := hcon0 (iota 0 x)
    rw [hpiiota 0 x] at hz
    exact add_right_cancel (hz.trans (zero_add (iota 0 x)).symm)
  | succ n =>
    have hz := hcon n (iota (n + 1) x)
    rw [hHiota n x, map_zero, zero_add, hpiiota (n + 1) x] at hz
    exact add_right_cancel (hz.trans (zero_add (iota (n + 1) x)).symm)

/-- **The inclusion of the retract is a map of complexes**: `d (ι x) = ι (d_L x)`.

The contraction identity at `y = d (ι x)` has both homotopy terms zero — the first by
`Crystalline.FinitePerturbation.homotopy_differential_inclusion_eq_zero` and the second because
`d y = d (d (ι x))` vanishes — so `y` *is* its own projection term, which is `ι (π (d (ι x)))`. -/
public theorem differential_inclusion
    (hdd : ∀ (i : ℕ) (x : C i), d (i + 1) (d i x) = 0)
    (hcon0 : ∀ x : C 0, H 0 (d 0 x) + iota 0 (pi 0 x) = x)
    (hcon : ∀ (n : ℕ) (x : C (n + 1)),
      d n (H n x) + H (n + 1) (d (n + 1) x) + iota (n + 1) (pi (n + 1) x) = x)
    (hpiiota : ∀ (i : ℕ) (x : L i), pi i (iota i x) = x)
    (hHiota : ∀ (i : ℕ) (x : L (i + 1)), H i (iota (i + 1) x) = 0) (i : ℕ) (x : L i) :
    d i (iota i x) = iota (i + 1) (retractDifferential d iota pi i x) := by
  have hz := hcon i (d i (iota i x))
  rw [homotopy_differential_inclusion_eq_zero d H iota pi hcon0 hcon hpiiota hHiota i x,
    hdd i (iota i x)] at hz
  simp only [map_zero, zero_add] at hz
  exact hz.symm

/-- **`π (d (H w)) = 0`.**  The contraction identity at `w`, pushed down by `π`: the term
`H (d w)` is killed because `π` kills the image of `H`, and the projection term returns `π w`
because `π ι = 1`. -/
public theorem retraction_differential_homotopy_eq_zero
    (hcon : ∀ (n : ℕ) (x : C (n + 1)),
      d n (H n x) + H (n + 1) (d (n + 1) x) + iota (n + 1) (pi (n + 1) x) = x)
    (hpiiota : ∀ (i : ℕ) (x : L i), pi i (iota i x) = x)
    (hpiH : ∀ (i : ℕ) (y : C (i + 1)), pi i (H i y) = 0) (n : ℕ) (w : C (n + 1)) :
    pi (n + 1) (d n (H n w)) = 0 := by
  have hz := congrArg (pi (n + 1)) (hcon n w)
  simp only [map_add, hpiH, hpiiota, add_zero] at hz
  exact add_right_cancel (hz.trans (zero_add (pi (n + 1) w)).symm)

/-- **The projection onto the retract is a map of complexes**: `π (d z) = d_L (π z)`.

The difference between `z` and `ι (π z)` is `d (H z) + H (d z)` — only the second term in degree
`0` — and `π (d −)` kills both: the first because `d d = 0` and the second by
`Crystalline.FinitePerturbation.retraction_differential_homotopy_eq_zero`. -/
public theorem retraction_differential
    (hdd : ∀ (i : ℕ) (x : C i), d (i + 1) (d i x) = 0)
    (hcon0 : ∀ x : C 0, H 0 (d 0 x) + iota 0 (pi 0 x) = x)
    (hcon : ∀ (n : ℕ) (x : C (n + 1)),
      d n (H n x) + H (n + 1) (d (n + 1) x) + iota (n + 1) (pi (n + 1) x) = x)
    (hpiiota : ∀ (i : ℕ) (x : L i), pi i (iota i x) = x)
    (hpiH : ∀ (i : ℕ) (y : C (i + 1)), pi i (H i y) = 0) (i : ℕ) (z : C i) :
    pi (i + 1) (d i z) = retractDifferential d iota pi i (pi i z) := by
  show pi (i + 1) (d i z) = pi (i + 1) (d i (iota i (pi i z)))
  cases i with
  | zero =>
    have hstep : pi 1 (d 0 (H 0 (d 0 z))) = 0 :=
      retraction_differential_homotopy_eq_zero d H iota pi hcon hpiiota hpiH 0 (d 0 z)
    calc pi 1 (d 0 z)
        = pi 1 (d 0 (H 0 (d 0 z) + iota 0 (pi 0 z))) := by rw [hcon0 z]
      _ = pi 1 (d 0 (H 0 (d 0 z))) + pi 1 (d 0 (iota 0 (pi 0 z))) := by rw [map_add, map_add]
      _ = pi 1 (d 0 (iota 0 (pi 0 z))) := by rw [hstep, zero_add]
  | succ n =>
    have hstep : pi (n + 2) (d (n + 1) (H (n + 1) (d (n + 1) z))) = 0 :=
      retraction_differential_homotopy_eq_zero d H iota pi hcon hpiiota hpiH (n + 1)
        (d (n + 1) z)
    calc pi (n + 2) (d (n + 1) z)
        = pi (n + 2) (d (n + 1) (d n (H n z) + H (n + 1) (d (n + 1) z) +
            iota (n + 1) (pi (n + 1) z))) := by rw [hcon n z]
      _ = pi (n + 2) (d (n + 1) (d n (H n z))) +
            pi (n + 2) (d (n + 1) (H (n + 1) (d (n + 1) z))) +
            pi (n + 2) (d (n + 1) (iota (n + 1) (pi (n + 1) z))) := by simp only [map_add]
      _ = pi (n + 2) (d (n + 1) (iota (n + 1) (pi (n + 1) z))) := by
            rw [hdd n (H n z), hstep]
            simp only [map_zero, zero_add]

/-- **The differential of the retract squares to zero.**  `ι` is injective, having `π` as a left
inverse, and `ι (d_L (d_L x)) = d (d (ι x)) = 0` because `ι` is a map of complexes. -/
public theorem retractDifferential_retractDifferential
    (hdd : ∀ (i : ℕ) (x : C i), d (i + 1) (d i x) = 0)
    (hcon0 : ∀ x : C 0, H 0 (d 0 x) + iota 0 (pi 0 x) = x)
    (hcon : ∀ (n : ℕ) (x : C (n + 1)),
      d n (H n x) + H (n + 1) (d (n + 1) x) + iota (n + 1) (pi (n + 1) x) = x)
    (hpiiota : ∀ (i : ℕ) (x : L i), pi i (iota i x) = x)
    (hHiota : ∀ (i : ℕ) (x : L (i + 1)), H i (iota (i + 1) x) = 0) (i : ℕ) (x : L i) :
    retractDifferential d iota pi (i + 1) (retractDifferential d iota pi i x) = 0 := by
  have h1 : iota (i + 2)
      (retractDifferential d iota pi (i + 1) (retractDifferential d iota pi i x)) = 0 := by
    rw [← differential_inclusion d H iota pi hdd hcon0 hcon hpiiota hHiota (i + 1)
        (retractDifferential d iota pi i x),
      ← differential_inclusion d H iota pi hdd hcon0 hcon hpiiota hHiota i x]
    exact hdd i (iota i x)
  calc retractDifferential d iota pi (i + 1) (retractDifferential d iota pi i x)
      = pi (i + 2) (iota (i + 2)
          (retractDifferential d iota pi (i + 1) (retractDifferential d iota pi i x))) :=
        (hpiiota (i + 2) _).symm
    _ = pi (i + 2) 0 := by rw [h1]
    _ = 0 := map_zero _

end ChainMap

/-! ### The perturbation lemma as a homotopy equivalence -/

section HomotopyEquiv

variable {C : ℕ → Type u} {L : ℕ → Type v} [∀ i, AddCommGroup (C i)] [∀ i, AddCommGroup (L i)]

/-- **The perturbation lemma as a homotopy equivalence of complexes.**

Let `d₀` and `t` be degree-`+1` additive maps on a graded abelian group, let `d = d₀ + t` square
to zero, let the cross-term identity `t (d x) + d₀ (t x) = 0` hold, let `t ∘ h` be nilpotent in
each degree, and let `(ι, π, h)` be a *special* deformation retract for `d₀`:

`h (d₀ x) + ι (π x) = x` in degree `0`,    `d₀ (h x) + h (d₀ x) + ι (π x) = x` above it,
`h ∘ h = 0`,   `h ∘ ι = 0`,   `π ∘ h = 0`,   `π ∘ ι = 1`.

Then the retract carries a differential `d_L` squaring to zero for which the perturbed comparison
maps `ι' = T ι` and `π' = π S` are maps of complexes, with `π' ι' = 1` and `ι' π'` chain homotopic
to the identity by `H`.  So `ι' : (L^*, d_L) → (C^*, d)` is a homotopy equivalence, and in
particular a quasi-isomorphism.

`d_L` is `π' ∘ d ∘ ι'`, `H` is `h ∘ (1 + t h)⁻¹` and `ι' π'` is the perturbed projection of
`Crystalline.FinitePerturbation.exists_perturbedContraction`; each is a finite sum in every degree
by the nilpotence, which is what replaces the limit argument of the source.  See the module
docstring. -/
public theorem exists_perturbedHomotopyEquiv (d0 t d : ∀ i, C i →+ C (i + 1))
    (h : ∀ i, C (i + 1) →+ C i) (iota : ∀ i, L i →+ C i) (pi : ∀ i, C i →+ L i)
    (hd : ∀ (i : ℕ) (x : C i), d i x = d0 i x + t i x)
    (hdd : ∀ (i : ℕ) (x : C i), d (i + 1) (d i x) = 0)
    (hcon0 : ∀ x : C 0, h 0 (d0 0 x) + iota 0 (pi 0 x) = x)
    (hcon : ∀ (n : ℕ) (x : C (n + 1)),
      d0 n (h n x) + h (n + 1) (d0 (n + 1) x) + iota (n + 1) (pi (n + 1) x) = x)
    (hcross : ∀ (i : ℕ) (x : C i), t (i + 1) (d i x) + d0 (i + 1) (t i x) = 0)
    (hhh : ∀ (i : ℕ) (y : C (i + 2)), h i (h (i + 1) y) = 0)
    (hhiota : ∀ (i : ℕ) (x : L (i + 1)), h i (iota (i + 1) x) = 0)
    (hpih : ∀ (i : ℕ) (y : C (i + 1)), pi i (h i y) = 0)
    (hpiiota : ∀ (i : ℕ) (x : L i), pi i (iota i x) = x) (m : ℕ → ℕ)
    (hnil : ∀ (i : ℕ) (x : C (i + 1)), (fun y ↦ t i (h i y))^[m i] x = 0) :
    ∃ (dL : ∀ i, L i →+ L (i + 1)) (iota' : ∀ i, L i →+ C i) (pi' : ∀ i, C i →+ L i)
      (H : ∀ i, C (i + 1) →+ C i),
      (∀ (i : ℕ) (x : L i), dL (i + 1) (dL i x) = 0) ∧
        (∀ (i : ℕ) (x : L i), pi' i (iota' i x) = x) ∧
          (∀ (i : ℕ) (x : L i), d i (iota' i x) = iota' (i + 1) (dL i x)) ∧
            (∀ (i : ℕ) (z : C i), pi' (i + 1) (d i z) = dL i (pi' i z)) ∧
              (∀ x : C 0, H 0 (d 0 x) + iota' 0 (pi' 0 x) = x) ∧
                ∀ (n : ℕ) (x : C (n + 1)),
                  d n (H n x) + H (n + 1) (d (n + 1) x) + iota' (n + 1) (pi' (n + 1) x) = x := by
  obtain ⟨S, T, hS, hT, hT'⟩ := exists_inverses_of_nilpotent t h m hnil
  have hpiiota' : ∀ (i : ℕ) (x : L i),
      perturbedRetractionFull pi S i (perturbedInclusion iota T i x) = x :=
    perturbedRetractionFull_perturbedInclusion t h iota pi S T hS hT hT' hhh hhiota hpih hpiiota
  have hpiH' : ∀ (i : ℕ) (y : C (i + 1)),
      perturbedRetractionFull pi S i (perturbedHomotopy h S i y) = 0 :=
    perturbedRetractionFull_perturbedHomotopy_eq_zero t h pi S T hS hT' hhh hpih
  have hHiota' : ∀ (i : ℕ) (x : L (i + 1)),
      perturbedHomotopy h S i (perturbedInclusion iota T (i + 1) x) = 0 :=
    perturbedHomotopy_perturbedInclusion_eq_zero t h iota S T hS hT hT' hhh hhiota
  have hc0 : ∀ x : C 0, perturbedHomotopy h S 0 (d 0 x) +
      perturbedInclusion iota T 0 (perturbedRetractionFull pi S 0 x) = x := fun x ↦
    perturbedContraction_zero d0 t d h (fun i ↦ (iota i).comp (pi i)) S T hd hS hT' hcon0 x
  have hcp : ∀ (n : ℕ) (x : C (n + 1)), d n (perturbedHomotopy h S n x) +
      perturbedHomotopy h S (n + 1) (d (n + 1) x) +
      perturbedInclusion iota T (n + 1) (perturbedRetractionFull pi S (n + 1) x) = x := fun n x ↦
    perturbedContraction d0 t d h (fun i ↦ (iota i).comp (pi i)) S T hd hS hT' hcon hcross n x
  exact ⟨retractDifferential d (perturbedInclusion iota T) (perturbedRetractionFull pi S),
    perturbedInclusion iota T, perturbedRetractionFull pi S, perturbedHomotopy h S,
    retractDifferential_retractDifferential d (perturbedHomotopy h S) (perturbedInclusion iota T)
      (perturbedRetractionFull pi S) hdd hc0 hcp hpiiota' hHiota',
    hpiiota',
    differential_inclusion d (perturbedHomotopy h S) (perturbedInclusion iota T)
      (perturbedRetractionFull pi S) hdd hc0 hcp hpiiota' hHiota',
    retraction_differential d (perturbedHomotopy h S) (perturbedInclusion iota T)
      (perturbedRetractionFull pi S) hdd hc0 hcp hpiiota' hpiH',
    hc0, hcp⟩


/-- **The perturbation lemma as a homotopy equivalence with the inclusion unperturbed.**

`Crystalline.FinitePerturbation.exists_perturbedHomotopyEquiv` produces the comparison `ι' = T ι`,
a perturbation of `ι`, and quantifies over it existentially, so nothing in its conclusion says
which map between the two complexes is the equivalence.  Under the one extra hypothesis

`h (t (ι x)) = 0`

the perturbation is trivial — `T ι = ι` by
`Crystalline.FinitePerturbation.perturbedInclusion_eq_self` — and the conclusion is about the
**given** `ι`: the retract carries a differential `d_L` squaring to zero for which `ι` itself is a
map of complexes, the perturbed `π'` is a map of complexes and a retraction of `ι`, and `ι π'` is
chain homotopic to the identity.  That is what makes a statement about a *named* comparison map,
and it is the shape [Stacks, Lemma 60.20.2, Tag 07LD] asserts: there the map is the canonical
comparison of de Rham complexes and not an unspecified equivalence.

Everything else is unchanged from
`Crystalline.FinitePerturbation.exists_perturbedHomotopyEquiv`; `d_L` is `π' ∘ d ∘ ι` and is
pinned by `ι` being a map of complexes, since `ι` is injective. -/
public theorem exists_homotopyEquivOfInclusion (d0 t d : ∀ i, C i →+ C (i + 1))
    (h : ∀ i, C (i + 1) →+ C i) (iota : ∀ i, L i →+ C i) (pi : ∀ i, C i →+ L i)
    (hd : ∀ (i : ℕ) (x : C i), d i x = d0 i x + t i x)
    (hdd : ∀ (i : ℕ) (x : C i), d (i + 1) (d i x) = 0)
    (hcon0 : ∀ x : C 0, h 0 (d0 0 x) + iota 0 (pi 0 x) = x)
    (hcon : ∀ (n : ℕ) (x : C (n + 1)),
      d0 n (h n x) + h (n + 1) (d0 (n + 1) x) + iota (n + 1) (pi (n + 1) x) = x)
    (hcross : ∀ (i : ℕ) (x : C i), t (i + 1) (d i x) + d0 (i + 1) (t i x) = 0)
    (hhh : ∀ (i : ℕ) (y : C (i + 2)), h i (h (i + 1) y) = 0)
    (hhiota : ∀ (i : ℕ) (x : L (i + 1)), h i (iota (i + 1) x) = 0)
    (hpih : ∀ (i : ℕ) (y : C (i + 1)), pi i (h i y) = 0)
    (hpiiota : ∀ (i : ℕ) (x : L i), pi i (iota i x) = x)
    (hhtiota : ∀ (i : ℕ) (x : L i), h i (t i (iota i x)) = 0) (m : ℕ → ℕ)
    (hnil : ∀ (i : ℕ) (x : C (i + 1)), (fun y ↦ t i (h i y))^[m i] x = 0) :
    ∃ (dL : ∀ i, L i →+ L (i + 1)) (pi' : ∀ i, C i →+ L i) (H : ∀ i, C (i + 1) →+ C i),
      (∀ (i : ℕ) (x : L i), dL (i + 1) (dL i x) = 0) ∧
        (∀ (i : ℕ) (x : L i), pi' i (iota i x) = x) ∧
          (∀ (i : ℕ) (x : L i), d i (iota i x) = iota (i + 1) (dL i x)) ∧
            (∀ (i : ℕ) (z : C i), pi' (i + 1) (d i z) = dL i (pi' i z)) ∧
              (∀ x : C 0, H 0 (d 0 x) + iota 0 (pi' 0 x) = x) ∧
                ∀ (n : ℕ) (x : C (n + 1)),
                  d n (H n x) + H (n + 1) (d (n + 1) x) + iota (n + 1) (pi' (n + 1) x) = x := by
  obtain ⟨S, T, hS, hT, hT'⟩ := exists_inverses_of_nilpotent t h m hnil
  have hTiota : ∀ (i : ℕ) (x : L i), perturbedInclusion iota T i x = iota i x := fun i x ↦
    perturbedInclusion_eq_self t h iota T hT' hhtiota i x
  have hpiiota' : ∀ (i : ℕ) (x : L i),
      perturbedRetractionFull pi S i (iota i x) = x := fun i x ↦
    (congrArg (perturbedRetractionFull pi S i) (hTiota i x)).symm.trans
      (perturbedRetractionFull_perturbedInclusion t h iota pi S T hS hT hT' hhh hhiota hpih
        hpiiota i x)
  have hpiH' : ∀ (i : ℕ) (y : C (i + 1)),
      perturbedRetractionFull pi S i (perturbedHomotopy h S i y) = 0 :=
    perturbedRetractionFull_perturbedHomotopy_eq_zero t h pi S T hS hT' hhh hpih
  have hHiota' : ∀ (i : ℕ) (x : L (i + 1)),
      perturbedHomotopy h S i (iota (i + 1) x) = 0 := by
    intro i x
    rw [← hTiota (i + 1) x]
    exact perturbedHomotopy_perturbedInclusion_eq_zero t h iota S T hS hT hT' hhh hhiota i x
  have hc0 : ∀ x : C 0, perturbedHomotopy h S 0 (d 0 x) +
      iota 0 (perturbedRetractionFull pi S 0 x) = x := by
    intro x
    rw [← hTiota 0 (perturbedRetractionFull pi S 0 x)]
    exact perturbedContraction_zero d0 t d h (fun i ↦ (iota i).comp (pi i)) S T hd hS hT' hcon0 x
  have hcp : ∀ (n : ℕ) (x : C (n + 1)), d n (perturbedHomotopy h S n x) +
      perturbedHomotopy h S (n + 1) (d (n + 1) x) +
      iota (n + 1) (perturbedRetractionFull pi S (n + 1) x) = x := by
    intro n x
    rw [← hTiota (n + 1) (perturbedRetractionFull pi S (n + 1) x)]
    exact perturbedContraction d0 t d h (fun i ↦ (iota i).comp (pi i)) S T hd hS hT' hcon hcross n x
  exact ⟨retractDifferential d iota (perturbedRetractionFull pi S),
    perturbedRetractionFull pi S, perturbedHomotopy h S,
    retractDifferential_retractDifferential d (perturbedHomotopy h S) iota
      (perturbedRetractionFull pi S) hdd hc0 hcp hpiiota' hHiota',
    hpiiota',
    differential_inclusion d (perturbedHomotopy h S) iota (perturbedRetractionFull pi S) hdd hc0
      hcp hpiiota' hHiota',
    retraction_differential d (perturbedHomotopy h S) iota (perturbedRetractionFull pi S) hdd hc0
      hcp hpiiota' hpiH',
    hc0, hcp⟩

/-- **The perturbation lemma as a homotopy equivalence onto a named differential.**

`Crystalline.FinitePerturbation.exists_homotopyEquivOfInclusion` produces a differential `d_L` on
the retract for which `ι` is a map of complexes, and quantifies over it.  As soon as `ι` is a map
of complexes for a differential `dL` one already has — the hypothesis `hchain` — that `d_L` *is*
`dL`: `ι` is injective, having `π'` as a left inverse, and both differentials are carried to
`d ∘ ι` by it.  So the conclusion can be stated for `dL`, with nothing existentially quantified
but the homotopy inverse `π'` and the homotopy `H`.

This is the shape [Stacks, Lemma 60.20.2, Tag 07LD] asserts: there both complexes and the map
between them are given, and the assertion is that the map is a quasi-isomorphism. -/
public theorem exists_homotopyEquivOfInclusion_of_chainMap (d0 t d : ∀ i, C i →+ C (i + 1))
    (h : ∀ i, C (i + 1) →+ C i) (iota : ∀ i, L i →+ C i) (pi : ∀ i, C i →+ L i)
    (dL : ∀ i, L i →+ L (i + 1))
    (hd : ∀ (i : ℕ) (x : C i), d i x = d0 i x + t i x)
    (hdd : ∀ (i : ℕ) (x : C i), d (i + 1) (d i x) = 0)
    (hcon0 : ∀ x : C 0, h 0 (d0 0 x) + iota 0 (pi 0 x) = x)
    (hcon : ∀ (n : ℕ) (x : C (n + 1)),
      d0 n (h n x) + h (n + 1) (d0 (n + 1) x) + iota (n + 1) (pi (n + 1) x) = x)
    (hcross : ∀ (i : ℕ) (x : C i), t (i + 1) (d i x) + d0 (i + 1) (t i x) = 0)
    (hhh : ∀ (i : ℕ) (y : C (i + 2)), h i (h (i + 1) y) = 0)
    (hhiota : ∀ (i : ℕ) (x : L (i + 1)), h i (iota (i + 1) x) = 0)
    (hpih : ∀ (i : ℕ) (y : C (i + 1)), pi i (h i y) = 0)
    (hpiiota : ∀ (i : ℕ) (x : L i), pi i (iota i x) = x)
    (hhtiota : ∀ (i : ℕ) (x : L i), h i (t i (iota i x)) = 0)
    (hchain : ∀ (i : ℕ) (x : L i), d i (iota i x) = iota (i + 1) (dL i x)) (m : ℕ → ℕ)
    (hnil : ∀ (i : ℕ) (x : C (i + 1)), (fun y ↦ t i (h i y))^[m i] x = 0) :
    ∃ (pi' : ∀ i, C i →+ L i) (H : ∀ i, C (i + 1) →+ C i),
      (∀ (i : ℕ) (x : L i), pi' i (iota i x) = x) ∧
        (∀ (i : ℕ) (z : C i), pi' (i + 1) (d i z) = dL i (pi' i z)) ∧
          (∀ x : C 0, H 0 (d 0 x) + iota 0 (pi' 0 x) = x) ∧
            ∀ (n : ℕ) (x : C (n + 1)),
              d n (H n x) + H (n + 1) (d (n + 1) x) + iota (n + 1) (pi' (n + 1) x) = x := by
  obtain ⟨dL', pi', H, -, hpiiota', hiota', hpi', hc0, hcp⟩ :=
    exists_homotopyEquivOfInclusion d0 t d h iota pi hd hdd hcon0 hcon hcross hhh hhiota hpih
      hpiiota hhtiota m hnil
  have hdLeq : ∀ (i : ℕ) (x : L i), dL' i x = dL i x := fun i x ↦
    ((hpiiota' (i + 1) (dL' i x)).symm.trans
        (congrArg (pi' (i + 1)) ((hiota' i x).symm.trans (hchain i x)))).trans
      (hpiiota' (i + 1) (dL i x))
  exact ⟨pi', H, hpiiota', fun i z ↦ (hpi' i z).trans (hdLeq i (pi' i z)), hc0, hcp⟩

end HomotopyEquiv

end FinitePerturbation

end Crystalline

end
