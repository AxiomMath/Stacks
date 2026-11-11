module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernSetup
public import StacksCore.Tactic.StacksAttribute

/-!
# Characteristic classes of a locally bounded complex on a quasi-compact scheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, and let `X`
be a scheme locally of finite type over `S`. **Stacks 0ESZ** attaches the total Chern class
`c(ℰ^•)` and the power sums `P_p(ℰ^•)` to a complex `ℰ^•` of finite locally free `𝒪_X`-modules
which is only *locally* bounded: each term is finite locally free and, on a neighbourhood of each
point, all but finitely many terms restrict to zero, the range of degrees being allowed to depend
on the point.

`StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex` constructs those classes for a complex
presented together with a window of degrees `a, …, a + k` outside which it vanishes, and says so:
the locally bounded case is not delivered there. This file delivers it when `X` is quasi-compact.
The reason the hypothesis suffices is
`Stacks.Chow.exists_bounds_of_isLocallyBoundedFiniteLocallyFree`: finitely many of the local
neighbourhoods already cover `X`, so the least of their lower bounds and the greatest of their
upper bounds bound the complex globally. A locally bounded complex on a quasi-compact scheme is
therefore bounded, and the classes are obtained by feeding one such global window to the
construction of the bounded case.

What makes the definition more than a choice is the characterisation below: the class so defined
agrees with the bounded-window class computed from *any* window outside which the complex
vanishes. The choice of window, in particular the one extracted from the covering, does not
matter.

## Main definitions

* `Stacks.Chow.totalChernClassComplexLocallyBounded` — the total Chern class `c(ℰ^•)` of a
  locally bounded complex of finite locally free modules on a quasi-compact scheme, in the carried
  form of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex`.
* `Stacks.Chow.powerSumClassComplexLocallyBounded` — the class `P_p(ℰ^•)` of such a complex, in
  the same carried form.

## Main results

* `Stacks.Chow.alternatingKClass_eq_of_isZero_outside_both` — two windows outside each of which a
  complex vanishes compute the same alternating class in `K_0(Vect(X))`, with no containment
  between the windows assumed.
* `Stacks.Chow.exists_window_of_isLocallyBoundedFiniteLocallyFree` — a locally bounded complex on
  a quasi-compact scheme vanishes outside a window of the form `a, …, a + k`.
* `Stacks.Chow.totalChernClassComplexLocallyBounded_eq`,
  `Stacks.Chow.powerSumClassComplexLocallyBounded_eq` — the classes of the locally bounded case
  agree with the bounded-window classes computed from any window outside which the complex
  vanishes.

## Implementation notes

The global window is extracted from the existential by `Exists.choose`, packaged as a base degree
and a length in `ℤ × ℕ` so that one choice produces both arguments the bounded-window
construction expects; the length is `(hi - lo).toNat`, which is why no sign hypothesis relating
the two bounds is needed.

Two windows outside each of which the complex vanishes need not be nested — they need not even
meet, in which case the complex is zero in every degree. So the characterisation is not a direct
application of `Stacks.Chow.alternatingKClass_eq_of_isZero_outside_of_subset`: both windows are
first enlarged to the window spanned by their union, which contains each of them.

The quasi-compactness hypothesis is `CompactSpace` on the underlying space of `X`, which is what
`Stacks.Chow.exists_bounds_of_isLocallyBoundedFiniteLocallyFree` consumes; no separation is
assumed. The truly local case of Stacks 0ESZ, where `X` is not quasi-compact and the classes are
assembled over a decomposition by Stacks 0FDZ, is not treated in this file.

Nothing in this file carries `@[stacks 0ESZ]`. The tag is registered on the constructed classes
of an arbitrary locally bounded complex, `Stacks.Chow.complexChern` and
`Stacks.Chow.complexPowerSumComponent`, and on their independence of the representative in
`D(𝒪_X)`, `Stacks.Chow.complexChern_eq_of_iso` and `Stacks.Chow.powerSumComplex_eq_of_iso`.

## References

* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### A global window of degrees -/

section Window

variable {X : Scheme.{u}}

/-- **Two windows outside each of which a complex vanishes compute the same alternating class.**
No containment between the windows is assumed: both are enlarged to the window spanned by their
union, outside which the complex also vanishes, and the alternating class is unchanged by such an
enlargement because the added terms are zero objects. -/
theorem alternatingKClass_eq_of_isZero_outside_both (P : CochainComplex X.Modules ℤ) {a a' : ℤ}
    {k k' : ℕ} (h : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n))
    (h' : ∀ n : ℤ, (n < a' ∨ a' + (k' : ℤ) < n) → IsZero (P.X n)) :
    alternatingKClass X P a k = alternatingKClass X P a' k' := by
  refine (alternatingKClass_eq_of_isZero_outside (a' := min a a')
    (k' := (max (a + (k : ℤ)) (a' + (k' : ℤ)) - min a a').toNat) P ?_ ?_ h).trans
    (alternatingKClass_eq_of_isZero_outside P ?_ ?_ h').symm <;> omega

/-- **On a quasi-compact scheme a locally bounded complex of finite locally free modules vanishes
outside a window `a, …, a + k`.** This is
`Stacks.Chow.exists_bounds_of_isLocallyBoundedFiniteLocallyFree` with the pair of global bounds
rewritten as a base degree together with a length, which is the shape the classes of Stacks 0ESZ
consume; the length being `(hi - lo).toNat` no inequality between the two bounds is needed. -/
theorem exists_window_of_isLocallyBoundedFiniteLocallyFree [CompactSpace X]
    {P : CochainComplex X.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P) :
    ∃ w : ℤ × ℕ, ∀ n : ℤ, (n < w.1 ∨ w.1 + (w.2 : ℤ) < n) → IsZero (P.X n) := by
  obtain ⟨lo, hi, h⟩ := exists_bounds_of_isLocallyBoundedFiniteLocallyFree hP
  exact ⟨⟨lo, (hi - lo).toNat⟩, fun n hn => h n (hn.imp id fun hn => by omega)⟩

end Window

/-! ### The total Chern class of a locally bounded complex -/

section TotalChernClass

open ChowCohomologySeriesRing

variable (C : ChowSituation.{u}) (Gy : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] [CompactSpace X] {R : ChowCohomologySeriesRing C Gy sX}

/-- **Carried form.** The total Chern class `c(ℰ^•) = ∏_n c(ℰ^n)^{(-1)^n}` of a *locally bounded*
complex of finite locally free modules on a quasi-compact scheme, as an element of the group of
series with constant term `1` inside `∏_{p ≥ 0} A^p(X)`. Such a complex vanishes outside a single
global window of degrees, and the class is the bounded-window class of Stacks 0ESZ on one. -/
def totalChernClassComplexLocallyBounded (D : TotalChernClassSeries C Gy sX R)
    (P : CochainComplex X.Modules ℤ) (hP : IsLocallyBoundedFiniteLocallyFree P) :
    UnitalSeries R :=
  totalChernClassComplex C Gy sX D P
    (exists_window_of_isLocallyBoundedFiniteLocallyFree hP).choose.1
    (exists_window_of_isLocallyBoundedFiniteLocallyFree hP).choose.2

/-- **The total Chern class of a locally bounded complex does not depend on the window.** For any
window `a, …, a + k` outside which the terms of the complex vanish, the class of the locally
bounded case agrees with the bounded-window class computed from that window; in particular the
window extracted from the covering of the quasi-compact scheme is immaterial. -/
theorem totalChernClassComplexLocallyBounded_eq (D : TotalChernClassSeries C Gy sX R)
    (P : CochainComplex X.Modules ℤ) (hP : IsLocallyBoundedFiniteLocallyFree P) {a : ℤ} {k : ℕ}
    (hvanish : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n)) :
    totalChernClassComplexLocallyBounded C Gy sX D P hP =
      totalChernClassComplex C Gy sX D P a k := by
  rw [totalChernClassComplexLocallyBounded, totalChernClassComplex, totalChernClassComplex,
    alternatingKClass_eq_of_isZero_outside_both P
      (exists_window_of_isLocallyBoundedFiniteLocallyFree hP).choose_spec hvanish]

end TotalChernClass

/-! ### The power sums of a locally bounded complex -/

section PowerSum

variable (C : ChowSituation.{u}) (Gy : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] [CompactSpace X]

/-- **Carried form.** The class `P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n) ∈ A^p(X)` of a *locally bounded*
complex of finite locally free modules on a quasi-compact scheme. Such a complex vanishes outside
a single global window of degrees, and the class is the bounded-window class of Stacks 0ESZ on
one. -/
def powerSumClassComplexLocallyBounded (W : PowerSumClassRule C Gy sX)
    (P : CochainComplex X.Modules ℤ) (hP : IsLocallyBoundedFiniteLocallyFree P) (p : ℕ) :
    chowCohomologyComponent C Gy sX (p : ℤ) :=
  powerSumClassComplex C Gy sX W P
    (exists_window_of_isLocallyBoundedFiniteLocallyFree hP).choose.1
    (exists_window_of_isLocallyBoundedFiniteLocallyFree hP).choose.2 p

/-- **The class `P_p` of a locally bounded complex does not depend on the window.** For any window
`a, …, a + k` outside which the terms of the complex vanish, the class of the locally bounded case
agrees with the bounded-window class computed from that window; in particular the window
extracted from the covering of the quasi-compact scheme is immaterial. -/
theorem powerSumClassComplexLocallyBounded_eq (W : PowerSumClassRule C Gy sX)
    (P : CochainComplex X.Modules ℤ) (hP : IsLocallyBoundedFiniteLocallyFree P) {a : ℤ} {k : ℕ}
    (hvanish : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n)) (p : ℕ) :
    powerSumClassComplexLocallyBounded C Gy sX W P hP p =
      powerSumClassComplex C Gy sX W P a k p := by
  rw [powerSumClassComplexLocallyBounded, powerSumClassComplex, powerSumClassComplex,
    alternatingKClass_eq_of_isZero_outside_both P
      (exists_window_of_isLocallyBoundedFiniteLocallyFree hP).choose_spec hvanish]

end PowerSum

end Stacks.Chow

end
