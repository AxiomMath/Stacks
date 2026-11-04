module

public import StacksFrontier.RingTheory.Fitting.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Fitting ideal sheaf of a finite type quasi-coherent module

Let `F` be a finite type quasi-coherent `𝒪_X`-module on a scheme `X`. On every affine open `U`
the sections `Γ(F, U)` are a finite `Γ(X, U)`-module
(`Stacks.AlgebraicGeometry.CoherentFinite.finite_sections`), so they have module-theoretic Fitting
ideals. This file shows that the resulting family of ideals *is* quasi-coherent ideal sheaf data,
i.e. that it is compatible with restriction to basic opens, and deduces that
`Scheme.IdealSheafData.ofIdeals` recovers it.

## Main definitions

* `Stacks.AlgebraicGeometry.FittingIdealSheaf.ideal` is the component of the `k`-th Fitting ideal
  sheaf on an affine open: the Fitting ideal of the sections there.
* `Stacks.AlgebraicGeometry.FittingIdealSheaf.sheaf` is the `k`-th Fitting ideal sheaf, as
  `Scheme.IdealSheafData`.
* `Stacks.AlgebraicGeometry.FittingIdealSheaf.cardFittingIdeal` is the ideal sheaf `ofIdeals` of
  the family that takes the Fitting ideal where the sections are finite and `⊥` elsewhere.

## Main results

* `Stacks.AlgebraicGeometry.FittingIdealSheaf.ideal_basicOpen`: the Fitting ideals of the
  sections are compatible with restriction to a basic open.
* `Stacks.AlgebraicGeometry.FittingIdealSheaf.cardFittingIdeal_ideal`: the component of the ideal
  sheaf on an affine open is the module-theoretic Fitting ideal of the sections.

## Implementation notes

`Scheme.IdealSheafData.ofIdeals` is the *largest* ideal sheaf below a prescribed family, so it
need not recover the family. It does here because the family already satisfies
`map_ideal_basicOpen`, and `Scheme.IdealSheafData.ofIdeals_ideal` then applies. The compatibility
is base change for Fitting ideals, `fittingIdeal_basic_properties` part (3), combined with
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.baseChangeEquiv`, which exhibits
`Γ(F, X.basicOpen f)` as `Γ(X, X.basicOpen f) ⊗_{Γ(X, U)} Γ(F, U)`. Only the nonnegative indices
carry content: at a negative index both sides are `⊥`.

`Module.Finite` is a `Prop`, so the instance that the module-theoretic `fittingIdeal` consumes is
irrelevant to the value of the ideal, and the instances supplied by `finite_affine` and by the
hypothesis of `cardFittingIdeal_ideal` need not be identified.

## References

* [Stacks Project, Tag 0C3D](https://stacks.math.columbia.edu/tag/0C3D)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.CoherentFinite

universe u

namespace Stacks.AlgebraicGeometry.FittingIdealSheaf

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/-- `Γ(F, U)` is a finite `Γ(X, U)`-module on every affine open `U`. -/
theorem finite_affine (U : X.affineOpens) : Module.Finite Γ(X, U.1) Γ(F, U.1) :=
  finite_sections F U.2

/-- The `k`-th Fitting ideal of the sections on an affine open. -/
noncomputable def ideal (k : ℤ) (U : X.affineOpens) : Ideal Γ(X, U.1) :=
  letI := finite_affine F U
  fittingIdeal (R := Γ(X, U.1)) (M := Γ(F, U.1)) k

/-- The Fitting ideals of the sections are compatible with restriction to a basic open: the
image of `ideal F k U` in `Γ(X, X.basicOpen f)` is `ideal F k (X.affineBasicOpen f)`. -/
theorem ideal_basicOpen (k : ℤ) (U : X.affineOpens) (f : Γ(X, U.1)) :
    (ideal F k U).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      ideal F k (X.affineBasicOpen f) := by
  have hU := finite_affine F U
  have hf : Module.Finite Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) :=
    finite_sections F (U.2.basicOpen f)
  show (fittingIdeal (R := Γ(X, U.1)) (M := Γ(F, U.1)) k).map
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
    fittingIdeal (R := Γ(X, X.basicOpen f)) (M := Γ(F, X.basicOpen f)) k
  rcases lt_or_ge k 0 with hk | hk
  · rw [fittingIdeal_eq_bot_of_lt_zero hk, fittingIdeal_eq_bot_of_lt_zero hk, Ideal.map_bot]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have hbc := (fittingIdeal_basic_properties.{u, u, u, u} (R := Γ(X, U.1)) (M := Γ(F, U.1))).2.2.1
      Γ(X, X.basicOpen f) n
    have heq := fittingIdeal_eq_of_linearEquiv
      (baseChangeEquiv F (U.2.basicOpen f) U.2 (X.basicOpen_le f)) n
    rw [← heq, hbc]
    rfl


/-! ### The Fitting ideal sheaf -/

/-- The `k`-th Fitting ideal sheaf of a finite type quasi-coherent module, as quasi-coherent
ideal sheaf data, whose component on an affine open is the module-theoretic Fitting ideal of the
sections there. -/
@[sga "7 VI 5.5" "special case"]
noncomputable def sheaf (k : ℤ) : X.IdealSheafData where
  ideal := ideal F k
  map_ideal_basicOpen := ideal_basicOpen F k

/-- The component of `sheaf F k` on an affine open `U` is `ideal F k U`. -/
@[simp] theorem sheaf_ideal (k : ℤ) (U : X.affineOpens) :
    (sheaf F k).ideal U = ideal F k U := rfl

/-! ### The Fitting ideal sheaf of an arbitrary module sheaf -/

/-- The family of ideals on affine opens given by the Fitting ideal of the sections where those
are a finite module, and `⊥` elsewhere. -/
noncomputable def cardFamily (G : X.Modules) (k : ℤ) (U : X.affineOpens) : Ideal Γ(X, U.1) := by
  classical
  exact if h : Module.Finite Γ(X, U.1) Γ(G, U.1) then
      letI := h
      fittingIdeal (M := Γ(G, U.1)) k
    else ⊥

/-- The `k`-th Fitting ideal sheaf of an arbitrary module sheaf `G`: the largest ideal sheaf
contained in `cardFamily G k`. -/
noncomputable def cardFittingIdeal (G : X.Modules) (k : ℤ) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals (cardFamily G k)

/-- For a finite type quasi-coherent module, `cardFamily F k` is the family `ideal F k`. -/
theorem cardFamily_eq (k : ℤ) : cardFamily F k = ideal F k := by
  classical
  funext U
  have := finite_affine F U
  simp only [cardFamily, this, dite_true]
  rfl

/-- For a finite type quasi-coherent module, `cardFittingIdeal F k` is `sheaf F k`. -/
theorem cardFittingIdeal_eq (k : ℤ) : cardFittingIdeal F k = sheaf F k := by
  rw [cardFittingIdeal, cardFamily_eq]
  exact Scheme.IdealSheafData.ofIdeals_ideal (sheaf F k)

/-- On every affine open, the Fitting ideal sheaf of a finite type quasi-coherent module is the
module-theoretic Fitting ideal of its sections. -/
@[sga "7 VI 5.5" "special case"]
theorem cardFittingIdeal_ideal (k : ℤ) (U : X.affineOpens)
    [Module.Finite Γ(X, U.1) Γ(F, U.1)] :
    (cardFittingIdeal F k).ideal U = fittingIdeal (M := Γ(F, U.1)) k := by
  rw [cardFittingIdeal_eq, sheaf_ideal]
  rfl

end Stacks.AlgebraicGeometry.FittingIdealSheaf

end
