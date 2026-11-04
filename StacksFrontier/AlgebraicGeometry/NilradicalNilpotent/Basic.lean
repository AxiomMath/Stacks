module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The nilradical of a Noetherian scheme is nilpotent

`AlgebraicGeometry.Scheme.nilradical X` is the radical of the zero ideal sheaf, and
`AlgebraicGeometry.Scheme.reduction X` is the closed subscheme it cuts out. This file proves that
on a quasi-compact scheme with Noetherian affine charts some power of that ideal sheaf is zero,
in the two forms the second paragraph of [Stacks, Tag 0AYW] uses: as `ℐ^{e+1} = 0` for ideal
sheaves, and as `ℐ^{e+1}·𝒪_X = 0` for the ideal-power filtration of the structure sheaf.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `Scheme.isNilpotent_nilradical`: `IsNilpotent X.nilradical`.
* `exists_nilradical_pow_succ_eq_bot`: `∃ e, X.nilradical ^ (e + 1) = ⊥`, the shape the source's
  induction runs on.
* `nilradical_pow_eq_bot_of_le`: every larger exponent kills it too.
* `idealPowerMultiple_nilradical_eq_bot`: `ℐ^{e+1}·𝒪_X = 0` as a subsheaf of the structure
  sheaf, for any exponent with `ℐ^{e+1} = ⊥`.

## Implementation notes

**This is one line of the [Stacks, Tag 01Y9] machinery, not a new argument.**
`AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_le_of_le_radical` already produces, on a
quasi-compact scheme with Noetherian affine charts, an exponent with `ℐ^n ≤ 𝒥` from
`ℐ ≤ 𝒥.radical`; the nilradical is by definition the radical of `⊥`, so the hypothesis holds at
`𝒥 = ⊥` by `AlgebraicGeometry.Scheme.IdealSheafData.radical_bot` and nothing has to be done
affine-locally here. What this file adds is the statement at the nilradical, together with its module-level form.

**Why the hypotheses are `[IsLocallyNoetherian X] [CompactSpace X]` rather than
`[IsNoetherian X]`.** They are the hypotheses of the lemma used, and `IsNoetherian` is their
conjunction, so the stronger form is a special case. Compactness is not removable: the exponent
is a maximum over an affine cover, and a locally Noetherian scheme with infinitely many
components can need arbitrarily large exponents.

**No `@[stacks 01Y9]` attribute is attached.** That tag is the equivalence, for a finite type
quasi-coherent `ℱ` and a finite type quasi-coherent ideal `ℐ`, between `ℐ^n ℱ = 0` for some `n`
and `Supp ℱ ⊆ V(ℐ)`, and it is already registered on
`AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset` and on
`Stacks.IdealPowerSupport.exists_idealPowerMultiple_eq_bot_iff_supp_subset`. What is proved here
is an instance of its forward direction, so the tag would overstate it.

## References

* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace AlgebraicGeometry

/-- **The nilradical of a Noetherian scheme is nilpotent.** Some power of the ideal sheaf whose
closed subscheme is `AlgebraicGeometry.Scheme.reduction X` is the zero ideal sheaf.

The nilradical is the radical of `⊥`, so this is
`AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_le_of_le_radical` at `𝒥 = ⊥`. -/
@[ega "I 6.1.6"]
theorem Scheme.isNilpotent_nilradical (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    IsNilpotent X.nilradical := by
  obtain ⟨n, hn⟩ := Scheme.IdealSheafData.exists_pow_le_of_le_radical
    (I := X.nilradical) (J := (⊥ : X.IdealSheafData))
    (le_of_eq (Scheme.IdealSheafData.radical_bot (X := X)).symm)
  exact ⟨n, le_antisymm hn bot_le⟩

/-- Once a power of the nilradical vanishes, so does every larger power. -/
theorem nilradical_pow_eq_bot_of_le {X : Scheme.{u}} {d e : ℕ} (hde : d ≤ e)
    (h : X.nilradical ^ d = ⊥) : X.nilradical ^ e = ⊥ :=
  le_antisymm ((Scheme.IdealSheafData.pow_le_pow_of_le X.nilradical hde).trans h.le) bot_le

/-- **The nilpotence of the nilradical with the exponent written `e + 1`** — the shape the
induction of the second paragraph of [Stacks, Tag 0AYW] runs on, where `e` is an exponent with
`ℐ^{e+1} = 0` and the induction is on `e`. -/
theorem exists_nilradical_pow_succ_eq_bot (X : Scheme.{u}) [IsLocallyNoetherian X]
    [CompactSpace X] : ∃ e : ℕ, X.nilradical ^ (e + 1) = ⊥ := by
  obtain ⟨n, hn⟩ := X.isNilpotent_nilradical
  exact ⟨n, nilradical_pow_eq_bot_of_le (Nat.le_succ n) hn⟩

/-- **The module-level form: `ℐ^{e+1}·𝒪_X = 0`.** A power of the nilradical that vanishes as an
ideal sheaf annihilates the structure sheaf, so it is zero as a step of the ideal-power
filtration of `𝒪_X` as well.

Affine-locally the condition is that `ℐ(U)^{e+1}·Γ(X, U) = 0`, and `ℐ(U)^{e+1}` is the zero
ideal. -/
theorem idealPowerMultiple_nilradical_eq_bot {X : Scheme.{u}} {e : ℕ}
    (he : X.nilradical ^ (e + 1) = ⊥) :
    idealPowerMultiple X.nilradical (e + 1) (SheafOfModules.unit X.ringCatSheaf) = ⊥ := by
  refine (Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_affine_smul_top
    X.nilradical (e + 1) (SheafOfModules.unit X.ringCatSheaf)).2 fun U => ?_
  have hbot : X.nilradical.ideal U ^ (e + 1) = ⊥ := by
    simpa using congrArg (fun I : X.IdealSheafData => I.ideal U) he
  simp [hbot]

end AlgebraicGeometry

end
