module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Effective
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksCore.Tactic.StacksAttribute

/-!
# Effective relative cycles

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type and let
`r ≥ 0`. A relative `r`-cycle `α` on `X/S`, that is an element of the group
`z(X/S, r) = Stacks.Chow.relativeCycles f r`, is *effective* when for every point `s` of `S` the
`r`-cycle `α_s` it carries on the scheme-theoretic fibre `X_s` is an effective cycle, that is has
nonnegative coefficients.

Effectivity is preserved by zero and by addition, so the effective relative `r`-cycles form a
submonoid `z^eff(X/S, r)` of `z(X/S, r)`. It is not a subgroup: the negative of a nonzero
effective cycle is not effective.

## Main definitions

* `Stacks.Chow.IsEffectiveRelativeCycle` — a relative `r`-cycle is effective when the cycle it
  carries on every fibre is effective.
* `Stacks.Chow.effectiveRelativeCycles` — the monoid `z^eff(X/S, r)` of effective relative
  `r`-cycles.

## Main results

* `Stacks.Chow.isEffectiveRelativeCycle_iff_isEffectiveFamily` — effectivity of a relative
  `r`-cycle is effectivity of the underlying family of cycles on fibres.
* `Stacks.Chow.mem_effectiveRelativeCycles` — membership in `z^eff(X/S, r)` is fibrewise
  effectivity.
* `Stacks.Chow.effectiveRelativeCycles_eq_comap` — `z^eff(X/S, r)` is the part of `z(X/S, r)`
  lying in the submonoid of effective families of cycles on fibres.

## References

* [Stacks Project, Definition 0H5R](https://stacks.math.columbia.edu/tag/0H5R)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Definition 0H47](https://stacks.math.columbia.edu/tag/0H47)
* [Stacks Project, Remark 0H5Y](https://stacks.math.columbia.edu/tag/0H5Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- A relative `r`-cycle `α` on `X/S` is *effective* when for every point `s` of `S` the
`r`-cycle `α_s` it carries on the scheme-theoretic fibre over `s` is an effective cycle. -/
@[stacks 0H5R "effectivity of a relative r-cycle"]
def IsEffectiveRelativeCycle {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : ↥(relativeCycles f r)) : Prop :=
  ∀ s : S, IsEffectiveCycle (α.1 s : AlgebraicCycle (f.fiber s) ℤ)

/-- Effectivity of a relative `r`-cycle is effectivity of the underlying family of `r`-cycles on
the fibres of `X/S`. -/
theorem isEffectiveRelativeCycle_iff_isEffectiveFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) (α : ↥(relativeCycles f r)) :
    IsEffectiveRelativeCycle f r α ↔ IsEffectiveFamily f r α.1 :=
  Iff.rfl

/-- The zero relative `r`-cycle is effective. -/
theorem isEffectiveRelativeCycle_zero {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) : IsEffectiveRelativeCycle f r 0 :=
  fun _ ↦ isEffectiveCycle_zero

/-- A sum of effective relative `r`-cycles is effective. -/
theorem IsEffectiveRelativeCycle.add {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] {r : ℕ} {α β : ↥(relativeCycles f r)}
    (hα : IsEffectiveRelativeCycle f r α) (hβ : IsEffectiveRelativeCycle f r β) :
    IsEffectiveRelativeCycle f r (α + β) :=
  fun s ↦ (hα s).add (hβ s)

/-- The monoid `z^eff(X/S, r)` of *effective relative `r`-cycles* on `X/S`: the submonoid of the
group `z(X/S, r)` of relative `r`-cycles consisting of those whose cycle on every fibre is
effective. -/
@[stacks 0H5R "the monoid z^eff(X/S, r)"]
def effectiveRelativeCycles {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) : AddSubmonoid ↥(relativeCycles f r) where
  carrier := {α | IsEffectiveRelativeCycle f r α}
  zero_mem' := isEffectiveRelativeCycle_zero f r
  add_mem' := fun hα hβ ↦ hα.add hβ

/-- Membership in `z^eff(X/S, r)` is fibrewise effectivity of the underlying family of cycles on
fibres. -/
@[simp]
theorem mem_effectiveRelativeCycles {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : ↥(relativeCycles f r)) :
    α ∈ effectiveRelativeCycles f r ↔ IsEffectiveFamily f r α.1 :=
  Iff.rfl

/-- The monoid `z^eff(X/S, r)` of effective relative `r`-cycles is the part of the group
`z(X/S, r)` of relative `r`-cycles lying in the submonoid of effective families of `r`-cycles on
fibres. -/
theorem effectiveRelativeCycles_eq_comap {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) :
    effectiveRelativeCycles f r = (effectiveFamilies f r).comap (relativeCycles f r).subtype :=
  AddSubmonoid.ext fun _ => Iff.rfl

end Stacks.Chow

end
