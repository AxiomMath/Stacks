module

public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The complete local base of a formal object belongs to the site

A formal object `ξ = (R, ξ_n, f_n)` of a category over the big fppf site `(Sch/S)_{fppf}` of
**Stacks 07X4** records that each infinitesimal thickening `Spec (R / 𝔪 ^ (n + 1))` is an object
of the site, but not that `Spec R` itself is: the site is the full subcategory `Sch_κ` of schemes
of size below a cutoff cardinal `κ`. This file shows that it is anyway. The ring `R` embeds into
the product of its truncations because it is `𝔪`-adically separated, so its cardinality is at
most `(sup_n #(R / 𝔪 ^ (n + 1))) ^ ℵ₀`, and **Stacks 000J (3), (4)** — the cutoff is a strong
limit cardinal of uncountable cofinality — keeps such a bound below `κ`.

This is the "site cardinality" step implicit in the source's Stacks 07X8: an effective formal
object is the restriction of an object of the stack over `Spec R`, which presupposes that
`Spec R` is an object of the site.

## Main results

* `Deformation.Artin.FormalBase.contains_spec_of_contains_truncation`: if every truncation of a
  complete local base belongs to the site, so does its spectrum.
* `Deformation.Artin.FormalObject.contains_spec_base`: the spectrum of the complete local base of a
  formal object belongs to the site.

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Cardinal IsLocalRing

universe u v w

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}}

/-- A complete local base all of whose infinitesimal thickenings belong to the site has its
spectrum in the site: the ring embeds into the product of its truncations, and a countable
product of objects of `Sch_κ` is bounded by **Stacks 000J (3), (4)**. -/
theorem FormalBase.contains_spec_of_contains_truncation (A : FormalBase S)
    (h : ∀ n, B.Contains (A.truncation n)) : B.Contains (Spec (.of A.R)) := by
  let F : ULift.{u} ℕ → Scheme.{u} := fun n => A.truncation n.down
  refine Scheme.size_lt_of_le_stacksBound_iSup B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    B.aleph0_lt_cutoff_cof (by simp) F (fun n => h n.down) ?_
  set s : Cardinal.{u} := ⨆ n, (F n).size
  have hs : ∀ n : ULift.{u} ℕ, max ℵ₀ #(A.R ⧸ maximalIdeal A.R ^ (n.down + 1)) ≤ s := fun n =>
    (Scheme.size_Spec (.of (A.R ⧸ maximalIdeal A.R ^ (n.down + 1)))).ge.trans
      (le_ciSup Cardinal.bddAbove_of_small n)
  have hℵ : ℵ₀ ≤ s := (le_max_left _ _).trans (hs ⟨0⟩)
  have hinj : Function.Injective fun (r : A.R) (n : ULift.{u} ℕ) =>
      Ideal.Quotient.mk (maximalIdeal A.R ^ (n.down + 1)) r := by
    intro x y hxy
    have : IsAdicComplete (maximalIdeal A.R) A.R := A.complete
    rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal A.R)]
    intro n
    have hn := congrFun hxy ⟨n⟩
    simp only [Ideal.Quotient.eq] at hn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) hn
  have hcard : #A.R ≤ s ^ ℵ₀ :=
    calc #A.R ≤ #(∀ n : ULift.{u} ℕ, A.R ⧸ maximalIdeal A.R ^ (n.down + 1)) :=
          Cardinal.mk_le_of_injective hinj
      _ = Cardinal.prod fun n : ULift.{u} ℕ => #(A.R ⧸ maximalIdeal A.R ^ (n.down + 1)) :=
          Cardinal.mk_pi _
      _ ≤ Cardinal.prod fun _ : ULift.{u} ℕ => s :=
          Cardinal.prod_le_prod _ _ fun n => (le_max_right _ _).trans (hs n)
      _ = s ^ ℵ₀ := by rw [Cardinal.prod_const', Cardinal.mk_uLift, Cardinal.mk_nat, lift_aleph0]
  rw [Scheme.size_Spec]
  exact le_max_of_le_left <|
    max_le (hℵ.trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0)) hcard

/-- **The complete local base of a formal object belongs to the site.** For a formal object
`ξ = (R, ξ_n, f_n)` (**Stacks 07X4**) over the big fppf site of `S`, the spectrum `Spec R` is an
object of the site, although only its infinitesimal thickenings are recorded as such. -/
theorem FormalObject.contains_spec_base {hS : B.Contains S} {F : Type v} [Category.{w} F]
    {p : F ⥤ BigFppfOver B S hS} (ξ : FormalObject B S hS p) :
    B.Contains (Spec (.of ξ.base.R)) :=
  ξ.base.contains_spec_of_contains_truncation ξ.contains

end Deformation.Artin

end
