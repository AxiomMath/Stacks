module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# Further clauses of Stacks 000R (9) for `Sch_κ`

Clause (9)(a) of Stacks 000R: if `Spec R` is an object of `Sch_κ = {S | size S < κ}` and
`I ⊆ R` is an ideal, then the spectrum of the completion `R^* = lim_n R/I^n` is an object of
`Sch_κ`. As a set `R^*` is the image of a map from a subset of `R^ℕ`, so
`#R^* ≤ #R ^ ℵ₀ ≤ size(Spec R) ^ ℵ₀`, and clause (9) applies.

Clause (9)(f): a scheme of finite type over a ring of cardinality at most `#R ^ ℵ₀` is an object
of `Sch_κ`, combining clause (9) with clause (5).

## Main results

* `AlgebraicGeometry.Scheme.size_Spec_adicCompletion_lt`: clause (9)(a).
* `AlgebraicGeometry.Scheme.size_lt_of_finiteType_of_mk_le_power`: clause (9)(f).

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open Cardinal

universe u

namespace AlgebraicGeometry

variable {κ : Cardinal.{u}}

/-- For an object `Spec R` of `Sch_κ` and an ideal `I ⊆ R`, the spectrum of the completion
`R^* = lim_n R/I^n` is an object of `Sch_κ`. As a set `R^*` is the image of a map from a subset of
`R^ℕ`, so `#R^* ≤ #R ^ ℵ₀ ≤ size(Spec R) ^ ℵ₀`. -/
@[stacks 000R "(9)(a)"]
theorem Scheme.size_Spec_adicCompletion_lt (hκ : ℵ₀ < κ) (hsl : Cardinal.IsStrongPrelimit κ)
    {R : Type u} [CommRing R] (I : Ideal R) (hR : (Spec (CommRingCat.of R)).size < κ) :
    (Spec (CommRingCat.of (AdicCompletion I R))).size < κ := by
  refine Scheme.size_Spec_lt_of_mk_le hκ hsl _ hR ?_
  calc Cardinal.mk (AdicCompletion I R)
      ≤ Cardinal.mk (AdicCompletion.AdicCauchySequence I R) :=
        Cardinal.mk_le_of_surjective (AdicCompletion.mk_surjective I R)
    _ ≤ Cardinal.mk (ℕ → R) := Cardinal.mk_le_of_injective Subtype.val_injective
    _ = Cardinal.mk R ^ ℵ₀ := by simp
    _ ≤ (Spec (CommRingCat.of R)).size ^ ℵ₀ :=
        power_le_power_right (by rw [Scheme.size_Spec]; exact le_max_right _ _)

/-- For an object `Spec R` of `Sch_κ`, any scheme `X` of finite type over a ring `A` with
`#A ≤ #R ^ ℵ₀` is an object of `Sch_κ`: `Spec A` lies in `Sch_κ` by (9), and then so does `X`
by (5). -/
@[stacks 000R "(9)(f)"]
theorem Scheme.size_lt_of_finiteType_of_mk_le_power (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) {R A : Type u} [CommRing R] [CommRing A]
    (hR : (Spec (CommRingCat.of R)).size < κ) (hA : Cardinal.mk A ≤ Cardinal.mk R ^ ℵ₀)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f]
    [QuasiCompact f] : X.size < κ :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f
    (Scheme.size_Spec_lt_of_mk_le hκ hsl _ hR (hA.trans
      (power_le_power_right (by rw [Scheme.size_Spec]; exact le_max_right _ _))))

end AlgebraicGeometry
