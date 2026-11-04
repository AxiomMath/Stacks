module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseExteriorSymmetricAlgebra
public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap
public import StacksFrontier.RingTheory.Koszul.Defs
public import StacksFrontier.RingTheory.Koszul.Semilinear

/-!
# Contraction on the integer-indexed exterior powers, and its base change

`StacksFrontier.RingTheory.Koszul.Defs` defines the Koszul differential of a functional
`φ : E →ₗ[R] R` as contraction `Koszul.contraction φ` of the exterior algebra, and records that
it carries `⋀^(n+1) E` into `⋀ⁿ E`. The sectionwise exterior algebra of a presheaf of modules
in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseExteriorSymmetricAlgebra` is graded
by `ℤ` rather than by `ℕ`, through `ExteriorAlgebra.intPiece`, and its restriction maps are the
semilinear base change `ExteriorAlgebra.mapₛₗ`.

This file supplies the facts about contraction that the presheaf-level Koszul differential needs
and that neither of those files has: that contraction carries the `ℤ`-indexed piece of degree
`n + 1` into the one of degree `n` for *every* integer `n`, and the graded form of its
compatibility with semilinear base change. The ungraded ingredients —
`Koszul.contraction_eq_zero_of_mem_zero`, that contraction kills exterior degree zero, and
`Koszul.mapₛₗ_contraction`, that it commutes with semilinear base change along a ring map
compatible with the two functionals — are taken from
`StacksFrontier.RingTheory.Koszul.Semilinear`.

## Main definitions

* `Koszul.intPowD`: the Koszul differential as a map `intPiece R E (n + 1) → intPiece R E n` of
  `ℤ`-indexed exterior powers.

## Main results

* `Koszul.contraction_mem_intPiece`: contraction lowers the `ℤ`-grading by one.
* `Koszul.intPowD_comp_intPowD`: the graded differential squares to zero.
* `Koszul.intPowMapₛₗ_intPowD`: the graded differentials commute with semilinear base change.

## Implementation notes

The three integer cases of `contraction_mem_intPiece` are genuinely different. In a
nonnegative degree it is `Koszul.contraction_mem`. In degree `-1` the source is exterior degree
zero, which is the image of the scalars (`Submodule.mem_one`), and contraction vanishes there by
`Koszul.contraction_eq_zero_of_mem_zero`. Below degree `-1` the source is already the zero
submodule.

## References

* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
-/

@[expose] public section

open scoped ExteriorAlgebra

namespace Koszul

universe u v u' v'

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- **Contraction lowers the integer grading by one.** For every integer `n`, contraction
carries the `ℤ`-indexed exterior power of degree `n + 1` into the one of degree `n`. -/
theorem contraction_mem_intPiece (φ : Module.Dual R E) (n : ℤ) {x : ExteriorAlgebra R E}
    (hx : x ∈ ExteriorAlgebra.intPiece R E (n + 1)) :
    contraction φ x ∈ ExteriorAlgebra.intPiece R E n := by
  cases n with
  | ofNat k => exact contraction_mem φ k hx
  | negSucc k =>
    rw [ExteriorAlgebra.intPiece_eq_bot_of_neg R E (by omega), Submodule.mem_bot]
    cases k with
    | zero =>
      rw [show (Int.negSucc 0) + 1 = ((0 : ℕ) : ℤ) from by decide] at hx
      exact contraction_eq_zero_of_mem_zero φ hx
    | succ m =>
      rw [ExteriorAlgebra.eq_zero_of_mem_intPiece_of_neg R E (by omega) hx, map_zero]

/-- **The Koszul differential on the integer-indexed exterior powers.** It is the restriction
of `Koszul.contraction φ` to the piece of degree `n + 1`, landing in the piece of degree `n`. -/
noncomputable def intPowD (φ : Module.Dual R E) (n : ℤ) :
    ↥(ExteriorAlgebra.intPiece R E (n + 1)) →ₗ[R] ↥(ExteriorAlgebra.intPiece R E n) :=
  LinearMap.codRestrict _
    (contraction φ ∘ₗ (ExteriorAlgebra.intPiece R E (n + 1)).subtype)
    (fun x => contraction_mem_intPiece φ n x.2)

/-- As an element of the exterior algebra, `intPowD φ n x` is the contraction of `x` by `φ`. -/
@[simp]
theorem intPowD_coe (φ : Module.Dual R E) (n : ℤ) (x : ↥(ExteriorAlgebra.intPiece R E (n + 1))) :
    (intPowD φ n x : ExteriorAlgebra R E) = contraction φ (x : ExteriorAlgebra R E) :=
  rfl

/-- The graded Koszul differential squares to zero. -/
theorem intPowD_comp_intPowD (φ : Module.Dual R E) (n : ℤ) :
    (intPowD φ n).comp (intPowD φ (n + 1)) = 0 :=
  LinearMap.ext fun x => Subtype.ext <|
    CliffordAlgebra.contractLeft_contractLeft φ (x : ExteriorAlgebra R E)

section BaseChange

variable {S : Type u'} [CommRing S] {N : Type v'} [AddCommGroup N] [Module S N]

/-- The graded form of `Koszul.mapₛₗ_contraction`: base change on the `ℤ`-indexed exterior
powers intertwines the graded Koszul differentials. -/
theorem intPowMapₛₗ_intPowD (ρ : R →+* S) (u : E →ₛₗ[ρ] N) (φ : Module.Dual R E)
    (ψ : Module.Dual S N) (h : ∀ e : E, ρ (φ e) = ψ (u e)) (n : ℤ)
    (x : ↥(ExteriorAlgebra.intPiece R E (n + 1))) :
    ExteriorAlgebra.intPowMapₛₗ n ρ u (intPowD φ n x) =
      intPowD ψ n (ExteriorAlgebra.intPowMapₛₗ (n + 1) ρ u x) :=
  Subtype.ext (mapₛₗ_contraction ρ u φ ψ h (x : ExteriorAlgebra R E))

end BaseChange

end Koszul

end
