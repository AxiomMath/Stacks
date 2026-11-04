module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.Monoidal
public import StacksFrontier.Algebra.DirectSum.ExternalGrading
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps

/-!
# The twisted sections as an internally graded module

The twisted-section module `Stacks.TwistedSections.twistModule F L`, that is
`Γ_*(X, F, L) = ⨁_{m ≥ 0} Γ(X, F ⊗ L ^⊗ m)`, is a module over the section ring
`Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)`, both being *external* direct sums. The degree-zero
localization `GradedModuleDegreeZeroLocalization` of Stacks Tag 01M4 — the source of the map of
Stacks Tag 0B5L — is stated in Mathlib's *internal* picture instead: an `ℕ`-indexed family of
additive subgroups of the ring with `GradedRing`, and an `ℤ`-indexed family of additive
subgroups of the module with `DirectSum.Decomposition` and `SetLike.GradedSMul`. This file
supplies both for the two direct sums above, so that the Tag 01M4 vocabulary applies to them.

## Main definitions

* `Stacks.TwistedSections.sectionGrading`: the internal grading of the section ring, which is
  `Stacks.ExternalGrading.summand` — the images of the structure maps of the direct sum. Its
  `GradedRing` instance is `Stacks.ExternalGrading.gradedRing` and needs nothing new.
* `Stacks.TwistedSections.embedZ`: a twisted section as an element of its graded piece.
* `Stacks.TwistedSections.moduleGrading`: the `ℤ`-indexed internal grading of the twisted-section
  module: the `m`-th summand in degree `m ≥ 0`, and `⊥` in negative degrees.

## Main results

* `Stacks.TwistedSections.instDecomposition`: `DirectSum.Decomposition (moduleGrading F L)`.
* `Stacks.TwistedSections.instGradedSMul`:
  `SetLike.GradedSMul (sectionGrading L) (moduleGrading F L)`, at the action
  `Stacks.GradedLocalization.instVAddNatInt` of `ℕ` on `ℤ` that Tag 01M4's statements use.
* `Stacks.TwistedSections.mem_moduleGrading_natCast_iff`: a homogeneous element of degree
  `m ≥ 0` is `DirectSum.of _ m t` for a unique twisted section `t`.

## Implementation notes

**The negative degrees are `⊥`, not absent.** `GradedModuleDegreeZeroLocalization` indexes the
module by `ℤ` because a graded module over an `ℕ`-graded ring is `ℤ`-graded in general; the
module of twisted sections happens to be concentrated in nonnegative degrees, and the honest way
to say that in this interface is to make the negative pieces the trivial subgroup rather than to
re-index the module. The decomposition's right inverse then has a second case in which the
homogeneous piece is forced to be zero.

**The grading of the section ring is `Stacks.ExternalGrading.summand` verbatim.** That file
already proves `GradedRing` for *any* `DirectSum.GRing`, so no grading of the absolute section
ring has to be built here; naming it is the whole of the ring half.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4) — the degree-zero
  localization of a graded module, whose interface this file matches.
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
-/

@[expose] public section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections sectionRing HasTrivialSelfBraiding)
open scoped Stacks.GradedLocalization

universe v u

namespace Stacks.TwistedSections

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] {F L : C}

/-- **The internal grading of the section ring**: the images of its own structure maps, with
`GradedRing` supplied by `Stacks.ExternalGrading.gradedRing`. -/
abbrev sectionGrading (L : C) : ℕ → AddSubgroup (sectionRing L) :=
  Stacks.ExternalGrading.summand (powSections L)

/-- **The `ℤ`-indexed internal grading of the twisted-section module**: the `m`-th summand in
degree `m ≥ 0`, and the trivial subgroup in negative degrees. -/
def moduleGrading (F L : C) : ℤ → AddSubgroup (twistModule F L)
  | .ofNat m => Stacks.ExternalGrading.summand (twistSections F L) m
  | .negSucc _ => ⊥

/-- The degree-`m` piece of `moduleGrading F L`, for `m ≥ 0`, is the `m`-th summand. -/
theorem moduleGrading_natCast (m : ℕ) :
    moduleGrading F L (m : ℤ) = Stacks.ExternalGrading.summand (twistSections F L) m := rfl

/-- The pieces of `moduleGrading F L` in negative degrees are trivial. -/
theorem moduleGrading_negSucc (k : ℕ) : moduleGrading F L (Int.negSucc k) = ⊥ := rfl

/-- A homogeneous element of nonnegative degree is the image of a twisted section. -/
theorem mem_moduleGrading_natCast_iff {m : ℕ} {x : twistModule F L} :
    x ∈ moduleGrading F L (m : ℤ) ↔ ∃ t : twistSections F L m,
      DirectSum.of (twistSections F L) m t = x := Iff.rfl

/-- A twisted section of degree `m`, as an element of the degree-`m` graded piece. -/
def embedZ (F L : C) (m : ℕ) : twistSections F L m →+ moduleGrading F L (m : ℤ) where
  toFun t := ⟨DirectSum.of (twistSections F L) m t, ⟨t, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

/-- The underlying element of `embedZ F L m t` is `DirectSum.of _ m t`. -/
@[simp] theorem embedZ_coe (m : ℕ) (t : twistSections F L m) :
    ((embedZ F L m t : moduleGrading F L (m : ℤ)) : twistModule F L) =
      DirectSum.of (twistSections F L) m t := rfl

/-- The componentwise decomposition of the twisted-section module into its `ℤ`-graded pieces. -/
noncomputable def decomposeZ (F L : C) :
    twistModule F L →+ ⨁ z : ℤ, moduleGrading F L z :=
  DirectSum.toAddMonoid fun m =>
    (DirectSum.of (fun z : ℤ => (moduleGrading F L z : Type v)) (m : ℤ)).comp (embedZ F L m)

/-- `decomposeZ F L` sends `DirectSum.of _ m t` to `embedZ F L m t` in degree `m`. -/
@[simp] theorem decomposeZ_of (m : ℕ) (t : twistSections F L m) :
    decomposeZ F L (DirectSum.of (twistSections F L) m t) =
      DirectSum.of (fun z : ℤ => (moduleGrading F L z : Type v)) (m : ℤ) (embedZ F L m t) :=
  DirectSum.toAddMonoid_of _ _ _

/-- **The `ℤ`-graded pieces decompose the twisted-section module.** -/
noncomputable instance instDecomposition : DirectSum.Decomposition (moduleGrading F L) where
  decompose' := decomposeZ F L
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of m t =>
        rw [decomposeZ_of, DirectSum.coeAddMonoidHom_of, embedZ_coe]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of z w =>
        obtain ⟨m⟩ | ⟨k⟩ := z
        · obtain ⟨t, ht⟩ := w.2
          rw [DirectSum.coeAddMonoidHom_of, ← ht, decomposeZ_of]
          exact congrArg _ (Subtype.ext ht)
        · have hw : (w : twistModule F L) = 0 := by
            simpa [moduleGrading_negSucc] using w.2
          rw [DirectSum.coeAddMonoidHom_of, hw, map_zero,
            show w = 0 from Subtype.ext hw, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

variable [(tensorRight L).Additive] [BraidedCategory C] [HasTrivialSelfBraiding L]

/-- **The grading of the section ring acts on the grading of the twisted sections**, at the
action `n +ᵥ z = n + z` of `ℕ` on `ℤ` that Stacks Tag 01M4's statements use. -/
instance instGradedSMul : SetLike.GradedSMul (sectionGrading L) (moduleGrading F L) where
  smul_mem := by
    rintro i z a w ⟨a₀, rfl⟩ hw
    obtain ⟨m⟩ | ⟨k⟩ := z
    · obtain ⟨t, rfl⟩ := hw
      rw [of_smul_of]
      exact ⟨gsmul a₀ t, rfl⟩
    · have hw0 : w = 0 := by simpa [moduleGrading_negSucc] using hw
      rw [hw0, smul_zero]
      exact zero_mem _

end Stacks.TwistedSections

end
