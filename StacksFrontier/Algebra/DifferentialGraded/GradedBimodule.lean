module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleDefs
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTotalization

/-!
# Bimodules, graded bimodules, and the graded bimodule underlying a differential graded one

Let `R` be a commutative ring. Tag 0FQH defines three notions in sequence: for `R`-algebras `A`
and `B` an `(A, B)`-bimodule, for `ℤ`-graded `R`-algebras a graded `(A, B)`-bimodule, and for
differential graded `R`-algebras a differential graded `(A, B)`-bimodule. The third notion is
already available in this tree as `DifferentialGraded.Bimodule`, a right differential graded
`B`-module together with a compatible left differential graded `A`-action (Tag 0FQI). This file
supplies the first two and connects all three: part (2) refines part (1) by construction, and the
graded bimodule underlying a differential graded bimodule is obtained by totalizing its left
action.

## Main definitions

* `AlgebraBimodule`: an `(A, B)`-bimodule, part (1) of the definition.
* `GradedBimodule`: a graded `(A, B)`-bimodule, part (2) of the definition. It extends
  `AlgebraBimodule`, so the forgetful passage from part (2) to part (1) — a graded bimodule is a
  bimodule — is the parent projection `GradedBimodule.toAlgebraBimodule`.
* `DifferentialGraded.Bimodule.leftModuleTotal`: the left `A`-module structure on the module
  underlying a differential graded `(A, B)`-bimodule.
* `DifferentialGraded.Bimodule.toGradedBimodule`: the graded `(A, B)`-bimodule underlying a
  differential graded `(A, B)`-bimodule, the forgetful passage from part (3) to part (2).

## Main results

* `DifferentialGraded.Bimodule.toGradedBimodule_smul` and
  `DifferentialGraded.Bimodule.toGradedBimodule_grading`: the left action and the grading of that
  graded bimodule are the totalized left action and the grading of the underlying right module.

## Implementation notes

*Part (1) carries no axioms of its own.* The source's data — an `R`-module `M` with `R`-bilinear
maps `A × M → M` and `M × B → M` — and its three clauses are exactly a list of Mathlib instances,
so `AlgebraBimodule` has one data field, the carrier, and no proof fields. The dictionary is:

* `Module A M` provides `(a, x) ↦ a • x`, and its `mul_smul` is clause (a) on the left,
  `a' • (a • x) = (a' * a) • x`;
* `Module Bᵐᵒᵖ M` provides `(x, b) ↦ MulOpposite.op b • x`, a genuine *right* action, and its
  `mul_smul`, `op b' • (op b • x) = op (b * b') • x`, is clause (a) on the right,
  `(xb)b' = x(bb')`;
* `SMulCommClass A Bᵐᵒᵖ M` *is* clause (b): its one field `smul_comm` reads
  `a • op b • x = op b • a • x`, which is `a(xb) = (ax)b`;
* `one_smul` for the two module structures is clause (c), `1x = x = x1`;
* `Module R M` with `IsScalarTower R A M` and `IsScalarTower R Bᵐᵒᵖ M` is the `R`-bilinearity of
  the two maps. Each tower gives linearity in the scalar, `(r • a) • x = r • (a • x)`; linearity
  in the module variable, `a • (r • x) = r • (a • x)`, is then automatic, since for an `R`-algebra
  `R` is central and Mathlib derives `SMulCommClass R A M` from `IsScalarTower R A M`.

This is the bimodule set-up of `Mathlib/Algebra/Module/Bimodule.lean`, and the same encoding that
`StacksFrontier/Algebra/Module/Bimodule.lean` records for the ungraded Tag 00D1, where the notion is
tagged on Mathlib's `SMulCommClass` rather than bundled. It is bundled here because parts (2) and
(3) quantify over bimodules as objects: a forgetful passage between the three parts has to be a map
of bundled objects, which is what makes the three parts one definition rather than three unrelated
encodings.

*Graded algebras are unbundled.* Part (2) takes its two `ℤ`-graded `R`-algebras as gradings
`𝒜 : ℤ → Submodule R A` carrying `[GradedAlgebra 𝒜]`, the form in which
`DifferentialGradedAlgebra` records its own grading, so that `GradedBimodule A.grading B.grading`
is the destination of the passage out of part (3) with no translation.

*The passage from part (3) to part (2) is the totalization of the left action.* A
`DifferentialGraded.Bimodule` records its left `A`-action as a left differential graded action on
the cochain complex underlying the right module, i.e. degreewise, so the left action of the whole
of `A` on the whole of `M` has to be assembled along the two direct sum decompositions. That
assembly is `DifferentialGraded.leftActionAlgHom`, and the laws of part (1) and part (2) for it are
its algebra-homomorphism property together with `DifferentialGraded.leftActionTotal_commutes`,
which is exactly the right `B`-linearity built into `DifferentialGradedModule.BimoduleStructure`.
The differential and the Leibniz rules of part (3) are discarded by this passage, as they should
be.

## References

* [Stacks Project, Tag 0FQH](https://stacks.math.columbia.edu/tag/0FQH)
* [Stacks Project, Tag 0FQI](https://stacks.math.columbia.edu/tag/0FQI) for the presentation of a
  differential graded bimodule used by `DifferentialGraded.Bimodule`.
* [Stacks Project, Tag 00D1](https://stacks.math.columbia.edu/tag/00D1) for the ungraded notion.
-/

@[expose] public section

universe u

/-- An `(A, B)`-bimodule over a commutative ring `R`, for `R`-algebras `A` and `B`: an `R`-module
`M` with an `R`-bilinear left `A`-action and an `R`-bilinear right `B`-action which commute.

All of the source's clauses are discharged by the Mathlib classes listed as fields, so the only
data is the carrier: `mul_smul` of the two module structures is clause (a), `SMulCommClass` is
clause (b), `one_smul` is clause (c), and the two `IsScalarTower` fields together with the
`R`-module structure are the `R`-bilinearity of the two actions. -/
@[stacks_fixed 0FQH "(1): an `(A, B)`-bimodule, bundled as a carrier together with the Mathlib \
classes that discharge the source's clauses — `Module A M` and `Module Bᵐᵒᵖ M` (clause (a) by \
`mul_smul`, clause (c) by `one_smul`), `SMulCommClass A Bᵐᵒᵖ M` (clause (b)), and `Module R M` \
with the two `IsScalarTower`s (`R`-bilinearity of the two actions)"]
structure AlgebraBimodule (R : Type u) [CommRing R] (A : Type u) [Ring A] [Algebra R A]
    (B : Type u) [Ring B] [Algebra R B] where
  /-- The underlying `R`-module. -/
  M : Type u
  [addCommGroup : AddCommGroup M]
  /-- The `R`-module structure, over which both actions are bilinear. -/
  [module : Module R M]
  /-- The left `A`-action `(a, x) ↦ a • x`. Clause (a) on the left is its `mul_smul` and clause
  (c) on the left is its `one_smul`. -/
  [leftModule : Module A M]
  /-- The right `B`-action, as a module over the opposite ring: `(x, b) ↦ MulOpposite.op b • x`.
  Clause (a) on the right is its `mul_smul`, `op b' • (op b • x) = op (b * b') • x`, and clause
  (c) on the right is its `one_smul`. -/
  [rightModule : Module Bᵐᵒᵖ M]
  /-- `R`-bilinearity of the left action: `(r • a) • x = r • (a • x)`. -/
  [leftTower : IsScalarTower R A M]
  /-- `R`-bilinearity of the right action: `(r • op b) • x = r • (op b • x)`. -/
  [rightTower : IsScalarTower R Bᵐᵒᵖ M]
  /-- Clause (b), `a (x b) = (a x) b`: the two actions commute. -/
  [smulComm : SMulCommClass A Bᵐᵒᵖ M]

attribute [instance] AlgebraBimodule.addCommGroup AlgebraBimodule.module
  AlgebraBimodule.leftModule AlgebraBimodule.rightModule AlgebraBimodule.leftTower
  AlgebraBimodule.rightTower AlgebraBimodule.smulComm

/-- A graded `(A, B)`-bimodule over a commutative ring `R`, for `ℤ`-graded `R`-algebras `𝒜` and
`ℬ`: an `(A, B)`-bimodule `M` with a grading `M = ⨁ Mⁿ` such that `Aⁿ Mᵐ ⊆ Mⁿ⁺ᵐ` and
`Mⁿ Bᵐ ⊆ Mⁿ⁺ᵐ`.

The underlying `(A, B)`-bimodule of part (1) is the parent projection
`GradedBimodule.toAlgebraBimodule`. -/
@[stacks_fixed 0FQH "(2): a graded `(A, B)`-bimodule, an `AlgebraBimodule` (part (1), the parent \
projection `toAlgebraBimodule`) together with a grading by `R`-submodules which decomposes the \
module and satisfies `Aⁿ Mᵐ ⊆ Mⁿ⁺ᵐ` and `Mⁿ Bᵐ ⊆ Mⁿ⁺ᵐ`"]
structure GradedBimodule {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] {B : Type u} [Ring B] [Algebra R B]
    (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ] extends AlgebraBimodule R A B where
  /-- The grading `M = ⨁ Mⁿ` by `R`-submodules. -/
  grading : ℤ → Submodule R M
  /-- The grading is a direct sum decomposition `M = ⨁ Mⁿ`. -/
  [decomposition : DirectSum.Decomposition grading]
  /-- `Aⁿ Mᵐ ⊆ Mⁿ⁺ᵐ`. -/
  smul_mem_left : ∀ (n m : ℤ) (a : A) (x : M), a ∈ 𝒜 n → x ∈ grading m →
    a • x ∈ grading (n + m)
  /-- `Mⁿ Bᵐ ⊆ Mⁿ⁺ᵐ`. -/
  smul_mem_right : ∀ (n m : ℤ) (x : M) (b : B), x ∈ grading n → b ∈ ℬ m →
    MulOpposite.op b • x ∈ grading (n + m)

attribute [instance] GradedBimodule.decomposition

namespace DifferentialGraded

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- The left `A`-module structure on the module underlying a differential graded
`(A, B)`-bimodule, assembled from its degreewise left differential graded action by
`DifferentialGraded.leftActionAlgHom`. -/
@[instance_reducible] noncomputable def Bimodule.leftModuleTotal (M : Bimodule.{u, u} A B) :
    Module A.A M.rightModule.M :=
  Module.compHom M.rightModule.M (leftActionAlgHom A B M.rightModule M.leftAction.1).toRingHom

/-- The left action of `DifferentialGraded.Bimodule.leftModuleTotal` is the totalized left
action `DifferentialGraded.leftActionTotal`. -/
theorem Bimodule.leftModuleTotal_smul (M : Bimodule.{u, u} A B) (a : A.A) (x : M.rightModule.M) :
    letI := M.leftModuleTotal
    a • x = leftActionTotal A B M.rightModule M.leftAction.1 a x := rfl

/-- The graded `(A, B)`-bimodule underlying a differential graded `(A, B)`-bimodule: the right
differential graded `B`-module with its grading, the left `A`-action totalized from the left
differential graded action, and the differential forgotten.

This is what makes the three parts of [Stacks, Tag 0FQH] one definition rather than three
unrelated ones: part (3), `DifferentialGraded.Bimodule`, refines part (2), `GradedBimodule`,
which in turn extends part (1), `AlgebraBimodule`. -/
@[stacks 0FQH "the graded (A, B)-bimodule underlying a differential graded one, which is what \
makes part (3) a refinement of part (2); the three parts themselves are tagged with \
stacks_fixed, which plain @[stacks] cannot carry on a structure"]
noncomputable def Bimodule.toGradedBimodule (M : Bimodule.{u, u} A B) :
    GradedBimodule A.grading B.grading :=
  letI leftMod := M.leftModuleTotal
  { M := M.rightModule.M
    leftModule := leftMod
    leftTower := ⟨fun r a x => by
      change leftActionTotal A B M.rightModule M.leftAction.1 (r • a) x =
        r • leftActionTotal A B M.rightModule M.leftAction.1 a x
      rw [map_smul]
      rfl⟩
    smulComm := ⟨fun a c x => by
      obtain ⟨b, rfl⟩ : ∃ b : B.A, MulOpposite.op b = c := ⟨MulOpposite.unop c, rfl⟩
      change leftActionTotal A B M.rightModule M.leftAction.1 a (MulOpposite.op b • x) =
        MulOpposite.op b • leftActionTotal A B M.rightModule M.leftAction.1 a x
      induction a using DirectSum.Decomposition.inductionOn A.grading with
      | zero => simp
      | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha', smul_add]
      | @homogeneous n a =>
        induction b using DirectSum.Decomposition.inductionOn B.grading with
        | zero => simp
        | add b b' hb hb' => simp only [MulOpposite.op_add, add_smul, map_add, hb, hb']
        | @homogeneous q b =>
          exact leftActionTotal_commutes A B M.rightModule M.leftAction.1 M.leftAction.2 a b x⟩
    grading := M.rightModule.grading
    smul_mem_left := fun n m a x ha hx => by
      rw [add_comm n m]
      exact leftActionTotal_apply_mem A B M.rightModule M.leftAction.1 ⟨a, ha⟩ ⟨x, hx⟩
    smul_mem_right := fun n m x b hx hb => M.rightModule.smul_mem n m x b hx hb }

@[simp] theorem Bimodule.toGradedBimodule_grading (M : Bimodule.{u, u} A B) :
    M.toGradedBimodule.grading = M.rightModule.grading := rfl

/-- The left action of the graded bimodule underlying a differential graded bimodule is the
totalized left action `DifferentialGraded.leftActionTotal`. -/
theorem Bimodule.toGradedBimodule_smul (M : Bimodule.{u, u} A B) (a : A.A)
    (x : M.toGradedBimodule.M) :
    a • x = leftActionTotal A B M.rightModule M.leftAction.1 a x := rfl

end DifferentialGraded
