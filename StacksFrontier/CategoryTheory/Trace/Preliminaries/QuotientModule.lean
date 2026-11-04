module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import StacksFrontier.CategoryTheory.Trace.Preliminaries.FreeModuleTrace
public import StacksCore.Tactic.StacksAttribute

/-!
# The scalar action on the additive commutator quotient

Let `Λ` be a possibly noncommutative ring and `A → Λ` a ring map whose image is central.  The
additive commutators of `Λ` are stable under the resulting scalar action, so the additive
commutator quotient `Λⁿᵃᵗ` of `Λ` is an `A`-module, compatibly with the quotient map.

## Main definitions

* `Stacks.Trace.additiveCommutatorSubmodule`: the additive commutator subgroup of `Λ`, as an
  `A`-submodule.
* `Stacks.Trace.InducedAdditiveCommutatorQuotientModule`: an `A`-module structure on the
  additive commutator quotient for which the quotient map is `A`-equivariant.
* `Stacks.Trace.inducedAdditiveCommutatorQuotientModule`: the module structure induced by a
  central ring map, together with its compatibility with the quotient map.
* `Stacks.Trace.additiveCommutatorQuotientModule`: that structure, as an instance.

## References

* [Stacks Project, Tag 03U8](https://stacks.math.columbia.edu/tag/03U8)
-/

@[expose] public section

open CategoryTheory.FilteredDerived

namespace Stacks.Trace

/-- The additive commutator subgroup of `Λ`, as an `A`-submodule along a central ring map
`A → Λ`. -/
@[sga "4½ Rapport 4.2" "partial"]
def additiveCommutatorSubmodule
    (A Λ : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] : Submodule A Λ where
  carrier := additiveCommutatorSubgroup Λ
  zero_mem' := AddSubgroup.zero_mem _
  add_mem' := AddSubgroup.add_mem _
  smul_mem' a x hx := by
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
        obtain ⟨u, v, rfl⟩ := hx
        exact AddSubgroup.subset_closure
          ⟨a • u, v, by rw [smul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]⟩
    | zero => simp
    | add x y _ _ hx hy => simpa only [smul_add, SetLike.mem_coe] using add_mem hx hy
    | neg x _ hx => simpa only [smul_neg, SetLike.mem_coe] using neg_mem hx

/-- An `A`-module structure on the additive commutator quotient for which the quotient map is
compatible with the scalar action coming from `A → Λ`. -/
structure InducedAdditiveCommutatorQuotientModule
    (A Λ : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] where
  toModule : Module A (AdditiveCommutatorQuotient Λ)
  smul_mk : letI := toModule
    ∀ (a : A) (x : Λ),
      a • additiveCommutatorQuotientMk Λ x =
        additiveCommutatorQuotientMk Λ (a • x)

/-- A central map `A → Λ` induces an `A`-module structure on the
additive commutator quotient of `Λ`. -/
@[stacks 03U8]
noncomputable def inducedAdditiveCommutatorQuotientModule
    (A Λ : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] :
    InducedAdditiveCommutatorQuotientModule A Λ :=
  ⟨(show Module A (Λ ⧸ additiveCommutatorSubmodule A Λ) from
    Submodule.Quotient.module _), fun _ _ ↦ rfl⟩

/-- The module structure on the additive commutator quotient induced by the central algebra
map. -/
@[sga "5 IIIB 5.0" "special case"]
noncomputable instance additiveCommutatorQuotientModule
    (A Λ : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] :
    Module A (AdditiveCommutatorQuotient Λ) :=
  (inducedAdditiveCommutatorQuotientModule A Λ).toModule

end Stacks.Trace
