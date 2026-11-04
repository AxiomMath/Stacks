module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Finiteness.Projective
public import StacksFrontier.CategoryTheory.Trace.Preliminaries.FreeModuleTrace
public import StacksCore.Tactic.StacksAttribute

/-!
# The group trace

Let `R` be a possibly noncommutative ring and `G` a group.  Taking the coefficient of the
identity element of the group ring `R[G]` kills the additive commutators of `R[G]`, so it
descends to a map `ε : R[G]ⁿᵃᵗ → Rⁿᵃᵗ` between additive commutator quotients.

The trace of an endomorphism of a finite projective module over a possibly noncommutative ring
is defined by writing the module as a direct summand of a finite free module and taking the
trace of the induced endomorphism of that free module.  Composing it with `ε` gives the group
trace of an endomorphism of a finite projective `R[G]`-module.

## Main definitions

* `Stacks.Trace.coeffOneAddMonoidHom`: taking the coefficient of the identity, as an additive
  homomorphism `R[G] →+ R`.
* `Stacks.Trace.epsilon`: the induced map on additive commutator quotients.
* `Stacks.Trace.projectiveModuleTrace`: the trace of an endomorphism of a finite projective
  module.
* `Stacks.Trace.groupTrace`: the group trace of an endomorphism of a finite projective
  `R[G]`-module.

## Main results

* `Stacks.Trace.exists_epsilon`: taking the coefficient of the identity factors through the
  additive commutator quotient of the group ring.
* `Stacks.Trace.epsilon_comp_mk` and `Stacks.Trace.epsilon_mk`: the defining factorization of
  `epsilon`, and its value on a class.

## Implementation notes

The factorization of the coefficient map is stated for additive groups, since the additive
commutator quotient of a ring need not itself be a ring.  `epsilonFactorization` packages the
chosen map together with its defining equality, and `epsilon` is its underlying additive
homomorphism.  The coefficient ring and the group live in independent universes, and the
factorization works for an arbitrary group because every element of a group ring has finite
support.

A finite projective module is a direct summand of a finite free module; the splitting used is
the one supplied by `Module.Finite.exists_comp_eq_id_of_projective`.  Independence of that
choice is the cyclic invariance of the trace.  Neither construction assumes that `G` is finite.

## References

* [Stacks Project, Tag 03U5](https://stacks.math.columbia.edu/tag/03U5)
* [Stacks Project, Tag 03U6](https://stacks.math.columbia.edu/tag/03U6)
-/

@[expose] public section

open scoped MonoidAlgebra

open CategoryTheory.FilteredDerived

universe u v w

namespace Stacks.Trace

/-- Taking the coefficient of the identity is an additive map from the group ring to its
coefficient ring. -/
noncomputable def coeffOneAddMonoidHom (R : Type u) (G : Type v) [Ring R] [Group G] :
    R[G] →+ R where
  toFun x := x.coeff 1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Taking the coefficient of the identity, followed by the additive commutator quotient map. -/
noncomputable def coeffOneToAdditiveCommutatorQuotient
    (R : Type u) (G : Type v) [Ring R] [Group G] :
    R[G] →+ AdditiveCommutatorQuotient R :=
  (additiveCommutatorQuotientMk R).comp (coeffOneAddMonoidHom R G)

/-- The coefficient-of-the-identity map on a group ring factors through additive commutator
quotients. -/
theorem exists_epsilon (R : Type u) (G : Type v) [Ring R] [Group G] :
    ∃ ε : AdditiveCommutatorQuotient R[G] →+ AdditiveCommutatorQuotient R,
      ε.comp (additiveCommutatorQuotientMk R[G]) =
        coeffOneToAdditiveCommutatorQuotient R G := by
  have hkill : additiveCommutatorSubgroup (R[G]) ≤
      (coeffOneToAdditiveCommutatorQuotient R G).ker := by
    unfold additiveCommutatorSubgroup; rw [AddSubgroup.closure_le]
    rintro z ⟨a, b, rfl⟩
    show additiveCommutatorQuotientMk R ((a * b - b * a).coeff 1) = 0
    rw [← AddMonoidHom.mem_ker]
    show (a * b - b * a).coeff 1 ∈
      (QuotientAddGroup.mk' (additiveCommutatorSubgroup R)).ker
    rw [QuotientAddGroup.ker_mk']; classical
    show (a * b).coeff 1 - (b * a).coeff 1 ∈ additiveCommutatorSubgroup R
    rw [MonoidAlgebra.coeff_mul_apply_left a b 1,
      MonoidAlgebra.coeff_mul_apply_right b a 1]
    simp only [Finsupp.sum, mul_one, one_mul, ← Finset.sum_sub_distrib]
    exact (additiveCommutatorSubgroup R).sum_mem fun g hg =>
      AddSubgroup.subset_closure ⟨a.coeff g, b.coeff g⁻¹, rfl⟩
  refine ⟨QuotientAddGroup.lift _ (coeffOneToAdditiveCommutatorQuotient R G) hkill, ?_⟩
  ext x; simp [additiveCommutatorQuotientMk]

/-- A selected coefficient-of-the-identity factorization, bundled with its defining equality. -/
noncomputable def epsilonFactorization (R : Type u) (G : Type v) [Ring R] [Group G] :
    { ε : AdditiveCommutatorQuotient R[G] →+ AdditiveCommutatorQuotient R //
      ε.comp (additiveCommutatorQuotientMk R[G]) =
        coeffOneToAdditiveCommutatorQuotient R G } :=
  ⟨Classical.choose (exists_epsilon R G), Classical.choose_spec (exists_epsilon R G)⟩

/-- The map induced on additive commutator quotients by taking the coefficient of the
identity. -/
noncomputable def epsilon (R : Type u) (G : Type v) [Ring R] [Group G] :
    AdditiveCommutatorQuotient R[G] →+ AdditiveCommutatorQuotient R :=
  epsilonFactorization R G

/-- The chosen coefficient-of-the-identity map factors the map on the group ring. -/
@[stacks 03U5, sga "4½ Rapport 5.5" "ε factorization"]
theorem epsilon_comp_mk (R : Type u) (G : Type v) [Ring R] [Group G] :
    (epsilon R G).comp (additiveCommutatorQuotientMk R[G]) =
      coeffOneToAdditiveCommutatorQuotient R G :=
  Classical.choose_spec (exists_epsilon R G)

/-- On a class represented by `x`, the chosen map takes the coefficient of the identity. -/
@[simp]
theorem epsilon_mk (R : Type u) (G : Type v) [Ring R] [Group G] (x : R[G]) :
    epsilon R G (additiveCommutatorQuotientMk R[G] x) =
      additiveCommutatorQuotientMk R (x.coeff 1) :=
  DFunLike.congr_fun (epsilon_comp_mk R G) x

/-- The trace of an endomorphism of a finite projective module, computed after embedding the
module as a summand of a finite free module. -/
noncomputable def projectiveModuleTrace (R : Type u) [Ring R]
    (P : Type w) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) : AdditiveCommutatorQuotient R := by
  let h := Module.Finite.exists_comp_eq_id_of_projective R P; let n := h.choose
  let p : (Fin n → R) →ₗ[R] P := h.choose_spec.choose
  let i : P →ₗ[R] (Fin n → R) := h.choose_spec.choose_spec.choose
  exact freeModuleTrace R (Fin n) (i.comp (f.comp p))

/-- The group trace of an endomorphism of a finite projective group-ring module. -/
@[stacks 03U6, sga "4½ Rapport 5.5" "tr_Λ^H definition"]
noncomputable abbrev groupTrace (R : Type u) (G : Type v) [Ring R] [Group G]
    (P : Type w) [AddCommGroup P] [Module R[G] P] [Module.Finite R[G] P]
    [Module.Projective R[G] P] (f : Module.End R[G] P) :
    AdditiveCommutatorQuotient R :=
  epsilon R G (projectiveModuleTrace R[G] P f)

end Stacks.Trace
