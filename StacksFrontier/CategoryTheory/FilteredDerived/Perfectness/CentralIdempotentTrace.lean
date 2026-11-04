module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FunctorTrace
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.ProjectiveTrace

/-!
# Traces on modules on which a central element acts trivially

Let `e` be a central element of a ring `S`. Multiplication by `e` descends to an additive
endomorphism `μ_e` of `S^♮ = S/[S, S]`. If `e` acts as the identity on a finite projective
`S`-module `P`, then `μ_e` fixes the trace of every endomorphism of `P`; consequently `μ_e` fixes
the values of the map `Φ♮` induced by an additive functor `Φ` all of whose values are modules on
which `e` acts trivially. If moreover `N e = 0`, the image of `μ_e` is killed by `N`.

This is how Step 3 of the proof of [Stacks, Tag 03UG] reduces to rings killed by a power of a
prime: for the primary idempotent `e_ℓ` of a finite ring `Λ`, the traces of a sheaf on which `e_ℓ`
acts trivially live in `e_ℓ Λ^♮`, which is killed by a power of `ℓ`.

## Main definitions

* `CategoryTheory.FilteredDerived.centralMulQuotient`: `μ_e : S^♮ → S^♮`.

## Main results

* `CategoryTheory.FilteredDerived.centralMulQuotient_projectiveModuleTrace`.
* `CategoryTheory.FilteredDerived.centralMulQuotient_functorTraceMap`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 3.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u u' v w

namespace CategoryTheory.FilteredDerived

section Central

variable {S : Type u'} [Ring S] (e : S) (hc : ∀ a : S, a * e = e * a)

include hc in
/-- **Multiplication by a central element on the additive commutator quotient.** -/
def centralMulQuotient : AdditiveCommutatorQuotient S →+ AdditiveCommutatorQuotient S :=
  QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft e) (by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, b, rfl⟩
    refine AddSubgroup.subset_closure ⟨e * a, b, ?_⟩
    change e * (a * b - b * a) = e * a * b - b * (e * a)
    rw [mul_sub, ← mul_assoc, ← mul_assoc, ← hc b, mul_assoc b e a])

/-- `μ_e` sends the class of `x` to the class of `e * x`. -/
lemma centralMulQuotient_mk (x : S) :
    centralMulQuotient e hc (additiveCommutatorQuotientMk S x) =
      additiveCommutatorQuotientMk S (e * x) := rfl

/-- If `N e = 0`, every element of the image of `μ_e` is killed by `N`. -/
lemma nsmul_centralMulQuotient_eq_zero {N : ℕ} (hN : (N : S) * e = 0)
    (y : AdditiveCommutatorQuotient S) : N • centralMulQuotient e hc y = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  show N • additiveCommutatorQuotientMk S (e * x) = 0
  rw [← map_nsmul, nsmul_eq_mul, ← mul_assoc, hN, zero_mul, map_zero]

/-- **`μ_e` fixes the trace of an endomorphism of a finite projective module on which `e` acts as
the identity.** -/
lemma centralMulQuotient_projectiveModuleTrace {P : Type v} [AddCommGroup P] [Module S P]
    [Module.Finite S P] [Module.Projective S P] (hP : ∀ x : P, e • x = x)
    (f : Module.End S P) :
    centralMulQuotient e hc (Stacks.Trace.projectiveModuleTrace S P f) =
      Stacks.Trace.projectiveModuleTrace S P f := by
  classical
  obtain ⟨n, p, i, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective S P
  rw [projectiveModuleTrace_eq_of_split S P f p i hpi.2.2, freeModuleTrace_apply,
    centralMulQuotient_mk, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  show e * i (f (p _)) j = i (f (p _)) j
  conv_rhs => rw [← hP (f (p _)), map_smul]
  rfl

end Central

section Functor

variable {R : Type u} [Ring R] {S : Type u'} [Ring S]
  (Φ : ModuleCat.{max u v} R ⥤ ModuleCat.{w} S) [Φ.Additive] (θ : Φ ⟶ Φ)
  (hΦ : PreservesFiniteProjective.{u, v, u', w} Φ) (e : S) (hc : ∀ a : S, a * e = e * a)

/-- **`μ_e` fixes the values of `Φ♮`** when `e` acts as the identity on every value of `Φ`. -/
lemma centralMulQuotient_functorTraceMap (hfix : ∀ (X : ModuleCat.{max u v} R) (x : Φ.obj X),
      e • x = x) (y : AdditiveCommutatorQuotient R) :
    centralMulQuotient e hc (functorTraceMap Φ θ hΦ y) = functorTraceMap Φ θ hΦ y := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective y
  let := (hΦ (regularModule.{u, v} R) inferInstance inferInstance).1
  let := (hΦ (regularModule.{u, v} R) inferInstance inferInstance).2
  exact centralMulQuotient_projectiveModuleTrace e hc (hfix _) _

end Functor

end CategoryTheory.FilteredDerived

end
