module

public import StacksFrontier.Deformation.Examples.Geometric.CompletionFirstOrder
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceExtension

/-!
# Adic completion of rank-one tensor coefficients

Let `k` be a field, `P` a `k`-algebra, `J ⊆ P` an ideal and `V` a one-dimensional `k`-vector
space, presented by a `k`-linear equivalence `ι : V ≃ₗ[k] k`. The two comparison maps of
**Stacks 0DZ4** are stated with coefficients `AdicCompletion J N` for a finite `P`-module `N`,
whereas the coefficients a first-order deformation over the base `k ⊕ V` produces are
`P ⊗[k] V` downstairs and `P^ ⊗[k] V` upstairs. At `N = P ⊗[k] V` the two differ by the
canonical `P^`-linear equivalence

`AdicCompletion J (P ⊗[k] V) ≃ₗ[P^] P^ ⊗[k] V`,

which is `Deformation.Examples.adicCompletionRankOneEquiv`: both sides are canonically `P^`
itself, since `V` has rank one. This file builds that equivalence and transports the two
bijectivity statements of Stacks 0DZ4 along it.

## Main definitions

* `Deformation.Examples.tensorRankOneTrivialization`: `A ⊗[k] V ≃ₗ[A] A` for a `k`-algebra `A`
  and a rank-one `V`.
* `Deformation.Examples.adicCompletionRankOneEquiv`: the `P^`-linear equivalence above.
* `Deformation.Examples.completionCoefficientMap`: the resulting `P`-linear coefficient map
  `P ⊗[k] V → P^ ⊗[k] V`, which on `p ⊗ v` is `p^ ⊗ v`.

## Main results

* `Deformation.Examples.bijective_naiveCotangentExtOneMap_completionCoefficientMap`: the map
  `Ext¹_P(NL_{P/k}, P ⊗[k] V) → Ext¹_P(NL_{P/k}, P^ ⊗[k] V)` is bijective.
* `Deformation.Examples.bijective_naiveCotangentExtOneTowerMap_rankOne`: the map
  `Ext¹_{P^}(NL_{P^/k}, P^ ⊗[k] V) → Ext¹_P(NL_{P/k}, P^ ⊗[k] V)` is bijective.

## Implementation notes

The coefficient map is the canonical map into the completion followed by the equivalence, so the
first transport is `Stacks.Deformation.naiveCotangentExtOneMap_comp` together with
`Stacks.Deformation.bijective_naiveCotangentExtOneMap_of_inverse`. The second uses
`Stacks.Deformation.naiveCotangentExtOneTowerMap_map`, the naturality of the restriction map of
**Stacks 0GPV** in the coefficients: the restriction map at the coefficients `P^ ⊗[k] V`,
precomposed with the bijection induced by the equivalence, is the restriction map at the
coefficients `AdicCompletion J (P ⊗[k] V)` postcomposed with another such bijection.

## References

* [Stacks Project, Tag 0DZ4](https://stacks.math.columbia.edu/tag/0DZ4)
* [Stacks Project, Tag 0GPV](https://stacks.math.columbia.edu/tag/0GPV)
-/

@[expose] public section

open Stacks.Deformation
open scoped TensorProduct

universe w

namespace Deformation.Examples

section RankOne

variable (k A : Type w) [Field k] [CommRing A] [Algebra k A]
  {V : Type w} [AddCommGroup V] [Module k V]

/-- **A rank-one tensor factor is trivial.** For a `k`-algebra `A` and a `k`-vector space `V`
presented as `k` by `ι`, the `A`-module `A ⊗[k] V` is `A`, by `a ⊗ v ↦ ι v • a`. -/
public noncomputable def tensorRankOneTrivialization (ι : V ≃ₗ[k] k) : A ⊗[k] V ≃ₗ[A] A :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) ι).trans
    (TensorProduct.AlgebraTensorModule.rid k A A)

/-- The trivialisation of a rank-one tensor factor, on a tensor. -/
public theorem tensorRankOneTrivialization_tmul (ι : V ≃ₗ[k] k) (a : A) (v : V) :
    tensorRankOneTrivialization k A ι (a ⊗ₜ[k] v) = ι v • a := rfl

/-- The inverse trivialisation of a rank-one tensor factor. -/
public theorem tensorRankOneTrivialization_symm_apply (ι : V ≃ₗ[k] k) (a : A) :
    (tensorRankOneTrivialization k A ι).symm a = a ⊗ₜ[k] ι.symm 1 := rfl

/-- A rank-one tensor factor leaves finiteness untouched. -/
public theorem module_finite_tensorRankOne (ι : V ≃ₗ[k] k) :
    Module.Finite A (A ⊗[k] V) :=
  Module.Finite.equiv (tensorRankOneTrivialization k A ι).symm

end RankOne

section Completion

variable (k P : Type w) [Field k] [CommRing P] [Algebra k P] (J : Ideal P)
  {V : Type w} [AddCommGroup V] [Module k V]

/-- **Completion commutes with a rank-one tensor factor.** Both
`AdicCompletion J (P ⊗[k] V)` and `P^ ⊗[k] V` are canonically `P^` itself, by
`Deformation.Examples.tensorRankOneTrivialization` below and above the completion, so they are
canonically `P^`-linearly isomorphic. -/
public noncomputable def adicCompletionRankOneEquiv (ι : V ≃ₗ[k] k) :
    AdicCompletion J (P ⊗[k] V) ≃ₗ[AdicCompletion J P] AdicCompletion J P ⊗[k] V :=
  (AdicCompletion.congr J (tensorRankOneTrivialization k P ι)).trans
    (tensorRankOneTrivialization k (AdicCompletion J P) ι).symm

/-- The comparison carries the canonical map into the completion to the completion map in the
left tensor factor. -/
public theorem adicCompletionRankOneEquiv_of_tmul (ι : V ≃ₗ[k] k) (p : P) (v : V) :
    adicCompletionRankOneEquiv k P J ι (AdicCompletion.of J (P ⊗[k] V) (p ⊗ₜ[k] v))
      = algebraMap P (AdicCompletion J P) p ⊗ₜ[k] v := by
  change AdicCompletion.of J P (ι v • p) ⊗ₜ[k] ι.symm 1 = _
  rw [LinearMap.map_smul_of_tower, TensorProduct.smul_tmul, ← map_smul ι.symm, smul_eq_mul,
    mul_one, ι.symm_apply_apply]
  rfl

/-- **The coefficient map of the completion comparison at rank-one coefficients**: the
`P`-linear map `P ⊗[k] V → P^ ⊗[k] V` completing the left tensor factor. -/
public noncomputable def completionCoefficientMap (ι : V ≃ₗ[k] k) :
    P ⊗[k] V →ₗ[P] AdicCompletion J P ⊗[k] V :=
  ((adicCompletionRankOneEquiv k P J ι :
      AdicCompletion J (P ⊗[k] V) →ₗ[AdicCompletion J P]
        AdicCompletion J P ⊗[k] V).restrictScalars P).comp
    (AdicCompletion.of J (P ⊗[k] V))

/-- The coefficient map completes the left tensor factor. -/
public theorem completionCoefficientMap_tmul (ι : V ≃ₗ[k] k) (p : P) (v : V) :
    completionCoefficientMap k P J ι (p ⊗ₜ[k] v)
      = algebraMap P (AdicCompletion J P) p ⊗ₜ[k] v :=
  adicCompletionRankOneEquiv_of_tmul k P J ι p v

end Completion

section Bijectivity

variable (k P : Type w) [Field k] [CommRing P] [Algebra k P] [Algebra.FiniteType k P]
  (J : Ideal P) {V : Type w} [AddCommGroup V] [Module k V]

/-- A map that agrees pointwise with a bijection is itself a bijection. -/
public theorem bijective_of_forall_eq {α β : Type*} {f g : α → β}
    (hf : Function.Bijective f) (h : ∀ a, g a = f a) : Function.Bijective g := by
  have hfg : g = f := funext h
  rw [hfg]
  exact hf

/-- **Stacks 0DZ4 at rank-one coefficients, the coefficient direction.** For a finite type
algebra `P` over a field `k` which is smooth over `k` outside the zero set of `J`, and a
one-dimensional `k`-vector space `V`, the map on first Ext groups induced by completing the
left tensor factor of `P ⊗[k] V` is bijective. -/
public theorem bijective_naiveCotangentExtOneMap_completionCoefficientMap
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (ι : V ≃ₗ[k] k) :
    Function.Bijective (naiveCotangentExtOneMap k P (completionCoefficientMap k P J ι)) := by
  have : Module.Finite P (P ⊗[k] V) := module_finite_tensorRankOne k P ι
  have hof := bijective_naiveCotangentExtOneMap_adicCompletion k P J hsm (P ⊗[k] V)
  have heq : Function.Bijective (naiveCotangentExtOneMap k P
      ((adicCompletionRankOneEquiv k P J ι :
        AdicCompletion J (P ⊗[k] V) →ₗ[AdicCompletion J P]
          AdicCompletion J P ⊗[k] V).restrictScalars P)) :=
    bijective_naiveCotangentExtOneMap_of_inverse k P _
      (((adicCompletionRankOneEquiv k P J ι).symm :
        AdicCompletion J P ⊗[k] V →ₗ[AdicCompletion J P]
          AdicCompletion J (P ⊗[k] V)).restrictScalars P)
      (fun m => (adicCompletionRankOneEquiv k P J ι).symm_apply_apply m)
      (fun n => (adicCompletionRankOneEquiv k P J ι).apply_symm_apply n)
  refine bijective_of_forall_eq (heq.comp hof) (fun x => ?_)
  exact naiveCotangentExtOneMap_comp k P (AdicCompletion.of J (P ⊗[k] V)) _ x

/-- **Stacks 0DZ4 at rank-one coefficients, the restriction direction.** Under the same
hypotheses, the restriction map along `P → P^` on first Ext groups with coefficients in
`P^ ⊗[k] V` is bijective. -/
public theorem bijective_naiveCotangentExtOneTowerMap_rankOne
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (ι : V ≃ₗ[k] k) :
    Function.Bijective (naiveCotangentExtOneTowerMap k P (AdicCompletion J P)
      (N := AdicCompletion J P ⊗[k] V)) := by
  have : Module.Finite P (P ⊗[k] V) := module_finite_tensorRankOne k P ι
  have htower := bijective_naiveCotangentExtOneTowerMap_adicCompletion k P J hsm (P ⊗[k] V)
  have hup : Function.Bijective (naiveCotangentExtOneMap k (AdicCompletion J P)
      (adicCompletionRankOneEquiv k P J ι :
        AdicCompletion J (P ⊗[k] V) →ₗ[AdicCompletion J P]
          AdicCompletion J P ⊗[k] V)) :=
    bijective_naiveCotangentExtOneMap_of_inverse k (AdicCompletion J P) _
      ((adicCompletionRankOneEquiv k P J ι).symm :
        AdicCompletion J P ⊗[k] V →ₗ[AdicCompletion J P]
          AdicCompletion J (P ⊗[k] V))
      (fun m => (adicCompletionRankOneEquiv k P J ι).symm_apply_apply m)
      (fun n => (adicCompletionRankOneEquiv k P J ι).apply_symm_apply n)
  have hdown : Function.Bijective (naiveCotangentExtOneMap k P
      ((adicCompletionRankOneEquiv k P J ι :
        AdicCompletion J (P ⊗[k] V) →ₗ[AdicCompletion J P]
          AdicCompletion J P ⊗[k] V).restrictScalars P)) :=
    bijective_naiveCotangentExtOneMap_of_inverse k P _
      (((adicCompletionRankOneEquiv k P J ι).symm :
        AdicCompletion J P ⊗[k] V →ₗ[AdicCompletion J P]
          AdicCompletion J (P ⊗[k] V)).restrictScalars P)
      (fun m => (adicCompletionRankOneEquiv k P J ι).symm_apply_apply m)
      (fun n => (adicCompletionRankOneEquiv k P J ι).apply_symm_apply n)
  refine (Function.Bijective.of_comp_iff _ hup).mp ?_
  refine bijective_of_forall_eq (hdown.comp htower) (fun ξ => ?_)
  exact naiveCotangentExtOneTowerMap_map k P (AdicCompletion J P)
    (adicCompletionRankOneEquiv k P J ι :
      AdicCompletion J (P ⊗[k] V) →ₗ[AdicCompletion J P]
        AdicCompletion J P ⊗[k] V) ξ

end Bijectivity

end Deformation.Examples

end
