module

public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.Different.Formula.SquarePresentation
public import StacksFrontier.RingTheory.Koszul.TorIndependence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The augmentation of a polynomial algebra, and the square it presents

Let `k` be a commutative ring and `P = k[x₁, …, x_r]`. Two `P`-algebra structures on two rings
are compared here.

The first is `k` itself, through the augmentation `x_i ↦ 0`. Its kernel is the ideal of the
variables (`MvPolynomial.ker_aeval_zero`), and the variables form a Koszul-regular sequence
(`Koszul.isKoszulRegular_mvPolynomial_X`): they are the relations of a presentation of `k` over
itself with as many relations as variables, hence of a relative global complete intersection, and
Tag 07D2 makes such relations Koszul-regular. Neither statement needs `k` nontrivial or `r`
positive.

The second is a `k`-algebra `R` together with a choice of `f₁, …, f_r ∈ R`, through `x_i ↦ f_i`.
If `T` is a quotient of `R` by exactly the ideal `(f₁, …, f_r)`, then

```
P  --→  R
|       |
k  --→  T
```

commutes (`MvPolynomial.algebraMap_comp_aeval_eq`) and is a pushout of rings, `T = R ⊗_P k`
(`MvPolynomial.isPushout_aeval_augmentation`); and `R` and `k` are Tor independent over `P` as
soon as `f₁, …, f_r` is Koszul-regular in `R`
(`MvPolynomial.torIndependent_aeval_augmentation`). Together these two say that the square
induces a quasi-isomorphism `R ⊗_P^𝐋 k = T`, in the form in which [Stacks, Tag 08QQ] asks for it.

## Main results

* `MvPolynomial.ker_aeval_zero`: the kernel of `k[x₁, …, x_r] → k`, `x_i ↦ 0`, is
  `(x₁, …, x_r)`.
* `Koszul.isKoszulRegular_mvPolynomial_X`: the variables of `k[x₁, …, x_r]` form a
  Koszul-regular sequence, for every commutative ring `k` and every `r`.
* `MvPolynomial.algebraMap_comp_aeval_eq`: the square commutes.
* `MvPolynomial.isPushout_aeval_augmentation`: **the square is a pushout**, `T = R ⊗_P k`.
* `MvPolynomial.torIndependent_aeval_augmentation`: **`R` and `k` are Tor independent over
  `P`**, when `f₁, …, f_r` is Koszul-regular in `R`.

## Implementation notes

The two `P`-algebra structures are supplied by `letI` in the statements rather than by instances:
`R` and `k` may well be the same type — the case `k = R`, which is the one the cotangent complex
of a Koszul-regular quotient is computed through — and then no instance can distinguish `x_i ↦ 0`
from `x_i ↦ f_i`. Keeping `k` and `R` as separate variables and letting the caller instantiate
both to one ring is what makes the two structures nameable at once.

`MvPolynomial.torIndependent_aeval_augmentation` has `R` in the first slot and `k` in the
second, which is the order of [Stacks, Tag 08QQ]; the Koszul resolution computes the other
order, so `RingTheory.TorIndependence.TorIndependent.symm` is applied.

`Koszul.isKoszulRegular_mvPolynomial_X` is not subsumed by `MvPolynomial.isKoszulRegular_X` of
`StacksFrontier/RingTheory/MvPolynomial/VariablesRegular.lean`, which proves the stronger
*regularity* of the sequence but only for `Fin (n + 1)` variables over a nontrivial ring — the
nontriviality being needed for the properness of the ideal they generate, and the positive arity
for the induction-free reading of the predecessor ideals. The route here, through the complete
intersection criterion, is insensitive to both.

## References

* [Stacks Project, Tag 07D2](https://stacks.math.columbia.edu/tag/07D2)
* [Stacks Project, Tag 00SP](https://stacks.math.columbia.edu/tag/00SP)
* [Stacks Project, Tag 0660](https://stacks.math.columbia.edu/tag/0660)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace MvPolynomial

/-- **The kernel of the augmentation of a polynomial algebra is the ideal of the variables.** A
polynomial is congruent to the constant `p(0)` modulo `(x₁, …, x_r)`, so it lies in the kernel of
`p ↦ p(0)` exactly when it lies in that ideal. -/
theorem ker_aeval_zero (k : Type u) [CommRing k] (r : ℕ) :
    RingHom.ker (MvPolynomial.aeval (0 : Fin r → k) :
        MvPolynomial (Fin r) k →ₐ[k] k).toRingHom =
      Ideal.span (Set.range (MvPolynomial.X : Fin r → MvPolynomial (Fin r) k)) := by
  set J : Ideal (MvPolynomial (Fin r) k) :=
    Ideal.span (Set.range (MvPolynomial.X : Fin r → MvPolynomial (Fin r) k)) with hJ
  have key (p : MvPolynomial (Fin r) k) :
      p - MvPolynomial.C (MvPolynomial.aeval (0 : Fin r → k) p) ∈ J := by
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simpa only [map_add, sub_add_sub_comm] using J.add_mem hp hq
    | mul_X p i hp => simpa using J.mul_mem_left p (Ideal.subset_span ⟨i, rfl⟩)
  refine le_antisymm (fun p hp => ?_) ?_
  · simpa only [show MvPolynomial.aeval (0 : Fin r → k) p = 0 from hp, map_zero, sub_zero]
      using key p
  · rw [hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]

end MvPolynomial

namespace Koszul

/-- **The variables of a polynomial ring form a Koszul-regular sequence**, over any commutative
ring and in any number. They are the relations of the presentation `k = k[x₁, …, x_r]/(x₁, …,
x_r)` of `k` over itself, which has as many relations as variables and whose target is
(trivially) quasi-finite, hence is a relative global complete intersection presentation of
Definition 00SP; the relations of such a presentation are Koszul-regular by [Stacks,
Tag 07D2]. -/
@[sga "6 VII 1.2" "more general"]
theorem isKoszulRegular_mvPolynomial_X (k : Type u) [CommRing k] (r : ℕ) :
    IsKoszulRegular (MvPolynomial.X : Fin r → MvPolynomial (Fin r) k) :=
  let P : Algebra.Presentation k k (Fin r) (Fin r) :=
    { val := 0
      σ' := MvPolynomial.C
      aeval_val_σ' := by simp
      algebra := (MvPolynomial.aeval (0 : Fin r → k)).toRingHom.toAlgebra
      algebraMap_eq := rfl
      relation := MvPolynomial.X
      span_range_relation_eq_ker := (MvPolynomial.ker_aeval_zero k r).symm }
  RingHom.isKoszulRegular_relation_of_isRelativeGlobalCompleteIntersection P
    (P.isRelativeGlobalCompleteIntersection_of_card_eq (by simp))

end Koszul

namespace MvPolynomial

variable (k R T : Type u) [CommRing k] [CommRing R] [CommRing T] [Algebra k R] [Algebra R T]
  [Algebra k T] [IsScalarTower k R T]

/-- **The square of the augmentation commutes.** Evaluating `x_i ↦ f_i` and then passing to a
quotient `T` of `R` by an ideal containing every `f_i` is the same as evaluating `x_i ↦ 0` and
then passing to `T`: the two agree on constants by the scalar tower, and both kill every
variable. -/
theorem algebraMap_comp_aeval_eq {r : ℕ} (f : Fin r → R)
    (hI : RingHom.ker (algebraMap R T) = Ideal.span (Set.range f)) :
    (algebraMap R T).comp
        ((MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] R).toRingHom) =
      (algebraMap k T).comp
        ((MvPolynomial.aeval (0 : Fin r → k) :
          MvPolynomial (Fin r) k →ₐ[k] k).toRingHom) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simpa using (IsScalarTower.algebraMap_apply k R T c).symm
  · intro i
    have hzero : algebraMap R T (f i) = 0 := by
      rw [← RingHom.mem_ker, hI]
      exact Ideal.subset_span ⟨i, rfl⟩
    simpa using hzero

/-- **The quotient of `R` by `(f₁, …, f_r)` is the pushout `R ⊗_{k[x]} k`.** Here `k[x₁, …, x_r]`
maps to `R` by `x_i ↦ f_i` and to `k` by `x_i ↦ 0`, and `T` is a quotient of `R` whose kernel is
exactly `(f₁, …, f_r)`.

The comparison `R ⊗_P k → T` is `a ⊗ c ↦ a · c`. Its inverse is produced from the surjection
`R → T`, whose kernel `(f₁, …, f_r)` is killed in `R ⊗_P k` because `f_i ⊗ 1 = 1 ⊗ 0 = 0`; the
two composites are the identity, the one on the tensor product because it suffices to check it on
`1 ⊗ c`. -/
theorem isPushout_aeval_augmentation (h : Function.Surjective (algebraMap R T))
    {r : ℕ} (f : Fin r → R)
    (hI : RingHom.ker (algebraMap R T) = Ideal.span (Set.range f)) :
    letI : Algebra (MvPolynomial (Fin r) k) k :=
      (MvPolynomial.aeval (0 : Fin r → k) :
        MvPolynomial (Fin r) k →ₐ[k] k).toRingHom.toAlgebra
    letI : Algebra (MvPolynomial (Fin r) k) R :=
      (MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] R).toRingHom.toAlgebra
    letI : Algebra (MvPolynomial (Fin r) k) T :=
      ((algebraMap R T).comp
        (MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] R).toRingHom).toAlgebra
    letI : IsScalarTower (MvPolynomial (Fin r) k) R T := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (MvPolynomial (Fin r) k) k T :=
      IsScalarTower.of_algebraMap_eq' (algebraMap_comp_aeval_eq k R T f hI)
    Algebra.IsPushout (MvPolynomial (Fin r) k) R k T := by
  classical
  let P := MvPolynomial (Fin r) k
  let _ : Algebra P k :=
    (MvPolynomial.aeval (0 : Fin r → k) : P →ₐ[k] k).toRingHom.toAlgebra
  let _ : Algebra P R := (MvPolynomial.aeval f : P →ₐ[k] R).toRingHom.toAlgebra
  let _ : Algebra P T :=
    ((algebraMap R T).comp (MvPolynomial.aeval f : P →ₐ[k] R).toRingHom).toAlgebra
  let _ : IsScalarTower P R T := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower P k T :=
    IsScalarTower.of_algebraMap_eq' (algebraMap_comp_aeval_eq k R T f hI)
  let tensor := R ⊗[P] k
  let _ : Algebra k tensor := Algebra.TensorProduct.rightAlgebra
  have tmul_one (p : P) :
      MvPolynomial.aeval f p ⊗ₜ[P] (1 : k) = (1 : R) ⊗ₜ[P] MvPolynomial.aeval (0 : Fin r → k) p :=
    Algebra.TensorProduct.tmul_one_eq_one_tmul (A := R) (B := k) p
  let inclusion : R →ₐ[R] tensor := Algebra.TensorProduct.includeLeft
  have hker : RingHom.ker (Algebra.ofId R T).toRingHom ≤ RingHom.ker inclusion.toRingHom := by
    rw [show (Algebra.ofId R T).toRingHom = algebraMap R T from rfl, hI]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply RingHom.mem_ker.mpr
    change f i ⊗ₜ[P] (1 : k) = 0
    simpa using tmul_one (MvPolynomial.X i)
  let inverse : T →ₐ[R] tensor := (Algebra.ofId R T).liftOfSurjective h inclusion hker
  let coefficientMap : k →ₐ[P] T := IsScalarTower.toAlgHom P k T
  let comparison : tensor →ₐ[R] T :=
    Algebra.TensorProduct.lift (Algebra.ofId R T) coefficientMap (fun _ _ => Commute.all _ _)
  have comparison_one_tmul (c : k) : comparison ((1 : R) ⊗ₜ[P] c) = algebraMap k T c := by
    refine (Algebra.TensorProduct.lift_tmul (Algebra.ofId R T) coefficientMap
      (fun _ _ => Commute.all _ _) 1 c).trans ?_
    simp [coefficientMap]
  have hleft : comparison.comp inverse = AlgHom.id R T := by
    refine AlgHom.ext fun value => ?_
    obtain ⟨preimage, rfl⟩ := h value
    change comparison (inverse ((Algebra.ofId R T) preimage)) = _
    simp [inverse, comparison, inclusion]
  have hright : inverse.comp comparison = AlgHom.id R tensor := by
    refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    ext c
    change inverse (comparison ((1 : R) ⊗ₜ[P] c)) = (1 : R) ⊗ₜ[P] c
    rw [comparison_one_tmul, IsScalarTower.algebraMap_apply k R T, inverse.commutes]
    change (algebraMap k R c) ⊗ₜ[P] (1 : k) = (1 : R) ⊗ₜ[P] c
    simpa using tmul_one (MvPolynomial.C c)
  exact Algebra.IsPushout.of_equiv (AlgEquiv.ofAlgHom comparison inverse hleft hright) (by
    ext c
    exact comparison_one_tmul c)

/-- **`R` and `k` are Tor independent over `k[x₁, …, x_r]`** when `f₁, …, f_r` is a Koszul-regular
sequence in `R`, the polynomial ring mapping to `R` by `x_i ↦ f_i` and to `k` by `x_i ↦ 0`.

Over `P = k[x₁, …, x_r]` the ring `k` is the quotient by the variables
(`MvPolynomial.ker_aeval_zero`), which are a Koszul-regular sequence
(`Koszul.isKoszulRegular_mvPolynomial_X`) whose images in `R` are `f₁, …, f_r`; so
`Koszul.torIndependent_of_isKoszulRegular_map` applies. -/
@[sga "6 VII 1.2" "special case"]
theorem torIndependent_aeval_augmentation {r : ℕ} (f : Fin r → R)
    (hf : Koszul.IsKoszulRegular f) :
    letI : Algebra (MvPolynomial (Fin r) k) k :=
      (MvPolynomial.aeval (0 : Fin r → k) :
        MvPolynomial (Fin r) k →ₐ[k] k).toRingHom.toAlgebra
    letI : Algebra (MvPolynomial (Fin r) k) R :=
      (MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] R).toRingHom.toAlgebra
    RingTheory.TorIndependence.TorIndependent (MvPolynomial (Fin r) k) R k := by
  let P := MvPolynomial (Fin r) k
  let _ : Algebra P k :=
    (MvPolynomial.aeval (0 : Fin r → k) : P →ₐ[k] k).toRingHom.toAlgebra
  let _ : Algebra P R := (MvPolynomial.aeval f : P →ₐ[k] R).toRingHom.toAlgebra
  refine RingTheory.TorIndependence.TorIndependent.symm
    (Koszul.torIndependent_of_isKoszulRegular_map (R := P) (C := k) (S := R) ?_
      MvPolynomial.X (Koszul.isKoszulRegular_mvPolynomial_X k r)
      (MvPolynomial.ker_aeval_zero k r) ?_)
  · intro c
    exact ⟨MvPolynomial.C c, MvPolynomial.aeval_C _ _⟩
  · change Koszul.IsKoszulRegular fun i => MvPolynomial.aeval f (MvPolynomial.X i : P)
    simpa using hf

end MvPolynomial

end
