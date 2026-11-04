module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Jacobson.Ring
public import StacksCore.Tactic.StacksAttribute

/-!
# The Hilbert Nullstellensatz

Let `k` be a field and let `k[x_1, ..., x_n]` be a polynomial ring in finitely many variables
over `k`. The Hilbert Nullstellensatz consists of two statements:

1. for every maximal ideal `𝔪 ⊆ k[x_1, ..., x_n]` the residue field `κ(𝔪) = k[x_1, ..., x_n] ⧸ 𝔪`
   is a finite extension of `k`;
2. every radical ideal `I ⊆ k[x_1, ..., x_n]` is the intersection of the maximal ideals
   containing it.

Both statements hold more generally in any `k`-algebra of finite type, and that is how they are
proved here. Statement (1) is Zariski's lemma `finite_of_finite_type_of_isJacobsonRing`, applied
to the field `A ⧸ 𝔪`, which is of finite type over `k` because `A` is. Statement (2) is the
assertion that a finite type algebra over a field is a Jacobson ring,
`isJacobsonRing_of_finiteType`, unfolded through the definition of `Ideal.jacobson` as the
infimum of the maximal ideals containing the given ideal.

Note that `A ⧸ 𝔪` carries a field structure, `Ideal.Quotient.field`, which is not an instance; it
plays no role in the proposition `Module.Finite k (A ⧸ 𝔪)` beyond being what makes that
proposition the finiteness of a field extension, and it is introduced locally in the proofs.

## Main results

* `Stacks.HilbertNullstellensatz.module_finite_quotient_mvPolynomial`: part (1).
* `Stacks.HilbertNullstellensatz.eq_sInf_isMaximal_mvPolynomial`: part (2).
* `Stacks.HilbertNullstellensatz.coe_eq_iInter_isMaximal_mvPolynomial`: part (2), written as an
  intersection of the underlying sets.
* `Stacks.HilbertNullstellensatz.module_finite_quotient_of_finiteType` and
  `Stacks.HilbertNullstellensatz.eq_sInf_isMaximal_of_finiteType`: the two parts for an arbitrary
  `k`-algebra of finite type.
-/

@[expose] public section

open Ideal

namespace Stacks.HilbertNullstellensatz

/-- **Hilbert Nullstellensatz**, part (1), for a finite type algebra: if `A` is a `k`-algebra of
finite type over a field `k` and `𝔪 ⊆ A` is a maximal ideal, then the residue field
`κ(𝔪) = A ⧸ 𝔪` is a finite extension of `k`.

The quotient `A ⧸ 𝔪` is a field by `Ideal.Quotient.field`, and it is of finite type over `k`
because `A` is, so Zariski's lemma over the Jacobson ring `k` applies. -/
@[stacks 00FV "part (1), for an arbitrary finite type algebra over the field",
  ega "IV 10.4.5" "a⇒b′ over a field"]
public theorem module_finite_quotient_of_finiteType (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (𝔪 : Ideal A) [𝔪.IsMaximal] :
    Module.Finite k (A ⧸ 𝔪) := by
  let _ := Ideal.Quotient.field 𝔪
  exact finite_of_finite_type_of_isJacobsonRing k (A ⧸ 𝔪)

/-- **Hilbert Nullstellensatz**, part (2), for a finite type algebra: a radical ideal `I` of a
`k`-algebra `A` of finite type over a field `k` is the infimum of the maximal ideals of `A`
containing `I`.

A finite type algebra over a field is a Jacobson ring, and in a Jacobson ring a radical ideal
equals its Jacobson radical, which is by definition that infimum. -/
@[stacks 00FV "part (2), for an arbitrary finite type algebra over the field",
  ega "IV 10.4.6" "partial"]
public theorem eq_sInf_isMaximal_of_finiteType (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (I : Ideal A) (hI : I.IsRadical) :
    I = sInf {J : Ideal A | I ≤ J ∧ J.IsMaximal} :=
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  (IsJacobsonRing.out inferInstance hI).symm

/-- **Hilbert Nullstellensatz**, part (2), for a finite type algebra, written elementwise: an
element of a `k`-algebra `A` of finite type over a field `k` lies in a radical ideal `I` if and
only if it lies in every maximal ideal of `A` containing `I`. -/
public theorem mem_iff_forall_mem_isMaximal_of_finiteType (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (I : Ideal A) (hI : I.IsRadical) (x : A) :
    x ∈ I ↔ ∀ J : Ideal A, I ≤ J → J.IsMaximal → x ∈ J := by
  refine ⟨fun hx J hJ _ => hJ hx, fun h => ?_⟩
  rw [eq_sInf_isMaximal_of_finiteType k A I hI]
  exact Submodule.mem_sInf.mpr fun J hJ => h J hJ.1 hJ.2

/-- **Hilbert Nullstellensatz**, part (1): for a field `k`, finitely many variables `ι` and a
maximal ideal `𝔪` of the polynomial ring `k[x_i : i ∈ ι]`, the residue field
`κ(𝔪) = k[x_i : i ∈ ι] ⧸ 𝔪` is a finite extension of `k`. -/
@[stacks 00FV "part (1)"]
public theorem module_finite_quotient_mvPolynomial (k : Type*) [Field k] (ι : Type*) [Finite ι]
    (𝔪 : Ideal (MvPolynomial ι k)) [𝔪.IsMaximal] :
    Module.Finite k (MvPolynomial ι k ⧸ 𝔪) :=
  module_finite_quotient_of_finiteType k (MvPolynomial ι k) 𝔪

/-- **Hilbert Nullstellensatz**, part (2): for a field `k` and finitely many variables `ι`, a
radical ideal `I` of the polynomial ring `k[x_i : i ∈ ι]` is the infimum of the maximal ideals
containing `I`. -/
@[stacks 00FV "part (2)"]
public theorem eq_sInf_isMaximal_mvPolynomial (k : Type*) [Field k] (ι : Type*) [Finite ι]
    (I : Ideal (MvPolynomial ι k)) (hI : I.IsRadical) :
    I = sInf {J : Ideal (MvPolynomial ι k) | I ≤ J ∧ J.IsMaximal} :=
  eq_sInf_isMaximal_of_finiteType k (MvPolynomial ι k) I hI

/-- **Hilbert Nullstellensatz**, part (2), as an equality of sets: a radical ideal `I` of the
polynomial ring `k[x_i : i ∈ ι]` over a field `k` in finitely many variables is, as a subset of
the polynomial ring, the intersection of the maximal ideals containing `I`. -/
@[stacks 00FV "part (2), as an intersection of the underlying sets"]
public theorem coe_eq_iInter_isMaximal_mvPolynomial (k : Type*) [Field k] (ι : Type*) [Finite ι]
    (I : Ideal (MvPolynomial ι k)) (hI : I.IsRadical) :
    (I : Set (MvPolynomial ι k)) =
      ⋂ J ∈ {J : Ideal (MvPolynomial ι k) | I ≤ J ∧ J.IsMaximal},
        (J : Set (MvPolynomial ι k)) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq, and_imp]
  exact mem_iff_forall_mem_isMaximal_of_finiteType k (MvPolynomial ι k) I hI x

end Stacks.HilbertNullstellensatz

-- Zariski's lemma over a Jacobson ring is the engine of part (1).
add_to_stacks 00FV "part (1) is this applied to the field `A ⧸ 𝔪`, which is of finite type over
`k`; see `Stacks.HilbertNullstellensatz.module_finite_quotient_of_finiteType`"
  finite_of_finite_type_of_isJacobsonRing
add_to_ega "IV 10.4.5" "a⇒b′" finite_of_finite_type_of_isJacobsonRing

-- Jacobson-ness of a polynomial ring over a field is the engine of part (2).
add_to_stacks 00FV "part (2): a radical ideal of a Jacobson ring equals its Jacobson radical,
which is the infimum of the maximal ideals containing it; see
`Stacks.HilbertNullstellensatz.eq_sInf_isMaximal_mvPolynomial`"
  MvPolynomial.isJacobsonRing
