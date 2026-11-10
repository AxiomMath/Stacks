module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Pure
public import StacksFrontier.RingTheory.Flat.FinitePresentationOfFlatFinite

/-!
# A finite flat module need not be finitely presented

A module which is finite and flat over a commutative ring need not be finitely presented: finite
presentation is genuinely stronger, and it is only for a finitely *presented* flat module that
projectivity follows (`Module.Flat.projective_of_finitePresentation`). This file produces the
counterexample and draws the consequence for the polynomial-ring hypothesis of
`Module.FinitePresentation.of_flat_of_finitePresentation_mvPolynomial`.

The witness is the simplest one available. In a ring all of whose elements are idempotent every
ideal `I` satisfies `I ⊓ J = I * J` for every ideal `J`, hence is pure, i.e. `R ⧸ I` is flat
(`Ideal.Pure.of_forall_mul_self_eq`). Taking `R = ℕ → ZMod 2`, whose elements are all idempotent
because `x * x = x` holds in `ZMod 2`, and `I` the ideal of finitely supported sequences, which is
not finitely generated because the elements of a finitely generated ideal have their supports
inside one fixed finite set, gives a cyclic — so certainly finite — flat module `R ⧸ I` which is
not finitely presented.

## Main definitions

* `Ideal.finiteSupport`: the ideal of finitely supported functions in a product ring `α → R`.

## Main results

* `Ideal.Pure.of_forall_mul_self_eq`: in a ring of idempotents every ideal is pure, i.e. the
  quotient by it is flat.
* `Ideal.not_fg_finiteSupport`: the ideal of finitely supported functions is not finitely
  generated when the index type is infinite and the coefficient ring is nontrivial.
* `Module.not_finitePresentation_quotient_of_not_fg`: the quotient of a ring by an ideal which is
  not finitely generated is not a finitely presented module.
* `Module.not_forall_finitePresentation_of_finite_of_flat`: a finite flat module over a
  commutative ring need not be finitely presented.
* `Module.not_forall_finitePresentation_mvPolynomial_of_finite_of_flat`: the polynomial-ring
  hypothesis of `Module.FinitePresentation.of_flat_of_finitePresentation_mvPolynomial` is not
  satisfiable over `ℕ → ZMod 2`, so that reduction theorem, and its algebra counterpart, are
  vacuous as they stand.

## Implementation notes

The two reduction theorems in
`StacksFrontier.RingTheory.Flat.FinitePresentationOfFlatFinite` take as a hypothesis, quantified
over
the number of variables, that every module over `R[x_1, …, x_n]` which is finite over it and flat
over `R` is finitely presented over it. Specialising that hypothesis to no variables at all gives
exactly the statement refuted here, so the hypothesis holds for no ring having a non-finitely
generated pure ideal, and in particular cannot be discharged in the generality in which it is
stated. The true statement in that direction is Stacks 05IL, which assumes in addition that `R`
has finitely many weakly associated primes; with that hypothesis the flat locus of a finite module
over a finitely presented algebra is open and the module is finitely presented over any standard
open contained in it. `weaklyAssociatedPrimes_finite_of_isDomain` in the same file is the input
that hypothesis is meant to be supplied by.

## References

* [Stacks Project, Tag 04PR](https://stacks.math.columbia.edu/tag/04PR)
* [Stacks Project, Tag 04PS](https://stacks.math.columbia.edu/tag/04PS)
* [Stacks Project, Tag 05IL](https://stacks.math.columbia.edu/tag/05IL)
-/

@[expose] public section

universe u v

/-! ### Quotients of a ring of idempotents are flat -/

/-- **In a ring all of whose elements are idempotent every ideal is pure**, that is, the quotient
by it is a flat module. Indeed `I ⊓ J = I * J` for all ideals `I` and `J`, because an element `x`
of `I ⊓ J` equals `x * x ∈ I * J`. -/
theorem Ideal.Pure.of_forall_mul_self_eq {R : Type u} [CommRing R] (h : ∀ x : R, x * x = x)
    (I : Ideal R) : I.Pure :=
  Ideal.Pure.of_inf_eq_mul I fun J _ =>
    le_antisymm
      (fun x hx => by
        rw [← h x]
        exact Ideal.mul_mem_mul (Submodule.mem_inf.mp hx).1 (Submodule.mem_inf.mp hx).2)
      Ideal.mul_le_inf

/-! ### The ideal of finitely supported functions -/

/-- The ideal of finitely supported functions in the product ring `α → R`. -/
def Ideal.finiteSupport (α : Type u) (R : Type v) [CommRing R] : Ideal (α → R) where
  carrier := {a | {i | a i ≠ 0}.Finite}
  zero_mem' := by simp
  add_mem' {a b} ha hb := (ha.union hb).subset fun i hi => by
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hi (by simp [hc.1, hc.2])
  smul_mem' c a ha := ha.subset fun i hi hc => hi (by simp [hc])

/-- A function `a : α → R` lies in `Ideal.finiteSupport α R` if and only if the set of indices
`i` with `a i ≠ 0` is finite. -/
@[simp]
theorem Ideal.mem_finiteSupport {α : Type u} {R : Type v} [CommRing R] {a : α → R} :
    a ∈ Ideal.finiteSupport α R ↔ {i | a i ≠ 0}.Finite := Iff.rfl

/-- **The ideal of finitely supported functions is not finitely generated** over an infinite index
type. Every element of an ideal generated by a finite set `s` is supported inside the union of the
supports of the members of `s`, a fixed finite set, whereas the indicator function of an index
outside that set is finitely supported. -/
theorem Ideal.not_fg_finiteSupport (α : Type u) (R : Type v) [CommRing R] [Infinite α]
    [Nontrivial R] : ¬ (Ideal.finiteSupport α R).FG := by
  classical
  rintro ⟨s, hs⟩
  set T : Set α := ⋃ x ∈ (s : Set (α → R)), {i | x i ≠ 0} with hT
  have hsmem : ∀ x ∈ s, x ∈ Ideal.finiteSupport α R := fun x hx => hs ▸ Ideal.subset_span hx
  have hTfin : T.Finite := Set.Finite.biUnion s.finite_toSet hsmem
  have hsupp : ∀ a ∈ Ideal.finiteSupport α R, {i | a i ≠ 0} ⊆ T := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem x hx => exact fun i hi => Set.mem_biUnion hx hi
    | zero => simp
    | add x y _ _ hx hy =>
      exact fun i hi => (Function.support_add x y hi).elim (@hx i) (@hy i)
    | smul c x _ hx => exact fun i hi => hx fun hc => hi (by simp [hc])
  obtain ⟨i, hi⟩ := hTfin.infinite_compl.nonempty
  refine hi (hsupp (Pi.single i 1) ?_ (by simp))
  exact (Set.finite_singleton i).subset Pi.support_single_subset

/-! ### A finite flat module need not be finitely presented -/

namespace Module

/-- **A quotient of a ring by an ideal which is not finitely generated is not a finitely presented
module.** Finite presentation of `R ⧸ I` would force the kernel of `R → R ⧸ I`, which is `I`, to
be finitely generated. -/
theorem not_finitePresentation_quotient_of_not_fg {R : Type u} [CommRing R] (I : Ideal R)
    (h : ¬ I.FG) : ¬ Module.FinitePresentation R (R ⧸ I) := fun _ =>
  h (by
    have := Module.FinitePresentation.fg_ker (Submodule.mkQ I) (Submodule.mkQ_surjective I)
    rwa [Submodule.ker_mkQ] at this)

/-- `ℕ → ZMod 2` is a ring of idempotents. -/
theorem mul_self_eq_of_piNat_zmodTwo (x : ℕ → ZMod 2) : x * x = x := by
  funext n
  have : ∀ a : ZMod 2, a * a = a := by decide
  exact this (x n)

/-- The quotient of `ℕ → ZMod 2` by the finitely supported sequences is flat: every ideal of a ring
of idempotents is pure. -/
theorem flat_quotient_finiteSupport_piNat_zmodTwo :
    Module.Flat (ℕ → ZMod 2) ((ℕ → ZMod 2) ⧸ Ideal.finiteSupport ℕ (ZMod 2)) :=
  Ideal.Pure.of_forall_mul_self_eq mul_self_eq_of_piNat_zmodTwo _

/-- The quotient of `ℕ → ZMod 2` by the finitely supported sequences is not finitely presented. -/
theorem not_finitePresentation_quotient_finiteSupport_piNat_zmodTwo :
    ¬ Module.FinitePresentation (ℕ → ZMod 2) ((ℕ → ZMod 2) ⧸ Ideal.finiteSupport ℕ (ZMod 2)) :=
  not_finitePresentation_quotient_of_not_fg _ (Ideal.not_fg_finiteSupport ℕ (ZMod 2))

/-- **A finite flat module over a commutative ring need not be finitely presented.** The witness is
the quotient of `ℕ → ZMod 2` by the ideal of finitely supported sequences: it is cyclic, it is flat
because every ideal of a ring of idempotents is pure, and it is not finitely presented because that
ideal is not finitely generated. -/
theorem not_forall_finitePresentation_of_finite_of_flat :
    ¬ ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M],
      Module.Finite R M → Module.Flat R M → Module.FinitePresentation R M := fun h =>
  not_finitePresentation_quotient_finiteSupport_piNat_zmodTwo
    (h _ _ inferInstance flat_quotient_finiteSupport_piNat_zmodTwo)

/-- **The polynomial-ring hypothesis of
`Module.FinitePresentation.of_flat_of_finitePresentation_mvPolynomial` is not satisfiable.** Over
`R = ℕ → ZMod 2` there is no proof that a module over `R[x_1, …, x_n]` which is finite over it and
flat over `R` is finitely presented over it, already for no variables at all: the quotient of `R`
by the finitely supported sequences is a counterexample, transported along the isomorphism
`R[x_1, …, x_0] ≅ R`, whose source is of finite type over `R` so that finite presentation passes
between the two rings.

Consequently that reduction theorem and its algebra counterpart
`Algebra.FinitePresentation.of_flat_of_finitePresentation_mvPolynomial` are vacuous as they stand,
and the hypothesis has to acquire the finiteness of the weakly associated primes of `R` which
Stacks 05IL assumes. -/
theorem not_forall_finitePresentation_mvPolynomial_of_finite_of_flat :
    ¬ ∀ (n : ℕ) (N : Type) [AddCommGroup N]
      [Module (MvPolynomial (Fin n) (ℕ → ZMod 2)) N] [Module (ℕ → ZMod 2) N]
      [IsScalarTower (ℕ → ZMod 2) (MvPolynomial (Fin n) (ℕ → ZMod 2)) N]
      [Module.Finite (MvPolynomial (Fin n) (ℕ → ZMod 2)) N] [Module.Flat (ℕ → ZMod 2) N],
      Module.FinitePresentation (MvPolynomial (Fin n) (ℕ → ZMod 2)) N := by
  intro h
  have hflat := flat_quotient_finiteSupport_piNat_zmodTwo
  let e := MvPolynomial.isEmptyAlgEquiv (ℕ → ZMod 2) (Fin 0)
  let : Algebra (MvPolynomial (Fin 0) (ℕ → ZMod 2)) (ℕ → ZMod 2) :=
    (e : MvPolynomial (Fin 0) (ℕ → ZMod 2) →+* (ℕ → ZMod 2)).toAlgebra
  let : Module (MvPolynomial (Fin 0) (ℕ → ZMod 2))
      ((ℕ → ZMod 2) ⧸ Ideal.finiteSupport ℕ (ZMod 2)) :=
    Module.compHom _ (e : MvPolynomial (Fin 0) (ℕ → ZMod 2) →+* (ℕ → ZMod 2))
  have htower : IsScalarTower (MvPolynomial (Fin 0) (ℕ → ZMod 2)) (ℕ → ZMod 2)
      ((ℕ → ZMod 2) ⧸ Ideal.finiteSupport ℕ (ZMod 2)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (ℕ → ZMod 2) (MvPolynomial (Fin 0) (ℕ → ZMod 2))
      ((ℕ → ZMod 2) ⧸ Ideal.finiteSupport ℕ (ZMod 2)) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change (e (algebraMap (ℕ → ZMod 2) (MvPolynomial (Fin 0) (ℕ → ZMod 2)) r)) • x = r • x
      rw [AlgEquiv.commutes]
      simp
  have hsurj : Function.Surjective
      (algebraMap (MvPolynomial (Fin 0) (ℕ → ZMod 2)) (ℕ → ZMod 2)) := e.surjective
  have : Module.Finite (MvPolynomial (Fin 0) (ℕ → ZMod 2)) (ℕ → ZMod 2) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) hsurj
  have : Module.Finite (MvPolynomial (Fin 0) (ℕ → ZMod 2))
      ((ℕ → ZMod 2) ⧸ Ideal.finiteSupport ℕ (ZMod 2)) :=
    Module.Finite.trans (ℕ → ZMod 2) _
  have : Algebra.FiniteType (MvPolynomial (Fin 0) (ℕ → ZMod 2)) (ℕ → ZMod 2) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId _ _) hsurj
  have := h 0 ((ℕ → ZMod 2) ⧸ Ideal.finiteSupport ℕ (ZMod 2))
  exact not_finitePresentation_quotient_finiteSupport_piNat_zmodTwo
    (Module.FinitePresentation.of_restrictScalars_of_finiteType
      (MvPolynomial (Fin 0) (ℕ → ZMod 2)) (ℕ → ZMod 2) _)

end Module

end
