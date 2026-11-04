module

public import Mathlib.RingTheory.NormalClosure
public import StacksCore.FieldTheory.MvRatFunc.Basic

/-! # Algebra instance on `MvRatFunc` -/

@[expose] public section

namespace MvRatFunc

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The `MvRatFunc σ R`-algebra structure on `MvRatFunc σ S` induced by an algebra map
`R → S` (with `FaithfulSMul R S`, so that `R` is a domain and the algebra map descends
to fraction rings). -/
noncomputable abbrev algebra (R S σ : Type*)
    [CommRing R] [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] :
    Algebra (MvRatFunc σ R) (MvRatFunc σ S) :=
  have : IsDomain R := .of_faithfulSMul R S
  Ring.instAlgebraFractionRing _ _

attribute [local instance] MvRatFunc.algebra

/-- The square `MvPolynomial σ R → MvRatFunc σ R → MvRatFunc σ S` and
`MvPolynomial σ R → MvPolynomial σ S → MvRatFunc σ S` commutes, allowing us to rewrite
out of the `MvRatFunc.algebra` instance. -/
@[simp] theorem algebraMap_algebraMap_mvPolynomial (R S σ : Type*) [CommRing R] [CommRing S]
    [IsDomain S] [Algebra R S] [FaithfulSMul R S] (p : MvPolynomial σ R) :
    algebraMap (MvRatFunc σ R) (MvRatFunc σ S) (algebraMap (MvPolynomial σ R) (MvRatFunc σ R) p) =
    algebraMap (MvPolynomial σ S) (MvRatFunc σ S)
      (algebraMap (MvPolynomial σ R) (MvPolynomial σ S) p) := by
  simp_rw [← Algebra.algHom_apply R, ← AlgHom.comp_apply]
  congr
  ext
  simp only [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply,
    ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_X]
  simp [IsScalarTower.algebraMap_apply (MvPolynomial σ R) (MvPolynomial σ S) (MvRatFunc σ S)]

/-- **Stacks 0G1M**.
For an algebraic extension `S/R` of commutative rings (with `S` a domain and
`FaithfulSMul R S`), the rank of `MvRatFunc σ S` over `MvRatFunc σ R` equals the rank of
`S` over `R`. -/
@[simp, stacks 0G1M]
theorem rank (R S σ : Type*) [CommRing R] [CommRing S]
    [IsDomain S] [Algebra R S] [Algebra.IsAlgebraic R S] [FaithfulSMul R S] :
    Module.rank (MvRatFunc σ R) (MvRatFunc σ S) = Cardinal.lift (Module.rank R S) :=
  Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial _

universe u

/-- **Stacks 0G1M** (universe monomorphic version).
Same as `MvRatFunc.rank`, but with all types in the same universe, so the equality of ranks
needs no universe lift. -/
@[stacks 0G1M "universe monomorphic version"]
theorem rank' (R : Type*) (S σ : Type u) [CommRing R] [CommRing S]
    [IsDomain S] [Algebra R S] [Algebra.IsAlgebraic R S] [FaithfulSMul R S] :
    Module.rank (MvRatFunc σ R) (MvRatFunc σ S) = Module.rank R S := by simp

/-- For a free algebraic extension `S/R`, the rational function field `MvRatFunc σ S` is
finite over `MvRatFunc σ R` iff `S` is finite over `R`. -/
@[simp] theorem finite_iff (R S σ : Type*) [CommRing R] [CommRing S]
    [IsDomain S] [Algebra R S] [Algebra.IsAlgebraic R S] [Module.Free R S] :
    Module.Finite (MvRatFunc σ R) (MvRatFunc σ S) ↔ Module.Finite R S := by
  have : IsDomain R := .of_faithfulSMul R S
  simp [← Module.rank_lt_aleph0_iff]

end MvRatFunc
