module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Catenary.Localization
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.IntegralClosure.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Heights of quotients across a finite integral extension

Over a universally catenary Noetherian ring `A`, a finite integral extension `A → B` does not
change the height of a quotient: for primes `p ≤ q` of `A` and primes `P ≤ Q` of `B` lying over
them, the height of `Q / P` in `B / P` equals the height of `q / p` in `A / p`.

## Main results

* `Ideal.quotient_height_eq_of_finite_integral` is this equality of heights.

## Implementation notes

The proof goes through the dimension formula `height_add_trdeg_residue_eq`: both transcendence
degrees that appear in it vanish, the one of `B / P` over `A / p` because the extension is
integral, and the one of the residue fields because the residue extension is algebraic. Being
catenary is used in the order-theoretic form `IsUniversallyCatenary`, which is deduced here from
`Ring.IsUniversallyCatenary`.

`A` and `B` lie in independent universes, as the statement has no universe content. Nothing is
needed to arrange this: the dimension formula already compares a ring with a finite-type algebra
over it across universes, and the only finite-type algebra `IsUniversallyCatenary A` is applied
to is `A ⧸ p`, which lives in `A`'s universe. The hypothesis reaches it as
`IsUniversallyCatenary.trans`, whose universe-free form is
`IsUniversallyCatenary.isCatenarySpace`.

## References

* [Stacks Project, Tag 0BJS](https://stacks.math.columbia.edu/tag/0BJS)
-/

@[expose] public section

open IrreducibleClosedsCodim TopologicalSpace

universe u v

namespace Ideal

/-! The private `ring_isCatenary_to_catenaryRing` that used to sit here restated
`Ring.IsCatenary.isCatenaryOrder` of
`StacksFrontier/RingTheory/Catenary/Localization.lean`, line 81: `Catenary.IsCatenaryRing R` is by
definition `Catenary.IsCatenaryOrder (PrimeSpectrum R)`. That survivor is used instead. -/

/-- The prime spectrum of a catenary ring is a catenary space in the codimension sense. -/
@[ega "0 16.1.4" "partial", ega "IV 5.1.1" "5.1.1.4"]
private theorem irreducibleCatenarySpace_of_ring_isCatenary
    {R : Type*} [CommRing R] (hR : Ring.IsCatenary R) :
    IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum R) := by
  have hOrder : Catenary.IsCatenaryOrder (IrreducibleCloseds (PrimeSpectrum R)) :=
    (Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum R).mp hR.isCatenaryOrder
  intro Y Z hYZ
  obtain ⟨⟨N, hN⟩, hlen⟩ := hOrder Y Z hYZ
  have hfin : topCodim Y Z ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top N)
    rw [topCodim_le_iff]
    intro s hs ht
    exact_mod_cast hN s hs ht
  refine ⟨hfin, fun s hs => ?_⟩
  obtain ⟨t, ht, htdim⟩ := exists_maximalChain_length_eq_topCodim Y Z hYZ hfin
  let s' : RelSeries {(a, b) : IrreducibleCloseds (PrimeSpectrum R) ×
      IrreducibleCloseds (PrimeSpectrum R) | a ⋖ b} :=
    ⟨s.length, s.toFun, hs.2.2⟩
  let t' : RelSeries {(a, b) : IrreducibleCloseds (PrimeSpectrum R) ×
      IrreducibleCloseds (PrimeSpectrum R) | a ⋖ b} :=
    ⟨t.length, t.toFun, ht.2.2⟩
  exact (congrArg (fun n : ℕ => (n : ℕ∞)) (hlen s' t' hs.1 hs.2.1 ht.1 ht.2.1)).trans htdim

/-- A universally catenary ring in the sense of `Ring.IsUniversallyCatenary` is universally
catenary in the codimension sense. -/
private theorem isUniversallyCatenary_of_ring_isUniversallyCatenary
    {R : Type u} [CommRing R]
    (hR : Ring.IsUniversallyCatenary R) : IsUniversallyCatenary R := by
  intro C _ _ hC
  have : Algebra.FiniteType R C := hC
  exact irreducibleCatenarySpace_of_ring_isCatenary (hR C)

/-- Primes `Q` over `q` induce primes `Q / P` over `q / p` in the quotients by `P` over `p`. -/
private theorem liesOver_map_quotientMk {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {p q : Ideal A} {P Q : Ideal B} [P.LiesOver p] [Q.LiesOver q] (hpq : p ≤ q) (hPQ : P ≤ Q) :
    (Q.map (Ideal.Quotient.mk P)).LiesOver (q.map (Ideal.Quotient.mk p)) := by
  rw [Ideal.liesOver_iff]
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  show (Ideal.Quotient.mk p a ∈ q.map (Ideal.Quotient.mk p)) ↔
    Ideal.Quotient.mk P (algebraMap A B a) ∈ Q.map (Ideal.Quotient.mk P)
  rw [Ideal.mem_quotient_iff_mem hpq, Ideal.mem_quotient_iff_mem hPQ]
  exact Ideal.mem_of_liesOver (P := Q) (p := q) a

/-- In an integral extension, the residue field extension at a prime lying over another is
algebraic. -/
private theorem isAlgebraic_residueField_of_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (q : Ideal R) (Q : Ideal S) [q.IsPrime] [Q.IsPrime]
    [Q.LiesOver q] :
    letI := Ideal.ResidueField.algebraOfLiesOver q Q
    Algebra.IsAlgebraic q.ResidueField Q.ResidueField := by
  let : Algebra q.ResidueField Q.ResidueField := Ideal.ResidueField.algebraOfLiesOver q Q
  let := Localization.AtPrime.algebraOfLiesOver q Q
  let : Algebra R Q.ResidueField :=
    ((algebraMap (S ⧸ Q) Q.ResidueField).comp (algebraMap R (S ⧸ Q))).toAlgebra
  have : IsScalarTower R S Q.ResidueField := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsIntegral (R ⧸ q) (S ⧸ Q) := Algebra.IsIntegral.tower_top R
  let : Algebra (R ⧸ q) Q.ResidueField :=
    ((algebraMap (S ⧸ Q) Q.ResidueField).comp (algebraMap (R ⧸ q) (S ⧸ Q))).toAlgebra
  have : IsScalarTower (R ⧸ q) (S ⧸ Q) Q.ResidueField := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic (R ⧸ q) Q.ResidueField := Algebra.IsAlgebraic.trans _ (S ⧸ Q) _
  have : IsScalarTower (R ⧸ q) q.ResidueField Q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    show algebraMap R Q.ResidueField x =
      Ideal.ResidueField.map q Q (algebraMap R S) Ideal.LiesOver.over
        (algebraMap R q.ResidueField x)
    rw [Ideal.ResidueField.map_algebraMap]
    exact (IsScalarTower.algebraMap_apply R S Q.ResidueField x).symm
  exact Algebra.IsAlgebraic.extendScalars (Ideal.injective_algebraMap_quotient_residueField q)

/-- **Stacks Project, Tag 0BJS, the height comparison.** For a finite integral extension of a
universally catenary Noetherian ring, the height of `Q / P` in `B / P` equals the height of
`q / p` in `A / p`. The two rings lie in independent universes. -/
@[ega "0 23.2.10" "(i)"]
theorem quotient_height_eq_of_finite_integral
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B] [Algebra.IsIntegral A B]
    (hA : Ring.IsUniversallyCatenary A)
    {p q : Ideal A} {P Q : Ideal B} [p.IsPrime] [q.IsPrime] [P.IsPrime] [Q.IsPrime]
    [P.LiesOver p] [Q.LiesOver q] (hpq : p ≤ q) (hPQ : P ≤ Q) :
    (Q.map (Ideal.Quotient.mk P)).height = (q.map (Ideal.Quotient.mk p)).height := by
  let R := A ⧸ p
  let S := B ⧸ P
  have : IsScalarTower A R S := Ideal.Quotient.isScalarTower_of_liesOver A P p
  let q' : Ideal R := q.map (Ideal.Quotient.mk p)
  let Q' : Ideal S := Q.map (Ideal.Quotient.mk P)
  have : q'.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have : Q'.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  have : Algebra.FiniteType A R :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A p) Ideal.Quotient.mk_surjective
  have hcat : IsUniversallyCatenary R :=
    (isUniversallyCatenary_of_ring_isUniversallyCatenary hA).trans
  have hinj : Function.Injective (algebraMap R S) := by
    show Function.Injective
      (Ideal.quotientMap P (algebraMap A B)
        (le_of_eq (Ideal.LiesOver.over (P := P) (p := p))))
    exact Ideal.quotientMap_injective' (by
      rw [Ideal.LiesOver.over (P := P) (p := p)])
  have : Q'.LiesOver q' := liesOver_map_quotientMk hpq hPQ
  have : Algebra.IsIntegral R S := Ideal.Quotient.algebra_isIntegral_of_liesOver P p
  have : Module.Finite A S := Module.Finite.trans B S
  have : Module.Finite R S := Module.Finite.of_restrictScalars_finite A R S
  have htrdeg : Algebra.trdeg R S = 0 := trdeg_eq_zero
  let : Algebra q'.ResidueField Q'.ResidueField :=
    Ideal.ResidueField.algebraOfLiesOver q' Q'
  have : Algebra.IsAlgebraic q'.ResidueField Q'.ResidueField :=
    isAlgebraic_residueField_of_isIntegral q' Q'
  have hres : Algebra.trdeg q'.ResidueField Q'.ResidueField = 0 := trdeg_eq_zero
  simpa [htrdeg, hres] using height_add_trdeg_residue_eq hinj hcat q' Q'

end Ideal
