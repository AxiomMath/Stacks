module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Weakly
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.IndEtaleFibres
public import StacksFrontier.RingTheory.WeaklyEtale.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.Field

@[expose] public section

/-!
# Residue field extensions of weakly étale ring maps

A weakly étale ring map induces separable algebraic extensions on residue fields at every pair
of primes lying over one another.

## Main definitions

There are no new definitions.

## Main results

* `isSeparable_and_isAlgebraic_residueField_of_weaklyEtale` (Stacks 092R): the residue field
  extensions induced by a weakly étale ring map are separable algebraic.

## Implementation notes

The residue field extension is the algebra structure induced by the canonical map
`Ideal.ResidueField.map p q (algebraMap A B) hpq`. The conclusion records separability and
algebraicity explicitly, following the source's formulation as a separable algebraic extension.

The argument passes through the fiber ring `p.Fiber B`, which is weakly étale over the field
`p.ResidueField`. Stacks 092Q (`flat_lmul_weaklyEtale_filteredColimitEtale_tfae`) makes every
finitely generated `p.ResidueField`-subalgebra of the fiber étale, which gives separability of
the whole fiber; `q.ResidueField` is then identified with a quotient of the fiber by the
maximal ideal corresponding to `q` under `PrimeSpectrum.primesOverOrderIsoFiber`, using
`Ideal.nonempty_fiber_residue_algEquiv`.

## References

* [The Stacks Project, Tag 092R](https://stacks.math.columbia.edu/tag/092R)
* [Olivier, *Anneaux absolument plats universels et épimorphismes à buts réduits*][Olivier-AF]
-/

universe u v

open TensorProduct

private theorem isSeparable_of_etale
    (K : Type u) (C : Type v) [Field K] [CommRing C] [Algebra K C]
    (hC : Algebra.Etale K C) : Algebra.IsSeparable K C := by
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K C).mp hC
  choose _ hsepAi using hAi
  exact (AlgEquiv.Algebra.isSeparable_iff e.symm).mp Algebra.IsSeparable.pi

private theorem isSeparable_of_fg_subalgebra_etale
    (K : Type u) (C : Type v) [Field K] [CommRing C] [Algebra K C]
    (h : ∀ D : Subalgebra K C, D.FG → Algebra.Etale K D) :
    Algebra.IsSeparable K C := by
  rw [Algebra.isSeparable_def]
  intro x
  let D : Subalgebra K C := Algebra.adjoin K ({x} : Set C)
  have hDfg : D.FG := by
    simpa [D] using Subalgebra.fg_adjoin_finset ({x} : Finset C)
  let y : D := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  simpa [y] using ((isSeparable_of_etale K D (h D hDfg)).isSeparable K y).map D.val
    (fun _ _ hxy => Subtype.ext hxy)

private theorem isSeparable_quotient
    (K : Type u) (C : Type v) [Field K] [CommRing C] [Algebra K C]
    (hC : Algebra.IsSeparable K C) (I : Ideal C) :
    Algebra.IsSeparable K (C ⧸ I) := by
  rw [Algebra.isSeparable_def]
  intro x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hdvd : minpoly K (Ideal.Quotient.mkₐ K I c) ∣ minpoly K c := by
    apply minpoly.dvd
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  exact (hC.isSeparable K c).of_dvd hdvd

/-- If `A → B` is weakly étale and a prime `q` of `B` lies over a prime `p` of `A`, then the
canonical residue field extension `κ(p) → κ(q)` is separable algebraic. -/
@[stacks 092R]
theorem isSeparable_and_isAlgebraic_residueField_of_weaklyEtale
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (h : Algebra.WeaklyEtale A B) (p : Ideal A) [p.IsPrime]
    (q : Ideal B) [q.IsPrime] (hpq : p = q.comap (algebraMap A B)) :
    letI := (Ideal.ResidueField.map p q (algebraMap A B) hpq).toAlgebra
    Algebra.IsSeparable p.ResidueField q.ResidueField ∧
      Algebra.IsAlgebraic p.ResidueField q.ResidueField := by
  have : q.LiesOver p := ⟨hpq⟩
  let : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap A B) hpq).toAlgebra
  let C := p.Fiber B
  have hCsep : Algebra.IsSeparable p.ResidueField C :=
    isSeparable_of_fg_subalgebra_etale p.ResidueField C
      ((flat_lmul_weaklyEtale_filteredColimitEtale_tfae p.ResidueField C).2
        (Algebra.WeaklyEtale.flat_lmul' p.ResidueField C))
  let qOver : ↥(p.primesOver B) := ⟨q, inferInstance, inferInstance⟩
  let P : PrimeSpectrum C := PrimeSpectrum.primesOverOrderIsoFiber A B p qOver
  have hQsep := isSeparable_quotient p.ResidueField C hCsep P.asIdeal
  have : P.asIdeal.IsMaximal :=
    have : Algebra.IsIntegral p.ResidueField (C ⧸ P.asIdeal) := hQsep.isAlgebraic.isIntegral
    Ideal.Quotient.maximal_of_isField P.asIdeal
      (isField_of_isIntegral_of_isField'
        (R := p.ResidueField) (S := C ⧸ P.asIdeal) (Field.toIsField p.ResidueField))
  obtain ⟨e⟩ := p.nonempty_fiber_residue_algEquiv (B := B) (P := P) qOver rfl
  have hqsep : Algebra.IsSeparable p.ResidueField q.ResidueField :=
    (AlgEquiv.Algebra.isSeparable_iff e).mp hQsep
  exact ⟨hqsep, hqsep.isAlgebraic⟩
