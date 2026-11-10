module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Residue fields of primes of a tensor product lie in the big fppf site

Let `A` and `C` be algebras over `R` whose spectra are objects of a big fppf site, and let `𝔰` be
a prime of `A ⊗_R C`. The residue field of `𝔰` and its algebraic closure then also have their
spectra in the site.

## Main results

* `AlgebraicGeometry.BigFppfSite.mk_lt_cutoff_of_contains_spec` and
  `AlgebraicGeometry.BigFppfSite.contains_spec_of_mk_lt_cutoff`: the spectrum of a ring is
  contained if and only if the cardinality of the ring is below the cutoff.
* `AlgebraicGeometry.BigFppfSite.contains_spec_tensorProduct`: the spectrum of a tensor product
  of two contained spectra is contained.
* `AlgebraicGeometry.BigFppfSite.contains_spec_algebraicClosure`: the spectrum of an algebraic
  closure of a contained field is contained.
* `AlgebraicGeometry.BigFppfSite.contains_spec_residueField_atPrime`: the spectrum of the
  residue field of a prime of a contained spectrum is contained.
* `AlgebraicGeometry.BigFppfSite.contains_spec_algebraicClosure_residueField_tensorProduct`:
  the spectrum of an algebraic closure of the residue field of a prime of `A ⊗_R C` is
  contained.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.BigFppfSite

/-- The cardinality of a ring whose spectrum is an object of the site is below the cutoff. -/
theorem mk_lt_cutoff_of_contains_spec (B : BigFppfSite.{u}) {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) : Cardinal.mk A < B.cutoff :=
  lt_of_le_of_lt (le_max_right _ _) (by simpa [Scheme.size_Spec] using hA)

/-- A ring whose cardinality is below the cutoff has its spectrum in the site. -/
theorem contains_spec_of_mk_lt_cutoff (B : BigFppfSite.{u}) {A : Type u} [CommRing A]
    (hA : Cardinal.mk A < B.cutoff) : B.Contains (Spec (.of A)) := by
  change (Spec (.of A)).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff hA

/-- The spectrum of a tensor product of two contained spectra is contained. -/
@[stacks 000R "(9), for a tensor product"]
theorem contains_spec_tensorProduct (B : BigFppfSite.{u}) {R A C : Type u}
    [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C))) :
    B.Contains (Spec (.of (A ⊗[R] C))) :=
  contains_spec_of_mk_lt_cutoff B (Cardinal.mk_tensorProduct_le.trans_lt (max_lt
    B.aleph0_lt_cutoff
    (max_lt (mk_lt_cutoff_of_contains_spec B hA) (mk_lt_cutoff_of_contains_spec B hC))))

/-- The spectrum of an algebraic closure of a contained field is contained. -/
@[stacks 000R "(9), for an algebraic closure"]
theorem contains_spec_algebraicClosure (B : BigFppfSite.{u}) {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) :
    B.Contains (Spec (.of (AlgebraicClosure K))) :=
  contains_spec_of_mk_lt_cutoff B
    ((Algebra.IsAlgebraic.cardinalMk_le_max K (AlgebraicClosure K)).trans_lt
      (max_lt (mk_lt_cutoff_of_contains_spec B hK) B.aleph0_lt_cutoff))

/-- The spectrum of the residue field of a prime of a contained spectrum is contained. -/
@[stacks 000R "(9), for the residue field of a prime"]
theorem contains_spec_residueField_atPrime (B : BigFppfSite.{u}) {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) (p : Ideal A) [p.IsPrime] :
    B.Contains (Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime p)))) := by
  have hL : B.Contains (Spec (.of (Localization.AtPrime p))) :=
    Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      p.primeCompl (Localization.AtPrime p) hA
  exact contains_spec_of_mk_lt_cutoff B ((Cardinal.mk_le_of_surjective
    (IsLocalRing.residue_surjective (R := Localization.AtPrime p))).trans_lt
      (mk_lt_cutoff_of_contains_spec B hL))

/-- For algebras `A` and `C` over `R` whose spectra are objects of the site and a prime `𝔰` of
`A ⊗_R C`, the spectrum of an algebraic closure of the residue field of `𝔰` is an object of the
site. -/
@[stacks 000R "(9), for the algebraic closure of the residue field of a prime of a tensor
product"]
theorem contains_spec_algebraicClosure_residueField_tensorProduct (B : BigFppfSite.{u})
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C)))
    (s : Ideal (A ⊗[R] C)) [s.IsPrime] :
    B.Contains (Spec (.of (AlgebraicClosure
      (IsLocalRing.ResidueField (Localization.AtPrime s))))) :=
  contains_spec_algebraicClosure B
    (contains_spec_residueField_atPrime B (contains_spec_tensorProduct B hA hC) s)

end AlgebraicGeometry.BigFppfSite

end
