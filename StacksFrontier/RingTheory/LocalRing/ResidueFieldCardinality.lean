module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Cardinality

/-!
# The cardinality of the residue field at a prime

The residue field `Ideal.ResidueField p` at a prime `p` of a commutative ring `R` is no larger
than `R`. By definition it is the residue field of the local ring `Localization.AtPrime p`,
hence a quotient of that localization, and a localization of `R` is no larger than `R`.

## Main results

* `Cardinal.mk_residueField_le` — the bound `#κ(p) ≤ #R`.
* `Cardinal.mk_residueField_le_max` — the same bound in the form `#κ(p) ≤ max ℵ₀ #R`.
-/

@[expose] public section

open Cardinal

universe u

namespace Cardinal

/-- The residue field at a prime `p` of a commutative ring `R` is no larger than `R`: it is the
quotient of the local ring `Localization.AtPrime p` by its maximal ideal, and a localization of
`R` has cardinality at most that of `R`. -/
public theorem mk_residueField_le {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    #p.ResidueField ≤ #R :=
  (mk_le_of_surjective (IsLocalRing.residue_surjective (R := Localization.AtPrime p))).trans
    (IsLocalization.cardinalMk_le (L := Localization.AtPrime p) p.primeCompl)

/-- The residue field at a prime of `R` has cardinality at most `max ℵ₀ #R`. -/
public theorem mk_residueField_le_max {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    #p.ResidueField ≤ max ℵ₀ #R :=
  (mk_residueField_le p).trans (le_max_right _ _)

end Cardinal
