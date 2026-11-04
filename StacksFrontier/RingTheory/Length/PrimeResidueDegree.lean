module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The residue degree of a prime over a prime

For a ring map `f : A →+* B`, a prime `p` of `A` and a prime `Q` of `B` lying over it, the
residue fields `κ(p)` and `κ(Q)` are related by the embedding
`Ideal.ResidueField.map p Q f : κ(p) →+* κ(Q)`, and the *residue degree* of `Q` over `p` is the
dimension of `κ(Q)` over `κ(p)` along it.

## Main definitions

* `Stacks.Length.primeResidueDegree`: the residue degree `[κ(Q) : κ(p)]`, set to `0` when `Q`
  does not lie over `p`.

## Implementation notes

The degree is defined for every pair of primes, with the value `0` off the fibre, so that it can
be summed over a set of primes cut out by the lying-over condition without carrying a proof of
that condition into the summand. `Module.finrank` is itself `0` on an infinite extension.
-/

@[expose] public section

namespace Stacks.Length

/-- The residue degree `[κ(Q) : κ(p)]` of a prime `Q` of `B` over a prime `p` of `A` along a ring
map `f : A →+* B`: the rank of `κ(Q)` over `κ(p)` through `Ideal.ResidueField.map`, when
`p = f⁻¹(Q)`, and `0` otherwise. -/
noncomputable def primeResidueDegree {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (p : Ideal A) [p.IsPrime] (Q : Ideal B) [Q.IsPrime] : ℕ :=
  if h : p = Q.comap f then
    letI := (Ideal.ResidueField.map p Q f h).toAlgebra
    Module.finrank p.ResidueField Q.ResidueField
  else 0

/-- On the fibre, the residue degree is the rank of `κ(Q)` over `κ(p)`. -/
theorem primeResidueDegree_of_eq {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (p : Ideal A) [p.IsPrime] (Q : Ideal B) [Q.IsPrime] (h : p = Q.comap f) :
    primeResidueDegree f p Q =
      letI := (Ideal.ResidueField.map p Q f h).toAlgebra
      Module.finrank p.ResidueField Q.ResidueField := by
  rw [primeResidueDegree, dite_eq_left h]

end Stacks.Length

end
