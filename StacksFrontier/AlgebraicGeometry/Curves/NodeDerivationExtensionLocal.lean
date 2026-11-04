module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeBranchResidues
public import StacksFrontier.AlgebraicGeometry.Curves.NodeDerivationExtension
public import StacksFrontier.RingTheory.Derivation.IntegralClosureUnique
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability

/-!
# Extending a derivation to the normalization of a local ring of a nodal curve

At a local ring of a curve with at worst nodal singularities there are two cases, and in both a
`k`-derivation extends to the integral closure of the ring in its total ring of fractions.

* The local ring is **regular**. Then it is integrally closed
  (`isIntegrallyClosed_of_isRegularLocalRing`), the integral closure is the ring itself,
  and the extension is the derivation one started with.
* The local ring is **nodal** with residue field `k`. Then its quadratic algebra splits, which
  produces the two branch residues, and
  `Stacks.Curves.existsUnique_extend_integralClosure_of_isNodalAlgebra` extends the derivation
  and makes the extension fix both branches.

The point of putting the two side by side is that together they are exactly the local input that
a local-to-global argument for the normalization of a whole affine open needs: the dichotomy
`Stacks.Curves.isRegularLocalRing_stalk_or_isNode_of_hasAtWorstNodalSingularities` says that at
every point of an at-worst-nodal curve one of the two applies, and neither case needs any
hypothesis about the other points.

In both statements the branch residues are produced rather than supplied. That is the difference
from `Stacks.Curves.existsUnique_extend_integralClosure_of_isNodalAlgebra`, whose `ε₁`, `ε₂` are
arguments: here the only datum is the rationality of the residue field, which over an
algebraically closed field is Zariski's lemma.

## Main results

* `Stacks.Curves.exists_extend_integralClosure_of_isIntegrallyClosed` — the extension at an
  integrally closed local ring, where the normalization changes nothing.
* `Stacks.Curves.exists_extend_integralClosure_of_isRegularLocalRing` — the same at a regular
  local ring.
* `Stacks.Curves.exists_extend_integralClosure_of_isNodalAlgebra_residueField` — **the extension
  at a nodal local ring whose residue field is the base field**, with the two branch residues
  produced from the splitting of the quadratic algebra.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 0567](https://stacks.math.columbia.edu/tag/0567)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

section IntegrallyClosed

variable (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]

/-- **At an integrally closed domain the normalization changes nothing**, so every
`k`-derivation already is its own extension to the integral closure in the fraction field. -/
theorem exists_extend_integralClosure_of_isIntegrallyClosed [IsDomain A] [IsIntegrallyClosed A]
    (D : Derivation k A A) :
    ∃ E : Derivation k ↥(integralClosure A (FractionRing A))
        ↥(integralClosure A (FractionRing A)),
      ∀ a : A, E (algebraMap A ↥(integralClosure A (FractionRing A)) a)
        = algebraMap A ↥(integralClosure A (FractionRing A)) (D a) := by
  obtain ⟨E, hE, -⟩ :=
    Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_eq_bot
      (L := FractionRing A) D (IsIntegrallyClosed.integralClosure_eq_bot A (FractionRing A))
  exact ⟨E, hE⟩

/-- **At a regular local ring the normalization changes nothing.** A regular local ring is
integrally closed by Tag 0567. -/
theorem exists_extend_integralClosure_of_isRegularLocalRing [IsRegularLocalRing A]
    (D : Derivation k A A) :
    ∃ E : Derivation k ↥(integralClosure A (FractionRing A))
        ↥(integralClosure A (FractionRing A)),
      ∀ a : A, E (algebraMap A ↥(integralClosure A (FractionRing A)) a)
        = algebraMap A ↥(integralClosure A (FractionRing A)) (D a) := by
  have := IsRegularLocalRing.isDomain A
  have : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  exact exists_extend_integralClosure_of_isIntegrallyClosed k A D

end IntegrallyClosed

section Nodal

variable (k : Type u) (A : Type v) [Field k] [IsSepClosed k] [CommRing A] [IsLocalRing A]
  [Algebra k A]

/-- **A `k`-derivation of a nodal local `k`-algebra with residue field `k` extends to the
integral closure in its total ring of fractions.** The residue field being `k` makes it
separably closed, so the quadratic algebra of the node splits; the splitting produces the two
branch residues, and the extension theorem at a node then applies. Unlike
`Stacks.Curves.existsUnique_extend_integralClosure_of_isNodalAlgebra`, the two residues are not
arguments here. -/
theorem exists_extend_integralClosure_of_isNodalAlgebra_residueField
    (hNagata : IsNagataRing A) (hnodal : IsNodalAlgebra k A)
    (eκ : ResidueField A ≃ₐ[k] k) (D : Derivation k A A) :
    ∃ E : Derivation k ↥(integralClosure A (FractionRing A))
        ↥(integralClosure A (FractionRing A)),
      ∀ a : A, E (algebraMap A ↥(integralClosure A (FractionRing A)) a)
        = algebraMap A ↥(integralClosure A (FractionRing A)) (D a) := by
  have : IsNoetherianRing A := hNagata.isNoetherianRing
  let : IsSepClosed (ResidueField A) := IsSepClosed.of_ringEquiv eκ.toRingEquiv
  obtain ⟨e⟩ := nonempty_quadraticAlgebra_algEquiv_prod_of_isSepClosed k A hNagata hnodal
  obtain ⟨ε₁, ε₂, hres, hne⟩ :=
    exists_branchResidues_of_quadraticAlgebra_algEquiv_prod k A eκ e
  obtain ⟨E, hE, -⟩ :=
    existsUnique_extend_integralClosure_of_isNodalAlgebra k A hnodal ε₁ ε₂ hres hne D
  exact ⟨E, hE.1⟩

end Nodal

end Stacks.Curves

end
