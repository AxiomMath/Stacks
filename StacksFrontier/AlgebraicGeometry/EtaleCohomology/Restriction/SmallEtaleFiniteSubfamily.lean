module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteSubfamily

/-!
# Finitely many members of an étale covering of a quasi-compact object already cover it

An object of the small étale site whose underlying scheme is quasi-compact is a quasi-compact
object of the site, by `AlgebraicGeometry.SmallEtale.isQuasiCompactObject_of_compactSpace`.
Hence finitely many arrows of any covering presieve of such an object already generate a
covering sieve.

This is the form in which quasi-compactness enters an argument that has to choose one integer —
a Tor-amplitude bound, a degree bound — per member of a covering of `X` and then take the
minimum or maximum over the members: the choice can be made over a finite set only after the
covering has been cut down to finitely many of its arrows.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_finite_ofArrows_mem_of_compactSpace`: finitely many
  arrows of a covering presieve of a quasi-compact object of the small étale site generate a
  covering sieve of it.

## References

* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Finitely many arrows of a covering presieve of a quasi-compact object of the small étale
site generate a covering sieve of it.** The underlying scheme of the object is quasi-compact, so
the object is a quasi-compact object of the site in the sense of Stacks 090H, and the general
statement `CategoryTheory.GrothendieckTopology.exists_finite_ofArrows_mem_of_isQuasiCompactObject`
applies. -/
public theorem exists_finite_ofArrows_mem_of_compactSpace (U : SmallEtale B S hS)
    (hU : CompactSpace ((toScheme B S hS).obj U))
    (R : Presieve U) (hR : Sieve.generate R ∈ topology B S hS U) :
    ∃ (ι : Type (u + 1)) (_ : Finite ι) (V : ι → SmallEtale B S hS) (f : ∀ i, V i ⟶ U),
      (∀ i, R (f i)) ∧ Sieve.ofArrows V f ∈ topology B S hS U :=
  GrothendieckTopology.exists_finite_ofArrows_mem_of_isQuasiCompactObject
    (isQuasiCompactObject_of_compactSpace B S hS U hU) R hR

end AlgebraicGeometry.SmallEtale

end
