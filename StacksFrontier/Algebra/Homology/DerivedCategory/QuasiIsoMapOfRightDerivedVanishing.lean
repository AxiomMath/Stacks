module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise

/-!
# A left exact functor preserves quasi-isomorphisms between complexes of acyclic objects

Let `G : A ⥤ B` be a left exact additive functor between abelian categories, `A` having enough
injectives. A quasi-isomorphism `φ : K ⟶ L` between bounded below cochain complexes all of whose
terms have vanishing higher right derived functors `RᵖG`, `p > 0`, stays a quasi-isomorphism after
`G` is applied termwise. This is [Stacks, Tag 015E] in the form "a complex of `G`-acyclic objects
computes `RG`", stated with the `ℕ`-indexed right derived functors `Functor.rightDerived` and with
no derived category in the statement.

The proof is `CategoryTheory.Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic`, for the
standard model of the derived categories, with right acyclicity read as the vanishing of the higher
right derived functors by
`Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived`.

## Main results

* `CategoryTheory.Functor.quasiIso_mapHomologicalComplex_of_isZero_rightDerived`: the statement
  above.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] [EnoughInjectives A]

/-- **A left exact functor carries a quasi-isomorphism of bounded below complexes of acyclic
objects to a quasi-isomorphism.** If every term of the bounded below complexes `K` and `L` has
vanishing higher right derived functors `RᵖG`, `p > 0`, then `G` applied termwise to a
quasi-isomorphism `K ⟶ L` is a quasi-isomorphism. -/
theorem quasiIso_mapHomologicalComplex_of_isZero_rightDerived (G : A ⥤ B) [G.Additive]
    [PreservesFiniteLimits G] {K L : CochainComplex A ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : CochainComplex.plus A K) (hL : CochainComplex.plus A L)
    (hKac : ∀ n p, 0 < p → IsZero ((G.rightDerived p).obj (K.X n)))
    (hLac : ∀ n p, 0 < p → IsZero ((G.rightDerived p).obj (L.X n))) :
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard B
  exact G.quasiIso_mapHomologicalComplex_of_rightAcyclic φ hK hL
    (fun n ↦ (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived G _).2
      (hKac n))
    (fun n ↦ (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived G _).2
      (hLac n))

end CategoryTheory.Functor
