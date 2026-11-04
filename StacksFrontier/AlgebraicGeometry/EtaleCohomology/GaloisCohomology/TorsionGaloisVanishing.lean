module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.AbsoluteGaloisPrimeBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.TorsionDerivedVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Higher Galois cohomology with torsion coefficients vanishes

Let `K` be a field with separable algebraic closure `Kˢᵉᵖ` and absolute Galois group
`G = Gal(Kˢᵉᵖ/K)`, and assume that the Brauer group of every finite subextension of `Kˢᵉᵖ/K`
vanishes. Then `H^q(G, M) = 0` for every torsion discrete `G`-module `M` and every `q ≥ 2`, the
groups being the continuous group cohomology.

## Main results

* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_of_isAddTorsion`: `H^q(Gal(Ω/K), M)`
  vanishes for every torsion discrete module `M` and `q ≥ 2`, for a separably closed `Ω` Galois
  over `K` such that `Br(L) = 0` for every intermediate field `L` of `Ω/K` finite over `K`.
* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_separableClosure_of_isAddTorsion`: the
  same statement at `Ω = Kˢᵉᵖ`.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe u v

namespace Stacks.GaloisCohomology

/-- If the Brauer group of every finite subextension of a separably closed Galois extension
`Ω/K` vanishes, then `H^q(Gal(Ω/K), M) = 0` for every torsion discrete `Gal(Ω/K)`-module `M` and
every `q ≥ 2`, the groups being the continuous group cohomology. -/
@[stacks 03R8 "part (2) in full, for the DERIVED-FUNCTOR groups continuousGroupCohomology of
Stacks 04JR: H^q(Gal(Ω/K), M) = 0 for EVERY torsion discrete Galois module M and EVERY q ≥ 2,
where Ω is any separably closed field Galois over K, so at Ω = K^sep this is exactly the tag's
part (2). The Brauer hypothesis is the one the source states, and in fact less: only the finite
SEPARABLE extensions of K inside Ω are used, whereas the tag asks for every finite extension, so
this statement implies the tag's rather than specialising it. The proof is the source's dévissage
carried out on locally constant cochains. A locally constant 2-cocycle on a profinite group takes
finitely many values, so it is a cocycle with values in a finite submodule; a finite module is
reduced to a module killed by a prime p along its p-torsion subgroup; a finite module killed by p
is handled over an open subgroup of index prime to p -- the preimage of a p-Sylow subgroup of a
finite quotient -- where the action factors through a p-group and the module is filtered by
copies of Z/p with trivial action, and the restriction-corestriction identity cor o res = n,
written out on cochains, carries the trivialization back to the whole group; and Z/p with trivial
action is the Kummer sequence of Stacks 03PL away from the characteristic and the Artin-Schreier
sequence of Stacks 0A3J in the characteristic, each fed by the two degrees of part (1) proved in
MultiplicativeGroupVanishingCriterion. Degrees above two come from dimension shifting along the
module of locally constant functions into a torsion divisible hull, which is an injective object
of the category of Stacks 04JP whose cokernel is again torsion. This registration is part (2);
part (1) has its own three registrations in MultiplicativeGroupVanishingCriterion",
  sga "4½ Arcata 3.1.6" "more general"]
theorem isZero_continuousGroupCohomology_of_isAddTorsion (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    (hBr : ∀ L : IntermediateField K Ω, FiniteDimensional K L → ∀ y : BrauerGroup L, y = 1)
    (M : ContinuousGModule.{u, max u v} Gal(Ω/K)) (hM : IsAddTorsion M.obj.obj.V)
    (q : ℕ) (hq : 2 ≤ q) :
    IsZero (continuousGroupCohomology.{u, v} Gal(Ω/K) q M) :=
  isZero_continuousGroupCohomology_of_torsion (hasPrimeBase_of_forall_brauer hBr) q hq M
    fun m ↦ isOfFinAddOrder_iff_nsmul_eq_zero.1 (hM m)

/-- If the Brauer group of every finite subextension of `Kˢᵉᵖ/K` vanishes then the continuous
cohomology of the absolute Galois group of `K` with torsion coefficients vanishes in every degree
`q ≥ 2`. -/
@[sga "4½ Arcata 3.1.6" "more general"]
theorem isZero_continuousGroupCohomology_separableClosure_of_isAddTorsion (K : Type u) [Field K]
    (hBr : ∀ L : IntermediateField K (SeparableClosure K), FiniteDimensional K L →
      ∀ y : BrauerGroup L, y = 1)
    (M : ContinuousGModule.{u, max u v} Gal(SeparableClosure K/K))
    (hM : IsAddTorsion M.obj.obj.V) (q : ℕ) (hq : 2 ≤ q) :
    IsZero (continuousGroupCohomology.{u, v} Gal(SeparableClosure K/K) q M) :=
  isZero_continuousGroupCohomology_of_isAddTorsion K (SeparableClosure K) hBr M hM q hq

end Stacks.GaloisCohomology

end
