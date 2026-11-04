module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedCohomology
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyTildeFunctor
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsion
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPushforward
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# Power-torsion cohomology and cohomological support on the spectrum

Let `A` be a commutative ring, let `I ⊆ A` be a finitely generated ideal, let `X = Spec A` and
let `Z = V(I)`.  Derived sheafification carries an object `K` of `D(A)` to the complex `K̃` of
`𝒪_X`-modules.  This module identifies the two conditions

* `K` has `I`-power-torsion cohomology — membership in `Dualizing.derivedPowerTorsionProperty`,
  the subcategory of which local cohomology `RΓ_Z` is the coreflection (Tag 0A6Q);
* `K̃` has cohomology sheaves supported on `Z` — `AlgebraicGeometry.CohomologySupportedOn`, the
  condition under which the canonical map `i_* R𝓗_Z(K̃) ⟶ K̃` of Tag 0AEF (2) is invertible.

Both are checked one degree at a time, and in degree `i` they are the two sides of Tag 0953: the
`i`-th cohomology sheaf of `K̃` is the sheafification of `H^i(K)`, because `~` is exact, and the
stalk of `M̃` at a prime is the localization `M_p`, so the sheaf is supported on `V(I)` exactly
when `Supp(H^i(K)) ⊆ V(I)`, which for a finitely generated `I` is `I`-power torsion.

## Main results

* `Stacks.LocalCohomologyTilde.cohomologySupportedOn_tilde_of_derivedPowerTorsion`: if `K` has
  `I`-power-torsion cohomology then `K̃` has cohomology supported on `V(I)`.
* `Stacks.LocalCohomologyTilde.derivedPowerTorsion_of_cohomologySupportedOn_tilde`: the converse,
  for a finitely generated `I`.
* `Stacks.LocalCohomologyTilde.derivedPowerTorsion_iff_cohomologySupportedOn_tilde`: the two
  conditions are equivalent.

## Implementation notes

Only finite generation of `I` is used, and only for the converse; neither direction needs `A`
Noetherian and neither needs `Z` closed as a separate hypothesis.

The degreewise identification of the cohomology sheaf is
`Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso` at the exact functor
`Stacks.LocalCohomologyTilde.tildeSheafFunctor`, whose exactness instances are the ones already
registered for it; the passage from a sheaf of modules to its underlying abelian presheaf, on
which `AlgebraicGeometry.CohomologySupportedOn` is stated, is `ExtensionByZeroModules.toAb`.  The
stalk dictionary is `Stacks.AffineTilde.isZero_stalk_tilde_of_exists_pow_smul_eq_zero` and
`Stacks.AffineTilde.notMem_support_of_isZero_stalk_tilde`.

Everything is stated at `CategoryTheory.HasDerivedCategory.standard`, which is the model
`Dualizing.derivedPowerTorsionProperty` and `AlgebraicGeometry.CohomologySupportedOn` are both
baked at, and the model at which the derived Spec–Γ equivalence of Tag 06Z0 is available as
`AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence`.  The local attribute setting that
model carries **priority 10000**: the import closure of this module reaches
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose `HasDerivedCategory` declarations
are global instances, and a global instance beats a default-priority local attribute, so the
plain attribute would silently keep the locally small model.

## References

* [Stacks Project, Tag 0953](https://stacks.math.columbia.edu/tag/0953)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

-- Standard model only: `Dualizing.derivedPowerTorsionProperty`, `CohomologySupportedOn`.
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomologyTilde

variable {A : CommRingCat.{u}} {I : Ideal A} (hI : I.FG)
  (W : DerivedCategory (ModuleCat.{u} A))

/-- The `i`-th cohomology sheaf of `K̃`, as the sheafification of the `i`-th cohomology module of
`K`: derived sheafification commutes with the cohomology functors because `~` is exact. -/
def tildeDerivedHomologyIso (i : ℤ) :
    (DerivedCategory.homologyFunctor
        (RingedSpaceModuleAdjunction.ModuleSheaves (Spec A).toRingedSpace) i).obj
        ((tildeSheafFunctor A).mapDerivedCategory.obj W) ≅
      (tildeSheafFunctor A).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj W) :=
  (Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso
    (tildeSheafFunctor A) i).app W

/-- **An object of `D(A)` with `I`-power-torsion cohomology sheafifies to one supported on
`V(I)`.**  In degree `i` the cohomology sheaf of `K̃` is `H^i(K)^~`, and the stalk of `M̃` at a
prime `p` not containing `I` vanishes because some element of `I` acts invertibly there while
every element of `M` is killed by a power of it. -/
theorem cohomologySupportedOn_tilde_of_derivedPowerTorsion
    (hW : Dualizing.derivedPowerTorsionProperty A I hI W) :
    CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace)
      (supportSubset (PrimeSpectrum.zeroLocus (I : Set A)))
      ((tildeSheafFunctor A).mapDerivedCategory.obj W) := by
  intro i x hx
  obtain ⟨g, hgI, hgx⟩ : ∃ g ∈ I, g ∉ x.asIdeal := by
    by_contra h
    push Not at h
    exact hx fun g hg => h g hg
  refine IsZero.of_iso ?_ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
    ((ExtensionByZeroModules.toAb _).mapIso (tildeDerivedHomologyIso W i)))
  exact Stacks.AffineTilde.isZero_stalk_tilde_of_exists_pow_smul_eq_zero _ g
    (fun m => by
      obtain ⟨n, _, hall⟩ := hW i m
      exact ⟨n, hall _ (Ideal.pow_mem_pow hgI n)⟩) x hgx

include hI

/-- **The converse, for a finitely generated ideal.**  If `K̃` has cohomology sheaves supported on
`V(I)` then the support of each cohomology module of `K` lies in `V(I)`, which for a finitely
generated `I` makes that module `I`-power torsion (Tag 0953). -/
theorem derivedPowerTorsion_of_cohomologySupportedOn_tilde
    (hW : CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace)
      (supportSubset (PrimeSpectrum.zeroLocus (I : Set A)))
      ((tildeSheafFunctor A).mapDerivedCategory.obj W)) :
    Dualizing.derivedPowerTorsionProperty A I hI W := by
  intro i
  refine isIPowerTorsion_of_support_subset hI fun p hp => ?_
  by_contra hpZ
  refine Stacks.AffineTilde.notMem_support_of_isZero_stalk_tilde _ p ?_ hp
  refine IsZero.of_iso (hW i p hpZ) (Iso.symm ?_)
  exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} _).mapIso
    ((ExtensionByZeroModules.toAb _).mapIso (tildeDerivedHomologyIso W i))

/-- **The dictionary.**  For a finitely generated ideal `I` of a commutative ring `A`, an object
of `D(A)` has `I`-power-torsion cohomology exactly when its derived sheafification has cohomology
sheaves supported on `V(I)`.

This is the translation between the subcategory of `D(A)` that local cohomology `RΓ_{V(I)}`
coreflects onto (Tag 0A6Q) and the subcategory of `D(𝒪_{Spec A})` that `i_* R𝓗_{V(I)}` coreflects
onto (Tag 0AEF (2)). -/
theorem derivedPowerTorsion_iff_cohomologySupportedOn_tilde :
    Dualizing.derivedPowerTorsionProperty A I hI W ↔
      CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace)
        (supportSubset (PrimeSpectrum.zeroLocus (I : Set A)))
        ((tildeSheafFunctor A).mapDerivedCategory.obj W) :=
  ⟨cohomologySupportedOn_tilde_of_derivedPowerTorsion hI W,
    derivedPowerTorsion_of_cohomologySupportedOn_tilde hI W⟩

end Stacks.LocalCohomologyTilde

end
