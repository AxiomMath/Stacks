module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafIrreducibleSectionsRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FiniteCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.TraceRetraction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafSliceSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafIrreducibleSections
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleSlicePowerSections
public import StacksFrontier.Topology.Dimension.OpenGeneralizingMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.TorsionLocalAnnihilation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.HigherDirectImageForget

/-!
# Finiteness of the cohomology of `j_!𝒢` for a locally constant `𝒢` on a unibranch open

Let `Λ` be a Noetherian ring, `k` an algebraically closed field and `X` a separated scheme of
finite type over `k` of dimension at most one. For an open immersion `j : U ⟶ X` with `U`
irreducible and geometrically unibranch and a finite type locally constant sheaf `𝒢` of
`Λ`-modules on `U_étale` killed by a power of a prime `ℓ`, the modules `H^q(X, j_!𝒢)` are finite
if `ℓ` is prime to the characteristic of `k` or `X` is proper. This is the proof of Stacks 0GJH,
in the form in which the proof of Stacks 0GJI uses it.

## Main results

* `Stacks.EtaleCohomology.module_finite_cohomology_extensionByZero_of_isGeometricallyUnibranch`
  — Stacks 0GJH for an irreducible geometrically unibranch `U`.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroFiniteDirectImageIso` — Stacks 0GJ1 for
  sheaves of `Λ`-modules, deduced from Stacks 0GJ1 for abelian sheaves.
* `Stacks.EtaleCohomology.exists_isOpenImmersion_isFinite_isPullback` — the diagram of Zariski's
  main theorem used in the proofs of Stacks 0GJH and 03SD, with `V = U ×_X Y`, and `Y` reduced
  when `V` is.
* `Stacks.EtaleCohomology.prop_of_relSeries` — a property closed under extensions passes along a
  finite filtration with the property on the successive quotients.

## Implementation notes

The named arguments are Theorem 03SC (`h03SC`), Lemma 0GJD (`h0GJD`) and Lemma 0GJ1 for abelian
sheaves (`h0GJ1`), the last one
stated on Mathlib's small étale site, which is where the sheaves of `Λ`-modules of this file live.
The form of 0GJ1 needed here, for sheaves of `Λ`-modules, is derived from the abelian one in
`etaleModuleExtensionByZeroFiniteDirectImageIso`: extension by zero and direct image are
`Λ`-linear and commute with forgetting the module structure, so a natural isomorphism of the
abelian functors commutes with the scalars and lifts.

Lemma 0GJ0 is `Stacks.EtaleCohomology.exists_finiteEtale_primeToEll_constantModuleFiltration`.
Nothing here carries a `@[stacks]` attribute, because of the
named arguments above.

## References

* [Stacks Project, Tag 0GJH](https://stacks.math.columbia.edu/tag/0GJH)
* [Stacks Project, Tag 0GJ0](https://stacks.math.columbia.edu/tag/0GJ0)
* [Stacks Project, Tag 0GJ1](https://stacks.math.columbia.edu/tag/0GJ1)
* [Stacks Project, Tag 03SH](https://stacks.math.columbia.edu/tag/03SH)
* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

section Linear

variable (Λ : Type r) [CommRing Λ]

/-- Restriction of sheaves of `Λ`-modules along an étale morphism is `Λ`-linear. -/
instance etaleModuleRestriction_linear {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleModuleRestriction.{u, r} Λ j).Linear Λ where
  map_smul _ _ := rfl

/-- Extension by zero of sheaves of `Λ`-modules is `Λ`-linear, being left adjoint to the linear
restriction functor. -/
instance etaleModuleExtensionByZero_linear {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleModuleExtensionByZero.{u, r} Λ j).Linear Λ :=
  AlgebraicGeometry.leftAdjoint_linear_of_rightAdjoint_linear Λ
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j)

end Linear

section Geometry

end Geometry

section Sheaves

variable (Λ : Type r) [CommRing Λ]

end Sheaves

section Filtration

end Filtration

section FinitePushforward

variable (Λ : Type r) [CommRing Λ] {U X V Y : Scheme.{u}} (j' : V ⟶ Y) (f : V ⟶ U)
  (fb : Y ⟶ X) (j : U ⟶ X) [Etale j] [Etale j']

end FinitePushforward

section Unibranch

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

end Unibranch

end Stacks.EtaleCohomology

end
