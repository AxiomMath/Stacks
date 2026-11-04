module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.Opposite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticModelTransport
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Module.Matlis
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.ExactFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.GeneralSupports.SupportedDerivedCategory
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.SupportedModulesComparison

/-!
# The bounded-below derived category of modules with support

Let `A` be a Noetherian ring and `T ⊆ Spec(A)` a subset stable under specialization. The
`A`-modules supported in `T` form a Serre subcategory `Mod_{A,T}` of `Mod_A` (Tag 0EEZ), and this
file proves that the canonical comparison
$$ D^{+}(\mathrm{Mod}_{A,T}) \longrightarrow D^{+}_{T}(A) $$
onto the bounded-below complexes of `A`-modules whose cohomology is supported in `T` is an
equivalence.

The argument runs through the dual statement. Tag 0FCL gives the corresponding comparison
`D⁻(ℬ) ⥤ D⁻_ℬ(𝒜)` for a Serre class `ℬ` in an abelian category `𝒜`, provided every epimorphism
onto an object of `ℬ` is covered by an object of `ℬ`. Applying it to the opposite category turns
that covering condition into a *monomorphism* condition: every module supported in `T` must embed
into an object of `Mod_{A,T}` that is injective as an `A`-module. This is exactly what Matlis
theory supplies, via `Stacks.LocalCohomology.exists_injective_supported_envelope`: the sections
with support in `T` of an injective hull are injective and supported in `T`. Transporting the
resulting equivalence back along the derived opposite equivalence
(`DerivedCategory.derivedOpEquivalence`) gives the bounded-below statement.

## Main results

* `Stacks.LocalCohomology.supportedModulesDerivedPlusEquivalence` — the equivalence
  `D^+(Mod_{A,T}) ≌ D^+_T(A)`.
* `Module.exists_supportedModulesDerivedPlusEquivalence` — the same equivalence
  together with the identification of its underlying functor, after inclusion into `D(A)`, with
  the functor induced by the inclusion of the Serre subcategory.

## Implementation notes

The target is expressed using `DerivedCategoryB.derivedCategoryBPlus`. The natural isomorphism in
the conclusion pins the equivalence to the canonical functor induced by the inclusion of the Serre
subcategory, rather than merely asserting an abstract equivalence of categories.

## References

* [Stacks Project, Tag 0EF2](https://stacks.math.columbia.edu/tag/0EF2)
* [Stacks Project, Tag 0FCL](https://stacks.math.columbia.edu/tag/0FCL)
* [Stacks Project, Tag 0EEZ](https://stacks.math.columbia.edu/tag/0EEZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The opposite Serre class

Everything needed to apply the bounded-above comparison of Tag 0FCL in the opposite category:
the opposite property is a Serre class closed under finite products, its inclusion is exact, and
epimorphisms into it are covered — the last being the Matlis-theoretic input. -/

attribute [local instance] Module.supportProperty_op_isSerre


/-! ### The equivalence -/

/-- **Stacks Project, Tag 0EF2.** For a specialization-closed subset `T` of the spectrum of a
Noetherian ring `A`, the bounded-below derived category of `A`-modules supported in `T` is
equivalent to the bounded-below derived category of complexes of `A`-modules whose cohomology is
supported in `T`.

The compatibility of this equivalence with the canonical comparison functor is
`Module.exists_supportedModulesDerivedPlusEquivalence`. -/
@[no_expose]
def supportedModulesDerivedPlusEquivalence (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T) :
    DerivedCategory.Plus (ModulesSupportedIn.{u, v} A T) ≌
      (DerivedCategoryB.derivedCategoryBPlus
        (supportModuleProperty.{u, v} A T)).FullSubcategory :=
  ((Module.supportedPlusOpEquivalence.{u, v} (R := A) T).trans
    ((Module.supportedMinusComparisonEquivalence.{u, v} (R := A) T hT).trans
      (Module.supportedDerivedPlusOpEquivalence.{u, v} (R := A) T).symm)).unop

end Stacks.LocalCohomology
