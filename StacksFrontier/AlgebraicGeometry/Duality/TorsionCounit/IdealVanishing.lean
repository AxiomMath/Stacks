module

public import StacksFrontier.AlgebraicGeometry.Duality.TorsionCounit.TorsionModule
public import StacksFrontier.AlgebraicGeometry.Duality.DivideByTorsion

/-!
# Higher ideal local cohomology of a torsion module vanishes

Let `I` be a finitely generated ideal of a Noetherian ring `A`. The functors `H^p_I` of
[Stacks, Tag 0AW0] are the cohomology modules of derived `I`-power torsion `RΓ_I`. For an
`I`-power-torsion module `N` the counit `RΓ_I(N) ⟶ N` is an isomorphism, by the module case of
part (1) of [Stacks, Tag 0955], so `H^p_I(N)` vanishes for `p ≠ 0`. Applied to the torsion
submodule `M[I^∞]` of an arbitrary module this is the `H^p_I` half of the higher-vanishing
assertion of Tag 0AW0.

This is the exact counterpart, for `H^p_I`, of the existing
`Stacks.Duality.supportLocalCohomology_torsion_higher` for `H^p_Z`. The two proofs have the
same shape — the relevant counit is invertible at a torsion module, so the value is the module
itself placed in degree zero — but the reasons differ: for `RΓ_Z` invertibility is formal, since
`RΓ_Z` is a coreflection onto the subcategory of objects with torsion cohomology, whereas for
`RΓ_I` the Noetherian hypothesis is indispensable. Over a non-Noetherian ring with `I` finitely
generated the counit `RΓ_I(N) ⟶ N` is not invertible at every `I`-power-torsion module `N`:
invertibility would make `Ext²_{D(I^∞-torsion)}(M, N) ⟶ Ext²_A(M, N)` bijective for every
`I`-power-torsion `M`, and part (3) of [Stacks, Tag 0A6P] exhibits a finitely generated ideal
for which it is not surjective. So the Noetherian hypothesis here, which the statement of Tag
0AW0 does not have, is not an artefact of this proof.

## Main results

* `Dualizing.TorsionCounit.idealLocalCohomology_isZero_of_isIPowerTorsion` — `H^p_I` of an
  `I`-power-torsion module vanishes for `p ≠ 0`.
* `Dualizing.TorsionCounit.idealLocalCohomology_torsion_higher` — the `H^p_I` higher-vanishing
  clause of [Stacks, Tag 0AW0]: `H^p_I(M[I^∞]) = 0` for `p > 0`.

## Implementation notes

No `@[stacks 0AW0]` attribute appears here. Seven of the tag's eight clause registrations are in
`StacksFrontier/RingTheory/Dualizing/TorsionQuotient.lean` and the eighth is in
`StacksFrontier/AlgebraicGeometry/Duality/DivideByTorsion.lean`; the conjunction of all eight,
which carries the tag whole, is `Stacks.Duality.localCohomology_divide_by_torsion` in the former.
Its `Stacks.Duality.idealLocalCohomology_torsion_higher` states this same clause with the same
hypotheses and carries the attribute for `part (1), higher cohomology of the torsion submodule`;
that file's module docstring records why the Noetherian hypothesis is there.

## References

* [Stacks Project, Tag 0AW0](https://stacks.math.columbia.edu/tag/0AW0)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 0A6P](https://stacks.math.columbia.edu/tag/0A6P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Dualizing.TorsionCounit

attribute [local instance] HasDerivedCategory.standard

/-- Ideal local cohomology of an `I`-power-torsion module is concentrated in degree zero: over a
Noetherian ring the counit `RΓ_I(N) ⟶ N` is invertible at such a module. -/
theorem idealLocalCohomology_isZero_of_isIPowerTorsion
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (N : ModuleCat.{max u v} A) (hN : IsIPowerTorsion A N I) (p : ℤ) (hp : p ≠ 0) :
    IsZero ((Stacks.Duality.idealLocalCohomology.{u, v} A I hI p).obj N) := by
  set P := derivedPowerTorsionProperty A I hI with hP
  set X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N with hX
  have hiso : IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app X) :=
    isIso_derivedPowerTorsionCounit_app_singleFunctor.{u, v} A I hI N hN
  have e : P.ι.obj ((powerTorsionComparison.{u, max u v} A I hI).obj
      ((derivedPowerTorsion.{u, v} A I hI).obj X)) ≅ X :=
    (powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI).app
        ((derivedPowerTorsion.{u, v} A I hI).obj X) ≪≫
      @asIso _ _ _ _ ((derivedPowerTorsionCounit.{u, v} A I hI).app X) hiso
  change IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) p).obj
    (P.ι.obj ((powerTorsionComparison.{u, max u v} A I hI).obj
      ((derivedPowerTorsion.{u, v} A I hI).obj X))))
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) p).mapIso e)
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) p).app
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj N))
  exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 N p hp

/-- **Higher ideal local cohomology of the `I`-power-torsion submodule vanishes.** This is the
`H^p_I` half of the higher-vanishing assertion of [Stacks, Tag 0AW0]. -/
theorem idealLocalCohomology_torsion_higher
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) (p : ℤ) (hp : 0 < p) :
    IsZero ((Stacks.Duality.idealLocalCohomology.{u, v} A I hI p).obj
      (ModuleCat.of A (Ideal.primaryComponent M I))) :=
  idealLocalCohomology_isZero_of_isIPowerTorsion.{u, v} A I hI _
    ((powerTorsionFunctor.{u, v} A I).obj M).property p hp.ne'

end Dualizing.TorsionCounit

end
