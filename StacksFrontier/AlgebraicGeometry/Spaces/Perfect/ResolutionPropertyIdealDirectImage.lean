module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDescentSituation
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel

/-!
# The direct image of the ideal sheaf of the situation on the resolution property

In the situation of Stacks 0GUY — a quasi-compact and quasi-separated algebraic space `X` over
a scheme `S`, an affine surjective étale chart `φ : V → X` factored as an open immersion
`j : V → Y` followed by a finite morphism `π : Y → X`, and a finite type quasi-coherent sheaf
of ideals `ℐ ⊆ 𝒪_Y` with `|V(ℐ)| = |Y| ∖ |j(V)|` — Stacks 0GV1 asserts that `X` has the
resolution property **if and only if** `π_*ℐ` is the quotient of a finite locally free
`𝒪_X`-module.

This file builds the `𝒪_X`-module `π_*ℐ` of that statement, shows it is quasi-coherent and of
finite type, and proves the implication that reads off those two facts: if `X` has the
resolution property then `π_*ℐ` is the quotient of a finite locally free `𝒪_X`-module.

## Main definitions

* `AlgebraicGeometry.Space.ResolutionPropertyDescentSituation.idealDirectImage` is the
  `𝒪_X`-module `π_*ℐ` of the situation, the direct image of `ℐ` along the finite morphism `π`.

## Main results

The results below live in the namespace
`AlgebraicGeometry.Space.ResolutionPropertyDescentSituation` of the situation of Stacks 0GUY.

* `isQuasicoherentOnSite_idealDirectImage` and `isFiniteTypeOnSite_idealDirectImage`: the
  module `π_*ℐ` is quasi-coherent and of finite type.
* `exists_isFiniteLocallyFreeOnSite_epi_idealDirectImage_of_hasResolutionProperty`: the
  implication of Stacks 0GV1 from the resolution property of `X` to `π_*ℐ` being the quotient
  of a finite locally free `𝒪_X`-module.

## Implementation notes

The direct image is the base-change spelling
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, the one in which Stacks 060Z is
stated in this development; it agrees with `AlgebraicGeometry.Space.modulePushforward` by
`AlgebraicGeometry.Space.modulePushforwardChartIso`.  The morphism `π` of the situation is a
map of the underlying presheaves, and the pushforward is indexed by a morphism of the category
of algebraic spaces, so `AlgebraicGeometry.Space.ResolutionPropertyDescentSituation.πHom`
names it as such; the two have the same underlying presheaf map, so every condition the
situation imposes on `π` transfers without a lemma.

Finite type of `π_*ℐ` is Stacks 060Z,
`AlgebraicGeometry.Space.isFiniteType_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite`,
which is stated for Mathlib's `SheafOfModules.IsFiniteType`, whereas the situation's ideal and
the resolution property are phrased with the categorical rendering
`SheafOfModules.IsFiniteTypeOnSite` of Stacks 03DL(5).  The two are compared by
`Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite` and
`Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType`.  Quasi-coherence of `π_*ℐ` is the
finite case `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallBaseChangeModulePushforward`.

### The converse implication of Stacks 0GV1 is not proved here

Stacks 0GV1 is an equivalence, and only the direction above is established; the `@[stacks]`
attribute records that scope.  The source proves the converse by reducing to the Noetherian
case, and none of the steps of that reduction is available:

* the Noetherian case itself, Stacks 0GV0, is not formalized, nor is the criterion Stacks 0GUZ
  it is proved from;
* writing `Y` as a limit of spaces finite and of finite presentation over `X` is Stacks 07VR;
* descending the closed subspace `V(ℐ)` and the surjection to a finite stage uses Stacks 0850
  and Stacks 084Z, and the closed subspace `V(ℐ)` is not formed in this development at all
  (only the point set `AlgebraicGeometry.Space.idealZeroLocus`, as the situation's own
  condition reflects);
* the affineness of the chart at a finite stage is Stacks 07SQ;
* absolute Noetherian approximation, Stacks 07SU, is in the library only in the form
  `AlgebraicGeometry.Space.hasNoetherianApproximation_of_isomorphicPresentation_limit`, which
  is not unconditional.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY)
* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
* [Stacks Project, Tag 060Z](https://stacks.math.columbia.edu/tag/060Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : AlgebraicSpaces B S hS}
    {hqc : IsQuasiCompactSpace B S hS X.1}
    {hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1}

namespace ResolutionPropertyDescentSituation

variable (sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- The finite morphism `π : Y ⟶ X` of the situation, read as a morphism of the category of
algebraic spaces over `S` rather than as the map of presheaves it is given as.  The underlying
presheaf map is `π` itself, so the conditions the situation imposes on `π` apply to it. -/
abbrev πHom : sit.Y ⟶ X := ObjectProperty.homMk sit.π

/-- **`π_*ℐ`.** The direct image along the finite morphism `π` of the situation of its sheaf of
ideals `ℐ ⊆ 𝒪_Y`, as an `𝒪_X`-module on the small étale site of `X`. -/
abbrev idealDirectImage : Modules.{u, u} B S hS X.1 X.2 :=
  (smallBaseChangeModulePushforward B S hS sit.πHom
      (relativelyRepresentable_hom_of_isFinite B S hS sit.πHom sit.isFinite_π)).obj
    sit.I.toSheafOfModules

/-- **`π_*ℐ` is quasi-coherent.**  The direct image along the finite morphism `π` of the
situation of its ideal sheaf `ℐ` is a quasi-coherent `𝒪_X`-module. -/
theorem isQuasicoherentOnSite_idealDirectImage :
    (idealDirectImage B S hS hZ sit).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_smallBaseChangeModulePushforward B S hS sit.πHom sit.isFinite_π
    sit.I.toSheafOfModules sit.isFiniteTypeQuasicoherent_I.1

/-- **`π_*ℐ` is of finite type.**  The direct image along the finite morphism `π` of the
situation of its ideal sheaf `ℐ` is an `𝒪_X`-module of finite type in the sense of
`SheafOfModules.IsFiniteTypeOnSite` (Stacks 03DL(5)); this is an instance of Stacks 060Z. -/
theorem isFiniteTypeOnSite_idealDirectImage :
    (idealDirectImage B S hS hZ sit).IsFiniteTypeOnSite :=
  Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _
    ((isFiniteType_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite B S hS sit.πHom
        sit.isFinite_π sit.I.toSheafOfModules sit.isFiniteTypeQuasicoherent_I.1).1
      (Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _
        sit.isFiniteTypeQuasicoherent_I.2))

/-- **Stacks 0GV1, the implication from the resolution property.**  In the situation of Stacks
0GUY, if the algebraic space `X` has the resolution property then `π_*ℐ` is the quotient of a
finite locally free `𝒪_X`-module. -/
@[stacks 0GV1 "the implication from the resolution property of `X` to `π_*ℐ` being the \
quotient of a finite locally free `𝒪_X`-module; the reverse implication, whose proof in the \
source reduces to the Noetherian case Stacks 0GV0, is not proved — see the module \
documentation for the inputs it needs"]
theorem exists_isFiniteLocallyFreeOnSite_epi_idealDirectImage_of_hasResolutionProperty
    (hX : HasResolutionProperty.{u, u} B S hS X.1 X.2) :
    ∃ (E : Modules.{u, u} B S hS X.1 X.2)
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (f : E ⟶ idealDirectImage B S hS hZ sit), Epi f := by
  have := isFiniteTypeOnSite_idealDirectImage B S hS hZ sit
  exact (hasResolutionProperty_iff B S hS X.1 X.2).mp hX
    (⟨idealDirectImage B S hS hZ sit, isQuasicoherentOnSite_idealDirectImage B S hS hZ sit⟩ :
      QuasicoherentSheaves.{u, u} B S hS X.1 X.2)

end ResolutionPropertyDescentSituation

end AlgebraicGeometry.Space

end
