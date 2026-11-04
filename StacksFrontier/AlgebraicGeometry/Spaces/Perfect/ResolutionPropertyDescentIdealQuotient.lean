module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDescentSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators

/-!
# The direct image of the ideal of the situation, over a Noetherian algebraic space

In the situation of Stacks 0GUY — a quasi-compact and quasi-separated algebraic space `X` over a
scheme `S`, an affine surjective étale chart `φ : V → X` factored as an open immersion
`j : V → Y` followed by a finite morphism `π : Y → X`, and a finite type quasi-coherent sheaf of
ideals `ℐ ⊆ 𝒪_Y` cutting out the complement of `j(V)` — Stacks 0GV0 asserts, for `X` Noetherian,
that `X` has the resolution property **if and only if** `π_*ℐ` is the quotient of a finite
locally free `𝒪_X`-module.

This file proves the direction from the resolution property: the module `π_*ℐ` is coherent,
hence a finite type quasi-coherent module, so the resolution property of `X` exhibits it as a
quotient of a finite locally free module.  The converse and the equivalence are
`AlgebraicGeometry.Space.hasResolutionProperty_of_exists_epi_modulePushforwardIdeal` and
`AlgebraicGeometry.Space.hasResolutionProperty_iff_exists_epi_modulePushforwardIdeal`.

## Main results

* `AlgebraicGeometry.Space.isCoherent_modulePushforwardIdeal`: the first sentence of the proof of
  Stacks 0GV0 — in the situation of Stacks 0GUY with `X` Noetherian, the direct image `π_*ℐ` of
  the chosen sheaf of ideals along the finite morphism `π` is a coherent `𝒪_X`-module.
* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_epi_modulePushforwardIdeal`:
  **Stacks 0GV0**, the direction from the resolution property.  If `X` has the resolution
  property then there are a finite locally free `𝒪_X`-module `E` and an epimorphism
  `E ⟶ π_*ℐ`.

## Implementation notes

Coherence of `π_*ℐ` is Stacks 07UH (Cohomology of Spaces, Lemma 69.12.9), whose coherence clause
for a finite morphism is `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite'`; it
needs a coherent module on `Y` and a locally Noetherian `X`.  `Y` is locally Noetherian because
`π` is finite, hence locally of finite type
(`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isFinite`), and local Noetherianity passes to
the source of a morphism locally of finite type by Stacks 04ZK
(`AlgebraicGeometry.Space.isLocallyNoetherian_of_isLocallyOfFiniteType`).  Over that `Y` the
sheaf of ideals `ℐ`, which the situation gives as quasi-coherent and of finite type, is coherent:
quasi-coherence supplies the base change property of its sections between affine charts
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`), and on a locally
Noetherian space a module with that property and of finite type is coherent on the small étale
ringed site by the implication (2) ⟹ (1) of Stacks 07UB
(`AlgebraicGeometry.Space.isCoherentOnSite_of_isCartesian_of_isLocallyNoetherian`).

The hypothesis that `X` is Noetherian is `AlgebraicGeometry.Space.IsNoetherian` of Stacks 03EA;
since `AlgebraicGeometry.Space.ResolutionPropertyDescentSituation` already has `X`
quasi-compact and quasi-separated, only its local Noetherianity is used.

## References

* [Stacks Project, Tag 0GV0](https://stacks.math.columbia.edu/tag/0GV0), Lemma 76.56.3.
* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY), Situation 76.56.1.
* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ), Lemma 76.56.2, the
  input to the converse direction.
* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS), the resolution
  property of an algebraic space.
* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH), coherence of the direct
  image along a finite morphism.
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA), Noetherian algebraic
  spaces.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

variable (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- The finite morphism `π : Y → X` of the situation of Stacks 0GUY, as a morphism of the
category of algebraic spaces over `S`. -/
abbrev ResolutionPropertyDescentSituation.piHom : D.Y ⟶ X := ObjectProperty.homMk D.π

/-- The direct image `π_*ℐ` of the sheaf of ideals of the situation of Stacks 0GUY along its
finite morphism `π`, as an `𝒪_X`-module. -/
noncomputable abbrev modulePushforwardIdeal : Modules.{u, u} B S hS X.1 X.2 :=
  (modulePushforward B S hS (D.piHom B S hS hZ X hqc hqs)).obj D.I.toSheafOfModules

/-- **The first sentence of the proof of Stacks 0GV0.**  In the situation of Stacks 0GUY with
`X` Noetherian, the direct image `π_*ℐ` of the chosen finite type quasi-coherent sheaf of ideals
along the finite morphism `π` is a coherent `𝒪_X`-module. -/
theorem isCoherent_modulePushforwardIdeal (hX : IsNoetherian B S hS hZ X.1) :
    IsCoherent B S hS X.1 X.2 (modulePushforwardIdeal B S hS hZ X hqc hqs D) := by
  have hYN : HasEtaleLocalProperty B S hS D.Y.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS D.Y.2 X.2 D.π
      (isLocallyOfFiniteType_of_isFinite B S hS D.Y.2 X.2 D.isFinite_π) hX.2.2
  have : Fact (HasEtaleLocalProperty B S hS D.Y.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hYN⟩
  have hIcoh : SheafOfModules.IsCoherentOnSite D.I.toSheafOfModules :=
    isCoherentOnSite_of_isCartesian_of_isLocallyNoetherian B S hS D.Y.1 D.Y.2
      D.I.toSheafOfModules
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS D.Y.1 D.Y.2
        D.I.toSheafOfModules D.isFiniteTypeQuasicoherent_I.1)
      (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite
        D.I.toSheafOfModules D.isFiniteTypeQuasicoherent_I.2)
  exact isCoherent_modulePushforward_of_isFinite' B S hS
    (D.piHom B S hS hZ X hqc hqs) D.isFinite_π hX.2.2 D.I.toSheafOfModules
    ((isCoherent_iff_isCoherentOnSite B S hS D.Y.1 D.Y.2 D.I.toSheafOfModules).2 hIcoh)

/-- **Stacks 0GV0, the direction from the resolution property.**  In the situation of
Stacks 0GUY with `X` Noetherian, if `X` has the resolution property then `π_*ℐ` is the quotient
of a finite locally free `𝒪_X`-module: there are a finite locally free `𝒪_X`-module `E` and an
epimorphism `E ⟶ π_*ℐ`. -/
@[stacks 0GV0 "the direction from the resolution property: `π_*ℐ` is coherent by Stacks 07UH, \
so the resolution property of the Noetherian `X` exhibits it as the quotient of a finite \
locally free module.  The converse direction is not claimed; its input Stacks 0GUZ, the powers \
`ℐ^n` of a quasi-coherent sheaf of ideals on an algebraic space, and the closure of finite \
local freeness under tensor powers and finite direct sums are all absent from the library, as \
the module documentation records"]
theorem exists_isFiniteLocallyFreeOnSite_epi_modulePushforwardIdeal
    (hX : IsNoetherian B S hS hZ X.1)
    (hRP : HasResolutionProperty.{u, u} B S hS X.1 X.2) :
    ∃ (E : Modules.{u, u} B S hS X.1 X.2)
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ modulePushforwardIdeal B S hS hZ X hqc hqs D), Epi p := by
  have hcoh := isCoherent_modulePushforwardIdeal B S hS hZ X hqc hqs D hX
  have : SheafOfModules.IsFiniteTypeOnSite
      (modulePushforwardIdeal B S hS hZ X hqc hqs D) :=
    Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType
      (modulePushforwardIdeal B S hS hZ X hqc hqs D)
      hcoh.toIsCoherentOnSite.isFiniteType
  exact hRP.exists_finiteLocallyFree_quotient ⟨_, hcoh.toIsQuasicoherentOnSite⟩

end AlgebraicGeometry.Space

end
