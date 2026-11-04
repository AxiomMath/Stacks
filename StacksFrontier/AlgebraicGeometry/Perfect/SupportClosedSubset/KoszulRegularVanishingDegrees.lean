module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyVanishingDegrees
public import StacksFrontier.RingTheory.Koszul.Defs

/-!
# Local cohomology along a locally Koszul-regular closed subset vanishes above its codimension

Let `X` be a scheme and let `Z ⊆ X` be a closed subset which can locally be cut out by a
Koszul-regular sequence of `c` elements of the structure sheaf.  Then the local cohomology
sheaves of a quasi-coherent `𝒪_X`-module `ℱ` vanish outside degree `c`.  Two parts of this are
proved here: the vanishing above degree `c`,

`ℋ ^i_Z(ℱ) = 0` for `i > c`,

and the vanishing in negative degrees, which needs none of the hypotheses,

`ℋ ^i_Z(ℱ) = 0` for `i < 0`.

The remaining range `0 ≤ i < c`, which needs both hypotheses, is
`LocalCohomologyDegrees.isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_lt`
in `StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.KoszulFlatVanishingLocal`, and the
whole of Stacks 0G7P is
`LocalCohomologyDegrees.isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_ne`.

Above degree `c` the Koszul-regularity of the local equations plays no role: a Koszul-regular
sequence of `c` elements is in particular a family of `c` elements, so `Z` is locally the common
zero locus of `c` sections of `𝒪_X`, and that is exactly the hypothesis of Stacks 0G7N.  Nor is
flatness of `ℱ` needed.

The complementary vanishing in degrees `i < c`
is a genuinely different argument: by Stacks 0G7M it asks, on an affine open `Spec A` on which
`Z` is cut out by a Koszul-regular sequence `f₁, …, f_c ∈ A`, for the vanishing below degree `c`
of the extended alternating Čech complex of `f` with coefficients in a flat module.

## How the `i < c` half goes

Its algebraic core is `Cech.cechComplex_homology_isZero_of_isKoszulRegular_of_flat`.  That is
*not* Stacks 0G6L on its own — 0G6L is the case of the coefficient module `A`; the flat case is
0G6L combined, through the degreewise identification `Čᵖ(M) ≅ M ⊗_A Čᵖ(A)` of Stacks 0G6H, with
the flatness of the coefficients.

The passage from there to the sheaf-level complex of Stacks 0G7I runs through
`Stacks.Perfect.AffineCechSections.complexIso`, which identifies the complex of sections over an
affine open with the algebraic extended alternating Čech complex of the restricted equations, and
`Stacks.Perfect.KoszulFlatVanishing.isZero_homology_derivedSupportedSections_of_lt`, which is the
global-equations case; the localization to the hypothesis used here is
`LocalCohomologyDegrees.isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_lt`.

One point of the hypothesis is worth recording, because the two halves read it differently.  The
`i < c` half needs Koszul-regularity on the affine opens, and the statement below places it in
the ring `Γ(U, 𝒪)` for an arbitrary open `U`.  For affine `U` the two agree, `Γ(U, 𝒪) → Γ(V, 𝒪)`
being flat so that
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegular_algebraMap_of_flat` applies; for a
general `U` regularity in the ring of sections of a possibly non-affine open does not restrict.
The whole-tag statement therefore asks for an *affine* open neighbourhood, which by Stacks 063G
is the source's own condition; the `i > c` half below needs no regularity at all and so keeps the
wider hypothesis.

The `@[stacks 0G7P]` attribute below is left on the `i > c` half deliberately: widening or
moving it is a decision for whoever holds 0G7P, and a second registration of the same tag
would itself be a defect.

## Main results

* `isZero_homology_derivedSupportedSections_of_locallyKoszulRegular`: the `i > c` half of
  **Stacks 0G7P**, at the wider hypothesis.
* `isZero_homology_derivedSupportedSections_of_neg`: the `i < 0` part of the `i < c` half of
  **Stacks 0G7P**, for an arbitrary module along an arbitrary closed subset.
* The whole of **Stacks 0G7P** is
  `LocalCohomologyDegrees.isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_ne`
  in `StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.KoszulFlatVanishingLocal`.

## References

* [Stacks Project, Tag 0G7P](https://stacks.math.columbia.edu/tag/0G7P)
* [Stacks Project, Tag 0G7N](https://stacks.math.columbia.edu/tag/0G7N)
* [Stacks Project, Tag 0G6H](https://stacks.math.columbia.edu/tag/0G6H)
* [Stacks Project, Tag 0G6L](https://stacks.math.columbia.edu/tag/0G6L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.Perfect.DerivedSupportedSectionsValue
  (isZero_homology_derivedSupportedSections_of_isZero)
open Stacks.SheafOfModules.SupportedSections (supportedSectionsFunctor)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.LocalCohomologyDegrees

attribute [local instance] HasDerivedCategory.standard

/-- **The vanishing above degree `c` in Stacks 0G7P.**  Let `X` be a scheme and let
`Z ⊆ X` be a closed subset which can locally be cut out by a Koszul-regular sequence of `c`
elements of the structure sheaf: every point of `X` has an open neighbourhood `U` carrying a
Koszul-regular sequence `f₁, …, f_c ∈ Γ(U, 𝒪)` whose common zero locus is the part of `Z` lying
in `U`.  Then the local cohomology sheaves of a quasi-coherent `𝒪_X`-module vanish above
degree `c`:

`ℋ ^i_Z(ℱ) = 0` for `i > c`.

Koszul-regularity of the local equations is not used: it is enough that there are `c` of them,
which is Stacks 0G7N.  Flatness of `ℱ`, which the source requires, is likewise unnecessary above
degree `c` and is omitted.  The companion vanishing in degrees `i < c` does need both, and is
`LocalCohomologyDegrees.isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_lt`
in `StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.KoszulFlatVanishingLocal`. -/
public theorem isZero_homology_derivedSupportedSections_of_locallyKoszulRegular {X : Scheme.{u}}
    (Z : Set X) (hZ : IsClosed Z) (c : ℕ)
    (hcut : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ f : Fin c → Γ(U.toScheme, ⊤),
      Koszul.IsKoszulRegular f ∧ U.ι ⁻¹' Z = equationsClosedSet f)
    (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : (c : ℤ) < i) :
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace Z))) i).obj
      ((derivedSupportedSectionsOnClosed X.toRingedSpace Z hZ).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F))) :=
  isZero_homology_derivedSupportedSections_of_locallyCutOut Z hZ c
    (fun x => (hcut x).imp fun _ h => ⟨h.1, h.2.imp fun _ hf => hf.2⟩) F i hi

/-- **Local cohomology sheaves vanish in negative degrees.**  The local cohomology
sheaves of *any* `𝒪_X`-module along *any* closed subset vanish in negative degrees:

`ℋ ^i_Z(ℱ) = 0` for `i < 0`.

This is the part of the `i < c` half of Stacks 0G7P that needs none of its conditions.  Sections
with support in `Z` is a left exact functor, so its right derived functor is computed on a
resolution of `ℱ` by injectives concentrated in non-negative degrees, and an additive functor
sends the zero objects in negative degrees to zero objects.  Neither the Koszul-regularity of
the local equations, nor the flatness of `ℱ`, nor its quasi-coherence plays any role, and all
three are omitted.

Together with `isZero_homology_derivedSupportedSections_of_locallyKoszulRegular` this covers every
degree outside `0 ≤ i < c`, and that range is
`LocalCohomologyDegrees.isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_lt`
in `StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.KoszulFlatVanishingLocal`, where the
whole of Stacks 0G7P is
`LocalCohomologyDegrees.isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_ne`. -/
public theorem isZero_homology_derivedSupportedSections_of_neg {X : Scheme.{u}}
    (Z : Set X) (hZ : IsClosed Z) (F : X.Modules) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace Z))) i).obj
      ((derivedSupportedSectionsOnClosed X.toRingedSpace Z hZ).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F))) := by
  classical
  obtain ⟨I, r, hr, hinj, hIGE⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      ((CochainComplex.singleFunctor X.Modules 0).obj F) 0
  have hKI : I.IsKInjective := @CochainComplex.isKInjective_of_injective _ _ _ I 0 hIGE hinj
  have hQr : IsIso (DerivedCategory.Q.map r) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ r).2 hr
  have eF : (DerivedCategory.singleFunctor X.Modules 0).obj F ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F ≪≫
      @asIso _ _ _ _ (DerivedCategory.Q.map r) hQr
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso
    ((derivedSupportedSectionsOnClosed X.toRingedSpace Z hZ).mapIso eF))
  refine isZero_homology_derivedSupportedSections_of_isZero X.toRingedSpace Z hZ I hKI i ?_
  set G := supportedSectionsFunctor X.toRingedSpace Z
  set K := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hzX : IsZero (K.X i) :=
    Functor.map_isZero G (CochainComplex.isZero_of_isStrictlyGE I 0 i hi)
  exact IsZero.of_epi (K.homologyπ i) (IsZero.of_mono (K.iCycles i) hzX)

end Stacks.Perfect.LocalCohomologyDegrees

end
