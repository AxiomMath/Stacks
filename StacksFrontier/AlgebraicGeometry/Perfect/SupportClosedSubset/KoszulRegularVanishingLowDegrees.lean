module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ExtendedAlternatingCechAffineSections
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.KoszulRegularVanishingDegrees
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk

/-!
# Local cohomology along a locally Koszul-regular closed subset vanishes below its codimension

Let `X` be a scheme and let `Z ⊆ X` be a closed subset which can locally, on affine opens, be
cut out by a Koszul-regular sequence of `c` elements of the structure sheaf.  Then for a *flat*
quasi-coherent `𝒪_X`-module `ℱ` the local cohomology sheaves vanish below degree `c`:

`ℋ ^i_Z(ℱ) = 0` for `i < c`.

`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/KoszulRegularVanishingDegrees.lean`
proves the complementary half, `ℋ ^i_Z(ℱ) = 0` for `i > c`, where neither Koszul-regularity nor
flatness is needed.  Both hypotheses are needed here, and this is the half of **Stacks 0G7P**
that was missing.  Together the two give the vanishing in every degree other than `c`, which is
the full statement of the tag; the statements here are in fact proved for every `i ≠ c` at once,
so each of them alone already gives it.

## Main results

* `isZero_homology_derivedSupportedSections_of_ne`: the vanishing for a closed subset cut out by
  `c` Koszul-regular *global* equations on an *affine* scheme.
* `isZero_homology_derivedSupportedSections_of_locallyKoszulRegularFlat`: the vanishing when the
  local data at each point carries the flatness of the restricted module.

## Implementation notes

The route is the one the source takes, and almost all of it is already in the library.  By
Stacks 0G7M — `Stacks.Perfect.CechDerivedSupport.nonempty_cechIso_derivedSupportedSections`, an
isomorphism and not merely a vanishing — the object `i_* Rℋ_Z(ℱ)` is the extended alternating
Čech complex of the equations, so the question becomes the vanishing of the cohomology sheaves of
that complex; and `i_*` is exact and fully faithful, so it detects the vanishing.  That is
exactly how the `i > c` half is read off in
`Stacks.Perfect.CechDerivedSupport.isZero_homology_derivedSupportedSections_of_gt`, and the only
new input is the vanishing below degree `c`, which is
`Stacks.Perfect.CechAffineSections.extendedAlternatingCech_exactAt_of_isKoszulRegular_of_flat`.
In negative degrees the complex has zero terms, so no hypothesis is used there.

Globalisation is the cover argument of
`Stacks.Perfect.LocalCohomologyDegrees.isZero_homology_derivedSupportedSections_of_locallyCutOut`
(Stacks 0G7N), reused unchanged: a sheaf vanishes as soon as it vanishes on an open cover,
restriction of a K-injective resolution by injectives is again one, and
`Stacks.Perfect.SupportedSectionsRestriction.exists_supportedSectionsComplexRestrictIso`
identifies the restriction of the complex of supported sections with the complex of sections
supported on the preimage.

**Why the neighbourhoods are affine here.** The `i > c` half needs no affineness: its local input
is the vanishing of the terms of the Čech complex, which is a statement about the index type.
Below degree `c` the local input is a computation of the cohomology of the Čech complex, and the
only description of that complex available is on global sections of an affine, where it is the
algebraic complex of Stacks 0G6L.  Affineness of the neighbourhoods is not a restriction in
practice: the affine opens are a basis.

**Which flatness.** `Module.Flat Γ(U, 𝒪) Γ(ℱ, U)` on affine opens is what the local computation
consumes, and `AlgebraicGeometry.SheafOfModules.IsFlat` — flatness of every stalk over the
corresponding stalk of `𝒪_X`, Stacks 05NE — is what a consumer has; the two are connected by
Stacks 01U4, `AlgebraicGeometry.isFlatOver_tfae`, read for the identity morphism of `X`.  A
finite locally free module is flat in this sense, by
`AlgebraicGeometry.isFlat_of_isFiniteLocallyFree`.  No Noetherian hypothesis enters anywhere.

## References

* [Stacks Project, Tag 0G7P](https://stacks.math.columbia.edu/tag/0G7P)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G6L](https://stacks.math.columbia.edu/tag/0G6L)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechAffineSections
  (extendedAlternatingCech_exactAt_of_isKoszulRegular_of_flat)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.CechSupportRepresentation (mapHomologyIso)
open Stacks.Perfect.DerivedSupportedSectionsValue
open Stacks.Perfect.ExtendedAlternatingCech (extendedAlternatingCech)
open Stacks.Perfect.SupportedSectionsRestriction (exists_supportedSectionsComplexRestrictIso)
open Stacks.SheafOfModules.SupportedSections
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.LocalCohomologyDegrees

attribute [local instance] HasDerivedCategory.standard

/-! ### The Čech complex of a Koszul-regular sequence, in every degree other than its length -/

/-- On an affine scheme, the `ℤ`-indexed extension of the extended alternating Čech complex of a
Koszul-regular sequence with flat coefficients has vanishing cohomology sheaves in every degree
other than the length of the sequence.  In negative degrees the terms vanish; in degree `p ≥ 0`
this is the exactness of the `ℕ`-indexed complex. -/
private theorem isZero_homology_extend_of_ne {X : Scheme.{u}} [IsAffine X] {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (hf : Koszul.IsKoszulRegular f) (F : X.Modules)
    [F.IsQuasicoherent] [Module.Flat Γ(X, ⊤) Γ(F, ⊤)] (i : ℤ) (hi : i ≠ (c : ℤ)) :
    IsZero (((extendedAlternatingCech f F).complex.extend
      ComplexShape.embeddingUpNat).homology i) := by
  rcases lt_or_ge i 0 with hneg | hpos
  · exact (HomologicalComplex.ExactAt.of_isZero
      ((extendedAlternatingCech f F).complex.isZero_extend_X ComplexShape.embeddingUpNat i
        (by intro j; simp; omega))).isZero_homology
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = (p : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hpos).symm⟩
    exact ((HomologicalComplex.extend_exactAt_iff _ ComplexShape.embeddingUpNat (j := p) rfl).2
      (extendedAlternatingCech_exactAt_of_isKoszulRegular_of_flat f hf F p
        (fun h => hi (by exact_mod_cast h)))).isZero_homology

/-! ### Global equations on an affine scheme -/

/-- **The vanishing away from degree `c` for `c` Koszul-regular global equations on an affine
scheme.**  If `X` is affine, `f₁, …, f_c ∈ Γ(X, 𝒪_X)` is a Koszul-regular sequence, `Z` is their
common zero locus and `ℱ` is a quasi-coherent `𝒪_X`-module whose global sections are flat over
`Γ(X, 𝒪_X)`, then

`ℋ ^i_Z(ℱ) = 0` for every `i ≠ c`.

By Stacks 0G7M the object `i_* Rℋ_Z(ℱ)` is the extended alternating Čech complex of `f`; that
complex is acyclic away from degree `c`, and `i_*` is exact and fully faithful, so it detects the
vanishing. -/
public theorem isZero_homology_derivedSupportedSections_of_ne {X : Scheme.{u}} [IsAffine X]
    {c : ℕ} (f : Fin c → Γ(X, ⊤)) (hf : Koszul.IsKoszulRegular f) (F : X.Modules)
    [F.IsQuasicoherent] [Module.Flat Γ(X, ⊤) Γ(F, ⊤)] (i : ℤ) (hi : i ≠ (c : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace
            (equationsClosedSet f)))) i).obj
      ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
          (isClosed_equationsClosedSet f)).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F))) := by
  let _ := pushforward_preservesFiniteLimits X.toRingedSpace (equationsClosedSet f)
  let _ := pushforward_preservesFiniteColimits X.toRingedSpace (equationsClosedSet f)
    (isClosed_equationsClosedSet f)
  obtain ⟨e⟩ := Stacks.Perfect.CechDerivedSupport.nonempty_cechIso_derivedSupportedSections f F
  refine isZero_of_isZero_modulePushforward X.toRingedSpace (equationsClosedSet f)
    (isClosed_equationsClosedSet f) _ ?_
  refine IsZero.of_iso ?_ ((exactFunctorDerivedHomologyIso
    (modulePushforward (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))) i).app
      ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
        (isClosed_equationsClosedSet f)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F))).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors X.Modules i).app _)
  exact isZero_homology_extend_of_ne f hf F i hi

/-! ### Globalisation -/

/-- The vanishing of the cohomology of `ℛℋ_Z` transfers along an isomorphism in the derived
category. -/
private theorem isZero_homology_derivedSupportedSections_of_iso {X : Scheme.{u}} (Z : Set X)
    (hZ : IsClosed Z) (i : ℤ) {A B : DerivedCategory X.Modules} (e : A ≅ B)
    (h : IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace Z))) i).obj
      ((derivedSupportedSectionsOnClosed X.toRingedSpace Z hZ).obj B))) :
    IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace Z))) i).obj
      ((derivedSupportedSectionsOnClosed X.toRingedSpace Z hZ).obj A)) :=
  h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    ((derivedSupportedSectionsOnClosed X.toRingedSpace Z hZ).mapIso e))

/-- **The vanishing away from degree `c` for a closed subset locally cut out by a Koszul-regular
sequence**, with the flatness of the module supplied together with the local equations.  Every
point of `X` has an affine open neighbourhood `U` on which the part of `Z` lying in `U` is the
common zero locus of a Koszul-regular sequence of `c` sections of `𝒪_U` and on which the sections
of `ℱ` are flat over those of `𝒪_U`.  Then

`ℋ ^i_Z(ℱ) = 0` for every `i ≠ c`.

This is the globalisation of `isZero_homology_derivedSupportedSections_of_ne` by the cover
argument of Stacks 0G7N. -/
public theorem isZero_homology_derivedSupportedSections_of_locallyKoszulRegularFlat
    {X : Scheme.{u}} (Z : Set X) (hZ : IsClosed Z) (c : ℕ) (F : X.Modules)
    [F.IsQuasicoherent]
    (hcut : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ _ : IsAffine U.toScheme,
      ∃ f : Fin c → Γ(U.toScheme, ⊤), Koszul.IsKoszulRegular f ∧
        U.ι ⁻¹' Z = equationsClosedSet f ∧
        Module.Flat Γ(U.toScheme, ⊤) Γ((Scheme.Modules.restrictFunctor U.ι).obj F, ⊤))
    (i : ℤ) (hi : i ≠ (c : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace Z))) i).obj
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
  refine isZero_homology_derivedSupportedSections_of_iso Z hZ i eF ?_
  refine isZero_homology_derivedSupportedSections_of_isZero X.toRingedSpace Z hZ I hKI i ?_
  choose V hxV hVaff f hf hfZ hflat using hcut
  refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover V ?_ _ ?_
  · exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩
  intro x
  refine IsZero.of_iso ?_ (mapHomologyIso
    (Scheme.Modules.restrictFunctor (V x).ι)
    (((supportedSectionsFunctor X.toRingedSpace Z).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I) i).symm
  obtain ⟨e⟩ := exists_supportedSectionsComplexRestrictIso Z (V x) I
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).mapIso e)
  have hinj' : ∀ n, Injective
      ((((Scheme.Modules.restrictFunctor (V x).ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).X n) := fun n =>
    injective_restrictFunctor_obj (V x) (I.X n)
  have hKI' : CochainComplex.IsKInjective
      (((Scheme.Modules.restrictFunctor (V x).ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    @CochainComplex.isKInjective_of_injective _ _ _ _ 0 (isStrictlyGE_restrictFunctor (V x) I hIGE)
      hinj'
  have hZ' : IsClosed ((V x).ι ⁻¹' Z) := hZ.preimage (V x).ι.continuous
  refine isZero_homology_supportedSectionsComplex_of_isZero (V x).toScheme.toRingedSpace
    ((V x).ι ⁻¹' Z) hZ' _ hKI' i ?_
  have eI : DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor (V x).ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅
      (DerivedCategory.singleFunctor (V x).toScheme.Modules 0).obj
        ((Scheme.Modules.restrictFunctor (V x).ι).obj F) :=
    ((Scheme.Modules.restrictFunctor (V x).ι).mapDerivedCategoryFactors.app I).symm ≪≫
      (Scheme.Modules.restrictFunctor (V x).ι).mapDerivedCategory.mapIso eF.symm ≪≫
      ((Scheme.Modules.restrictFunctor (V x).ι).mapDerivedCategorySingleFunctor 0).app F
  refine isZero_homology_derivedSupportedSections_of_iso _ hZ' i eI ?_
  let := hVaff x
  let := hflat x
  revert hZ'
  rw [hfZ x]
  intro hZ'
  exact isZero_homology_derivedSupportedSections_of_ne (f x) (hf x)
    ((Scheme.Modules.restrictFunctor (V x).ι).obj F) i hi

/-! ### The flatness hypothesis in its global form -/

/-- On an affine open of a scheme, the sections of a flat quasi-coherent module are flat over the
sections of the structure sheaf.  This reads Stacks 01U4 for the identity morphism of `X`. -/
private theorem flat_sections_restrict_of_affine {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent]
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Flat Γ(U.toScheme, ⊤) Γ((Scheme.Modules.restrictFunctor U.ι).obj F, ⊤) := by
  have hstalk := (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf F).mp hflat
  have hself : AlgebraicGeometry.IsFlatOver ((𝟙 X : X ⟶ X).toLRSHom.toShHom) F := by
    intro x
    change @Module.Flat (X.presheaf.stalk ((𝟙 X : X ⟶ X).base x)) (F.presheaf.stalk x) _ _
      (Module.compHom _ ((𝟙 X : X ⟶ X).stalkMap x).hom)
    rw [Scheme.Hom.stalkMap_id]
    exact hstalk x
  have hle : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U := by simp
  have hres := AlgebraicGeometry.isFlatOver_resLE F hself U U hle
  have hid : (𝟙 X : X ⟶ X).resLE U U hle = 𝟙 U.toScheme :=
    (Scheme.Hom.resLE_id (X := X) (V := U) (V' := U) hle).trans (X.homOfLE_rfl U)
  rw [hid] at hres
  let : IsAffine U.toScheme := hU
  have hsections := ((AlgebraicGeometry.isFlatOver_tfae (𝟙 U.toScheme)
    ((Scheme.Modules.restrictFunctor U.ι).obj F)).out 1 2 rfl rfl).mp hres
      ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _) (by simp)
  convert hsections using 1
  apply Module.ext'
  intro a m
  have hone : ((𝟙 U.toScheme : U.toScheme ⟶ U.toScheme).appLE ⊤ ⊤ (by simp)) =
      𝟙 Γ(U.toScheme, ⊤) :=
    (Scheme.Hom.appLE_eq_app (𝟙 U.toScheme) (U := ⊤)).trans (Scheme.Hom.id_app ⊤)
  change a • m = (((𝟙 U.toScheme : U.toScheme ⟶ U.toScheme).appLE ⊤ ⊤ (by simp)).hom a) • m
  rw [hone]
  simp

end Stacks.Perfect.LocalCohomologyDegrees

end
