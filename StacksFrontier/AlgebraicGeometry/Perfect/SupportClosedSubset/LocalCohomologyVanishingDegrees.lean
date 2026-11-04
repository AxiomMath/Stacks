module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DerivedSupportInvertsAugmentation
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback

/-!
# Local cohomology vanishes above the number of local equations

Let `X` be a scheme and let `T ⊆ X` be a closed subset which can locally be cut out by at most
`c` elements of the structure sheaf.  Then the local cohomology sheaves of a quasi-coherent
`𝒪_X`-module vanish above degree `c`:

`ℋ ^i_T(ℱ) = 0` for `i > c`.

This is Stacks 0G7N.  The proof is the source's: `ℋ ^i_T(ℱ)` is computed on a K-injective
resolution `ℐ^•` of `ℱ` by injective modules, where it is the degree-`i` cohomology sheaf of the
explicit complex `ℋ_T(ℐ^•)`; a sheaf vanishes as soon as it vanishes on an open cover, and over
an open on which `T` is cut out by `c` global equations the restriction of `ℋ_T(ℐ^•)` is
`ℋ_{T ∩ U}(ℐ^•|_U)`, which is where Stacks 0G7M puts the extended alternating Čech complex and
so has no cohomology above degree `c`.

## Main results

* `isZero_homology_derivedSupportedSections_of_locallyCutOut`: **Stacks 0G7N**.
* `injective_restrictFunctor_obj`: restriction to an open subscheme preserves injective modules.

## Implementation notes

The source states Stacks 0G7N with a closed subset named `T` and then writes `ℋ ^i_Z`, a slip:
no `Z` is in scope, and its proof appeals to "the local description of `Rℋ_T(ℱ)`".  The
statement below is therefore about `T`, which is what the proof supports; the attribute records
the correction.

`Stacks.Perfect.DerivedSupportedSectionsValue.isZero_homology_derivedSupportedSections_of_isZero`
turns the tag into a statement about the complex `ℋ_T(ℐ^•)`, after which everything is a
question about sheaves on `X`: the cover criterion is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover`, restriction is
exact so it commutes with the formation of cohomology sheaves, and
`Stacks.Perfect.SupportedSectionsRestriction.exists_supportedSectionsComplexRestrictIso`
identifies the restriction of the subcomplex of supported sections with the subcomplex of
sections supported on the preimage.  The restricted resolution is again a resolution of `ℱ|_U`
by injectives, bounded below, hence K-injective, so the converse reduction
`isZero_homology_supportedSectionsComplex_of_isZero` applies on `U` and the global-equations case
`Stacks.Perfect.CechDerivedSupport.isZero_homology_derivedSupportedSections_of_gt` finishes.

## References

* [Stacks Project, Tag 0G7N](https://stacks.math.columbia.edu/tag/0G7N)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.Perfect.CechSupportRepresentation (mapHomologyIso)
open Stacks.Perfect.DerivedSupportedSectionsValue
open Stacks.Perfect.SupportedSectionsRestriction (exists_supportedSectionsComplexRestrictIso)
open Stacks.SheafOfModules.SupportedSections
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.LocalCohomologyDegrees

attribute [local instance] HasDerivedCategory.standard

/-- **Restriction to an open subscheme preserves injective modules** (Stacks 01E1), read on
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`. -/
public theorem injective_restrictFunctor_obj {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    [Injective M] : Injective ((Scheme.Modules.restrictFunctor U.ι).obj M) := by
  have hoi : SheafedSpace.IsOpenImmersion (X.toRingedSpace.ofRestrict U.isOpenEmbedding) :=
    inferInstance
  have hpi : Functor.PreservesInjectiveObjects
      (modulePullback (X.toRingedSpace.ofRestrict U.isOpenEmbedding)) :=
    Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects _
  have h : Injective ((Scheme.Modules.pullback U.ι).obj M) :=
    hpi.injective_obj (inferInstanceAs (Injective M))
  exact Injective.of_iso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm h

/-- The restriction of a complex bounded below by degree `0` is bounded below by degree `0`. -/
public theorem isStrictlyGE_restrictFunctor {X : Scheme.{u}} (U : X.Opens)
    (I : CochainComplex X.Modules ℤ) (hI : CochainComplex.IsStrictlyGE I 0) :
    CochainComplex.IsStrictlyGE
      (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact Functor.map_isZero (Scheme.Modules.restrictFunctor U.ι)
    (CochainComplex.isZero_of_isStrictlyGE I 0 n hn)

/-- Vanishing of the homology of the derived supported sections transfers along an isomorphism
in the derived category. -/
private theorem isZero_homology_derivedSupportedSectionsOnClosed_of_iso {X : Scheme.{u}}
    (T : Set X) (hT : IsClosed T) (i : ℤ) {A B : DerivedCategory X.Modules} (e : A ≅ B)
    (h : IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace T))) i).obj
      ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj B))) :
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace T))) i).obj
      ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj A)) :=
  h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).mapIso e))

/-- **Stacks Project, Tag 0G7N.**  Let `X` be a scheme and let `T ⊆ X` be a closed subset which
can locally be cut out by `c` elements of the structure sheaf.  Then the local cohomology sheaves
of a quasi-coherent `𝒪_X`-module vanish above degree `c`:

`ℋ ^i_T(ℱ) = 0` for `i > c`.

The hypothesis is that every point has an open neighbourhood `U` on which the part of `T` lying
in `U` is the common zero locus of `c` functions on `U`. -/
@[stacks 0G7N "stated for the closed subset T; the source writes ℋ^i_Z for it, a slip"]
public theorem isZero_homology_derivedSupportedSections_of_locallyCutOut {X : Scheme.{u}}
    (T : Set X) (hT : IsClosed T) (c : ℕ)
    (hcut : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ f : Fin c → Γ(U.toScheme, ⊤),
      U.ι ⁻¹' T = Stacks.Perfect.CechDerivedSupport.equationsClosedSet f)
    (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : (c : ℤ) < i) :
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace T))) i).obj
      ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj
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
  refine isZero_homology_derivedSupportedSectionsOnClosed_of_iso T hT i eF ?_
  refine isZero_homology_derivedSupportedSections_of_isZero X.toRingedSpace T hT I hKI i ?_
  choose V hxV f hf using hcut
  refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover V ?_ _ ?_
  · refine eq_top_iff.2 ?_
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩
  intro x
  refine IsZero.of_iso ?_ (mapHomologyIso
    (Scheme.Modules.restrictFunctor (V x).ι)
    (((supportedSectionsFunctor X.toRingedSpace T).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I) i).symm
  obtain ⟨e⟩ := exists_supportedSectionsComplexRestrictIso T (V x) I
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).mapIso e)
  -- the restricted resolution
  have hinj' : ∀ n, Injective
      ((((Scheme.Modules.restrictFunctor (V x).ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).X n) := fun n =>
    have : Injective (I.X n) := hinj n
    injective_restrictFunctor_obj (V x) (I.X n)
  have hIGE' := isStrictlyGE_restrictFunctor (V x) I hIGE
  have hKI' : CochainComplex.IsKInjective
      (((Scheme.Modules.restrictFunctor (V x).ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    @CochainComplex.isKInjective_of_injective _ _ _ _ 0 hIGE' hinj'
  have hT' : IsClosed ((V x).ι ⁻¹' T) := hT.preimage (V x).ι.continuous
  refine isZero_homology_supportedSectionsComplex_of_isZero (V x).toScheme.toRingedSpace
    ((V x).ι ⁻¹' T) hT' _ hKI' i ?_
  -- compare with the single complex on the open subscheme
  have eI : DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor (V x).ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅
      (DerivedCategory.singleFunctor (V x).toScheme.Modules 0).obj
        ((Scheme.Modules.restrictFunctor (V x).ι).obj F) :=
    ((Scheme.Modules.restrictFunctor (V x).ι).mapDerivedCategoryFactors.app I).symm ≪≫
      (Scheme.Modules.restrictFunctor (V x).ι).mapDerivedCategory.mapIso eF.symm ≪≫
      ((Scheme.Modules.restrictFunctor (V x).ι).mapDerivedCategorySingleFunctor 0).app F
  refine isZero_homology_derivedSupportedSectionsOnClosed_of_iso _ hT' i eI ?_
  -- the global-equations case on the open subscheme
  have key : ∀ (Z' : Set (V x).toScheme) (hZ' : IsClosed Z'),
      Z' = equationsClosedSet (f x) →
      IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace
            (V x).toScheme.toRingedSpace Z'))) i).obj
        ((derivedSupportedSectionsOnClosed (V x).toScheme.toRingedSpace Z' hZ').obj
          ((DerivedCategory.singleFunctor (V x).toScheme.Modules 0).obj
            ((Scheme.Modules.restrictFunctor (V x).ι).obj F)))) := by
    intro Z' hZ' hEq
    subst hEq
    exact Stacks.Perfect.CechDerivedSupport.isZero_homology_derivedSupportedSections_of_gt
      (f x) ((Scheme.Modules.restrictFunctor (V x).ι).obj F) i hi
  exact key _ hT' (hf x)

end Stacks.Perfect.LocalCohomologyDegrees

end
