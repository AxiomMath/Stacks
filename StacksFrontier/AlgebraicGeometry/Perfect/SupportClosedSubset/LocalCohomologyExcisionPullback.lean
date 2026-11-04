module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonSourceNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonTransitivity
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologyExcisionCounit
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySheafExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.RightDerivedCompIsoTargetCongr
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyExcision

/-!
# Excision for sections with support: the pullback spelling is the restriction spelling

The project carries excision for the subsheaf of sections with support, and excision for its
right derived functors, in **two spellings of one functor**: along the abstract pullback
`RingedSpaceModuleAdjunction.modulePullback` of the ringed-space inclusion of an open
subscheme, and along `AlgebraicGeometry.Scheme.Modules.restrictFunctor` of the inclusion of that
open subscheme.  The two functors are identified by
`Stacks.Gysin.modulePullbackRestrictFunctorIso`, but neither excision had been carried across
that identification; the implementation notes of
`Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcision` record the degree-zero half
of that as open, "what stands in the way is the spelling".  This file closes both halves.

## Main results

* `supportedSectionsRestrictNatIso_hom_app_modulePullback`: **degree zero.**  The excision
  `Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso` along the abstract
  pullback and the excision
  `Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso` along
  `restrictFunctor` correspond under `Stacks.Gysin.modulePullbackRestrictFunctorIso`.
* `supportedSectionsRestrictNatIso_eq_pullback`: the same, as an equality of natural
  isomorphisms with a common target, which is the shape
  `Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_congr` consumes.

## Implementation notes

**Degree zero is a cancellation of one monomorphism.**  Both comparisons are pinned down by
their compatibility with the inclusion of the subsheaf into the coefficient module — on the
`restrictFunctor` side that is
`Stacks.Cohomology.SupportedComplexes.supportedSectionsRestrictNatIso_hom_app_ι`, which is the
`choose_spec` of `Stacks.Perfect.SupportedSectionsRestriction`
`.exists_supportedSectionsRestrictIso`, and on the pullback side
`Stacks.Cohomology.SupportedComplexes`'s
`supportedSectionsPullbackNatIso_hom_comp_supportedSectionsι` — and that inclusion is a
monomorphism (`Stacks.SheafOfModules.SupportedSections.supportedSectionsSheafι_mono`).
So the square
commutes after composing with it, and the two remaining steps are the naturality of the
inclusion and the naturality of the identification of the two spellings.

**What is *not* here: the same crossing in every degree.**  The classical degree-`n` excision
along the abstract pullback is
`Stacks.Cohomology.SupportedComplexes.supportedSectionsRightDerivedPullbackNatIso`, and it is
*not* identified here with `localCohomologyRestrictNatIso`.  The mathematics of that is three
naturality statements of the library —
`Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_congr` for the first factor at the
common target `restrictFunctor ⋙ H_{W ∩ T}` (which is what
`supportedSectionsPullbackRestrictTargetIso` is for),
`Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app` to move that target, and
`Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app_natTrans_exact` for the
second factor — with `supportedSectionsRestrictNatIso_eq_pullback` as the degree-zero input.
What stands in the way is not mathematics but the two spellings of the category of modules on
`W`: a statement mixing `supportedSectionsOn` with `modulePullback` elaborates at a spelling in
which neither functor's recorded `CategoryTheory.Functor.Additive` instance is found.

**No `@[stacks ...]` attribute is attached**: this is a passage between two spellings of one
construction, not the statement of a tag, exactly as for
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso` itself.

## References

* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections

universe u

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

namespace Stacks.Perfect.LocalCohomologyExcision

/-! ### Cancelling the inclusion of the subsheaf -/

/-- A square of four morphisms into a common object, two of whose sides are computed after
composing with a monomorphism.  Stated at an arbitrary category with the objects implicit and the
morphisms explicit, so that it applies by a single `exact`: at the categories of sheaves of
modules below the two spellings of the category of modules on the open subscheme are
definitionally but not syntactically equal, and `rw` is not usable across them. -/
private theorem mono_square {C : Type*} [Category* C] {a b c d g : C}
    (l : a ⟶ b) (r : b ⟶ c) (p : a ⟶ d) (s : d ⟶ c) (m : c ⟶ g) (t : b ⟶ g) (v : d ⟶ g)
    (hm : Mono m) (hr : r ≫ m = t) (hs : s ≫ m = v) (h : l ≫ t = p ≫ v) :
    l ≫ r = p ≫ s := by
  refine (cancel_mono m).1 ?_
  rw [Category.assoc, Category.assoc, hr, hs, h]

/-- Two naturality squares pasted, in the shape the degree-zero crossing produces them: the
compatibility of the comparison with the inclusion, followed by the naturality of the
identification of the two spellings.  Stated at an arbitrary category with the objects implicit
and the morphisms explicit. -/
private theorem paste_two {C : Type*} [Category* C] {a b c d g : C}
    (x : a ⟶ b) (t : b ⟶ g) (p : a ⟶ d) (i : d ⟶ c) (lam : c ⟶ g) (mi : a ⟶ c)
    (hA : p ≫ i = mi) (hB : mi ≫ lam = x ≫ t) : x ≫ t = p ≫ i ≫ lam := by
  rw [← Category.assoc, hA, hB]

variable {Y : Scheme.{u}} (T : Set Y) (W : Y.Opens)

/-! ### Degree zero -/

/-- **Degree-zero excision for sections with support: the two spellings of the restriction
agree.**  The comparison `H_T(ℱ)|_W ≅ H_{W ∩ T}(ℱ|_W)` built along the abstract pullback
`Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso` and the one built along
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`
(`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso`) correspond under
`Stacks.Gysin.modulePullbackRestrictFunctorIso`.

Both are compatible with the inclusion of the subsheaf into the restriction of the coefficient
module, and that inclusion is a monomorphism, so the square commutes. -/
theorem supportedSectionsRestrictNatIso_hom_app_modulePullback (M : Y.Modules) :
    (Stacks.Gysin.modulePullbackRestrictFunctorIso W).hom.app
          ((supportedSectionsOn Y T).obj M) ≫
        (supportedSectionsRestrictNatIso T W).hom.app M =
      (supportedSectionsPullbackNatIso
            (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T).hom.app M ≫
        (supportedSectionsOn W.toScheme (W.ι ⁻¹' T)).map
          ((Stacks.Gysin.modulePullbackRestrictFunctorIso W).hom.app M) := by
  refine mono_square _ _ _ _
    (supportedSectionsSheafι (W.ι ⁻¹' T) ((Scheme.Modules.restrictFunctor W.ι).obj M))
    ((Scheme.Modules.restrictFunctor W.ι).map (supportedSectionsSheafι T M))
    (supportedSectionsSheafι (W.ι ⁻¹' T)
        ((modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj M) ≫
      (Stacks.Gysin.modulePullbackRestrictFunctorIso W).hom.app M)
    (supportedSectionsSheafι_mono _ _)
    (supportedSectionsRestrictNatIso_hom_app_ι T W M)
    (supportedSectionsSheafι_naturality (W.ι ⁻¹' T)
      ((Stacks.Gysin.modulePullbackRestrictFunctorIso W).hom.app M)) ?_
  exact paste_two _ _ _ _ _
    ((modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).map
      (supportedSectionsSheafι T M))
    (supportedSectionsPullbackNatIso_hom_comp_supportedSectionsι
      (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T M)
    ((Stacks.Gysin.modulePullbackRestrictFunctorIso W).hom.naturality
      (supportedSectionsSheafι T M))

/-- **Degree-zero excision along the abstract pullback, with its target moved to the
`restrictFunctor` spelling.**  This is the comparison
`Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso` followed by the
identification of the two spellings, so that it has the same target as
`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso`.  Having the two
comparisons at one target is what lets
`Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_congr`, which fixes the target, be
applied to them. -/
def supportedSectionsPullbackRestrictTargetIso :
    supportedSectionsOn Y T ⋙ modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) ≅
      Scheme.Modules.restrictFunctor W.ι ⋙ supportedSectionsOn W.toScheme (W.ι ⁻¹' T) :=
  supportedSectionsPullbackNatIso (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T ≪≫
    Functor.isoWhiskerRight (Stacks.Gysin.modulePullbackRestrictFunctorIso W)
      (supportedSectionsOn W.toScheme (W.ι ⁻¹' T))

/-- The components of `supportedSectionsPullbackRestrictTargetIso`, factor by factor. -/
theorem supportedSectionsPullbackRestrictTargetIso_hom_app (M : Y.Modules) :
    (supportedSectionsPullbackRestrictTargetIso T W).hom.app M =
      (supportedSectionsPullbackNatIso
            (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T).hom.app M ≫
        (supportedSectionsOn W.toScheme (W.ι ⁻¹' T)).map
          ((Stacks.Gysin.modulePullbackRestrictFunctorIso W).hom.app M) := rfl

/-- **The two degree-zero excisions, at one target.**  The identification of the two spellings of
the restriction carries `supportedSectionsRestrictNatIso` to
`supportedSectionsPullbackRestrictTargetIso`; this is
`supportedSectionsRestrictNatIso_hom_app_modulePullback` in the shape the hypothesis `hα` of
`Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_congr` asks for. -/
theorem supportedSectionsRestrictNatIso_eq_pullback (M : Y.Modules) :
    (Stacks.Gysin.modulePullbackRestrictFunctorIso W).hom.app
          ((supportedSectionsOn Y T).obj M) ≫
        (supportedSectionsRestrictNatIso T W).hom.app M =
      (supportedSectionsPullbackRestrictTargetIso T W).hom.app M :=
  supportedSectionsRestrictNatIso_hom_app_modulePullback T W M

end Stacks.Perfect.LocalCohomologyExcision

end
