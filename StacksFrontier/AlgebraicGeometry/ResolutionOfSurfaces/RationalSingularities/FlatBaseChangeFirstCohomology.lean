module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CohomologyModelBridge
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity

/-!
# Flat base change of the first higher direct image to a local ring

Let `g : X' ⟶ X` be proper, `x ∈ X`, and `Y` the base change of `g` along the flat morphism
`Spec 𝒪_{X, x} ⟶ X`. If `R¹g_*𝒪_{X'} = 0` then `H¹(Y, 𝒪_Y) = 0`: by [Stacks, Tag 02KH] (1) the
first higher direct image of `𝒪_Y` along `Y ⟶ Spec 𝒪_{X, x}` is the pullback of `R¹g_*𝒪_{X'}`,
hence zero, and over the affine base `Spec 𝒪_{X, x}` its global sections are `H¹(Y, 𝒪_Y)`
([Stacks, Tag 01XK]). This is `AlgebraicGeometry.FlatBaseChangeFirstCohomologyVanishing`.

## Main results

* `AlgebraicGeometry.flatBaseChangeFirstCohomologyVanishing`.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry


/-- **Flat base change for `R¹` to the spectrum of a local ring.** -/
theorem flatBaseChangeFirstCohomologyVanishing : FlatBaseChangeFirstCohomologyVanishing.{u} := by
  intro X X' Y x g p q hsq hg hR1
  have : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  have : IsProper p := MorphismProperty.of_isPullback hsq hg
  have : QuasiCompact g := inferInstance
  have : QuasiSeparated g := inferInstance
  let : HasDerivedCategory X.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory X'.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory Y.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory (Spec (X.presheaf.stalk x)).Modules := HasDerivedCategory.standard _
  have hR1' : IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus 1).obj
      (SheafOfModules.unit X'.ringCatSheaf)) :=
    (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).1 hR1
  have e := Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso hsq
    (SheafOfModules.unit X'.ringCatSheaf) 1
  have h1 := (@Functor.map_isZero _ _ _ _ _ _
    (RingedSpaceModuleAdjunction.modulePullback (X.fromSpecStalk x).toLRSHom.toShHom)
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (RingedSpaceModuleAdjunction.modulePullback_additive _)) _ hR1').of_iso e.symm
  have h2 : IsZero (((Scheme.Modules.pushforward p).rightDerivedPlus 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)) :=
    h1.of_iso (((Scheme.Modules.pushforward p).rightDerivedPlus 1).mapIso
      (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso q.toLRSHom.toShHom)).symm
  have h3 := ((Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward
    p 1).app ⟨SheafOfModules.unit Y.ringCatSheaf, inferInstance⟩)
  have h4 := (Functor.map_isZero
    (Stacks.Cohomology.AffineBase.moduleGlobalSections (Spec (X.presheaf.stalk x))) h2).of_iso h3
  refine (isZeroFirstStructureSheafCohomology_iff_isZero_firstCohomologyStructureSheaf Y).2 ?_
  rw [ModuleCat.isZero_iff_subsingleton] at h4 ⊢
  exact h4

end AlgebraicGeometry
