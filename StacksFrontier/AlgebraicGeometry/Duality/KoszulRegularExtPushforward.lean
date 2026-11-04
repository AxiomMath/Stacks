module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.OpenIndependence
import all StacksFrontier.AlgebraicGeometry.RegularImmersion.OpenIndependence
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulRegularDerivedDual

/-!
# The cohomology sheaves of `R ℰom(𝒪_X, 𝒪_Y)` for a closed immersion, pushed forward

Let `i : X ⟶ Y` be a closed immersion of schemes with ideal sheaf `𝓘 ⊆ 𝒪_Y`, and let
`s : 𝒪_Y ⟶ J` be a K-injective resolution of `𝒪_Y` placed in degree zero. Sheaf Hom with exact
support applied termwise to `J` is a complex `ℰom(𝒪_X, J)` of `𝒪_X`-modules representing
`R ℰom(𝒪_X, 𝒪_Y)` ([Stacks, Tag 0A76]). This file identifies the pushforward of its cohomology
sheaves with the Ext sheaves on `Y` of [Stacks, Tag 0BQZ]:

`i_* Hⁿ(ℰom(𝒪_X, J)) ≅ 𝓔xtⁿ_{𝒪_Y}(𝒪_Y/𝓘, 𝒪_Y)`.

This is the step of the proof of [Stacks, Tag 0BR0] that reads "`a(𝒪_Y)` is an object of
`D_QCoh(𝒪_X)` whose pushforward to `Y` is `R𝓗om_{𝒪_Y}(i_*𝒪_X, 𝒪_Y)`" ([Stacks, Tags 0A9X and
0A77]) on cohomology sheaves.

## Main results

* `Stacks.Duality.KoszulRegular.cokernelDefiningIdealIso`: `𝒪_Y/𝓘 ≅ i_* 𝒪_X`.
* `Stacks.Duality.KoszulRegular.nonempty_pushforward_homology_iso_extInto`: the identification
  above.

## Implementation notes

The statements are about complexes and sheaves only; the derived categories used in the proof
are the standard models (`HasDerivedCategory.standard`), at which [Stacks, Tag 0A77] (in the form
`derivedSheafHomExactSupportPushforwardNatIso`) and the Ext sheaves `extInto` of [Stacks, Tag 0BQZ]
are stated. Nothing about the derived category leaks into the statements, so the result is
available at any other model, in particular at the locally small model where the right adjoint
`a` of [Stacks, Tag 0A9E] lives.

## References

* [Stacks Project, Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction HomologicalComplex

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality.KoszulRegular

open Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]

/-- **`𝒪_Y/𝓘 ≅ i_* 𝒪_X`** for a closed immersion `i : X ⟶ Y` with ideal sheaf `𝓘`: the map
`𝒪_Y ⟶ i_* 𝒪_X` is an epimorphism and `𝓘` is its kernel. Its body is not exposed: it is built
from the private `Stacks.AlgebraicGeometry.kernelQuotientIso_of_epi` of
`StacksFrontier.AlgebraicGeometry.RegularImmersion.OpenIndependence`, read through `import all`. -/
@[no_expose] def cokernelDefiningIdealIso :
    cokernel (definingIdealOfHom i).ι ≅
      (modulePushforward (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).obj
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) :=
  @Stacks.AlgebraicGeometry.kernelQuotientIso_of_epi _ _ _ _ _ _ _
    (AlgebraicGeometry.Scheme.Modules.epi_unitToPushforwardObjUnit i)

/-- The structure sheaf `𝒪_Y` placed in degree zero, written over the sheaf of rings of the closed
quotient attached to `i`, the spelling in which sheaf Hom with exact support is stated. -/
abbrev structureComplex :
    CochainComplex (SheafOfModules.{u}
      (structureSheafRing (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X)) ℤ :=
  (single _ (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit
      (structureSheafRing (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X))

open Stacks.SheafOfModules in
/-- **`i_* Hⁿ(ℰom(𝒪_X, J)) ≅ 𝓔xtⁿ_{𝒪_Y}(𝒪_Y/𝓘, 𝒪_Y)`.** For a closed immersion `i : X ⟶ Y`
with ideal sheaf `𝓘` and a K-injective resolution `s : 𝒪_Y ⟶ J`, the pushforward of the
cohomology sheaves of the termwise sheaf Hom with exact support `ℰom(𝒪_X, J)` are the Ext sheaves
of `𝒪_Y/𝓘` into `𝒪_Y`. The proof is [Stacks, Tag 0A77]: `Ri_* R ℰom(𝒪_X, -) ≅ R𝓗om(i_*𝒪_X, -)`,
read on cohomology, `i_*` being exact, together with `i_*𝒪_X ≅ 𝒪_Y/𝓘`. -/
theorem nonempty_pushforward_homology_iso_extInto
    {J : CochainComplex (SheafOfModules.{u}
      (structureSheafRing (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X)) ℤ}
    (s : structureComplex i ⟶ J) [J.IsKInjective] [QuasiIso s] (n : ℤ) :
    Nonempty ((modulePushforward (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).obj
        ((((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).sheafHomExactSupport
          |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj J).homology n) ≅
      extInto (definingIdealOfHom i)
        (SheafOfModules.unit (structureSheaf Y.toRingedSpace.sheaf)) n) := by
  let S := Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i
  have hQs : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 inferInstance
  have e2 : DerivedCategory.Q.obj ((S.sheafHomExactSupport.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) ≅
      S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj (structureComplex i)) :=
    (S.derivedSheafHomExactSupportKInjectiveIso J).symm ≪≫
      S.derivedSheafHomExactSupport.mapIso (asIso (DerivedCategory.Q.map s)).symm
  have e3 := ((modulePushforward S.i).mapDerivedCategoryHomologyIso n).app
    (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj (structureComplex i)))
  have e4 := (DerivedCategory.homologyFunctor _ n).mapIso
    (S.derivedSheafHomExactSupportPushforwardNatIso.app
      (DerivedCategory.Q.obj (structureComplex i)))
  have e5 : DerivedCategory.Q.obj ((single (StructureSheafModules Y.toRingedSpace.sheaf)
        (ComplexShape.up ℤ) 0).obj (cokernel (definingIdealOfHom i).ι)) ≅
      (modulePushforward S.i).mapDerivedCategory.obj
        (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite S.Z.sheaf)) :=
    DerivedCategory.Q.mapIso ((single _ (ComplexShape.up ℤ) 0).mapIso
        (cokernelDefiningIdealIso i) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex (modulePushforward S.i)
        (ComplexShape.up ℤ) 0).symm.app _) ≪≫
    ((modulePushforward S.i).mapDerivedCategoryFactors.app _).symm
  exact ⟨(modulePushforward S.i).mapIso
      (((DerivedCategory.homologyFunctorFactors _ n).app _).symm ≪≫
        (DerivedCategory.homologyFunctor _ n).mapIso e2) ≪≫ e3.symm ≪≫ e4 ≪≫
      Stacks.SheafOfModules.derivedSheafExtMapIso Y.toRingedSpace.sheaf n e5 (Iso.refl _)⟩

end Stacks.Duality.KoszulRegular
