/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.SubmoduleBasis
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.Equivalence
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeSchemeNeighborhood
public import StacksFrontier.AlgebraicGeometry.Modules.ClosedSubschemeQuotient
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.TwistQuotients
public import StacksFrontier.AlgebraicGeometry.TopIdeals.Meet

/-!
# A member of `Quot_{OO/Pn/Z}(T)` cuts out a closed subscheme flat and of finite presentation

`AlgebraicGeometry.ProjectiveQuot.exists_isClosedImmersion_ker_eq_idealOfFamily_of_mem` turns a
member `K` of `Quot_{OO/Pn/Z}(T)`, a submodule of `OO^{+1}` on `Pn_T`, into a closed subscheme
`Z` of `Pn_T` (Stacks 01QQ), cut out by the sheaf of ideals
`AlgebraicGeometry.ProjectiveQuot.idealOfFamily`. This file proves that `Z -> T` is flat and of
finite presentation, which is the flatness-and-finite-presentation half of the dictionary of
Stacks 0D00 read on `Pn_T`.

The content is the identification of the quotient with the pushforward of the structure sheaf of
the subscheme, `OO^{+1}/K = OO_{Pn_T}/I = i_* OO_Z`, after which both conditions are read off the
quotient:

* **flatness.** The library's `OO_X/I` *is* `i_* OO_Z`
  (`Stacks.ClosedSubscheme.cokernelIso`), so the quotient is the pushforward, and
  `AlgebraicGeometry.flat_of_isFlatOver_pushforward_unitModule` -- Stacks 0FLM for the affine
  closed immersion, followed by `AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt` -- turns
  relative flatness of the pushforward into flatness of `Z -> T`. The forward direction is
  `Stacks.Chow.isFlatOver_pushforwardStructureSheaf`.
* **finite presentation.**
  `AlgebraicGeometry.finitePresentation_of_isFinitePresentation_pushforward_unit` gives
  `Z -> Pn_T` of finite presentation from finite presentation of the pushforward, and
  `Pn_T -> T` is of finite presentation.

## Main definitions

* `Stacks.Divisors.cokernelIsoPushforwardUnit`: the quotient of the structure sheaf by a
  quasi-coherent submodule `J` is the pushforward of the structure sheaf of the closed subscheme
  `J` cuts out.
* `AlgebraicGeometry.ProjectiveQuot.subschemeOfFamily`,
  `AlgebraicGeometry.ProjectiveQuot.subschemeOfFamilyι`: that closed subscheme of `Pn_T`, named.
* `AlgebraicGeometry.ProjectiveQuot.pushforwardUnitSubschemeOfFamilyIso`: the pushforward of its
  structure sheaf is the quotient by the member.

## Main results

* `Stacks.Divisors.submodule_eq_ker_structureSheafProjection`: a quasi-coherent submodule of the
  structure sheaf is the kernel of the projection onto the structure sheaf of the closed
  subscheme it cuts out.
* `AlgebraicGeometry.flat_of_isFlatOver_pushforward_unitModule`: a closed subscheme is flat over
  the base as soon as its pushed-forward structure sheaf is.
* `AlgebraicGeometry.ProjectiveQuot.exists_isClosedImmersion_flat_finitePresentation_of_mem`:
  **a member of `Quot_{OO/Pn/Z}(T)` cuts out a closed subscheme of `Pn_T` which is flat and of
  finite presentation over `T`.**

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a non-reducible wrapper of `SheafOfModules`, past which
neither instance search nor `rw` unfolds. The steps of the cokernel comparison are therefore
*applications* of statements proved over an abstract category --
`Stacks.AlgebraicGeometry.Tag01YHTopIdeals.cokernelIsoOfIsoComp`,
`CategoryTheory.Limits.cokernel.mapIso` with its compatibility supplied as a term -- rather than
rewrites; a `rw [Iso.refl_hom]` on a goal mentioning `SheafOfModules.unit X.ringCatSheaf` read at
`X.Modules` fails, reporting that the target is not type-correct at implicit transparency.

For the same reason `Stacks.ClosedSubscheme.epi_structureSheafProjection` is supplied by name in
`Stacks.Divisors.cokernelIsoPushforwardUnit` rather than found by instance search.

Quasi-coherence of `AlgebraicGeometry.ProjectiveQuot.idealOfFamily` is an instance argument of
`Stacks.Divisors.idealSheafDataOfSubmodule`, and it is only available once the quotient is known
to be of finite presentation; so `AlgebraicGeometry.ProjectiveQuot.subschemeOfFamily` and its
closed immersion carry that hypothesis as an explicit argument rather than being functions of `K`
alone.

## References

* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

open AlgebraicGeometry.SheafOfModules.Submodule

variable {X : Scheme.{u}} (J : (SheafOfModules.unit X.ringCatSheaf).Submodule)
  [(J.toSheafOfModules : X.Modules).IsQuasicoherent]

/-- **A quasi-coherent submodule of the structure sheaf is the kernel of the projection onto the
structure sheaf of the closed subscheme it cuts out.** Over an arbitrary open the sections of the
kernel are the sections killed by the closed immersion, which are the sections of the submodule by
`Stacks.Divisors.subschemeι_app_eq_zero_iff_mem_of_isQuasicoherent`. -/
theorem submodule_eq_ker_structureSheafProjection :
    J = SheafOfModules.Submodule.ker
      (Stacks.ClosedSubscheme.structureSheafProjection (idealSheafDataOfSubmodule J)) := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext ?_)
  intro U
  ext s
  exact (subschemeι_app_eq_zero_iff_mem_of_isQuasicoherent J U.unop s).symm

/-- **`OO_X / J` is `i_* OO_Z`** for the closed subscheme `Z` of `X` cut out by a quasi-coherent
submodule `J` of `OO_X`: the projection `OO_X -> i_* OO_Z` is an epimorphism
(`Stacks.ClosedSubscheme.epi_structureSheafProjection`) with kernel `J`, so
`Stacks.LefschetzCone.cokernelIsoOfEqKer` applies. -/
def cokernelIsoPushforwardUnit :
    cokernel (C := X.Modules) (SheafOfModules.Submodule.ιModules J) ≅
      (Scheme.Modules.pushforward (idealSheafDataOfSubmodule J).subschemeι).obj
        (SheafOfModules.unit (idealSheafDataOfSubmodule J).subscheme.ringCatSheaf) :=
  @Stacks.LefschetzCone.cokernelIsoOfEqKer _ _ _
    (Stacks.ClosedSubscheme.structureSheafProjection (idealSheafDataOfSubmodule J))
    (Stacks.ClosedSubscheme.epi_structureSheafProjection (idealSheafDataOfSubmodule J)) J
    (submodule_eq_ker_structureSheafProjection J)

end Stacks.Divisors

namespace AlgebraicGeometry

/-- **A closed subscheme is flat over the base as soon as its structure sheaf, pushed forward to
the ambient scheme, is flat there.** The converse of
`Stacks.Chow.isFlatOver_pushforwardStructureSheaf`: Stacks 0FLM
(`AlgebraicGeometry.isFlatOver_pushforward_iff`, available because a closed immersion is affine)
turns the hypothesis into relative flatness of `𝒪_Z` over `Y`, and that is flatness of `Z ⟶ Y`
point by point (`AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt`). -/
theorem flat_of_isFlatOver_pushforward_unitModule {X Y Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (f : X ⟶ Y)
    (h : IsFlatOver f.toLRSHom.toShHom
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :
    Flat (i ≫ f) :=
  (Flat.iff_flat_stalkMap (i ≫ f)).mpr fun x =>
    (isFlatOverAt_unit_iff_isFlatAt (i ≫ f) x).mp
      ((isFlatOver_pushforward_iff i f (Stacks.Ample.unitModule Z)).mpr h x)

namespace ProjectiveQuot

open AlgebraicGeometry.SheafOfModules.Submodule

variable {n : ℕ} {T : Scheme.{u}}

/-- **The sheaf of ideals of `𝒪_{ℙⁿ_T}` cut out by a subobject of `𝒪^{⊕ 1}` with quotient of
finite presentation**, in Mathlib's affine-local spelling. -/
abbrev idealSheafDataOfFamily (K : Subobject (freeModule n 1 T))
    (hK : (quotient K).IsFinitePresentation) : (projectiveSpaceOver n T).IdealSheafData :=
  @Stacks.Divisors.idealSheafDataOfSubmodule _ (idealOfFamily K)
    (isQuasicoherent_idealOfFamily K hK)

/-- **The closed subscheme of `ℙⁿ_T` cut out by a subobject of `𝒪^{⊕ 1}`.** -/
abbrev subschemeOfFamily (K : Subobject (freeModule n 1 T))
    (hK : (quotient K).IsFinitePresentation) : Scheme.{u} :=
  (idealSheafDataOfFamily K hK).subscheme

/-- Its closed immersion into `ℙⁿ_T`. -/
abbrev subschemeOfFamilyι (K : Subobject (freeModule n 1 T))
    (hK : (quotient K).IsFinitePresentation) :
    subschemeOfFamily K hK ⟶ projectiveSpaceOver n T :=
  (idealSheafDataOfFamily K hK).subschemeι

/-- **The quotient `𝒪^{⊕ 1}/K` is the quotient of `𝒪_{ℙⁿ_T}` by the sheaf of ideals
`AlgebraicGeometry.ProjectiveQuot.idealOfFamily`.** The rank-one free module is the structure
sheaf (`AlgebraicGeometry.ProjectiveQuot.freeModuleOneIso`), a subobject is isomorphic to the
subobject it presents (`CategoryTheory.Subobject.underlyingIso`), and a subobject is the subsheaf
of its sections (`AlgebraicGeometry.Scheme.Modules.subobjectSubmoduleIso`). -/
def quotientIsoCokernelIdealOfFamily (K : Subobject (freeModule n 1 T)) :
    quotient K ≅
      cokernel (C := (projectiveSpaceOver n T).Modules) (ιModules (idealOfFamily K)) :=
  cokernel.mapIso (C := (projectiveSpaceOver n T).Modules) K.arrow
      (K.arrow ≫ (freeModuleOneIso n T).hom) (Iso.refl _) (freeModuleOneIso n T)
      (Category.id_comp (K.arrow ≫ (freeModuleOneIso n T).hom)).symm ≪≫
    Stacks.AlgebraicGeometry.Tag01YHTopIdeals.cokernelIsoOfIsoComp
        (Subobject.underlyingIso (K.arrow ≫ (freeModuleOneIso n T).hom)).symm _
        (unitSubobject K).arrow
        (Subobject.underlyingIso_hom_comp_eq_mk (K.arrow ≫ (freeModuleOneIso n T).hom)) ≪≫
      Stacks.AlgebraicGeometry.Tag01YHTopIdeals.cokernelIsoOfIsoComp
        (Scheme.Modules.subobjectSubmoduleIso (unitSubobject K)) _
        (ιModules (idealOfFamily K))
        (Scheme.Modules.subobjectSubmoduleIso_inv_arrow (unitSubobject K))

/-- **The structure sheaf of the closed subscheme cut out by a subobject of `𝒪^{⊕ 1}`, pushed
forward to `ℙⁿ_T`, is the quotient by that subobject.** -/
def pushforwardUnitSubschemeOfFamilyIso (K : Subobject (freeModule n 1 T))
    (hK : (quotient K).IsFinitePresentation) :
    (Scheme.Modules.pushforward (subschemeOfFamilyι K hK)).obj
        (Stacks.Ample.unitModule (subschemeOfFamily K hK)) ≅ quotient K :=
  (@Stacks.Divisors.cokernelIsoPushforwardUnit _ (idealOfFamily K)
      (isQuasicoherent_idealOfFamily K hK)).symm ≪≫
    (quotientIsoCokernelIdealOfFamily K).symm

/-- **The closed subscheme cut out by a member of `Quot_{𝒪/ℙⁿ/ℤ}(T)` is flat over `T`.** The
quotient is flat over `T` by the membership condition, it is the pushforward of the structure
sheaf of the subscheme, and `AlgebraicGeometry.flat_of_isFlatOver_pushforward_unitModule`
(Stacks 0FLM) turns that into flatness of the subscheme over `T`. -/
theorem flat_subschemeOfFamilyι_comp {K : Subobject (freeModule n 1 T)}
    (hK : K ∈ families n 1 T) :
    Flat (subschemeOfFamilyι K hK.1 ≫ (projectiveSpaceOver n T ↘ T)) :=
  flat_of_isFlatOver_pushforward_unitModule _ _
    (ProjectiveQuotOverSpace.isFlatOver_of_iso
      (pushforwardUnitSubschemeOfFamilyIso K hK.1).symm hK.2)

/-- **The closed subscheme cut out by a subobject of `𝒪^{⊕ 1}` with quotient of finite
presentation is of finite presentation over `ℙⁿ_T`**, by
`AlgebraicGeometry.finitePresentation_of_isFinitePresentation_pushforward_unit`. -/
theorem finitePresentation_subschemeOfFamilyι {K : Subobject (freeModule n 1 T)}
    (hK : (quotient K).IsFinitePresentation) :
    FinitePresentation (subschemeOfFamilyι K hK) :=
  finitePresentation_of_isFinitePresentation_pushforward_unit (subschemeOfFamilyι K hK)
    (SheafOfModules.IsFinitePresentation.of_iso hK
      (pushforwardUnitSubschemeOfFamilyIso K hK).symm)

/-- **The closed subscheme cut out by a member of `Quot_{𝒪/ℙⁿ/ℤ}(T)` is of finite presentation
over `T`**: it is of finite presentation over `ℙⁿ_T`, which is of finite presentation over `T`. -/
theorem finitePresentation_subschemeOfFamilyι_comp {K : Subobject (freeModule n 1 T)}
    (hK : K ∈ families n 1 T) :
    FinitePresentation (subschemeOfFamilyι K hK.1 ≫ (projectiveSpaceOver n T ↘ T)) :=
  (finitePresentation_subschemeOfFamilyι hK.1).comp (finitePresentation_projectiveSpaceOver n T)

/-- **A member of `Quot_{𝒪/ℙⁿ/ℤ}(T)` cuts out a closed subscheme of `ℙⁿ_T` which is flat and of
finite presentation over `T`.** This is the flatness-and-finite-presentation entry of the
dictionary of Stacks 0D00, at the spelling of
`AlgebraicGeometry.ProjectiveQuot.families`. -/
theorem exists_isClosedImmersion_flat_finitePresentation_of_mem
    {K : Subobject (freeModule n 1 T)} (hK : K ∈ families n 1 T) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ projectiveSpaceOver n T), IsClosedImmersion i ∧
      Flat (i ≫ (projectiveSpaceOver n T ↘ T)) ∧
        FinitePresentation (i ≫ (projectiveSpaceOver n T ↘ T)) :=
  ⟨subschemeOfFamily K hK.1, subschemeOfFamilyι K hK.1, inferInstance,
    flat_subschemeOfFamilyι_comp hK, finitePresentation_subschemeOfFamilyι_comp hK⟩

end ProjectiveQuot

end AlgebraicGeometry

end
