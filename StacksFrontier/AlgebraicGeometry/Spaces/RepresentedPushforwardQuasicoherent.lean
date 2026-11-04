module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange

/-!
# The direct image along a morphism of representable algebraic spaces, and quasi-coherence

Let `B` be a big fppf site containing a scheme `S` and let `g : T' ⟶ T` be a morphism of the big
fppf category over `S`.  The direct image of modules along the morphism of representable
algebraic spaces `g` represents is, across the identification of the small étale site of
`yoneda.obj U` with the small étale site of the scheme underlying `U`, the small étale direct
image of the underlying morphism of schemes:
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`.  This file evaluates that
identification at one module and deduces that quasi-coherence of the direct image is a
statement about the small étale sites of the two *schemes*.

## Main definitions

* `Space.representedModulePushforwardObjIso` is `Space.representedModulePushforwardSquareIso`
  evaluated at a module.

## Main results

* `Space.isQuasicoherentOnSite_modulePushforward_representedSmallEtaleModule_iff`: the direct
  image of modules along a morphism of representable algebraic spaces is quasi-coherent exactly
  when the small étale direct image of the underlying morphism of schemes is.
* `Space.isQuasicoherentOnSite_modulePushforward_representedSpaceMap_iff`: the same for an
  arbitrary `𝒪`-module on the source, read through the equivalence of module categories.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- The direct image of modules along a morphism of representable algebraic spaces is the small
étale direct image of the underlying morphism of schemes, at one module: this is
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` evaluated at `M`. -/
noncomputable def representedModulePushforwardObjIso
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T')) :
    representedSmallEtaleModule B S hS T
        ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).obj M) ≅
      (modulePushforward B S hS (representedSpaceMap B S hS g)).obj
        (representedSmallEtaleModule B S hS T' M) :=
  (representedModulePushforwardSquareIso B S hS g
    (relativelyRepresentable_yoneda_map B S hS g)).app M

/-- Quasi-coherence of the direct image along a morphism of representable algebraic spaces is
quasi-coherence of the small étale direct image on the underlying schemes. -/
theorem isQuasicoherentOnSite_modulePushforward_representedSmallEtaleModule_iff
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T')) :
    ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj
        (representedSmallEtaleModule B S hS T' M)).IsQuasicoherentOnSite ↔
      ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).obj
        M).IsQuasicoherentOnSite := by
  rw [← isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T]
  exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
      (representedModulePushforwardObjIso B S hS g M).symm,
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (representedModulePushforwardObjIso B S hS g M)⟩

/-- Quasi-coherence of the direct image of an arbitrary `𝒪`-module along a morphism of
representable algebraic spaces is quasi-coherence of the small étale direct image of the
corresponding module on the small étale site of the scheme underlying `T'`, read through
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`. -/
theorem isQuasicoherentOnSite_modulePushforward_representedSpaceMap_iff
    (F : Modules.{u, u} B S hS (yoneda.obj T')
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T')) :
    ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj F).IsQuasicoherentOnSite ↔
      ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).obj
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj
          F)).IsQuasicoherentOnSite := by
  have e : representedSmallEtaleModule B S hS T'
      ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj F) ≅ F :=
    (representedSmallEtaleModuleEquivalence B S hS T').counitIso.app F
  rw [← isQuasicoherentOnSite_modulePushforward_representedSmallEtaleModule_iff B S hS g]
  exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((modulePushforward B S hS (representedSpaceMap B S hS g)).mapIso e).symm,
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((modulePushforward B S hS (representedSpaceMap B S hS g)).mapIso e)⟩

end AlgebraicGeometry.Space

end
