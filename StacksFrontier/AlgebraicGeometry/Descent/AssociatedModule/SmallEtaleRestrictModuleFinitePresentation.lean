module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentTransfer

/-!
# Finite presentation across the restriction to the small Zariski site

Let `S` be a scheme in a big étale site `B`.  The associated-module functor `𝓕 ↦ 𝓕^a` of
Stacks 03DU and its right adjoint, restriction along the inclusion of the small Zariski site of
`S`, restrict to mutually inverse equivalences between the quasi-coherent modules on `S` and the
quasi-coherent `𝒪`-modules on `S_étale`; the counit `(restrictModule 𝒢)^a ⟶ 𝒢` is the
isomorphism witnessing one half of that.  Combining it with Stacks 05VG for clause (7) of
Stacks 03DL reads finite presentation of a quasi-coherent module on `S_étale` off its
restriction to the small Zariski site of `S`.

## Main results

* `AlgebraicGeometry.SmallEtale.isFinitePresentation_restrictModule_iff`: **a quasi-coherent
  `𝒪`-module on `S_étale` is of finite presentation exactly when its restriction to the small
  Zariski site of `S` is.**

## Implementation notes

The counit, as an isomorphism, is `AlgebraicGeometry.SmallEtale.counitIso`; the name
`AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso` is kept as an alias of it.  Its
quasi-coherence hypothesis on the restriction is discharged by
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`, so quasi-coherence of the module
on `S_étale` is the only hypothesis left.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

noncomputable alias associatedModuleRestrictModuleIso := AlgebraicGeometry.SmallEtale.counitIso

/-- **Finite presentation of a quasi-coherent module on `S_étale` is finite presentation of its
restriction to the small Zariski site of `S`.**

Stacks 05VG for clause (7) of Stacks 03DL,
`AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_iff`, applied to the
restriction — which is quasi-coherent by
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule` — compares finite presentation of
the restriction with finite presentation of the module associated with it, and the counit
identifies that associated module with the original one. -/
theorem isFinitePresentation_restrictModule_iff
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite) :
    SheafOfModules.IsFinitePresentation (R := S.ringCatSheaf)
        ((restrictModule B S hS).obj G) ↔
      G.IsFinitePresentation := by
  rw [isFinitePresentation_associatedModule_iff B S hS ((restrictModule B S hS).obj G)
    (isQuasicoherent_restrictModule B S hS G hG)]
  exact ⟨fun h ↦ Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      (associatedModuleRestrictModuleIso B S hS G hG) h,
    fun h ↦ Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      (associatedModuleRestrictModuleIso B S hS G hG).symm h⟩

end SmallEtale

end AlgebraicGeometry
