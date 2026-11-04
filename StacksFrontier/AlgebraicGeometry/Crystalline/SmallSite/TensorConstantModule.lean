module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TensorConstantModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseQuasicoherentCrystal

/-!
# The tensor product `N ⊗_A M` restricted to the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)` and write `A = Γ(S, 𝒪_S)`.  For a
quasi-coherent sheaf of `𝒪_{X/S}`-modules `N` on the big crystalline site `CRIS(X/S)` and an
`A`-module `M`, `Crystalline.GlobalCrystallineSituation.tensorConstantModule N M` is the sheaf
`N ⊗_A M` on `CRIS(X/S)` whose sections over an object with affine ambient scheme are
`N(T) ⊗_A M`.  This file shows that its restriction to the small crystalline site `Cris(X/S)`
(`Crystalline.GlobalCrystallineSituation.SmallSite.restrictSheafOfModules`) is a crystal in
quasi-coherent modules, whose sections over an object `(U, T, δ)` of `Cris(X/S)` with `T` affine
are naturally `N(T) ⊗_A M`.

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isQuasiCoherentCrystal_restrictSheafOfModules_tensorConstantModule` — the restriction of
  `N ⊗_A M` to `Cris(X/S)` is a crystal in quasi-coherent modules.
* `restrictTensorConstantModuleSectionsEquiv` and its naturality
  `restrictTensorConstantModuleSectionsEquiv_restrict` — its sections over an object of `Cris(X/S)`
  with affine ambient scheme are `N(T) ⊗_A M`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open TensorConstant

variable {S : GlobalCrystallineSituation.{u}}
  (N : SheafOfModules.{u} (crystallineStructureSheaf S)) [N.IsQuasicoherentOnSite]
  (M : ModuleCat.{u} (BaseRing S))

/-- **The restriction of `N ⊗_A M` to `Cris(X/S)` is a crystal in quasi-coherent modules.** -/
theorem isQuasiCoherentCrystal_restrictSheafOfModules_tensorConstantModule :
    IsQuasiCoherentCrystal S (restrictSheafOfModules (tensorConstantModule N M)) :=
  isQuasiCoherentCrystal_restrictSheafOfModules inferInstance

/-- **The restriction of `N ⊗_A M` to `Cris(X/S)` is quasi-coherent.** -/
instance isQuasicoherentOnSite_restrictSheafOfModules_tensorConstantModule :
    (restrictSheafOfModules (tensorConstantModule N M)).IsQuasicoherentOnSite :=
  (isQuasiCoherentCrystal_restrictSheafOfModules_tensorConstantModule N M).1

/-- **The sections of the restriction of `N ⊗_A M` over an object `(U, T, δ)` of `Cris(X/S)` with
`T` affine are `N(T) ⊗_A M`.** -/
def restrictTensorConstantModuleSectionsEquiv (B : CrystallineThickening S)
    [IsAffine B.obj.thickening.target.scheme] :
    (restrictSheafOfModules (tensorConstantModule N M)).val.obj (op B) ≃ₗ[crysSheafRing S B.obj]
      TensorSections N.val M B.obj :=
  tensorConstantModuleSectionsEquiv N M B.obj

/-- **The identification of the sections of the restriction of `N ⊗_A M` with `N(T) ⊗_A M` is
natural** for the morphisms of `Cris(X/S)` between objects with affine ambient schemes. -/
theorem restrictTensorConstantModuleSectionsEquiv_restrict {B B' : CrystallineThickening S}
    [IsAffine B.obj.thickening.target.scheme] [IsAffine B'.obj.thickening.target.scheme]
    (g : B' ⟶ B) (x : (restrictSheafOfModules (tensorConstantModule N M)).val.obj (op B)) :
    restrictTensorConstantModuleSectionsEquiv N M B'
        ((restrictSheafOfModules (tensorConstantModule N M)).val.map g.op x) =
      tensorRestrict N.val M g.hom (restrictTensorConstantModuleSectionsEquiv N M B x) :=
  tensorConstantModuleSectionsEquiv_restrict N M g.hom x

end Crystalline.GlobalCrystallineSituation.SmallSite

end
