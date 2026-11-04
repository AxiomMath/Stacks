module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCriterion
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentAffineGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictScalars

/-!
# The restriction of a locally quasi-coherent module to an affine ambient scheme

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the big crystalline site of a global crystalline
situation and let `(U, T, δ)` be an object of that site.  Local quasi-coherence of `F`,
`Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent`, says that the restriction `F_T`
is a quasi-coherent module over the restriction of `𝒪_{X/S}` to the ambient scheme `T`.  When `T`
is affine, [Stacks, Tag 03DX] turns quasi-coherence of an `𝒪_T`-module into a *global*
presentation, a cokernel of a map between coproducts of copies of `𝒪_T`.  That is the first step
of the direction "locally quasi-coherent and a crystal implies quasi-coherent" of
[Stacks, Tag 07IT], and this file takes it.

## The change of scalars

The two sheaves of rings involved are not the same sheaf.  Local quasi-coherence is a condition
on a module over
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf`, the restriction of
`𝒪_{X/S}` to the opens of `T`, whose value over an open `W` is the ring of global sections of the
open subscheme `W`; [Stacks, Tag 03DX] is a statement about a module over
`AlgebraicGeometry.Scheme.ringCatSheaf`, whose value over `W` is the sections of the structure
sheaf of `T` over `W`.  The two are isomorphic, by
`Crystalline.GlobalCrystallineSituation.Thickening.restrictionStructureIso`, and the bridge is
restriction of scalars along that isomorphism, which carries quasi-coherence by
`Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso` — the
  restriction of `𝒪_{X/S}` to the ambient scheme of an object is the structure sheaf of that
  scheme, as an isomorphism of sheaves of rings.
* `Crystalline.GlobalCrystallineSituation.Thickening.ambientModuleRestriction` — the restriction
  `F_T` of a sheaf of `𝒪_{X/S}`-modules to the ambient scheme of an object, with its scalars read
  in the structure sheaf of that scheme.

## Main results

* `Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_moduleRestrictionSheaf` — local
  quasi-coherence, read with the sheaf-of-modules restriction rather than with the presheaf-level
  one together with its sheaf condition.
* `Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_ambientModuleRestriction` — the
  restriction of a locally quasi-coherent module is a quasi-coherent module over the structure
  sheaf of the ambient scheme.
* `Crystalline.GlobalCrystallineSituation.Thickening.isQuasicoherentOnSite_ofAmbient` — the
  converse change of scalars: a quasi-coherent `𝒪_T`-module, read over the restriction of
  `𝒪_{X/S}`, is quasi-coherent.
* `Crystalline.GlobalCrystallineSituation.hasGlobalPresentation_ambientModuleRestriction` —
  **[Stacks, Tag 03DX] for the restriction of a locally quasi-coherent sheaf of
  `𝒪_{X/S}`-modules**: over an object whose ambient scheme is affine, that restriction is a
  cokernel of a map between coproducts of copies of `𝒪_T`.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

/-- **The restriction of the structure sheaf of the big crystalline site to the ambient scheme of
an object is the structure sheaf of that scheme**, as an isomorphism of sheaves of rings on that
scheme.  It is
`Crystalline.GlobalCrystallineSituation.Thickening.restrictionStructureIso` read through the
forgetful functor from commutative rings to rings, the forgetful functor from sheaves to
presheaves being fully faithful. -/
noncomputable def ringRestrictionSheafStructureIso (A : Thickening S) :
    A.ringRestrictionSheaf ≅ A.thickening.target.scheme.ringCatSheaf :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology ↥A.thickening.target.scheme)
    RingCat.{u}).preimageIso
      (Functor.isoWhiskerRight (restrictionStructureIso A)
        (forget₂ CommRingCat.{u} RingCat.{u}))

/-- **Stacks Project, Tag 07IQ.**  The restriction `F_T` of a sheaf of `𝒪_{X/S}`-modules to the
ambient scheme of an object, with its scalars read in the structure sheaf of that scheme rather
than in the restriction of `𝒪_{X/S}`.  The two sheaves of rings are identified by
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`, and the
module is unchanged on sections: this is a restriction of scalars along an isomorphism. -/
noncomputable def ambientModuleRestriction
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S) :
    SheafOfModules.{u} A.thickening.target.scheme.ringCatSheaf :=
  (SheafOfModules.restrictScalars (ringRestrictionSheafStructureIso A).inv).obj
    (moduleRestrictionSheaf M A)

/-- **A quasi-coherent `𝒪_T`-module on the ambient scheme of an object, read over the restriction
of `𝒪_{X/S}` to that scheme, is quasi-coherent.**  This is the change of scalars of
`Crystalline.GlobalCrystallineSituation.Thickening.ambientModuleRestriction` run in the other
direction. -/
theorem isQuasicoherentOnSite_ofAmbient (A : Thickening S)
    (N : SheafOfModules.{u} A.thickening.target.scheme.ringCatSheaf)
    (hN : N.IsQuasicoherentOnSite) :
    ((SheafOfModules.restrictScalars (ringRestrictionSheafStructureIso A).hom).obj
      N).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso _ N hN

end Thickening

/-- **Local quasi-coherence, read with the sheaf-of-modules restriction.**  The definition of
`Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent` quantifies over the sheaf
condition of the presheaf-level restriction; that condition always holds, and the sheaf of
modules it produces is
`Crystalline.GlobalCrystallineSituation.Thickening.moduleRestrictionSheaf`. -/
theorem isQuasicoherentOnSite_moduleRestrictionSheaf
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hM : IsLocallyQuasiCoherent M)
    (A : Thickening S) : (Thickening.moduleRestrictionSheaf M A).IsQuasicoherentOnSite :=
  (hM A).choose_spec

/-- **The restriction of a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules to the ambient scheme
of an object is a quasi-coherent module over the structure sheaf of that scheme.** -/
theorem isQuasicoherentOnSite_ambientModuleRestriction
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hM : IsLocallyQuasiCoherent M)
    (A : Thickening S) : (Thickening.ambientModuleRestriction M A).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso _ _
    (isQuasicoherentOnSite_moduleRestrictionSheaf hM A)

/-- **Stacks Project, Tag 03DX, for the restriction of a locally quasi-coherent sheaf of
`𝒪_{X/S}`-modules.**  Over an object `(U, T, δ)` of the big crystalline site whose ambient scheme
`T` is affine, the restriction `F_T` of a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules has a
global presentation: it is a cokernel of a map between coproducts of copies of `𝒪_T`.

This is the first step of the direction "locally quasi-coherent and a crystal implies
quasi-coherent" of [Stacks, Tag 07IT], reached from the reduction to affine ambient schemes of
`Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_of_forall_isAffine`.  The step which
remains is to turn this presentation into a global presentation of `F` on the localised site
`CRIS(X/S)/(U, T, δ)`, which is where the crystal condition and [Stacks, Tag 01XB] enter; see the
module documentation. -/
theorem hasGlobalPresentation_ambientModuleRestriction
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hM : IsLocallyQuasiCoherent M)
    (A : Thickening S) [IsAffine A.thickening.target.scheme] :
    (Thickening.ambientModuleRestriction M A).HasGlobalPresentation :=
  Stacks.AlgebraicGeometry.AffinePresentation.hasGlobalPresentation_of_isQuasicoherentOnSite
    _ _ (isQuasicoherentOnSite_ambientModuleRestriction hM A)

end Crystalline.GlobalCrystallineSituation

end
