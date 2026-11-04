module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NoncommExtendScalarsUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFree
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# The quasi-inverse of Stacks 08AI on free modules

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `𝒜 = f_*𝒪_Y`, and let `L : 𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢` be the left adjoint of the
direct image over `𝒜` constructed in
`StacksFrontier/AlgebraicGeometry/Spaces/DirectImageAlgebraModulePullback.lean`.  This file computes
`L` on the free `𝒜`-modules: it carries the free `𝒜`-module on a type to the free `𝒪_Y`-module on
the same type, and the result is quasi-coherent.

At the level of schemes, the corresponding computations are
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModulesObjFreeIso` and
`isQuasicoherent_pullbackModules_free`, and they are what the unit and counit arguments of
Stacks 01SB are reduced to by the colimit argument of
`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_app_of_isColimit`.  No hypothesis on `f` is
needed for any of it.

## Main definitions

* `AlgebraicGeometry.Space.directImageAlgebraPullbackObjUnitIso` — `𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒜 ≅ 𝒪_Y`.
* `AlgebraicGeometry.Space.directImageAlgebraPullbackFreeIso` — the quasi-inverse carries the
  free `𝒜`-module on a type to the free `𝒪_Y`-module on the same type.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback_free` — the
  quasi-inverse carries a free `𝒜`-module to a quasi-coherent `𝒪_Y`-module.

## Implementation notes

The index type is arbitrary, not finite.  `Stacks.Sheaves.ToposPullback.pullbackModuleFreeIso`
asks for a finite index type, because the inverse image of modules along a
finite-product-preserving functor of sheaves of sets is only known to preserve *finite*
coproducts; here the functor is a left adjoint, by
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction`, so it preserves all of them and
the comparison of colimit points is available at any index type.

The inverse image half of `L` carries the unit `𝒜`-module to the unit `f⁻¹𝒜`-module on the nose
(`Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso` is `CategoryTheory.Iso.refl`), so the whole
content of the unit computation is that extension of scalars does the same, which is
`Stacks.NoncommChangeOfRings.Sheaf.extendScalarsObjUnitIso`.

Quasi-coherence of the free `𝒪_Y`-module is unconditional on the small étale site: a free module
is cartesian on affine charts by `AlgebraicGeometry.Space.isCartesianOnAffineCharts_free`, and
that implication of Descent, Proposition 03DX(2) is proved in this tree as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`.

## References

* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-- **The quasi-inverse of Stacks 08AI at the unit module**: `𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒜 ≅ 𝒪_Y`, for
`𝒜 = f_*𝒪_Y`.

The inverse image carries the unit `𝒜`-module to the unit `f⁻¹𝒜`-module on the nose, and
extension of scalars along the ring-level counit `f⁻¹𝒜 ⟶ 𝒪_Y` carries that to the unit
`𝒪_Y`-module. -/
noncomputable def directImageAlgebraPullbackObjUnitIso (f : Y ⟶ X) :
    (directImageAlgebraPullback B S hS f).obj
        (SheafOfModules.unit (structureRingSheafDirectImage B S hS f)) ≅
      SheafOfModules.unit (structureRingSheaf B S hS Y) :=
  (Stacks.NoncommChangeOfRings.Sheaf.extendScalars.{u}
        (directImageAlgebraRingCounit B S hS f)).mapIso
      (pullbackModuleUnitIso (SmallEtale.topology B S hS Y.1)
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom.inverseImage
        (structureRingSheafDirectImage B S hS f)).symm ≪≫
    Stacks.NoncommChangeOfRings.Sheaf.extendScalarsObjUnitIso.{u}
      (directImageAlgebraRingCounit B S hS f)

/-- The quasi-inverse of Stacks 08AI preserves colimits, being a left adjoint. -/
instance preservesColimitsOfSize_directImageAlgebraPullback (f : Y ⟶ X) :
    PreservesColimitsOfSize.{u, u} (directImageAlgebraPullback B S hS f) :=
  (directImageAlgebraPullbackAdjunction B S hS f).leftAdjoint_preservesColimits

/-- **The quasi-inverse of Stacks 08AI carries free modules to free modules**: for an arbitrary
type `I`, it carries the free `𝒜`-module on `I` to the free `𝒪_Y`-module on `I`.

The free module is the coproduct of copies of the unit module, the quasi-inverse preserves that
coproduct because it is a left adjoint, and it carries the unit module to the unit module by
`AlgebraicGeometry.Space.directImageAlgebraPullbackObjUnitIso`. -/
noncomputable def directImageAlgebraPullbackFreeIso (f : Y ⟶ X) (I : Type u) :
    (directImageAlgebraPullback B S hS f).obj
        (SheafOfModules.free.{u} (R := structureRingSheafDirectImage B S hS f) I) ≅
      SheafOfModules.free.{u} (R := structureRingSheaf B S hS Y) I :=
  (isColimitOfPreserves (directImageAlgebraPullback B S hS f)
      (SheafOfModules.isColimitFreeCofan I)).coconePointsIsoOfNatIso
    (SheafOfModules.isColimitFreeCofan I)
    (Discrete.natIso fun _ ↦ directImageAlgebraPullbackObjUnitIso B S hS f)

/-- **The quasi-inverse of Stacks 08AI carries a free `𝒜`-module to a quasi-coherent
`𝒪_Y`-module**, for an arbitrary index type and with no hypothesis on `f`: it is the free
`𝒪_Y`-module on the same type, which is cartesian on affine charts and hence quasi-coherent. -/
theorem isQuasicoherentOnSite_directImageAlgebraPullback_free (f : Y ⟶ X) (I : Type u) :
    ((directImageAlgebraPullback B S hS f).obj
      (SheafOfModules.free.{u} (R := structureRingSheafDirectImage B S hS f)
        I)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (directImageAlgebraPullbackFreeIso B S hS f I).symm
    (isQuasicoherentOnSite_of_isCartesianOnAffineCharts _ (isCartesianOnAffineCharts_free I))

end AlgebraicGeometry.Space

end
