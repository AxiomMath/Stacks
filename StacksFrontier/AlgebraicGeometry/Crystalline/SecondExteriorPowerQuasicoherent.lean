module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerPresheafModel
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickening

/-!
# Quasi-coherence of `Ω²_{T/Y,δ}`

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`, let `Ω_{T/Y,δ}` be its sheaf of
divided power differentials and let `Ω²_{T/Y,δ} = Crystalline.dpSecondExteriorPower` be the
second exterior power of the latter.  This module identifies `Ω²_{T/Y,δ}` with the *bundled*
second exterior power `⋀² Ω_{T/Y,δ}` of `AlgebraicGeometry.Scheme.Modules.exteriorPower`, and
transports quasi-coherence across that identification.

## Why an identification is needed

`Crystalline.dpSecondExteriorPower` is *defined* as the sheafification of the presheaf
`PresheafOfModules.extPow 2` of sectionwise second exterior powers, because that is the
description [Stacks, Tag 01CG] gives of an exterior power of a sheaf of modules.  The
quasi-coherence of exterior powers is available only for the bundled form
`AlgebraicGeometry.Scheme.Modules.exteriorPower`, a homogeneous piece of the chosen exterior
algebra `SheafOfModules.algebras`.  The two are compared by
`SheafOfModules.presheafModelExteriorPowerIso`: the `n`-th exterior power of a sheaf of modules
is the sheafification of the sectionwise `n`-th exterior power of *any* presheaf model of it.
The presheaf model used here is `Ω_{T/Y,δ}` read as a presheaf of modules,
`Crystalline.dpDifferentialsModules`, which is a model of itself through the counit
`SheafOfModules.sheafifySectionsIso` of the sheafification adjunction.

## Main definitions

* `Crystalline.dpSecondExteriorPowerIso` — the identification `Ω²_{T/Y,δ} ≅ ⋀² Ω_{T/Y,δ}`.
* `Crystalline.dpSecondExteriorModulesIso` — the same identification read as presheaves of
  modules, the spelling in which the second-order construction consumes `Ω²_{T/Y,δ}`.

## Main results

* `Crystalline.dpSecondExteriorPower_isQuasicoherent` — **`Ω²_{T/Y,δ}` is quasi-coherent.**

## What this feeds

[Stacks, Tag 07J3] asserts that the second-order universal thickening `(U, T'', δ'')` is an
object of `CRIS(X/S)`, and that clause is the one assertion of the tag the library does not have;
the sheaf-level content of the tag is complete in
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickening` and
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningDeRham`.  The route to it set out
in the "What is and is not proved" note of
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningOrder` realizes `T''` as a
square-zero extension of the first-order thickening `T'`
(`Crystalline.secondOrderThickening_ker_proj_sq`) and feeds that to
`Stacks.Thickenings.squareZeroExtension_realization`, whose `quasicoherent` field is the
quasi-coherence of the kernel `K = 0 ⊕ 0 ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}`.  That note names three
missing inputs; this module supplies the first of them, and nothing else.  No `stacks` attribute
is claimed here: quasi-coherence of `Ω²_{T/Y,δ}` is an input to a clause of Tag 07J3, not one of
its assertions.

## What is and is not proved

**The identification costs nothing beyond Tag 07IY.**  It needed no finiteness and no local
freeness hypothesis on `Ω_{T/Y,δ}`: `SheafOfModules.presheafModelExteriorPowerIso` holds for an
arbitrary presheaf model of an arbitrary sheaf of modules, and the only input to the
quasi-coherence statement is `Crystalline.dpDifferentialsSheaf_isQuasicoherent`, the
quasi-coherence of `Ω_{T/Y,δ}` itself [Stacks, Tag 07IY].  The bundled statement transported here
is `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_exteriorPower`, which likewise asks only
that its argument be quasi-coherent.

`SheafOfModules.exteriorPower_isSheafification`, the library's form of Tag 01CG, is *not* used:
it packages the comparison morphism inside an existential together with its two defining equation
families, so it cannot produce an isomorphism of objects.  Its content is the same, and
`SheafOfModules.presheafModelExteriorPowerIso` is the unpackaged comparison that the universal
property of the exterior algebra produces directly.

**The other two inputs named in `SecondOrderThickeningOrder` are untouched.**  That `K` is a
quasi-coherent `𝒪_{T'}`-module is a statement about an extension of `Ω²_{T/Y,δ}` by `Ω_{T/Y,δ}`
over the structure sheaf of the *realized* scheme `T'`, not about a module on `T`, and nothing
here bears on it; neither does anything here bear on the bookkeeping that a composite of two
first-order thickenings of schemes is a second-order thickening.

`Crystalline.dpSecondExteriorModules` is a presheaf of modules, so quasi-coherence is not a
predicate that applies to it; `Crystalline.dpSecondExteriorModulesIso` records the identification
in that spelling, and a consumer that needs quasi-coherence must read it on the sheaf
`Crystalline.dpSecondExteriorPower`, where `Crystalline.dpSecondExteriorPower_isQuasicoherent`
supplies it as an instance.

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Crystalline

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- **`Ω²_{T/Y,δ}` is the second exterior power of `Ω_{T/Y,δ}`**, in the bundled sense of
`AlgebraicGeometry.Scheme.Modules.exteriorPower`.

`Crystalline.dpSecondExteriorPower` is the sheafification of the presheaf of sectionwise second
exterior powers of `Crystalline.dpDifferentialsModules`, and that presheaf of modules is a
presheaf model of `Ω_{T/Y,δ}` — it *is* its presheaf of sections, and sheafifying the sections of
a sheaf of modules returns it, by the counit `SheafOfModules.sheafifySectionsIso`.  So this is
`SheafOfModules.presheafModelExteriorPowerIso` at that model, in degree two. -/
def dpSecondExteriorPowerIso :
    dpSecondExteriorPower T Y f ≅
      Scheme.Modules.exteriorPower (dpDifferentialsSheaf T Y f) 2 :=
  SheafOfModules.presheafModelExteriorPowerIso _ (dpDifferentialsModules T Y f)
    (SheafOfModules.algebras _ (dpDifferentialsSheaf T Y f))
    (SheafOfModules.sheafifySectionsIso (dpDifferentialsSheaf T Y f)).symm 2

/-- **`Ω²_{T/Y,δ}` is quasi-coherent.**  It is the second exterior power of `Ω_{T/Y,δ}` by
`Crystalline.dpSecondExteriorPowerIso`, that sheaf is quasi-coherent by [Stacks, Tag 07IY]
(`Crystalline.dpDifferentialsSheaf_isQuasicoherent`), and every exterior power of a quasi-coherent
sheaf of modules on a scheme is quasi-coherent
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_exteriorPower`). -/
instance dpSecondExteriorPower_isQuasicoherent :
    (dpSecondExteriorPower T Y f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent T.scheme.ringCatSheaf).prop_of_iso
    (dpSecondExteriorPowerIso T Y f).symm
    (Scheme.Modules.isQuasicoherent_exteriorPower (dpDifferentialsSheaf T Y f) 2)

/-- **The identification of `Ω²_{T/Y,δ}` with `⋀² Ω_{T/Y,δ}`, read as presheaves of modules.**
This is the spelling in which the second-order universal thickening consumes `Ω²_{T/Y,δ}` — it is
the target of the exterior product `Crystalline.dpWedge` and the top summand of `𝒪_{T''}` — so
it is recorded alongside the identification of sheaves it is the image of. -/
def dpSecondExteriorModulesIso :
    dpSecondExteriorModules T Y f ≅
      (Scheme.Modules.toPresheafOfModules T.scheme).obj
        (Scheme.Modules.exteriorPower (dpDifferentialsSheaf T Y f) 2) :=
  (Scheme.Modules.toPresheafOfModules T.scheme).mapIso (dpSecondExteriorPowerIso T Y f)

end Crystalline

end
