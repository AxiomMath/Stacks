module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHomSheafGlue
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteInternalHom
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.InternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# The two constructions of the sheaf of homomorphisms on the small étale site agree

The sheaf `SheafHom_𝒪(F, G)` on the small étale site of a scheme `S` is constructed twice in
this development.

* `AlgebraicGeometry.SmallEtale.sheafHom`, in
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleHomSheafGlue.lean`, is the
  internal hom of presheaves of modules over the commutative-ring-valued structure presheaf of
  the site, together with [Stacks Project, Tag 03EM].  Its sections over an object are the
  linear maps on the localization there, so it lands one universe above its arguments.
* `AlgebraicGeometry.SmallEtale.internalHomSheaf`, in
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleRingedSiteInternalHom.lean`, is the
  internal hom of the *ringed site* `AlgebraicGeometry.smallEtaleRingedSite`, shrunk back to the
  module universe along the essential smallness of the small étale site.

Neither file mentions the other, and no module imported both.  This file identifies them.

## What the identification costs

Nothing: the two structure presheaves are the same functor, `((inclusion ⋙ Over.post) ⋙
Over.forget S).op ⋙ Γ` against `(SmallEtale.toScheme).op ⋙ Γ`, which differ only by the
associativity of `CategoryTheory.Functor.comp`; so
`AlgebraicGeometry.SmallEtale.sheafHom` and
`AlgebraicGeometry.RingedSite.internalHomSheaf` of the ringed site are *definitionally* the same
sheaf of modules, and the comparison with
`AlgebraicGeometry.SmallEtale.internalHomSheaf` is the universe lift
`AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso` already in place.

## Main results

* `AlgebraicGeometry.SmallEtale.sheafHom_eq_internalHomSheaf`: the two constructions agree —
  `sheafHom` is the internal hom of the small étale ringed site.
* `AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIsoSheafHom`: **the comparison of the
  two**, `sheafHom` being the universe lift of
  `AlgebraicGeometry.SmallEtale.internalHomSheaf`.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf_of_isFiniteLocallyFree`:
  **the internal hom out of a finite locally free quasi-coherent sheaf is quasi-coherent, in the
  module universe of the site** — [Stacks Project, Tag 0GNC] carried down the universe lift.

## Implementation notes

`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf_of_isFiniteLocallyFree` is
stated with its arguments read over `(AlgebraicGeometry.smallEtaleRingedSite B S hS).ringSheaf`
rather than over `AlgebraicGeometry.SmallEtale.structureSheaf`.  The two sheaves of rings are
definitionally equal, but instance search does not unfold the projection, so the quasi-coherence of
the arguments is only found at the spelling in which
`AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent` consumes it.

The descent of quasi-coherence along the universe lift is
`AlgebraicGeometry.SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'`, whose lift
`AlgebraicGeometry.SheafOfModules.uliftForPresentation` is the same construction as
`Stacks.SheafOfModules.moduleULift` by
`AlgebraicGeometry.uliftForPresentation_eq_moduleULift`.

No `@[stacks]` attribute is placed: [Stacks Project, Tag 0GNC] is already registered on
`AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`, and what is added here is the
reading of it at one site, in one universe.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two constructions agree -/

/-- **The sheaf of homomorphisms of the small étale site is the internal hom of the small étale
ringed site.**  The two constructions use the same commutative-ring-valued structure presheaf,
written with its composition bracketed in the two ways, so they are the same sheaf of modules on
the nose. -/
theorem sheafHom_eq_internalHomSheaf (F G : SheafOfModules.{u} (structureSheaf B S hS)) :
    sheafHom B S hS F G =
      RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS) F G := rfl

/-- **The comparison of the two constructions of the sheaf of homomorphisms**: the universe lift
of `AlgebraicGeometry.SmallEtale.internalHomSheaf`, which lives in the module universe of the
site, is `AlgebraicGeometry.SmallEtale.sheafHom`, whose sections are the linear maps on the
localizations and so lie one universe above.

This is `AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso` read through
`AlgebraicGeometry.SmallEtale.sheafHom_eq_internalHomSheaf`. -/
def moduleULiftInternalHomSheafIsoSheafHom (F G : SheafOfModules.{u} (structureSheaf B S hS)) :
    (Stacks.SheafOfModules.moduleULift.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS).O)).obj (internalHomSheaf B S hS F G) ≅
      sheafHom B S hS F G :=
  moduleULiftInternalHomSheafIso B S hS F G ≪≫
    eqToIso (sheafHom_eq_internalHomSheaf B S hS F G).symm

/-! ### Quasi-coherence in the module universe of the site -/

/-- **The internal hom out of a finite locally free quasi-coherent sheaf is quasi-coherent, in
the module universe of the small étale site.**

[Stacks Project, Tag 0GNC] gives the quasi-coherence of
`AlgebraicGeometry.RingedSite.internalHomSheaf`, which on the small étale ringed site lives one
universe above the module universe; `AlgebraicGeometry.SmallEtale.internalHomSheaf` is the
descent of that sheaf along the universe lift
(`AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso`), and quasi-coherence descends
along the lift. -/
theorem isQuasicoherentOnSite_internalHomSheaf_of_isFiniteLocallyFree
    (F G : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))
    [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F] :
    (internalHomSheaf B S hS F G).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'.{u + 1, u, u, u, u + 1}
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      (moduleULiftInternalHomSheafIso B S hS F G).symm
      (RingedSite.internalHomSheaf_isQuasicoherent (smallEtaleRingedSite B S hS) F G))

end AlgebraicGeometry.SmallEtale

end
