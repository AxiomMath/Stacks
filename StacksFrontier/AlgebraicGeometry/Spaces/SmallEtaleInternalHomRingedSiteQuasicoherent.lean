module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# The internal Hom on the small étale site of an algebraic space is quasi-coherent

The internal Hom of two `𝒪_F`-modules on the small étale site of an algebraic space `F` is
written twice in this development.

* `AlgebraicGeometry.Space.smallEtaleInternalHom` is the internal Hom presheaf of
  [Stacks Project, Tag 04TT] on the small étale ringed site, which is a sheaf by
  [Stacks Project, Tag 03EM].  Its sections over an étale chart are the morphisms of the
  restrictions, so it lands one universe above its arguments.  This is the spelling in which
  the sheaf acting on the lifts of [Stacks Project, Tag 061D],
  `AlgebraicGeometry.Space.liftActionSheaf`, is defined.
* `AlgebraicGeometry.RingedSite.internalHomSheafSmall` of the small étale ringed site is the
  same sheaf shrunk back to the module universe along the essential smallness of the small
  étale site.  This is the spelling in which [Stacks Project, Tag 03M1] (6) is proved, as
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_internalHomSheafSmall`.

The two agree on the nose (`AlgebraicGeometry.Space.smallEtaleInternalHom_eq_internalHomSheaf`).
This file carries the quasi-coherence across, so that the internal Hom out of a module of finite
presentation is quasi-coherent **in the spelling its consumers use**.

## The point

`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation` also
concludes quasi-coherence of `AlgebraicGeometry.Space.smallEtaleInternalHom`, but it carries two
hypotheses the present statement does not: a *global* presentation of the first argument rather
than [Stacks Project, Tag 03DL] (7)'s étale-local one, and the assertion `h03DX` that
quasi-coherence is being cartesian on affine charts.  Both were needed because the route to the
conclusion went through the unshrunk sheaf directly.  Going through the shrunk one instead
reaches the same conclusion from that form of Tag 03M1 (6) with nothing carried.

## Main results

* `isQuasicoherentOnSite_smallEtaleInternalHom_of_isFinitePresentationOnSite`:
  **[Stacks Project, Tag 03M1] (6) in the unshrunk spelling** — the internal Hom of two
  quasi-coherent `𝒪_F`-modules with the first of finite presentation on the site is
  quasi-coherent.

## Implementation notes

The identification of the two spellings is `rfl`: both sheaves have
`Stacks.SheafOfModules.InternalHom.internalHom` of the structure sheaf of the small étale ringed
site as their underlying presheaf of modules, and the sheaf condition is a `Prop`.

Quasi-coherence is carried *up* the universe lift here, by
`SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'`, the shrunk sheaf being the one whose
quasi-coherence is proved; the lift is identified with the unshrunk sheaf by
`AlgebraicGeometry.RingedSite.internalHomSheafSmallIso`.

No `@[stacks]` attribute is placed: [Stacks Project, Tag 03M1] (6) is already registered on
`AlgebraicGeometry.Space.isQuasicoherentOnSite_internalHomSheafSmall`, and what is added here is
the reading of it at the other spelling of the same sheaf.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1), clause (6).
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT), the internal Hom.
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM), that it is a sheaf.
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D), the acting sheaf whose
  quasi-coherence this supplies.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Quasi-coherence in the unshrunk spelling -/

/-- **[Stacks Project, Tag 03M1] (6), in the spelling
`AlgebraicGeometry.Space.smallEtaleInternalHom`.**  Let `M`, `N` be quasi-coherent
`𝒪_F`-modules on an algebraic space `F` with `M` of finite presentation on the site
([Stacks Project, Tag 03DL] (7)).  Then `𝓗om_{𝒪_F}(M, N)` is quasi-coherent.

Nothing is carried: the shrunk internal Hom is quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_internalHomSheafSmall`, quasi-coherence is
preserved by raising the universe of the sections, and the raised sheaf is this one by
`AlgebraicGeometry.RingedSite.internalHomSheafSmallIso`. -/
theorem isQuasicoherentOnSite_smallEtaleInternalHom_of_isFinitePresentationOnSite
    (M N : Modules.{u, u} B S hS F hF)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hfp : M.IsFinitePresentationOnSite) :
    (smallEtaleInternalHom B S hS F hF M N).IsQuasicoherentOnSite := by
  let := smallEtaleRingedSite_essentiallySmall B S hS F hF
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    (RingedSite.internalHomSheafSmallIso (smallEtaleRingedSite B S hS F hF) M N) ?_
  exact SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'.{u + 1, u, u, u, u + 1}
    (isQuasicoherentOnSite_internalHomSheafSmall B S hS F hF M N hM hN hfp)

end AlgebraicGeometry.Space

end
