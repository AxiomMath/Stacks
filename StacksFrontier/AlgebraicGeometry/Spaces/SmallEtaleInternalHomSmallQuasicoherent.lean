module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.InternalHomQuasicoherentChartLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentTensorProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal Hom at the module universe of the schemes is quasi-coherent

`AlgebraicGeometry.Space.smallEtaleInternalHomSmall` is the internal Hom `𝓗om_{𝒪_F}(M, N)` of two
`𝒪_F`-modules with sections in `u`, again with sections in `u`.  Clause (6) of Stacks 03M1,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom`, is about
`AlgebraicGeometry.Space.smallEtaleInternalHom`, whose sections are in `u + 1`.  This file
carries the clause across, which is what makes it usable: everything the tree proves about an
ideal-power quotient over an affine chart is stated for an
`AlgebraicGeometry.Space.Modules.{u, u}`.

The transport needs one generic bridge.  The two universe lifts of the sections of a sheaf of
modules in this development — `Stacks.SheafOfModules.moduleULift`, which the shrinking of
`AlgebraicGeometry.RingedSite.internalHomSheafSmall` is stated against, and
`SheafOfModules.uliftForPresentation`, which the quasi-coherence transfers are stated against —
have the same sections, `ULift` of the sections, but install the module structure differently:
one through `CategoryTheory.PresheafOfModules.ofPresheaf`, the other directly on
`ModuleCat.of`.  They are isomorphic by the identity on sections.

## Main definitions

* `Stacks.SheafOfModules.moduleULiftIsoUliftForPresentation`: **the two universe lifts of the
  sections of a sheaf of modules agree**, by the identity on sections.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHomSmall`: **clause (6) of
  Stacks 03M1 at the module universe of the schemes.**

## Implementation notes

No `@[stacks 03M1]` attribute is carried here: the clause is registered on
`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom`, in
`StacksFrontier.AlgebraicGeometry.Spaces.InternalHomQuasicoherentChartLocal`.  What is below is that
clause read through an isomorphism, not a second proof of it.

The hypotheses are the source's three, exactly as there.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w m t

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **The two universe lifts of the sections of a sheaf of modules agree.**

`Stacks.SheafOfModules.moduleULift` installs the module structure on the lifted sections through
`CategoryTheory.PresheafOfModules.ofPresheaf`, and
`SheafOfModules.uliftForPresentation` installs it directly on `ModuleCat.of`; the sections are
`ULift` of the sections either way, and the scalar action agrees, so the identity on sections is
an isomorphism.

It is what lets the quasi-coherence transfers, which are stated for
`SheafOfModules.uliftForPresentation`, be applied to the shrinking of
`AlgebraicGeometry.RingedSite.internalHomSheafSmall`, which is stated for
`Stacks.SheafOfModules.moduleULift`. -/
def moduleULiftIsoUliftForPresentation (R : Sheaf J RingCat.{w})
    (N : _root_.SheafOfModules.{m} R) :
    (moduleULift.{t} R).obj N ≅ _root_.SheafOfModules.uliftForPresentation.{u, v, w, m, t} N :=
  (_root_.SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by
      intro X Y f
      ext x
      rfl))

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Clause (6) of Stacks 03M1 at the module universe of the schemes.**  For `𝒪_F`-modules
`M`, `N` with sections in `u`, `M` of finite presentation and `N` quasi-coherent, the internal Hom
`AlgebraicGeometry.Space.smallEtaleInternalHomSmall` — the same internal Hom, with its sections
in `u` rather than in `u + 1` — is quasi-coherent.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom`, which carries the
registration of the clause, transported along
`AlgebraicGeometry.Space.smallEtaleInternalHomSmallIso` and
`Stacks.SheafOfModules.moduleULiftIsoUliftForPresentation` and then reflected by
`SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'`.  Quasi-coherence is invariant
under isomorphism and is reflected by the universe lift of the sections, so no hypothesis is
added and none is lost. -/
@[sga "3 III 0.6" "more general"]
theorem isQuasicoherentOnSite_smallEtaleInternalHomSmall (M N : Modules.{u, u} B S hS F hF)
    (hN : N.IsQuasicoherentOnSite) (hMfp : M.IsFinitePresentationOnSite) :
    (smallEtaleInternalHomSmall B S hS F hF M N).IsQuasicoherentOnSite := by
  let hP := _root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  refine _root_.SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'.{u + 1, u, u, u,
    u + 1} ?_
  exact hP.prop_of_iso
    (Stacks.SheafOfModules.moduleULiftIsoUliftForPresentation.{u + 1, u, u, u, u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
      (smallEtaleInternalHomSmall B S hS F hF M N))
    (hP.prop_of_iso (smallEtaleInternalHomSmallIso B S hS F hF M N).symm
      (isQuasicoherentOnSite_smallEtaleInternalHom B S hS F hF M N hN hMfp))

end AlgebraicGeometry.Space

end
