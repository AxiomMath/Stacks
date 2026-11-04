module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras

/-!
# Section 17.21 at the canonical package of algebras

Every statement of Stacks Section 17.21 in this library is stated over a package
`SheafOfModules.TensorExteriorSymmetricAlgebras J F` taken as a **hypothesis**. That is the
stronger form — `TensorExteriorSymmetricAlgebras.tensorAlgebraIso`, `exteriorAlgebraIso` and
`symmetricAlgebraIso` identify any two packages over one `F` degreewise, compatibly with the
generators and with multiplication, so a statement quantified over packages is a statement about
the canonical objects. A consumer that wants the conclusion about *the* exterior or symmetric
algebra of a given `F`, with nothing to supply, needs it at one chosen package instead, and on a
ringed space the chosen one is `SheafOfModules.ringedSpaceAlgebras` — the only thing that makes
such an instantiation possible, and the reason this file can exist at all.

This file instantiates there the two conclusions of Tag 01CL. The stalk conclusions of Tag 01CH
already have their canonical-package forms, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerStalk`,
`…Sheaf.SymmetricStalkSheaf`, `…Sheaf.ExteriorStalkUngraded` and `…Sheaf.AlgebraStalkUngraded`.

## Main results

* `Stacks.SheafOfModules.isQuasicoherent_ringedSpaceSymmetricAlgebraSheaf`: **the symmetric
  algebra of a quasi-coherent sheaf of modules on a ringed space is quasi-coherent**, stated at
  `SheafOfModules.ringedSpaceAlgebras`.
* `Stacks.SheafOfModules.isQuasicoherent_ringedSpaceExteriorAlgebraSheaf`: the same for the
  exterior algebra.

## Implementation notes

**No `@[stacks]` attribute.** Tag 01CL is already carried, by the two package-quantified forms
`Stacks.SheafOfModules.isQuasicoherent_symmetricAlgebraSheaf_of_isQuasicoherent` and
`isQuasicoherent_exteriorAlgebraSheaf_of_isQuasicoherent` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras`, which are what the two
results below are those theorems applied to one package. A second carrier of 01CL here would be
duplicate coverage, not a second clause. Tag 01CF, the construction of the package itself, is
carried by `SheafOfModules.ringedSpaceAlgebras`.

**Universes.** Those of the results being instantiated: a ringed space in `Type u` with sections
in `Type u`, and modules in `Type u`. The collapse is forced by
`SheafOfModules.TensorExteriorSymmetricAlgebras` and by the stalkwise route of Tag 01CJ that the
quasi-coherence proof goes through, not chosen here.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
  AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} (F : _root_.SheafOfModules.{u} (structureSheafRing X))
  [F.IsQuasicoherent]

/-- **The symmetric algebra of a quasi-coherent sheaf of modules on a ringed space is
quasi-coherent**, for the canonical package of algebras. -/
theorem isQuasicoherent_ringedSpaceSymmetricAlgebraSheaf :
    (_root_.SheafOfModules.ringedSpaceAlgebras X F).symmetricAlgebraSheaf.IsQuasicoherent :=
  isQuasicoherent_symmetricAlgebraSheaf_of_isQuasicoherent F
    (_root_.SheafOfModules.ringedSpaceAlgebras X F)

/-- **The exterior algebra of a quasi-coherent sheaf of modules on a ringed space is
quasi-coherent**, for the canonical package of algebras. -/
theorem isQuasicoherent_ringedSpaceExteriorAlgebraSheaf :
    (_root_.SheafOfModules.ringedSpaceAlgebras X F).exteriorAlgebraSheaf.IsQuasicoherent :=
  isQuasicoherent_exteriorAlgebraSheaf_of_isQuasicoherent F
    (_root_.SheafOfModules.ringedSpaceAlgebras X F)

end Stacks.SheafOfModules

end
