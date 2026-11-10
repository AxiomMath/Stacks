module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Sections on a principal open of a quasi-compact quasi-separated open

Let `X` be a scheme, let `U` be a quasi-compact and quasi-separated open of `X`, and let
`f` be a section of the structure sheaf over `U`. Restricting sections to the principal
open `X.basicOpen f` realizes the sections of a quasi-coherent module over that principal
open as the localization at `f` of the sections over `U`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.restrictionLinearMap`: restriction of module sections
  along an inclusion of opens, regarded as a linear map over the ring of functions on the
  larger open by restriction of scalars.

## Main results

* `AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs`: restriction of the
  sections of a quasi-coherent module to a principal open of a quasi-compact
  quasi-separated open is localization at the defining function.

Mathlib's `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs` is the same statement for
the structure sheaf, and is tagged here as the other half of the covering set.

## Implementation notes

The mathematical content is
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact`: the same
assertion for the restriction map
`AlgebraicGeometry.Scheme.Modules.restrictBasicOpenₗ`, which takes the module structure on
the sections over the principal open as a parameter together with a scalar tower making it
compatible with the native one. All this file adds is the shape asked for in the source:
the module structure obtained by restricting scalars along the restriction map of the
structure sheaf, supplied as a `let` in the statement so that no instance is left in the
environment, and `IsLocalizedModule.Away`, which expresses canonically that restriction
induces an isomorphism after localizing without choosing a model of the localized module.
The scalar tower for that particular module structure holds by `rfl`.

## References

* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

/-- Restriction of sections of a sheaf of modules, as a linear map after restricting
scalars along the corresponding restriction map of functions. -/
noncomputable def restrictionLinearMap {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (i : U ⟶ V) :
    letI : Module Γ(X, V) Γ(M, U) := Module.compHom Γ(M, U) (X.presheaf.map i.op).hom
    Γ(M, V) →ₗ[Γ(X, V)] Γ(M, U) := by
  letI : Module Γ(X, V) Γ(M, U) := Module.compHom Γ(M, U) (X.presheaf.map i.op).hom
  exact
    { toFun := (M.presheaf.map i.op).hom
      map_add' := map_add _
      map_smul' := M.map_smul i }

end Scheme.Modules

/-- On a quasi-compact, quasi-separated open, restriction of sections of a quasi-coherent
module to a principal open is localization at the defining function. -/
@[stacks 01P7 "quasi-coherent modules", ega "III 1.4.5" "H⁰, L = 𝒪_X, qcqs"]
theorem isLocalizedModule_restriction_basicOpen_of_qcqs {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (f : Γ(X, U)) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
      Module.compHom Γ(M, X.basicOpen f)
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
    IsLocalizedModule.Away f
      (Scheme.Modules.restrictionLinearMap M (homOfLE (X.basicOpen_le f))) := by
  let : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom Γ(M, X.basicOpen f)
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  change IsLocalizedModule (Submonoid.powers f) (Scheme.Modules.restrictBasicOpenₗ M f)
  exact Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact M hU hU' f

add_to_stacks 01P7 "the structure sheaf, for a quasi-compact quasi-separated open"
  AlgebraicGeometry.isLocalization_basicOpen_of_qcqs
add_to_ega "I 1.4.1" "special case" AlgebraicGeometry.isLocalization_basicOpen_of_qcqs
add_to_ega "I 9.3.2" "Case L = O" AlgebraicGeometry.isLocalization_basicOpen_of_qcqs
add_to_ega "I 9.3.3" "special case" AlgebraicGeometry.isLocalization_basicOpen_of_qcqs
add_to_ega "III 1.2.2" "special case" AlgebraicGeometry.isLocalization_basicOpen_of_qcqs
add_to_ega "III 1.4.13" "q = 0 and F = O_X" AlgebraicGeometry.isLocalization_basicOpen_of_qcqs
add_to_ega "III 1.4.6" "degree zero, F = O_X" AlgebraicGeometry.isLocalization_basicOpen_of_qcqs
add_to_ega "III 2.1.2" "special case" AlgebraicGeometry.isLocalization_basicOpen_of_qcqs

end AlgebraicGeometry
