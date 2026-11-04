module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# The resolution property for algebraic spaces

An algebraic space has the *resolution property* when every quasi-coherent module of finite
type on it is a quotient of a finite locally free module. This is the algebraic-space
counterpart of `AlgebraicGeometry.HasResolutionProperty`.

## Main definitions

* `AlgebraicGeometry.Space.HasResolutionProperty` is the resolution property for an algebraic
  space over a scheme.

## Main results

* `AlgebraicGeometry.Space.hasResolutionProperty_iff` characterizes the resolution property by
  the existence of epimorphisms onto finite type quasi-coherent modules from finite locally
  free ones.

## Implementation notes

Modules on the algebraic space `F` are the sheaves of modules
`AlgebraicGeometry.Space.Modules` on its small étale ringed site, and the quasi-coherent ones
are the full subcategory `AlgebraicGeometry.Space.QuasicoherentSheaves` of Stacks 03G9; a
quotient is an epimorphism there. Finite type and finite local freeness are the site-level
notions `SheafOfModules.IsFiniteTypeOnSite` and `SheafOfModules.IsFiniteLocallyFreeOnSite` of
Stacks 03DL, which are phrased by local generation and local triviality on the site and so
require no sheafification instances on its slices. The universe of the module sections stays
independent of the universe of the schemes.

The property is a class, as for schemes; the characterizing equivalence lets it be used
propositionally as well, while the class projection supplies the quotient directly.

## References

* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

/-- **Stacks 0GUS.** An algebraic space has the *resolution property* when every
quasi-coherent module of finite type on it is a quotient of a finite locally free module. -/
@[stacks 0GUS]
class HasResolutionProperty (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) : Prop where
  /-- Every quasi-coherent module of finite type is the target of an epimorphism from a
  finite locally free module. -/
  exists_finiteLocallyFree_quotient
    (M : QuasicoherentSheaves.{u, m} B S hS F hF) [SheafOfModules.IsFiniteTypeOnSite M.obj] :
    ∃ (E : Modules.{u, m} B S hS F hF) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (f : E ⟶ M.obj), Epi f

/-- An algebraic space has the resolution property exactly when every quasi-coherent module of
finite type on it is an epimorphic image of a finite locally free module. -/
@[simp]
theorem hasResolutionProperty_iff (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasResolutionProperty.{u, m} B S hS F hF ↔
      ∀ (M : QuasicoherentSheaves.{u, m} B S hS F hF) [SheafOfModules.IsFiniteTypeOnSite M.obj],
        ∃ (E : Modules.{u, m} B S hS F hF) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
          (f : E ⟶ M.obj), Epi f :=
  ⟨fun h M => h.1 M, fun h => ⟨h⟩⟩

end AlgebraicGeometry.Space

end
