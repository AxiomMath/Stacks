module

public import Mathlib.Algebra.Module.Presentation.Tautological
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Presentation
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf associated to a module is quasi-coherent

For a ringed space `X` and a ring homomorphism `α : R ⟶ Γ(X, 𝒪_X)`, construction (3) of
Stacks 01BH sends an `R`-module `M` to a sheaf of `𝒪_X`-modules `M̃`. It is quasi-coherent, for
every `M`: a presentation of `M` by generators and relations gives a presentation of `M̃`, and a
sheaf of modules with a presentation is quasi-coherent.

## Main definitions

* `Stacks.AssociatedSheaf.quasicoherentAssociatedSheafFunctor`: construction (3) read as a functor
  from `R`-modules to the full subcategory of quasi-coherent sheaves of `𝒪_X`-modules, which is
  the form clause (2) of Stacks 01BH states it in.

## Main results

* `Stacks.AssociatedSheaf.isQuasicoherent_associatedSheafFunctor_obj`: `M̃` is quasi-coherent.

## Implementation notes

No finiteness is needed, because every module has a presentation:
`Module.Presentation.tautological` takes one generator for each element and the additivity and
homogeneity relations between them. `Stacks.AssociatedSheaf.associatedSheaf_isFinitePresentation`
is the finitely presented refinement and needs the finiteness, since it asserts a *finite*
presentation of the associated sheaf.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01BE](https://stacks.math.columbia.edu/tag/01BE), quasi-coherence.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AssociatedSheaf

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

/-- **Stacks 01BH and 01BE.** The sheaf of `𝒪_X`-modules associated to an `R`-module along a
ring homomorphism `R ⟶ Γ(X, 𝒪_X)` is quasi-coherent, with no hypothesis on the module: the
tautological presentation of the module gives a presentation of the associated sheaf. -/
@[stacks 01BH "ℱ_M is quasi-coherent"]
theorem isQuasicoherent_associatedSheafFunctor_obj (X : RingedSpace.{u, u}) {R : Type u}
    [CommRing R] (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat.{u} R) :
    ((associatedSheafFunctor.{u, u} X α).obj M).IsQuasicoherent :=
  (sheafPresentation.{u} X α (Module.Presentation.tautological R M)).isQuasicoherent

variable (X : RingedSpace.{u, u}) {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- **Stacks 01BH, clause (2): the construction is a functor into quasi-coherent sheaves.**
Construction (3) lifts through the full subcategory of quasi-coherent sheaves of `𝒪_X`-modules,
by `Stacks.AssociatedSheaf.isQuasicoherent_associatedSheafFunctor_obj`. The colimit-preservation
half of the clause is
`Stacks.AssociatedSheaf.preservesColimitsOfSize_associatedSheafFunctor`. -/
@[stacks 01BH "a functor from R-modules to quasi-coherent sheaves on X"]
noncomputable def quasicoherentAssociatedSheafFunctor : ModuleCat.{u} R ⥤
    (SheafOfModules.isQuasicoherent
      (structureSheafRing X)).FullSubcategory :=
  ObjectProperty.lift _ (associatedSheafFunctor.{u, u} X α)
    (isQuasicoherent_associatedSheafFunctor_obj X α)

end Stacks.AssociatedSheaf

end
