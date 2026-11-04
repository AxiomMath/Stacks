module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsAdjunction

/-!
# Sections supported on the whole space are all the sections

For a closed subset `Z` of a ringed space `X` the functor `H_Z` of
`Stacks.SheafOfModules.SupportedSections.supportedSectionsFunctor` carves out of a sheaf of
modules the subsheaf of sections whose support lies in `Z`.  When `Z` is all of `X` that is no
condition at all: the support of a section over `U` is by its very definition a subset of `U`, so
the containment `Supp(s) ⊆ Z ∩ U` that defines the subsheaf is satisfied by every section.  This
file records that degeneration, as an isomorphism `H_X ≅ 𝟭` of endofunctors.

It is the degenerate case the Gysin map of [Stacks, Tag 0G86] meets at conormal rank `c = 0`.
There a chart carries an **empty** family of equations, whose common zero locus is therefore the
whole chart, and the target of the local Gysin map of [Stacks, Tag 0G83] is read with supports in
that zero locus.  So the whole tower of local cohomology with supports has to be evaluated at
`Z = X`, where it must collapse; the degree-zero step of that collapse is this file, and
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyOnZeroIso` turns it into the statement
about `ℋ ⁰`.

## Main results

* `Stacks.SheafOfModules.SupportedSections.isIso_supportedSectionsSheafι_of_eq_univ`: the
  inclusion of the subsheaf of sections supported on `Z` is an isomorphism when `Z = X`.
* `Stacks.SheafOfModules.SupportedSections.supportedSectionsFunctorIsoId`: `H_X ≅ 𝟭`, naturally.

## Implementation notes

The hypothesis is `Z = Set.univ` rather than a literal `Set.univ` in the statement so that a
caller holding a *proof* that its closed subset is everything — which is how the empty family of
equations presents itself, through `Stacks.Gysin.equationsClosedSet_empty` — can apply this
directly instead of transporting the conclusion along that proof.  Transporting a natural
isomorphism of endofunctors along an equality of subsets costs an `eqToHom` at every subsequent
use; carrying the equality as a hypothesis costs nothing, the two proofs below using it only to
produce a membership.

Both halves of bijectivity are immediate, and neither needs the characterisation
`Stacks.SheafOfModules.SupportedSections.mem_supportedSectionsSheafι_range_iff` of the range of
the inclusion: the sections of the subsheaf are literally a subtype of the sections of the sheaf,
by `Stacks.SheafOfModules.SupportedSections.supportedSectionsSheafι_app`, so injectivity is
`Subtype.ext` and surjectivity is the construction of the membership proof.  That proof is where
`Z = X` enters, and it enters only as the first component of the pair
`Supp(s) ⊆ Z ∩ U`; the second component, `Supp(s) ⊆ U`, holds for every `Z` because
`AlgebraicGeometry.RingedSpace.ModuleSheaf.suppSection` is defined as a set of points *of* `U`.

## References

* [Stacks Project, Tag 0G6N](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules.SupportedSections

variable {X : RingedSpace.{u, u}}

/-- **A section is supported on the whole space.**  The defining containment of the
supported-sections subsheaf asks that the support of a section over `U` lie in `Z ∩ U`; when `Z`
is everything both components hold for every section, the second because
`AlgebraicGeometry.RingedSpace.ModuleSheaf.suppSection` consists of points of `U`. -/
theorem mem_supportedSubmodule_of_eq_univ {Z : Set X.carrier} (hZ : Z = Set.univ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) (U : (Opens X.carrier)ᵒᵖ)
    (s : F.val.obj U) :
    s ∈ (supportedSubmodule Z
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F)).obj U :=
  fun x hx => ⟨hZ ▸ Set.mem_univ x, hx.1⟩

/-- **Taking the sections supported on the whole space changes nothing**: the inclusion of the
subsheaf into the sheaf is an isomorphism.

It is bijective on the sections over every open — injective because those sections are a subtype
of the sections of the sheaf, surjective by `mem_supportedSubmodule_of_eq_univ` — and a morphism
of sheaves of modules bijective on every group of sections is an isomorphism, by
`Stacks.SheafOfModules.isIso_of_bijective_app`. -/
theorem isIso_supportedSectionsSheafι_of_eq_univ {Z : Set X.carrier} (hZ : Z = Set.univ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    IsIso (supportedSectionsSheafι Z F) :=
  Stacks.SheafOfModules.isIso_of_bijective_app _ fun U =>
    ⟨fun _ _ h => Subtype.ext h,
      fun s => ⟨⟨s, mem_supportedSubmodule_of_eq_univ hZ F U s⟩, rfl⟩⟩

/-- **`H_X ≅ 𝟭`: sections supported on the whole space are all the sections**, as an isomorphism
of endofunctors of sheaves of `𝒪_X`-modules.

The components are the inclusions of the subsheaves, which are isomorphisms by
`isIso_supportedSectionsSheafι_of_eq_univ`, and they are natural in the module by
`supportedSectionsSheafι_naturality`. -/
def supportedSectionsFunctorIsoId (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : Z = Set.univ) :
    supportedSectionsFunctor X Z ≅ Functor.id _ :=
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ (supportedSectionsSheafι Z F)
      (isIso_supportedSectionsSheafι_of_eq_univ hZ F))
    fun f => supportedSectionsSheafι_naturality Z f

end Stacks.SheafOfModules.SupportedSections

end
