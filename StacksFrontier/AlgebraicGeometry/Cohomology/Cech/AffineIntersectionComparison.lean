module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Čech cohomology computes the cohomology of a quasi-coherent module

Let `X` be a scheme and let `U : I → X.Opens` be an open covering of `X` all of whose finite
intersections `U_{i₀} ⊓ … ⊓ U_{iₚ}` are affine. For a quasi-coherent `𝒪_X`-module `ℱ` the
canonical comparison from the Čech cohomology of the covering to the cohomology of `ℱ` is an
isomorphism in every degree, so that

`Ȟᵖ(𝒰, ℱ) = Hᵖ(X, ℱ)` as `Γ(X, 𝒪_X)`-modules for all `p`.

This is [Stacks, Tag 01XD]. The comparison is the component at `ℱ` of the natural
transformation `Stacks.Cohomology.CechDerived.cechCohomologyToCohomology`, so the statement is
about the canonical map and not merely about an abstract isomorphism.

## Main results

* `Stacks.Cohomology.Cech.isZero_rightDerived_evaluation_of_isZero_hgroup`: the module-valued
  cohomology of a module on a scheme vanishes as soon as the corresponding cohomology group
  does.
* `Stacks.Cohomology.Cech.isIso_cechCohomologyToCohomology_app_of_isAffineOpen`:
  [Stacks, Tag 01XD], the comparison from Čech cohomology to cohomology is an isomorphism for a
  covering with affine finite intersections.
* `Stacks.Cohomology.Cech.isIso_cechCohomologyToCohomology_app_of_affineDiagonal`: the same for
  a covering by affine opens of a scheme with affine diagonal, in particular of a separated
  scheme.

## Implementation notes

The hypothesis of [Stacks, Tag 01ET] is the vanishing, in positive degrees, of the right
derived functors of the *module*-valued sections functor
`CategoryTheory.SheafOfModules.evaluation` on each intersection selected by a tuple, whereas
[Stacks, Tag 01XB] is stated for `Stacks.Cohomology.Hgroup`, the right derived functors of the
abelian-group-valued sections functor. The two are identified by [Stacks, Tag 01F1] part (1),
available as `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`; vanishing
transports across it because an abelian group isomorphic to a zero object is a subsingleton and
a subsingleton module is a zero object.

For a scheme with affine diagonal the finite intersections of a family of affine opens are
affine by `AlgebraicGeometry.IsAffineOpen.iInf`, which is why the covering in the second
statement need only consist of affine opens; the tuples are indexed by `Fin (p + 1)`, which is
finite and nonempty, so no further hypothesis on the index type is needed.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 0BDX](https://stacks.math.columbia.edu/tag/0BDX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.Cech

attribute [local instance] HasDerivedCategory.standard

/-- **The module-valued cohomology of a module on a scheme vanishes with its cohomology
group.** The right derived functors of the module-valued sections functor on an open subset and
the cohomology groups `Stacks.Cohomology.Hgroup` are identified by [Stacks, Tag 01F1] part (1),
so a vanishing cohomology group forces the corresponding module to be a zero object. -/
public theorem isZero_rightDerived_evaluation_of_isZero_hgroup (X : Scheme.{u}) (U : X.Opens)
    (F : X.Modules) (p : ℕ) (h : IsZero (Hgroup X.ringCatSheaf U p F)) :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op U)).rightDerived p).obj F) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    (AddCommGrpCat.subsingleton_of_isZero
      (h.of_iso ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
        X.ringCatSheaf U p).app F)))

/-- **[Stacks, Tag 01XD].** Let `X` be a scheme and let `U` be an open covering of `X` such
that every intersection `U_{i₀} ⊓ … ⊓ U_{iₚ}` is affine. For a quasi-coherent `𝒪_X`-module `ℱ`
the canonical comparison from the Čech cohomology of the covering to the cohomology of `ℱ` is
an isomorphism of `Γ(X, 𝒪_X)`-modules in every degree. -/
@[stacks 01XD, ega "III 1.4.1"]
public theorem isIso_cechCohomologyToCohomology_app_of_isAffineOpen (X : Scheme.{u})
    {I : Type u} (U : I → X.Opens) (hU : IsOpenCover U)
    (hUaffine : ∀ (p : ℕ) (i : Fin (p + 1) → I), IsAffineOpen (⨅ j, U (i j)))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    IsIso ((Stacks.Cohomology.CechDerived.cechCohomologyToCohomology X.ringCatSheaf
      (⊤ : X.Opens) U hU.symm (p : ℤ)).app F) :=
  Stacks.Cohomology.CechAcyclic.isIso_cechCohomologyToCohomology_app X.ringCatSheaf ⊤ U hU.symm
    F (fun r s q hq => isZero_rightDerived_evaluation_of_isZero_hgroup X _ F q
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F _
        (hUaffine r s) q hq)) p

/-- **Čech cohomology computes cohomology for an affine covering of a scheme with affine
diagonal.** On such a scheme — in particular on a separated scheme — the finite intersections
of affine opens are affine, so [Stacks, Tag 01XD] applies to every covering by affine opens. -/
@[ega "III 1.4.1" "more general", ega "III 1.4.2" "special case"]
public theorem isIso_cechCohomologyToCohomology_app_of_affineDiagonal (X : Scheme.{u})
    [IsAffineHom (pullback.diagonal (terminal.from X))] {I : Type u} (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaffine : ∀ i, IsAffineOpen (U i)) (F : X.Modules)
    [F.IsQuasicoherent] (p : ℕ) :
    IsIso ((Stacks.Cohomology.CechDerived.cechCohomologyToCohomology X.ringCatSheaf
      (⊤ : X.Opens) U hU.symm (p : ℤ)).app F) :=
  isIso_cechCohomologyToCohomology_app_of_isAffineOpen X U hU
    (fun _ i => IsAffineOpen.iInf fun j => hUaffine (i j)) F p

end Stacks.Cohomology.Cech

end
