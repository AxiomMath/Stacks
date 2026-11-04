module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.AlgebraicGeometry.SerreCriterionH1.Hgroup
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Čech cohomology of a quasi-coherent module for a cover with affine intersections

Let `X` be a scheme, let `U` be an open subset of `X` covered by a family `Ui` all of whose
finite intersections `U_{i₀…i_p}` are affine open, and let `F` be a quasi-coherent
`𝒪_X`-module. Then the canonical comparison from the Čech cohomology of the cover to the
cohomology of `F` over `U` is an isomorphism of `Γ(U, 𝒪_X)`-modules in every degree. This is
[Stacks, Tag 01XD].

## Main results

* `Stacks.Cohomology.CechAffineCover.isIso_cechToDerivedGlobalSections_app_of_isAffineOpen`: the
  derived comparison of [Stacks, Tag 01EQ] is an isomorphism in `D⁺(Γ(U, 𝒪_X))` for such a
  cover.
* `Stacks.Cohomology.CechAffineCover.isIso_cechCohomologyToCohomology_app_of_isAffineOpen`:
  **[Stacks, Tag 01XD]** in the form the source states it, degreewise on cohomology.
* `Stacks.Cohomology.CechAffineCover.isIso_cechCohomologyToCohomology_app_of_isOpenCover`: the
  case `U = ⊤`, i.e. an open cover of the whole scheme.

## Implementation notes

The source states the tag for a cover of the whole scheme; the statement here is for a cover of
an arbitrary open `U`, and the source's statement is the case `U = ⊤`. The Čech complex functor
and the derived global-sections functor of [Stacks, Tag 01EQ] both take values in
`ModuleCat (SectionRing 𝒪_X U)`, so the conclusion is an isomorphism of `Γ(U, 𝒪_X)`-modules.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.CechDerived

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.CechAffineCover

variable (X : Scheme.{u})

/-- **Serre vanishing in the spelling [Stacks, Tag 01ET] consumes.** The higher cohomology of a
quasi-coherent module on an affine open vanishes, stated for the module-valued right derived
functor of `SheafOfModules.evaluation` rather than for `Hgroup`. -/
theorem isZero_rightDerived_evaluation_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent]
    (V : X.Opens) (hV : IsAffineOpen V) (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op V)).rightDerived n).obj F) :=
  Stacks.SerreCriterionH1.isZero_rightDerived_evaluation_of_isZero_hgroup
    X.ringCatSheaf V n F
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F V hV n hn)

variable {I : Type u} (U : X.Opens) (Ui : I → X.Opens) (hU : U = ⨆ i, Ui i)

/-- **The derived Čech comparison is an isomorphism for a cover with affine intersections.** For
a quasi-coherent module `F`, the transformation of [Stacks, Tag 01EQ] from the Čech complex of
the cover to derived global sections on `U` is an isomorphism in the bounded-below derived
category of `Γ(U, 𝒪_X)`-modules. -/
theorem isIso_cechToDerivedGlobalSections_app_of_isAffineOpen
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, Ui (s k)))
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((cechToDerivedGlobalSections X.ringCatSheaf U Ui hU).app F) :=
  CechAcyclic.isIso_cechToDerivedGlobalSections_app X.ringCatSheaf U Ui hU F
    (fun r s m hm ↦ isZero_rightDerived_evaluation_of_isAffineOpen X F _ (haff r s) m hm)

/-- **[Stacks, Tag 01XD]: a cover of a scheme whose finite intersections are affine computes the
cohomology of a quasi-coherent module by its Čech complex.** The canonical comparison
`Ȟᵖ(𝒰, F) ⟶ Hᵖ(U, F)` of [Stacks, Tag 01EQ] is an isomorphism of `Γ(U, 𝒪_X)`-modules for every
`p`. -/
@[stacks 01XD, ega "III 1.4.1", ega "III 1.4.2" "more general"]
theorem isIso_cechCohomologyToCohomology_app_of_isAffineOpen
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, Ui (s k)))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    IsIso ((cechCohomologyToCohomology X.ringCatSheaf U Ui hU (p : ℤ)).app F) :=
  CechAcyclic.isIso_cechCohomologyToCohomology_app X.ringCatSheaf U Ui hU F
    (fun r s q hq ↦ isZero_rightDerived_evaluation_of_isAffineOpen X F _ (haff r s) q hq) p

/-- **[Stacks, Tag 01XD] for a cover of the whole scheme**, which is the form the source states:
`X = ⋃ᵢ Uᵢ` with every finite intersection affine open. -/
theorem isIso_cechCohomologyToCohomology_app_of_isOpenCover (W : I → X.Opens)
    (hW : IsOpenCover W)
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, W (s k)))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    IsIso ((cechCohomologyToCohomology X.ringCatSheaf (⊤ : X.Opens) W hW.symm (p : ℤ)).app F) :=
  isIso_cechCohomologyToCohomology_app_of_isAffineOpen X (⊤ : X.Opens) W hW.symm haff F p

end Stacks.Cohomology.CechAffineCover

end
