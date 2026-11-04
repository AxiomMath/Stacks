module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Čech cohomology of a covering by affine opens computes sheaf cohomology

Let `X` be a scheme, let `Ui : I → X.Opens` be an open covering of an open `U` all of whose
finite intersections `Ui (s 0) ⊓ ⋯ ⊓ Ui (s r)` are affine opens, and let `F` be a quasi-coherent
`𝒪_X`-module. Then the canonical comparison from the Čech cohomology of the covering to the
cohomology of `F` over `U` is an isomorphism of `Γ(U, 𝒪_X)`-modules in every degree. This is
[Stacks, Tag 01XD], and, as in the source, the proof is nothing but
[Stacks, Tag 01XB] fed into [Stacks, Tag 01ET].

## Main results

* `Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup`: the two spellings
  of sheaf cohomology used by the two tags agree on vanishing.
* `Stacks.Cohomology.Affine.isIso_cechCohomologyToCohomology_of_isAffineOpen`:
  **[Stacks, Tag 01XD]**.

## Implementation notes

The two inputs are stated in different spellings of the same group, and the only work here is
the translation. [Stacks, Tag 01XB] is
`Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`, phrased with the library's
abelian-group-valued `Hgroup`, the right derived functor of `Γ(U, -) : Mod(𝒪_X) ⥤ Ab`;
[Stacks, Tag 01ET] is `Stacks.Cohomology.CechAcyclic.isIso_cechCohomologyToCohomology_app`,
whose acyclicity hypothesis is phrased with the right derived functor of
`SheafOfModules.evaluation`, which lands in `Γ(U, 𝒪_X)`-modules. The composite of
`ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying` — which commutes the derived functor
past the forgetful functor `Mod(𝒪_X) ⥤ Ab`-sheaves — with
`ModuleComparison.rightDerivedSectionsForgetIso` of [Stacks, Tag 01F1] identifies the second
with the underlying abelian group of the first, and `forget₂` to abelian groups reflects
vanishing because it leaves the carrier alone. That is
`isZero_rightDerived_evaluation_of_isZero_Hgroup`, and the tag is then a one-line application.

The affineness of the intersections is a hypothesis, exactly as in the source: nothing here
asks for separatedness, and the hypothesis is the form a client with a concrete covering can
discharge directly.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.Cohomology.Affine

open Stacks.Cohomology.CechAcyclic Stacks.Cohomology.CechDerived

section Translation

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]

/-- **The two spellings of `Hⁿ(U, F)` agree on vanishing.** The library's `Hgroup` is the `n`-th
right derived functor of sections over `U` valued in abelian groups; the Čech comparison of
[Stacks, Tag 01ET] is stated against the right derived functor of `SheafOfModules.evaluation`,
valued in `Γ(U, 𝒪)`-modules. The second is the first with its module structure remembered, so
one vanishes exactly when the other does. -/
public theorem isZero_rightDerived_evaluation_of_isZero_Hgroup
    (U : Opens X) (n : ℕ) (F : SheafOfModules.{u} R) (h : IsZero (Hgroup R U n F)) :
    IsZero (((SheafOfModules.evaluation.{u} R (op U)).rightDerived n).obj F) := by
  obtain ⟨-, -, hopen⟩ := ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying
    (Opens.grothendieckTopology X) R
  obtain ⟨eU, -⟩ := hopen U
  have hderived : IsZero ((((sheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (op U)).rightDerived n).obj
      ((SheafOfModules.toSheaf R).obj F)) := IsZero.of_iso h ((eU n).app F).symm
  have hforget : IsZero ((forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}).obj
      (((SheafOfModules.evaluation R (op U)).rightDerived n).obj F)) :=
    IsZero.of_iso hderived ((ModuleComparison.rightDerivedSectionsForgetIso R U n).app F)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.subsingleton_of_isZero hforget

end Translation

/-- **[Stacks, Tag 01XD].** A covering of an open subset of a scheme whose finite intersections
are all affine opens computes the cohomology of a quasi-coherent module by its Čech complex: the
canonical comparison of [Stacks, Tag 01EQ] from Čech cohomology to sheaf cohomology is an
isomorphism of `Γ(U, 𝒪_X)`-modules in every degree. -/
@[stacks 01XD, ega "III 1.4.1", ega "III 1.4.2" "more general"]
public theorem isIso_cechCohomologyToCohomology_of_isAffineOpen
    (X : Scheme.{u}) {I : Type u} (U : X.Opens) (Ui : I → X.Opens) (hU : U = ⨆ i, Ui i)
    (haffine : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, Ui (s k)))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    IsIso ((cechCohomologyToCohomology X.ringCatSheaf U Ui hU (p : ℤ)).app F) :=
  isIso_cechCohomologyToCohomology_app X.ringCatSheaf U Ui hU F
    (fun r s q hq => isZero_rightDerived_evaluation_of_isZero_Hgroup X.ringCatSheaf _ q F
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F _ (haffine r s) q hq)) p

end Stacks.Cohomology.Affine

end
