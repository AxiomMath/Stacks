module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Čech cohomology of a covering by affine opens

A covering of an open subset of a scheme whose finite intersections are all affine computes the
cohomology of a quasi-coherent module. This is the combination of the Čech-to-cohomology
comparison for an acyclic covering with Serre vanishing on an affine open, and it is the form in
which both are usable outside the Čech machinery.

The two inputs are stated in different categories, and reconciling them is the whole content of
this file. The comparison takes its acyclicity hypothesis as the vanishing of the higher right
derived functors of *module-valued* sections `SheafOfModules.evaluation`, whose values are
modules over the ring of sections of the structure sheaf; Serre vanishing is stated for the
abelian-group-valued cohomology `Hgroup`, the right derived functors of the composite of
`SheafOfModules.toSheaf` with sections. The two agree: the comparison
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` of Stacks 01F1 identifies
the underlying abelian group of the first with the second, and forgetting the module structure is
a faithful functor, so it reflects vanishing.

## Main results

* `Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup` — the
  acyclicity hypothesis of Stacks 01ET is the vanishing of `Hgroup`.
* `Stacks.Cohomology.CechAcyclic.isIso_cechCohomologyToCohomology_app_of_isZero_Hgroup` — the
  Čech-to-cohomology comparison of a covering is an isomorphism as soon as the abelian-group
  cohomology of the sheaf vanishes on the intersections of the covering.
* `Stacks.Cohomology.CechAcyclic.isIso_cechCohomologyToCohomology_app_of_isAffineOpen` — for a
  quasi-coherent module on a scheme, a covering of an open by opens whose finite intersections
  are affine computes its cohomology.

## References

* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.Cohomology.CechAcyclic

/-! ### The acyclicity hypothesis from abelian-group cohomology -/

section Hgroup

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)]

/-- **The two spellings of the cohomology of a sheaf of modules over an open subset vanish
together.** They are the right derived functors of `SheafOfModules.evaluation`, with values in
modules over `O(V)`, and the right derived functors `Hgroup` of the underlying
abelian-group-valued sections. The comparison of Stacks 01F1 part (1) identifies the first, after
forgetting the module structure, with the second; the forgetful functor to abelian groups is
additive, so it preserves vanishing, and faithful, so it reflects it. -/
theorem isZero_rightDerived_evaluation_iff_isZero_Hgroup (V : Opens X) (n : ℕ)
    (F : SheafOfModules.{u} O) :
    IsZero (((SheafOfModules.evaluation.{u} O (op V)).rightDerived n).obj F) ↔
      IsZero (Hgroup O V n F) := by
  constructor
  · exact fun h => IsZero.of_iso
      (Functor.map_isZero (forget₂ (ModuleCat.{u} (O.obj.obj (op V))) AddCommGrpCat.{u}) h)
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso O V n).app F).symm
  · intro h
    have hforget : IsZero ((forget₂ (ModuleCat.{u} (O.obj.obj (op V))) AddCommGrpCat.{u}).obj
        (((SheafOfModules.evaluation.{u} O (op V)).rightDerived n).obj F)) :=
      h.of_iso ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso O V n).app F)
    exact (IsZero.iff_id_eq_zero _).2 (Functor.map_injective
      (forget₂ (ModuleCat.{u} (O.obj.obj (op V))) AddCommGrpCat.{u}) (hforget.eq_of_tgt _ _))

variable {I : Type u} (U : Opens X) (Ui : I → Opens X) (hU : U = ⨆ i, Ui i)

/-- **A covering on whose intersections the abelian-group cohomology of a sheaf of modules
vanishes computes that cohomology.** This is Stacks 01ET with its acyclicity hypothesis supplied
in the `Hgroup` spelling, which is the one in which vanishing theorems are available. -/
theorem isIso_cechCohomologyToCohomology_app_of_isZero_Hgroup (F : SheafOfModules.{u} O)
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → I) (q : ℕ), 0 < q →
      IsZero (Hgroup O (⨅ k, Ui (s k)) q F))
    (p : ℕ) :
    IsIso ((Stacks.Cohomology.CechDerived.cechCohomologyToCohomology O U Ui hU
      (p : ℤ)).app F) :=
  isIso_cechCohomologyToCohomology_app O U Ui hU F
    (fun r s q hq =>
      (isZero_rightDerived_evaluation_iff_isZero_Hgroup O (⨅ k, Ui (s k)) q F).2
        (hac r s q hq)) p

end Hgroup

/-! ### Coverings of a scheme by affine opens -/

/-- **A covering whose finite intersections are affine computes the cohomology of a quasi-coherent
module.** Let `X` be a scheme, `F` a quasi-coherent module on `X`, and let the open `U` be the
union of a family `Ui` such that every intersection of finitely many members of the family is an
affine open. Then the Čech-to-cohomology comparison of the covering is an isomorphism in every
degree.

Serre vanishing on an affine open (Stacks 01XB) supplies the acyclicity hypothesis of
Stacks 01ET through
`Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup`. -/
@[ega "III 1.4.2" "more general"]
theorem isIso_cechCohomologyToCohomology_app_of_isAffineOpen (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] {I : Type u} (U : X.Opens) (Ui : I → X.Opens) (hU : U = ⨆ i, Ui i)
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, Ui (s k))) (p : ℕ) :
    IsIso ((Stacks.Cohomology.CechDerived.cechCohomologyToCohomology X.ringCatSheaf U Ui hU
      (p : ℤ)).app F) :=
  isIso_cechCohomologyToCohomology_app_of_isZero_Hgroup X.ringCatSheaf U Ui hU F
    (fun r s q hq =>
      Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F
        (⨅ k, Ui (s k)) (haff r s) q hq) p

end Stacks.Cohomology.CechAcyclic

end
