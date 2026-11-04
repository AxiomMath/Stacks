module

public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.VanishingCriterion
public import StacksFrontier.AlgebraicGeometry.SerreCriterionH1.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.TwoSpellingsAgree
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre's criterion for affineness with abelian-group-valued cohomology

`Hgroup R U n` is the right derived functor of the abelian-group-valued sections functor
`secF R U`, which is `SheafOfModules.evaluation R (op U)` followed by the forgetful functor to
abelian groups. By [Stacks, Tag 01F1] part (1), in the form
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`, its value at `ℱ` is the
underlying abelian group of the right derived functor of `SheafOfModules.evaluation R (op U)` at
`ℱ`. Since forgetting the module structure reflects zero objects, vanishing of `Hgroup` gives
vanishing of the module-valued cohomology, and Serre's criterion [Stacks, Tag 01XF] holds with the
hypothesis stated for `Hgroup`.

## Main results

* `Stacks.SerreCriterionH1.isZero_rightDerived_evaluation_of_isZero_hgroup`: vanishing of
  `Hⁿ(U, ℱ)` in the abelian-group spelling gives vanishing in the module spelling.
* `Stacks.SerreCriterionH1.isAffine_of_forall_isZero_hgroup_one_ideal`: [Stacks, Tag 01XF] with
  `Hgroup`. A quasi-compact scheme with `H¹(X, 𝓘) = 0` for every quasi-coherent sheaf of ideals
  is affine.
* `Stacks.SerreCriterionH1.isAffine_of_isFinite_surjective_of_isNoetherian_of_isZero_hgroup`: a
  Noetherian scheme receiving a finite surjective morphism from an affine scheme, and with
  `H¹(X, 𝓘) = 0` for every quasi-coherent sheaf of ideals, is affine.

## References

* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SerreCriterionH1

/-- **Forgetting the module structure reflects zero objects**: a module whose underlying additive
group is zero is zero. -/
theorem isZero_of_isZero_forget₂ {S : RingCat.{u}} {M : ModuleCat.{u} S}
    (h : IsZero ((forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}).obj M)) : IsZero M :=
  ModuleCat.isZero_iff_subsingleton.2
    (AddCommGrpCat.subsingleton_of_isZero (G := (forget₂ _ AddCommGrpCat.{u}).obj M) h)

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **Vanishing of `Hgroup` gives vanishing of the module-valued right derived functor**: if
`Hⁿ(U, ℱ)` vanishes as an abelian group, then so does the `n`-th right derived functor of
`SheafOfModules.evaluation R (op U)` at `ℱ`. -/
theorem isZero_rightDerived_evaluation_of_isZero_hgroup
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} R)]
    (U : Opens X) (n : ℕ) (F : SheafOfModules.{u} R)
    (h : IsZero (Hgroup R U n F)) :
    IsZero (((SheafOfModules.evaluation R (op U)).rightDerived n).obj F) :=
  isZero_of_isZero_forget₂
    (h.of_iso ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso R U n).app F))

/-- **Serre's criterion for affineness, [Stacks, Tag 01XF], with `Hgroup`.** A quasi-compact
scheme on which `H¹(X, 𝓘)` vanishes for every quasi-coherent sheaf of ideals `𝓘 ⊆ 𝒪_X` is
affine. -/
@[ega "III 1.4.7" "(ii), special case"]
theorem isAffine_of_forall_isZero_hgroup_one_ideal (Y : Scheme.{u}) [CompactSpace Y]
    (hH₁ : ∀ I : Subobject (SheafOfModules.unit Y.ringCatSheaf),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (Hgroup Y.ringCatSheaf ⊤ 1 (Subobject.underlying.obj I))) :
    IsAffine Y :=
  Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal Y fun I hI ↦
    isZero_rightDerived_evaluation_of_isZero_hgroup Y.ringCatSheaf ⊤ 1 _ (hH₁ I hI)

/-- A Noetherian scheme receiving a finite surjective morphism from an affine scheme is affine as
soon as `H¹(X, 𝓘) = 0` for every quasi-coherent sheaf of ideals `𝓘 ⊆ 𝒪_X`. -/
theorem isAffine_of_isFinite_surjective_of_isNoetherian_of_isZero_hgroup
    {Z W : Scheme.{u}} (f : Z ⟶ W) [IsFinite f] [Surjective f] [IsAffine Z] [IsNoetherian W]
    (hH₁ : ∀ I : Subobject (SheafOfModules.unit W.ringCatSheaf),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (Hgroup W.ringCatSheaf ⊤ 1 (Subobject.underlying.obj I))) :
    IsAffine W :=
  isAffine_of_forall_isZero_hgroup_one_ideal W hH₁

end Stacks.SerreCriterionH1

end
