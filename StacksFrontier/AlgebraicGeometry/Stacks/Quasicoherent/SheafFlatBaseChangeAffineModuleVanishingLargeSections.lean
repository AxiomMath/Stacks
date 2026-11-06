module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineVanishingLargeSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishingLargeCoefficients
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftCohomology
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSite
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage

/-!
# Affine vanishing of module cohomology for `LQCoh^fbc` at module universe `u + 1`

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids with objects in `Type (u + 1)` and
morphisms in `Type u`, and `F` a sheaf of modules on its fppf site with sections in `Type (u + 1)`
in the faithful `LQCoh^fbc(𝒪_𝒳)`. For an object `x` over an affine scheme and `n > 0`, the
module-valued cohomology `Rⁿ Γ(x, -)(F)`, the right derived functor of
`SheafOfModules.evaluation`, vanishes.

`AlgebraicGeometry.Stack.isZero_rightDerived_sheafSections_of_sheafFlatBaseChange_succ` is the
same vanishing for the cohomology of the underlying abelian sheaf. The rings of the structure
sheaf lie in `Type u`, below the sections of the modules, so the comparison of the two
cohomologies (Stacks 03FD, `isZero_rightDerived_evaluation_of_isZero_rightDerived_sheafSections`
in the namespace `Stacks.Cohomology.ObjectSections`) is applied after lifting the rings to
`Type (u + 1)` along `ULift` (`Stacks.UniverseLift.uliftRingTransport`), which changes neither
the sections nor the cohomology
(`Stacks.UniverseLift.RingTransport.isZero_rightDerived_evaluation_iff`).

## Main definitions

* `AlgebraicGeometry.Stack.structureSheafULift`: the structure sheaf with its rings lifted.

## Main results

* `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_succ`: the
  affine vanishing of module cohomology of `LQCoh^fbc` at module universe `u + 1`.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ isGrothendieckAbelian_fppfAbelianSheavesSucc

/-- The structure sheaf with its rings lifted to `Type (u + 1)`, read as a sheaf of rings. -/
abbrev structureSheafULift : Sheaf (associatedTopology B S hS p B.topology) RingCat.{u + 1} :=
  ⟨((structureSheaf B S hS p hp B.topology le_rfl).obj ⋙
      AlgebraicGeometry.SheafOfModules.commRingCatULift.{u, u + 1}) ⋙
      forget₂ CommRingCat RingCat,
    GrothendieckTopology.HasSheafCompose.isSheaf _
      (Stacks.UniverseLift.isSheaf_comp_commRingCatULift _
        (structureSheaf B S hS p hp B.topology le_rfl).property)⟩

include E h in
/-- **Higher module cohomology of `LQCoh^fbc` over an affine object vanishes**, at module
universe `u + 1`. -/
theorem isZero_rightDerived_evaluation_of_sheafFlatBaseChange_succ
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u + 1}
      B E h S hS p hp F.val)
    (x : 𝒳) (hx : IsAffine ((toScheme B S hS p).obj x)) (n : ℕ) (hn : 0 < n) :
    letI := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS p hp B.topology le_rfl
    IsZero (((SheafOfModules.evaluation (ringStructureSheafCore B S hS p hp B.topology le_rfl)
      (op x)).rightDerived n).obj F) := by
  let := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS p hp B.topology le_rfl
  let T := Stacks.UniverseLift.uliftRingTransport.{u + 1}
    (structureSheaf B S hS p hp B.topology le_rfl).obj
  have : EnoughInjectives (SheafOfModules.{u + 1} (structureSheafULift B S hS p hp)) :=
    EnoughInjectives.of_equivalence
      (Stacks.UniverseLift.RingTransport.sheafEquivalence (R := ringStructureSheafCore B S hS p hp
        B.topology le_rfl) (R' := structureSheafULift B S hS p hp) T).inverse
  refine (Stacks.UniverseLift.RingTransport.isZero_rightDerived_evaluation_iff
    (R := ringStructureSheafCore B S hS p hp B.topology le_rfl)
    (R' := structureSheafULift B S hS p hp) T F (op x) n).1 ?_
  open Stacks.Cohomology.ObjectSections in
  exact isZero_rightDerived_evaluation_of_isZero_rightDerived_sheafSections.{0}
    (associatedTopology B S hS p B.topology) (structureSheafULift B S hS p hp)
    ((Stacks.UniverseLift.RingTransport.sheafFunctor (R := ringStructureSheafCore B S hS p hp
      B.topology le_rfl) (R' := structureSheafULift B S hS p hp) T).obj F) x n
    (isZero_rightDerived_sheafSections_of_sheafFlatBaseChange_succ B E h S hS p hp F hF x hx n hn)

end AlgebraicGeometry.Stack
