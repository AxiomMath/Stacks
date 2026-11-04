module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreSheafNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Cohomology of a quasi-coherent module as ordered Čech cohomology, naturally

Let `X` be a scheme and `W : ι → X.Opens` a covering of `X`, indexed by a linearly ordered type
in the universe of `X`, all of whose finite intersections are affine. For a quasi-coherent
`𝒪_X`-module `G` the cohomology group `Hᵖ(X, G)` — the right derived functor `Hgroup` of the
abelian-group-valued global sections — is the homology of the ordered Čech complex of `G` for the
covering ([Stacks, Tags 01XD, 01FJ]), and the identification is natural in `G`.

The isomorphism is the composite of three isomorphisms of the library: the comparison of [Stacks, Tag 01F1]
between `Hgroup` and the module-valued derived functor of sections, the Čech comparison
`Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived` of [Stacks, Tag 01XD], and the comparison
`Stacks.Cohomology.CechSheaf.orderedCechHomologyModuleIso` of the full and the ordered Čech
complexes [Stacks, Tag 01FJ]; each is natural, which gives the naturality square.

## Main definitions

* `Stacks.Algebraization.hgroupIsoOrderedCechHomology`: the identification.

## Main results

* `Stacks.Algebraization.hgroupIsoOrderedCechHomology_naturality`: its naturality.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.Cohomology.CechSheaf

universe u

namespace Stacks.Algebraization

variable (X : Scheme.{u}) {ι : Type u} [LinearOrder ι] (W : ι → X.Opens)
  (hW : (⊤ : X.Opens) = ⨆ i, W i)
  (haff : ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ k, W (s k)))

/-- **`Hᵖ(X, G)` is the homology of the ordered Čech complex of an affine covering**, as abelian
groups, for a quasi-coherent `G`. -/
def hgroupIsoOrderedCechHomology (G : X.Modules) [G.IsQuasicoherent] (p : ℕ) :
    Hgroup X.ringCatSheaf ⊤ p G ≅
      (forget₂ (ModuleCat.{u} (SectionRing X.ringCatSheaf ⊤)) AddCommGrpCat.{u}).obj
        ((orderedModuleComplex ⊤ W hW G).homology p) :=
  ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤ p).app
      G).symm ≪≫
    (forget₂ (ModuleCat.{u} (SectionRing X.ringCatSheaf ⊤)) AddCommGrpCat.{u}).mapIso
      (Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived X ⊤ W hW haff G p) ≪≫
    (forget₂ (ModuleCat.{u} (SectionRing X.ringCatSheaf ⊤)) AddCommGrpCat.{u}).mapIso
      (orderedCechHomologyModuleIso ⊤ W hW G p).symm

/-- **The identification is natural in the quasi-coherent module.** -/
theorem hgroupIsoOrderedCechHomology_naturality {G G' : X.Modules} [G.IsQuasicoherent]
    [G'.IsQuasicoherent] (φ : G ⟶ G') (p : ℕ) :
    (Hfunctor X.ringCatSheaf ⊤ p).map φ ≫ (hgroupIsoOrderedCechHomology X W hW haff G' p).hom =
      (hgroupIsoOrderedCechHomology X W hW haff G p).hom ≫
        (forget₂ (ModuleCat.{u} (SectionRing X.ringCatSheaf ⊤)) AddCommGrpCat.{u}).map
          (HomologicalComplex.homologyMap (orderedModuleMap ⊤ W hW φ) p) := by
  have h₁ : (Hfunctor X.ringCatSheaf ⊤ p).map φ ≫
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
        p).app G').inv =
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
        p).app G).inv ≫
        (forget₂ (ModuleCat.{u} (SectionRing X.ringCatSheaf ⊤)) AddCommGrpCat.{u}).map
          (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived p).map φ) :=
    ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
      p).inv.naturality φ)
  have h₂ := Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived_naturality X ⊤ W hW haff φ p
  have h₃ := sq_inv _ _ _ _ (orderedCechHomologyModuleIso_naturality ⊤ W hW φ p)
  have h₂' := (Functor.map_comp _ _ _).symm.trans ((congrArg
    (forget₂ (ModuleCat.{u} (SectionRing X.ringCatSheaf ⊤)) AddCommGrpCat.{u}).map h₂).trans
      (Functor.map_comp _ _ _))
  have h₃' := (Functor.map_comp _ _ _).symm.trans ((congrArg
    (forget₂ (ModuleCat.{u} (SectionRing X.ringCatSheaf ⊤)) AddCommGrpCat.{u}).map h₃).trans
      (Functor.map_comp _ _ _))
  exact paste_three _ _ _ _ _ _ _ _ _ _ h₁ h₂' h₃'

end Stacks.Algebraization

end
