module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyAbelianDegreeOne

/-!
# Naturality of the degree-one comparison on Čech cocycles

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings. The map
`Stacks.Cech.Hypercohomology.abelianToModuleH1 : H¹(X, ℱ_{ab}) ⟶ H¹(X, ℱ)` sends the class of a
Čech `1`-cocycle of the underlying abelian sheaf of a sheaf of `𝒪_X`-modules `ℱ` to the class of
the same cocycle in the cohomology of `ℱ` as a sheaf of modules. This file proves that it is
natural in `ℱ` for morphisms of sheaves of `𝒪_X`-modules: both sides carry a cocycle to the
pushed-forward cocycle.

All names are in the namespace `Stacks.Cech.Hypercohomology`.

## Main definitions

* `pushCocycle`: the push-forward of a Čech `1`-cocycle along a morphism of sheaves of modules.

## Main results

* `abelianToModuleH1_naturality`: naturality in the sheaf.
* `moduleClassOfCocycle_naturality`: naturality of the class of a Čech cocycle.

## References

* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.LerayLowDegree (abelianCohomology)

universe u

namespace Stacks.Cech.Hypercohomology

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {F G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G)

/-- The Čech `1`-cocycle of the underlying abelian sheaf of `𝒢` obtained by pushing a cocycle of
`ℱ` forward along a morphism of sheaves of modules. -/
def pushCocycle {I : Type u} (Ui : I → Opens X)
    (z : CechCochains.cocycles1 Ui (abelianSheaf F).presheaf) :
    CechCochains.cocycles1 Ui (abelianSheaf G).presheaf :=
  ⟨Stacks.Cohomology.CechOne.push Ui ((SheafOfModules.toSheaf _).map f).hom 1 z.val, by
    rw [CechCochains.mem_cocycles1_iff, ← Stacks.Cohomology.CechOne.push_cechD,
      (CechCochains.mem_cocycles1_iff _ _ _).mp z.2, map_zero]⟩

/-- **The class of a Čech cocycle is natural in the sheaf of modules.** -/
theorem moduleClassOfCocycle_naturality {I : Type u} (Ui : I → Opens X) (hUi : ⊤ = ⨆ i, Ui i)
    (z : CechCochains.cocycles1 Ui (abelianSheaf F).presheaf) :
    hypercohomologyMap O (singlePlusMap O f) 1 (moduleClassOfCocycle F Ui hUi z) =
      moduleClassOfCocycle G Ui hUi (pushCocycle f Ui z) :=
  hypercohomologyMap_cechCocycleClass Ui hUi f z.val _

/-- **The degree-one comparison `H¹(X, ℱ_{ab}) ⟶ H¹(X, ℱ)` is natural in the sheaf of
modules.** -/
theorem abelianToModuleH1_naturality
    (x : (abelianCohomology.{u, u} X ⊤ 1).obj (abelianSheaf F)) :
    abelianToModuleH1 G ((abelianCohomology.{u, u} X ⊤ 1).map
        ((SheafOfModules.toSheaf _).map f) x) =
      hypercohomologyMap O (singlePlusMap O f) 1 (abelianToModuleH1 F x) := by
  obtain ⟨I, Ui, hUi, z, rfl⟩ := exists_cechH1ToRightDerivedSections_eq (abelianSheaf F) x
  rw [abelianToModuleH1_cechH1ToRightDerivedSections, moduleClassOfCocycle_naturality]
  have h := Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections_naturality.{u, u, u} X ⊤ Ui hUi
    ((SheafOfModules.toSheaf _).map f) z (pushCocycle f Ui z) fun _ => rfl
  rw [show (abelianCohomology.{u, u} X ⊤ 1).map ((SheafOfModules.toSheaf _).map f) =
    (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)).rightDerived
      1).map ((SheafOfModules.toSheaf _).map f) from rfl, h,
    abelianToModuleH1_cechH1ToRightDerivedSections]

end Stacks.Cech.Hypercohomology

end
