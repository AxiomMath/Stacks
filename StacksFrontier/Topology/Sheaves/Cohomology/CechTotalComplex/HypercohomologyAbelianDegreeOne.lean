module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologySingleCochains
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.LowDegreeSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.SquareZeroExtensionBoundaryDerivation
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.LocalTriviality

/-!
# First cohomology of a sheaf of modules and of its underlying abelian sheaf

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings and `ℱ` a sheaf of
`𝒪_X`-modules. Every class of `H¹(X, ℱ)`, computed as an abelian sheaf, is the class of a Čech
`1`-cocycle on some open covering: it is the class of a torsor ([Stacks, Tag 02FQ]), and the
transition cocycle of local sections of the torsor represents it. Sending that Čech cocycle to its
class in the cohomology of `ℱ` as a sheaf of modules is well defined, because the comparison of
Čech classes with abelian-sheaf cohomology is injective on every covering
([Stacks, Tag 0B8R]) and compatible with refinement. This is the identification of
[Stacks, Tag 03FD] in degree one, computed on Čech cocycles.

## Main definitions

* `Stacks.Cech.Hypercohomology.abelianToModuleH1`: the map
  `H¹(X, ℱ_{ab}) ⟶ H¹(X, ℱ)` on Čech classes.

## Main results

* `Stacks.Cech.Hypercohomology.exists_cechH1ToRightDerivedSections_eq`: every class of
  `H¹(X, ℱ_{ab})` is a Čech class.
* `Stacks.Cech.Hypercohomology.abelianToModuleH1_cechH1ToRightDerivedSections`: the map on the
  class of a Čech cocycle.

## References

* [Stacks Project, Tag 02FQ](https://stacks.math.columbia.edu/tag/02FQ)
* [Stacks Project, Tag 0B8R](https://stacks.math.columbia.edu/tag/0B8R)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (abSections)
open Stacks.Cohomology.LerayLowDegree (abelianCohomology)
open Stacks.Cohomology.SheafTorsor

universe u

namespace Stacks.Cech.Hypercohomology

variable {X : TopCat.{u}}

/-- **Every class of `H¹(X, H)` is a Čech class**, on the covering by the neighbourhoods of the
points on which a torsor representing it has a section. -/
theorem exists_cechH1ToRightDerivedSections_eq (H : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : (abelianCohomology.{u, u} X ⊤ 1).obj H) :
    ∃ (I : Type u) (Ui : I → Opens X) (hUi : ⊤ = ⨆ i, Ui i)
      (z : CechCochains.cocycles1 Ui H.presheaf),
      Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi H
        (CechCochains.cls Ui H.presheaf z) = x := by
  obtain ⟨c, hc⟩ := (torsorClassEquivSheafCohomologyOne X H).surjective x
  obtain ⟨F, rfl⟩ := Quotient.exists_rep c
  choose Ui hx s using F.isTorsor.2
  have hUi : (⊤ : Opens X) = ⨆ p, Ui p :=
    (eq_top_iff.2 fun p _ => Opens.mem_iSup.2 ⟨p, hx p⟩).symm
  refine ⟨X, Ui, hUi, torsorTransitionCocycle F Ui fun p => (s p).some, ?_⟩
  rwa [← torsorClassEquivSheafCohomologyOne_of_cocycle X H F Ui hUi _ _
    (torsorTransitionCocycle_spec F Ui _)]

variable {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (F : SheafOfModules.{u} (ringSheaf O))

/-- The sheaf of abelian groups underlying a sheaf of `𝒪_X`-modules. -/
abbrev abelianSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (SheafOfModules.toSheaf (ringSheaf O)).obj F

/-- **The class in `H¹(X, ℱ)` of a Čech `1`-cocycle of the underlying abelian sheaf.** -/
def moduleClassOfCocycle {I : Type u} (Ui : I → Opens X) (hUi : ⊤ = ⨆ i, Ui i)
    (z : CechCochains.cocycles1 Ui (abelianSheaf F).presheaf) :
    hypercohomology O (singlePlus O F 0) 1 :=
  cechCocycleClass Ui hUi F z.val ((CechCochains.mem_cocycles1_iff _ _ _).mp z.2)

/-- **Cocycles with the same abelian-sheaf class have the same class in `H¹(X, ℱ)`.** Both are
refined to the common refinement of the two coverings, where their abelian-sheaf classes agree,
hence ([Stacks, Tag 0B8R]) they differ by a Čech coboundary. -/
theorem moduleClassOfCocycle_eq {I J : Type u} (Ui : I → Opens X) (hUi : ⊤ = ⨆ i, Ui i)
    (Vj : J → Opens X) (hVj : ⊤ = ⨆ j, Vj j)
    (z : CechCochains.cocycles1 Ui (abelianSheaf F).presheaf)
    (z' : CechCochains.cocycles1 Vj (abelianSheaf F).presheaf)
    (h : Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi (abelianSheaf F)
        (CechCochains.cls Ui _ z) =
      Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections X ⊤ Vj hVj (abelianSheaf F)
        (CechCochains.cls Vj _ z')) :
    moduleClassOfCocycle F Ui hUi z = moduleClassOfCocycle F Vj hVj z' := by
  let W : I × J → Opens X := fun ij => Ui ij.1 ⊓ Vj ij.2
  have hW : ⊤ = ⨆ ij, W ij := iSup_inf_eq_top Ui hUi Vj hVj
  have h₁ : ∀ ij, W ij ≤ Ui (Prod.fst ij) := fun _ => inf_le_left
  have h₂ : ∀ ij, W ij ≤ Vj (Prod.snd ij) := fun _ => inf_le_right
  let a := CechCochains.refinementCocycles1 Ui W Prod.fst h₁ (abelianSheaf F).presheaf z
  let b := CechCochains.refinementCocycles1 Vj W Prod.snd h₂ (abelianSheaf F).presheaf z'
  have hab : CechCochains.cls W _ a = CechCochains.cls W _ b := by
    refine cechH1ToRightDerivedSections_injective.{u, u, u} (abelianSheaf F) W hW ?_
    have ea :=
      Stacks.Cohomology.SquareZeroBoundary.cechH1ToRightDerivedSections_refinement.{u, u, u, u}
        Ui W Prod.fst h₁ hUi hW (abelianSheaf F) (CechCochains.cls Ui _ z)
    have eb :=
      Stacks.Cohomology.SquareZeroBoundary.cechH1ToRightDerivedSections_refinement.{u, u, u, u}
        Vj W Prod.snd h₂ hVj hW (abelianSheaf F) (CechCochains.cls Vj _ z')
    rw [CechCochains.refinementCechH1_cls] at ea eb
    exact ea.trans (h.trans eb.symm)
  obtain ⟨t, ht⟩ := (CechCochains.cls_eq_zero_iff W _ (a - b)).mp (by
    rw [CechCochains.cls, QuotientAddGroup.mk_sub]
    exact sub_eq_zero.mpr hab)
  have hrefa := cechCocycleClass_refinement Ui hUi F W hW Prod.fst h₁ z.val
    ((CechCochains.mem_cocycles1_iff _ _ _).mp z.2)
  have hrefb := cechCocycleClass_refinement Vj hVj F W hW Prod.snd h₂ z'.val
    ((CechCochains.mem_cocycles1_iff _ _ _).mp z'.2)
  unfold moduleClassOfCocycle
  rw [← hrefa, ← hrefb]
  refine cechCocycleClass_eq_of_eq_add W hW F _ _ _ _ t ?_
  rw [ht]
  change a.val = b.val + (a - b).val
  rw [AddSubgroup.coe_sub]
  abel

/-- **The identification `H¹(X, ℱ_{ab}) ⟶ H¹(X, ℱ)` of [Stacks, Tag 03FD] in degree one,
on Čech cocycles**: a class of the underlying abelian sheaf is represented by a Čech `1`-cocycle
on some open covering (`exists_cechH1ToRightDerivedSections_eq`), and is sent to the class of that
cocycle in the cohomology of `ℱ` as a sheaf of modules. By `moduleClassOfCocycle_eq` it does not
depend on the cocycle. -/
def abelianToModuleH1 (x : (abelianCohomology.{u, u} X ⊤ 1).obj (abelianSheaf F)) :
    hypercohomology O (singlePlus O F 0) 1 :=
  moduleClassOfCocycle F
    (exists_cechH1ToRightDerivedSections_eq (abelianSheaf F) x).choose_spec.choose
    (exists_cechH1ToRightDerivedSections_eq (abelianSheaf F) x).choose_spec.choose_spec.choose
    (exists_cechH1ToRightDerivedSections_eq (abelianSheaf F)
      x).choose_spec.choose_spec.choose_spec.choose

/-- **`H¹(X, ℱ_{ab}) ⟶ H¹(X, ℱ)` on the class of a Čech cocycle** is the class of the cocycle. -/
theorem abelianToModuleH1_cechH1ToRightDerivedSections {I : Type u} (Ui : I → Opens X)
    (hUi : ⊤ = ⨆ i, Ui i) (z : CechCochains.cocycles1 Ui (abelianSheaf F).presheaf) :
    abelianToModuleH1 F (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi
      (abelianSheaf F) (CechCochains.cls Ui _ z)) = moduleClassOfCocycle F Ui hUi z :=
  moduleClassOfCocycle_eq F _ _ Ui hUi _ z
    (exists_cechH1ToRightDerivedSections_eq (abelianSheaf F)
        _).choose_spec.choose_spec.choose_spec.choose_spec

end Stacks.Cech.Hypercohomology
