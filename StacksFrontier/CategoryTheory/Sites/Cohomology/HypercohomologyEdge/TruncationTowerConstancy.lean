module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
import StacksCore.Tactic.StacksAttribute

/-! # The hypercohomology tower of a truncation tower is eventually constant

Let `(C, O)` be a ringed site, `U` an object of `C` and `K` an object of the unbounded derived
category of `O`-modules whose cohomology sheaves have no higher cohomology over `U`. This file
proves that the inverse system of hypercohomology modules

`n ↦ H^j(U, τ_{≥ -n} K)`

has invertible transition maps as soon as `-j ≤ n`. Both the inverse limit and the first derived
inverse limit of such a system are therefore computed by any late enough term, which is the step
of Stacks 0BKZ that turns the Milnor sequence of the truncation tower into the identification
`H^j(U, K) = Γ(U, H^j(K))`.

The mechanism is the comparison triangle of two truncation levels,
`Stacks.TruncationLevel.exists_distTriang_truncGE`: the step from `τ_{≥ -(n+1)}K` to `τ_{≥ -n}K`
has for its fibre the one-step interval truncation, which is the cohomology sheaf `H^{-(n+1)}(K)`
placed in degree `-(n+1)`. Derived sections over `U` is an exact functor of triangulated
categories, so it carries that triangle to a distinguished triangle, and the hypothesis on `K`
says exactly that the derived sections of the fibre are concentrated in the single degree
`-(n+1)`: above that degree by the vanishing of the classical higher right derived functors of
evaluation, below it by left t-exactness of the unbounded right derived functor. A map in a
distinguished triangle whose complementary vertex has no cohomology in the two adjacent degrees is
inverted by cohomology, which gives the claim for every `j > -(n+1)`.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.isZero_homology_derivedSections_truncLTGE`: the derived
  sections of the one-step interval truncation are concentrated in its own degree.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_homologyMap_derivedSections_natTransTruncGEOfLE`:
  one step of the truncation tower is invertible on degree-`j` hypercohomology above the step.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_homologyMap_derivedSections_truncGETower_map`: the
  same, indexed as the transition maps of `Stacks.DerivedLimit.truncGETower`.

## Implementation notes

The vanishing hypothesis is phrased with `CategoryTheory.Functor.rightDerived` of evaluation at
`U`, which is the form the statement of Stacks 0BKZ uses, and it is needed over the single object
`U` only -- the hypothesis of the tag over a whole covering collection is what the *other* half of
its proof, the convergence of the truncation tower, consumes.

Exactness of derived sections is `Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor`,
whose conclusion is typeable only under the shift-commutation datum attached to the unit; that
datum is therefore bound before the instance is introduced.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing})
  [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]
  [EnoughInjectives (SheafOfModules.{wModule} O)]

attribute [local instance] evaluation_additive

/-- The unit exhibiting `Stacks.Cohomology.HypercohomologyEdge.derivedSections` as the unbounded
right derived functor of evaluation at `U`. -/
abbrev derivedSectionsUnit (U : C) :
    homotopySections O U ⟶ DerivedCategory.Qh ⋙ derivedSections O U :=
  (homotopySections O U).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))

/-- **The derived sections of a one-step interval truncation are concentrated in one degree.**
If the degree-`a` cohomology sheaf of `K` has no higher cohomology over `U`, then the derived
sections over `U` of the interval truncation `τ_{< a + 1}(τ_{≥ a}K)` have no cohomology outside
degree `a`.

Above degree `a` this is the hypothesis, read through the identification of the interval
truncation with `H^a(K)` placed in degree `a`; below it, it is left t-exactness. -/
lemma isZero_homology_derivedSections_truncLTGE (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) (a b : ℤ) (hb : a + 1 = b)
    (hK : ∀ p : ℕ, 0 < p →
      IsZero (((SheafOfModules.evaluation O (.op U)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) a).obj K)))
    (i : ℤ) (hi : i ≠ a) :
    IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{wModule} (O.obj.obj (.op U))) i).obj
      ((derivedSections O U).obj
        ((DerivedCategory.TStructure.t.truncLTGE a b).obj K))) := by
  subst hb
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
      (SheafOfModules.evaluation O (.op U)) _ a i hlt
  · obtain ⟨e⟩ := Stacks.TruncationLevel.nonempty_iso_singleFunctor_truncLTGE a K
    exact IsZero.of_iso
      (Stacks.DerivedFunctor.isZero_homologyTotalRightDerived_single_of_rightDerived_isZero
        (SheafOfModules.evaluation O (.op U)) (derivedSections O U) (derivedSectionsUnit O U)
        Stacks.Cohomology.Localization.enoughKInjectives _ hK a i hgt)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{wModule} (O.obj.obj (.op U))) i).mapIso ((derivedSections O U).mapIso e))

/-- **One step of the truncation tower is invertible on hypercohomology above the step.** If the
degree-`a` cohomology sheaf of `K` has no higher cohomology over `U`, then the canonical map
`τ_{≥ a}K ⟶ τ_{≥ a + 1}K` induces an isomorphism on degree-`j` hypercohomology over `U` for every
`j > a`. -/
theorem isIso_homologyMap_derivedSections_natTransTruncGEOfLE (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) (a b : ℤ) (hb : a + 1 = b)
    (hab : a ≤ b)
    (hK : ∀ p : ℕ, 0 < p →
      IsZero (((SheafOfModules.evaluation O (.op U)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) a).obj K)))
    (j : ℤ) (haj : a < j) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) j).map
      ((derivedSections O U).map
        ((DerivedCategory.TStructure.t.natTransTruncGEOfLE a b hab).app K))) := by
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedSections O U) (derivedSectionsUnit O U)
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) ℤ
  have : (derivedSections O U).IsTriangulated :=
    Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
      Stacks.Cohomology.Localization.enoughKInjectives (homotopySections O U)
      (derivedSections O U) (derivedSectionsUnit O U)
  obtain ⟨δ, hδ⟩ := Stacks.TruncationLevel.exists_distTriang_truncGE
    DerivedCategory.TStructure.t a b hab K
  exact Stacks.TruncationLevel.isIso_homologyMap_mor₂ _
    ((derivedSections O U).map_distinguished _ hδ) j
    (isZero_homology_derivedSections_truncLTGE O U K a b hb hK j (by omega))
    (isZero_homology_derivedSections_truncLTGE O U K a b hb hK (j + 1) (by omega))

/-- **The hypercohomology tower of a truncation tower is eventually constant.** If the cohomology
sheaves of `K` have no higher cohomology over `U`, then the transition map out of level `n + 1` of
the truncation tower is invertible on degree-`j` hypercohomology over `U` as soon as `-j ≤ n`. -/
theorem isIso_homologyMap_derivedSections_truncGETower_map (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O))
    (hK : ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation O (.op U)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).obj K)))
    (j : ℤ) (n : ℕ) (hn : -j ≤ (n : ℤ)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) j).map
      ((derivedSections O U).map
        ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K).map
          (homOfLE (Nat.le_succ n)).op))) := by
  rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
  exact isIso_homologyMap_derivedSections_natTransTruncGEOfLE O U K
    (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) (by omega)
    (hK _) j (by omega)

end Stacks.Cohomology.HypercohomologyEdge

end
