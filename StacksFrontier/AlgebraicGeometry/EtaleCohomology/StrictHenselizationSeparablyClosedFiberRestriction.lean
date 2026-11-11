module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackRestrictionMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationSeparablyClosedFiber
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationSeparablyClosedFiberCohomology

/-!
# Tag 0EZV as stated fails for the restriction maps of its statement

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationSeparablyClosedFiber` states
Tag 0EZV with the restriction maps
`Stacks.EtaleCohomology.strictHenselizationFiberRestriction` (condition (1)) and
`Stacks.EtaleCohomology.strictHenselizationPointRestriction` (condition (2)), built from
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` on abelian sheaves of the universe
`max (u + 1) v` with cohomology `CategoryTheory.Sheaf.H.{w}`.
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationSeparablyClosedFiberCohomology`
gives an example, the nodal cubic, where condition (2) holds and condition (1) fails, for the
restriction maps `Stacks.EtaleCohomology.strictHenselizationPointCohomologyPullback` and
`Stacks.EtaleCohomology.strictHenselizationFiberCohomologyPullback` built from
`Stacks.EtaleCohomology.etaleCohomologyPullback` on abelian sheaves of the universe `u + 1` with
cohomology `CategoryTheory.Sheaf.H.{u + 1}`.

This file transports that example to the maps of the statement, at the universes `v = 0`, so that
the coefficients `AddCommGrpCat.{max (u + 1) 0}` are `Ab.{u + 1}`, and `w = u + 1`. At those
universes each map of the statement is bijective exactly when the corresponding map of the example
is, by `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_iff`.

The data of the example are named in `Stacks.EtaleCohomology.NodeCounterexample`, following the
construction in `exists_bijective_pointRestriction_and_not_bijective_fiberRestriction`; the field
`K` and its two points come from `Stacks.EtaleCohomology.NodeCounterexample.exists_two_points` by
choice. Naming them, rather than stating an existential over eleven binders, keeps the kernel from
re-checking the statement once per binder.

## Main results

* `Stacks.EtaleCohomology.bijective_strictHenselizationFiberRestriction_iff`,
  `Stacks.EtaleCohomology.bijective_strictHenselizationPointRestriction_iff`: the restriction maps
  of the statement are bijective exactly when those of the example are.
* `Stacks.EtaleCohomology.bijective_strictHenselizationFiberRestriction_iff_forall_lift`: the
  corrected form of the tag for the restriction maps of the statement, condition (1) if and only
  if condition (2) at every lift of `Spec K ⟶ S` to the strict henselization.
* `Stacks.EtaleCohomology.isEmpty_sepClosedFiberLocallyConstantPresentation`: where condition (2)
  holds and condition (1) fails, the datum
  `Stacks.EtaleCohomology.SepClosedFiberLocallyConstantPresentation` of the printed equivalence
  is empty.
* `Stacks.EtaleCohomology.not_nonempty_sepClosedFiberLocallyConstantPresentation_onBranchSpecPoint`
  states that at the data of the example, condition (2) holds, condition (1) fails, and that
  datum cannot be constructed, over any index space.
* `Stacks.EtaleCohomology.not_forall_bijective_strictHenselizationFiberRestriction_iff`: the
  negation of Tag 0EZV as stated, for the restriction maps of the statement.

## References

* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Comparison

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X) {K : Type u} [Field K]
  (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f))

/-- **Condition (1) of Tag 0EZV in the two models.** At the coefficient universe `u + 1` and the
cohomology universe `u + 1`, the restriction map
`Stacks.EtaleCohomology.strictHenselizationFiberRestriction` of the statement is bijective exactly
when the pull back map `Stacks.EtaleCohomology.strictHenselizationFiberCohomologyPullback` is: the
two maps differ by the identification of the two inverse images, applied both to the coefficient
sheaf on `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` and to the map itself. -/
public theorem bijective_strictHenselizationFiberRestriction_iff
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology Ab.{u + 1}) (q : ℕ) :
    Function.Bijective (strictHenselizationFiberRestriction.{u, 0, u + 1} B hX hS f x k F q) ↔
      Function.Bijective (strictHenselizationFiberCohomologyPullback B hX hS f x k F q) :=
  (bijective_etaleCohomologyRestrictionMap_iff _ _ q).trans
    (bijective_etaleCohomologyPullback_iff_of_iso _
      ((smallEtalePullbackAbIsoEtaleAbelianInverseImage _).app F).symm q)

/-- **Condition (2) of Tag 0EZV in the two models.** At the coefficient universe `u + 1` and the
cohomology universe `u + 1`, the restriction map
`Stacks.EtaleCohomology.strictHenselizationPointRestriction` of the statement is bijective exactly
when the pull back map `Stacks.EtaleCohomology.strictHenselizationPointCohomologyPullback` is. -/
public theorem bijective_strictHenselizationPointRestriction_iff
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology Ab.{u + 1}) (q : ℕ) :
    Function.Bijective (strictHenselizationPointRestriction.{u, 0, u + 1} B hX hS f x k F q) ↔
      Function.Bijective (strictHenselizationPointCohomologyPullback B hX hS f x k F q) :=
  bijective_etaleCohomologyRestrictionMap_iff _ F q

/-- **The presentation of the printed form of Tag 0EZV is empty where the tag fails.** If condition
(2) holds and condition (1) fails for the restriction maps of the statement, then
`Stacks.EtaleCohomology.SepClosedFiberLocallyConstantPresentation` is empty for every
topological space `A`, since by
`Stacks.EtaleCohomology.bijective_strictHenselizationFiberRestriction_iff_of_presentation` a
presentation makes the two conditions equivalent. -/
public theorem isEmpty_sepClosedFiberLocallyConstantPresentation [IsSepClosed K] (A : Type u)
    [TopologicalSpace A] (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology Ab.{u + 1})
    (q : ℕ)
    (h₂ : Function.Bijective
      (strictHenselizationPointRestriction.{u, 0, u + 1} B hX hS f x k F q))
    (h₁ : ¬ Function.Bijective
      (strictHenselizationFiberRestriction.{u, 0, u + 1} B hX hS f x k F q)) :
    IsEmpty (SepClosedFiberLocallyConstantPresentation.{u, 0, u + 1} B hX hS f x k A F q) :=
  ⟨fun P => h₁ ((bijective_strictHenselizationFiberRestriction_iff_of_presentation B hX hS f x k
    A F q P).2 h₂)⟩

/-- **[Stacks, Tag 0EZV], corrected, for the restriction maps of the statement.** Let `f : X ⟶ S`
be a morphism of schemes, `x̄` a geometric point of `X` with image `s̄`,
`k : Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` with `K` separably closed, `ℱ` an abelian sheaf on `Spec K` and
`q ≥ 0`. The restriction map
`H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K, ℱ) ⟶ H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K, ℱ)` is bijective if
and only if the restriction map
`H^q(Spec K, ℱ) ⟶ H^q(Spec(𝒪^{sh}_{X,x̄}) ×_{Spec(𝒪^{sh}_{S,s̄}), k'} Spec K, ℱ)` is bijective
for every lift `k'` of the composite `Spec K ⟶ S` to the strict henselization. This is
`Stacks.EtaleCohomology.bijective_strictHenselizationFiberCohomologyPullback_iff` read through
`Stacks.EtaleCohomology.bijective_strictHenselizationFiberRestriction_iff` and
`Stacks.EtaleCohomology.bijective_strictHenselizationPointRestriction_iff`. -/
@[stacks 0EZV "corrected, for the restriction maps `strictHenselizationFiberRestriction` and
`strictHenselizationPointRestriction`: condition (1) is equivalent to condition (2) at every lift
`k'` of `Spec K ⟶ S` to the strict henselization"]
public theorem bijective_strictHenselizationFiberRestriction_iff_forall_lift [IsSepClosed K]
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology Ab.{u + 1}) (q : ℕ) :
    Function.Bijective (strictHenselizationFiberRestriction.{u, 0, u + 1} B hX hS f x k F q) ↔
      ∀ k' : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f),
        k' ≫ strictHenselizationToBase B S hS (x.map f) =
            k ≫ strictHenselizationToBase B S hS (x.map f) →
          Function.Bijective
            (strictHenselizationPointRestriction.{u, 0, u + 1} B hX hS f x k' F q) := by
  rw [bijective_strictHenselizationFiberRestriction_iff,
    bijective_strictHenselizationFiberCohomologyPullback_iff]
  exact forall_congr' fun k' => imp_congr_right fun _ =>
    (bijective_strictHenselizationPointRestriction_iff B hX hS f x k' F q).symm

end Comparison

section Counterexample

namespace NodeCounterexample

/-- The base field of the counterexample: an algebraic closure of `ℚ`. -/
public abbrev nodeBaseField : Type u := AlgebraicClosure (ULift.{u} ℚ)

/-- `2 ≠ 0` in the base field, which has characteristic zero. -/
public theorem nodeBaseField_two_ne_zero : (2 : nodeBaseField.{u}) ≠ 0 := by
  rw [← map_ofNat (algebraMap (ULift.{u} ℚ) nodeBaseField) 2, map_ne_zero]
  intro h
  have := congrArg ULift.down h
  norm_num at this

/-- A big étale site containing the nodal cubic. -/
public abbrev nodeSite : BigEtaleSite.{u} := BigEtaleSite.containing (nodeScheme nodeBaseField)

/-- `nodeSite` contains the node. -/
public theorem contains_nodeSite : nodeSite.{u}.Contains (nodeScheme nodeBaseField) :=
  BigEtaleSite.contains_containing _

/-- The branch `X = Spec(𝒪^{sh}_{S,s̄}/(y - x√(1 + x)))` of the node. -/
public abbrev branchOfNode : Scheme.{u} :=
  branchScheme nodeSite contains_nodeSite (nodePoint nodeBaseField)
    (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero

/-- A big étale site containing the node and the branch. -/
public abbrev nodeAndBranchSite : BigEtaleSite.{u} :=
  BigEtaleSite.ofSet ({nodeScheme nodeBaseField, branchOfNode} : Set Scheme.{u})

/-- `nodeAndBranchSite` contains the node. -/
public theorem nodeAndBranchSite_contains_node :
    nodeAndBranchSite.{u}.Contains (nodeScheme nodeBaseField) :=
  BigEtaleSite.contains_ofSet _ (Set.mem_insert _ _)

/-- `nodeAndBranchSite` contains the branch. -/
public theorem nodeAndBranchSite_contains_branch : nodeAndBranchSite.{u}.Contains branchOfNode :=
  BigEtaleSite.contains_ofSet _ (Set.mem_insert_of_mem _ rfl)

/-- The morphism `f : X ⟶ S` from the branch to the node. -/
public abbrev branchOfNodeToNode : branchOfNode.{u} ⟶ nodeScheme nodeBaseField :=
  branchToNode nodeSite contains_nodeSite (nodePoint nodeBaseField)
    (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero

/-- The geometric point `x̄` of the branch over the node. -/
public abbrev branchOfNodePoint : GeometricPoint branchOfNode.{u} :=
  branchPoint nodeSite contains_nodeSite (nodePoint nodeBaseField)
    (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero

/-- The algebraically closed field `K` carrying the two points `κ` and `τ`, chosen by
`Stacks.EtaleCohomology.NodeCounterexample.exists_two_points`. -/
public def twoPointsField : Type u :=
  Classical.choose (exists_two_points nodeSite contains_nodeSite
    (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero)

/-- The field structure on `twoPointsField`, chosen with it. -/
public instance twoPointsField.instField : Field twoPointsField.{u} :=
  Classical.choose (Classical.choose_spec (exists_two_points nodeSite contains_nodeSite
    (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero))

/-- `twoPointsField` is algebraically closed. -/
public instance twoPointsField.instIsAlgClosed : IsAlgClosed twoPointsField.{u} :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (exists_two_points nodeSite
    contains_nodeSite (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero)))

/-- The point `κ` of the strict henselization at the node, on the branch. -/
public def onBranchPoint :
    shRing nodeSite contains_nodeSite (nodePoint nodeBaseField) →+* twoPointsField.{u} :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (exists_two_points nodeSite contains_nodeSite (nodePoint_hom_closedPoint nodeBaseField)
      nodeBaseField_two_ne_zero))))

/-- The point `τ` of the strict henselization at the node, off the branch. -/
public def offBranchPoint :
    shRing nodeSite contains_nodeSite (nodePoint nodeBaseField) →+* twoPointsField.{u} :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_two_points nodeSite contains_nodeSite
      (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero)))))

/-- `κ` and `τ` lie over one point of the node, `κ` on the branch and `τ` off it. -/
public theorem onBranchPoint_offBranchPoint_spec :
    onBranchPoint.{u}.comp (structureSheafStalkFromLocalRing nodeSite _ contains_nodeSite
        (nodePoint nodeBaseField)) =
      offBranchPoint.comp (structureSheafStalkFromLocalRing nodeSite _ contains_nodeSite
        (nodePoint nodeBaseField)) ∧
    onBranchPoint.{u} (branch nodeSite contains_nodeSite
      (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero) = 0 ∧
    offBranchPoint.{u} (branch nodeSite contains_nodeSite
      (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero) ≠ 0 :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_two_points nodeSite contains_nodeSite
      (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero)))))

/-- The point `k = κ : Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` of the counterexample. -/
public abbrev onBranchSpecPoint :
    Spec (CommRingCat.of twoPointsField.{u}) ⟶ strictHenselization nodeAndBranchSite
      (nodeScheme nodeBaseField) nodeAndBranchSite_contains_node
      (branchOfNodePoint.map branchOfNodeToNode) :=
  pointAtImage nodeSite contains_nodeSite (nodePoint nodeBaseField)
    (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero nodeAndBranchSite
    nodeAndBranchSite_contains_node onBranchPoint

end NodeCounterexample

open NodeCounterexample in
/-- **At the data of the nodal cubic example no presentation for the printed form of Tag 0EZV
exists.** For `S` the nodal cubic over `ℚ̄`, `X` a branch of its node, `x̄` the point of `X`
over the node, `K` algebraically closed, `k = κ` a `K`-point of `Spec(𝒪^{sh}_{S,s̄})` on the
branch, `ℱ = ℤ` and `q = 0`, the data constructed in
`Stacks.EtaleCohomology.exists_bijective_pointRestriction_and_not_bijective_fiberRestriction`:
condition (2) holds and condition (1) fails for the restriction maps of the statement, and
`Stacks.EtaleCohomology.SepClosedFiberLocallyConstantPresentation` is empty for every topological
space `A`, since by
`Stacks.EtaleCohomology.bijective_strictHenselizationFiberRestriction_iff_of_presentation` a
presentation would make condition (1) follow from condition (2). -/
public theorem not_nonempty_sepClosedFiberLocallyConstantPresentation_onBranchSpecPoint :
    Function.Bijective (strictHenselizationPointRestriction.{u, 0, u + 1} nodeAndBranchSite
        nodeAndBranchSite_contains_branch nodeAndBranchSite_contains_node branchOfNodeToNode
        branchOfNodePoint onBranchSpecPoint (constantZ (Spec (CommRingCat.of twoPointsField))) 0) ∧
      ¬ Function.Bijective (strictHenselizationFiberRestriction.{u, 0, u + 1} nodeAndBranchSite
        nodeAndBranchSite_contains_branch nodeAndBranchSite_contains_node branchOfNodeToNode
        branchOfNodePoint onBranchSpecPoint (constantZ (Spec (CommRingCat.of twoPointsField))) 0) ∧
      ∀ (A : Type u) [TopologicalSpace A],
        ¬ Nonempty (SepClosedFiberLocallyConstantPresentation.{u, 0, u + 1} nodeAndBranchSite
          nodeAndBranchSite_contains_branch nodeAndBranchSite_contains_node branchOfNodeToNode
          branchOfNodePoint onBranchSpecPoint A
            (constantZ (Spec (CommRingCat.of twoPointsField))) 0) := by
  let B := nodeAndBranchSite.{u}
  let hX := nodeAndBranchSite_contains_branch.{u}
  let hS := nodeAndBranchSite_contains_node.{u}
  let f := branchOfNodeToNode.{u}
  let x := branchOfNodePoint.{u}
  let k := onBranchSpecPoint.{u}
  obtain ⟨hκτ, hκ, hτ⟩ := onBranchPoint_offBranchPoint_spec.{u}
  have h₂ : Function.Bijective
      (strictHenselizationPointCohomologyPullback B hX hS f x k
        (constantZ (Spec (CommRingCat.of twoPointsField))) 0) := by
    have := isIso_pullback_snd_of_branch nodeSite contains_nodeSite (nodePoint nodeBaseField)
      (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero B hS hX onBranchPoint hκ
    exact bijective_etaleCohomologyPullback_of_isIso _ _ 0
  have h₁ : ¬ Function.Bijective
      (strictHenselizationFiberCohomologyPullback B hX hS f x k
        (constantZ (Spec (CommRingCat.of twoPointsField))) 0) := by
    intro hb
    have hτκ := pointAtImage_comp_toBase nodeSite contains_nodeSite (nodePoint nodeBaseField)
      (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero B hS onBranchPoint
      offBranchPoint hκτ
    let t : Spec (CommRingCat.of twoPointsField) ⟶ strictHenselizationBaseFiber B hS f x k :=
      pullback.lift (pointAtImage nodeSite contains_nodeSite (nodePoint nodeBaseField)
        (nodePoint_hom_closedPoint nodeBaseField) nodeBaseField_two_ne_zero B hS offBranchPoint)
        (𝟙 _) (by rwa [Category.id_comp])
    refine not_injective_strictHenselizationFiberCohomologyPullback_of_isEmpty B hX hS f x k t
      ⟨fun z => (isEmpty_pullback_of_not_branch nodeSite contains_nodeSite
        (nodePoint nodeBaseField) (nodePoint_hom_closedPoint nodeBaseField)
        nodeBaseField_two_ne_zero B hS hX offBranchPoint hτ).false
        ((pullback.lift (pullback.fst _ t ≫ pullback.fst (strictHenselizationToBase B _ hX x ≫ f)
          (sepClosedPointToBase B hS f x k)) (pullback.snd _ t) ?_).base z)⟩ hb.1
    rw [Category.assoc, ← strictHenselizationFiberMap_comp_fst, ← Category.assoc,
      pullback.condition, Category.assoc, pullback.lift_fst]
  have h₂' := (bijective_strictHenselizationPointRestriction_iff B hX hS f x k _ 0).2 h₂
  have h₁' : ¬ Function.Bijective (strictHenselizationFiberRestriction.{u, 0, u + 1} B hX hS f x k
      (constantZ (Spec (CommRingCat.of twoPointsField))) 0) :=
    mt (bijective_strictHenselizationFiberRestriction_iff B hX hS f x k _ 0).1 h₁
  exact ⟨h₂', h₁', fun A _ => not_nonempty_iff.2
    (isEmpty_sepClosedFiberLocallyConstantPresentation B hX hS f x k A _ 0 h₂' h₁')⟩

open NodeCounterexample in
/-- **Tag 0EZV as printed is false**, for the restriction maps of the statement at coefficients
`Ab.{u + 1}` and cohomology `Sheaf.H.{u + 1}`. Let `S` be the nodal cubic `y² = x²(1 + x)` over
`ℚ̄`, `s̄` its node, `X = Spec(𝒪^{sh}_{S,s̄}/(y - x√(1 + x)))` one branch with `x̄` over `s̄`, `K`
algebraically closed with `K`-points `κ` on and `τ` off the branch over one point of `S`, `k = κ`,
`ℱ = ℤ` and `q = 0`. Condition (2) sees only the fibre `Spec K` over `κ` and holds; condition (1)
also sees the empty fibre over `τ` and fails. -/
public theorem not_forall_bijective_strictHenselizationFiberRestriction_iff :
    ¬ ∀ (B : BigEtaleSite.{u}) (X S : Scheme.{u}) (hX : B.Contains X) (hS : B.Contains S)
      (f : X ⟶ S) (x : GeometricPoint X) (K : Type u) [Field K] [IsSepClosed K]
      (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f))
      (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) 0})
      (q : ℕ),
      Function.Bijective (strictHenselizationFiberRestriction.{u, 0, u + 1} B hX hS f x k F q) ↔
        Function.Bijective
          (strictHenselizationPointRestriction.{u, 0, u + 1} B hX hS f x k F q) := by
  intro h
  obtain ⟨h₂, h₁, -⟩ :=
    not_nonempty_sepClosedFiberLocallyConstantPresentation_onBranchSpecPoint.{u}
  exact h₁ ((h _ _ _ _ _ _ _ _ _ (constantZ _) 0).2 h₂)

end Counterexample

end Stacks.EtaleCohomology

end
