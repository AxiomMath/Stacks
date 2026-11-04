module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeTFAE
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaBranches.LowerBound
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.FaithfullyFlatStalk
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.DeltaInvariantFieldChange
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.GeometricBranchesFieldChange
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
import all StacksFrontier.AlgebraicGeometry.Properties.Unibranch

/-!
# The delta invariant and the geometric branches at a node over an arbitrary field

At a node of a one-dimensional scheme locally of finite type over an arbitrary field the local
ring is reduced, has delta invariant one and has two geometric branches; consequently a node
whose residue field is separable over the base field has a nodal local ring.

## Main results

* `isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode` — the three
  conditions on the local ring at a node, over an arbitrary field.
* `isNodalAlgebra_stalk_of_isNode_of_isSeparableExtension` — a node with separable residue field
  has a nodal local ring.
* `isNode_tfae_of_isSeparableExtension` — being a node, having a nodal local ring, the geometric
  form of the node condition and the delta-invariant form are equivalent at a point with separable
  residue field, as soon as a nodal local ring makes the point a node.

## Implementation notes

The `k`-algebra structure on `𝒪_{X,x}` is the one induced by the germ at `x` of the structure
morphism, and the structure on `κ(x)` is induced from it along the residue map.

The local ring of the base change at a point above `x` carries the nodal-algebra condition over
the algebraic closure, which gives it delta invariant one and two geometric branches.  Those two
numbers then come down to `x`: the number of geometric branches is unchanged by an extension of
the ground field, the delta invariant can only grow, and it is bounded below by one less than the
number of geometric branches.  Reducedness descends because the map of local rings is faithfully
flat.

Separability of `κ(x)/k` is not obtained here, and appears as a hypothesis where it is needed.
It is a theorem: `Stacks.Curves.isSeparableExtension_residueField_of_isNode`, which does not go
through the source's closed subscheme cut out by the first Fitting ideal of `Ω_{X/k}` but through
the special fibre of the map on local rings along the base change to `k^{1/p}`.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C40](https://stacks.math.columbia.edu/tag/0C40)
* [Stacks Project, Tag 0C43](https://stacks.math.columbia.edu/tag/0C43)
* [Stacks Project, Tag 0C3X](https://stacks.math.columbia.edu/tag/0C3X)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C4Y](https://stacks.math.columbia.edu/tag/0C4Y)
* [Stacks Project, Tag 033F](https://stacks.math.columbia.edu/tag/033F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

universe u v

namespace Stacks.Curves

/-- A nontrivial ring of dimension at most one and of nonzero dimension has dimension one. -/
private theorem ringKrullDim_eq_one_of_le_one_of_ne_zero (A : Type v) [CommRing A] [Nontrivial A]
    (hle : ringKrullDim A ≤ (1 : WithBot ℕ∞)) (hne : ringKrullDim A ≠ 0) :
    ringKrullDim A = 1 := by
  have hbot : ringKrullDim A ≠ ⊥ := fun h => by
    simpa [h] using (ringKrullDim_nonneg_of_nontrivial (R := A))
  lift ringKrullDim A to ℕ∞ using hbot with d hd
  have hd1 : d ≤ 1 := by exact_mod_cast hle
  lift d to ℕ using ne_top_of_le_ne_top (by simp) hd1 with n hn
  have hn1 : n ≤ 1 := by exact_mod_cast hd1
  have hn0 : n ≠ 0 := fun he => hne (by norm_num [he])
  have hneq : n = 1 := by omega
  norm_num [hneq]

/-- **At a node of a one-dimensional scheme locally of finite type over an arbitrary field the
local ring is reduced, has delta invariant one and has two geometric branches.**

These are the three conditions of condition (6) of Stacks Tag 0C4D other than separability of the
residue field extension.  Separability is not asserted: the source obtains it from the closed
subscheme cut out by the first Fitting ideal of `Ω_{X/k}`. -/
theorem isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hnode : IsNode k X x) :
    _root_.IsReduced (X.presheaf.stalk x) ∧
      Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
        AlgebraicGeometry.numberOfGeometricBranches X x = 2 := by
  obtain ⟨-, xbar, hxbar, hodp⟩ := hnode
  let K := AlgebraicClosure k
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
  let q : Y ⟶ AlgebraicGeometry.Spec (.of K) :=
    pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g
  let instY : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
  have hlft : LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g))
  let algB : Algebra K (Y.presheaf.stalk xbar) :=
    (((Scheme.ΓSpecIso (.of K)).inv ≫ (Y ↘ AlgebraicGeometry.Spec (.of K)).appTop ≫
      Y.presheaf.germ ⊤ xbar trivial).hom).toAlgebra
  -- the local ring at a point above `x` is a nodal algebra over the algebraic closure
  have hnodalB : IsNodalAlgebra K (Y.presheaf.stalk xbar) :=
    ((isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk K Y xbar).mp hodp).2
  have hNagB : IsNagataRing (Y.presheaf.stalk xbar) :=
    isNagataRing_stalk_of_locallyOfFiniteType K (Y ↘ AlgebraicGeometry.Spec (.of K)) xbar
  obtain ⟨-, hredB, -, hdeltaB, hbrB⟩ :=
    deltaInvariant_eq_one_and_two_geometricBranches_of_isNodalAlgebra K
      (Y.presheaf.stalk xbar) hNagB hnodalB
  -- the number of geometric branches is unchanged by the extension of the ground field
  have hbr : AlgebraicGeometry.numberOfGeometricBranches X x = 2 := by
    rw [AlgebraicGeometry.numberOfGeometricBranches_baseChange_fieldExtension k K X
      (X ↘ AlgebraicGeometry.Spec (.of k)) x xbar hxbar]
    exact hbrB
  -- reducedness descends along the faithfully flat map of local rings
  have hff := AlgebraicGeometry.faithfullyFlat_stalkMap_fieldExtension k K X
    (X ↘ AlgebraicGeometry.Spec (.of k)) x xbar hxbar
  have hred : _root_.IsReduced (X.presheaf.stalk x) := by
    let : _root_.IsReduced (Y.presheaf.stalk xbar) := hredB
    exact hff.isReduced
  let : _root_.IsReduced (X.presheaf.stalk x) := hred
  have hNagA : IsNagataRing (X.presheaf.stalk x) :=
    isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ AlgebraicGeometry.Spec (.of k)) x
  -- the local ring is one-dimensional: a reduced zero-dimensional local ring is a field, and a
  -- field has one geometric branch
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    refine ringKrullDim_eq_one_of_le_one_of_ne_zero _
      (hX ▸ AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim x) fun h0 => ?_
    let : Ring.KrullDimLE 0 (X.presheaf.stalk x) :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr h0
    let : Field (X.presheaf.stalk x) :=
      (Ring.KrullDimLE.isField_of_isReduced (R := X.presheaf.stalk x)).toField
    have hone : numberOfGeometricBranchesOfLocalRing (X.presheaf.stalk x) = 1 :=
      (numberOfGeometricBranchesOfLocalRing_eq_one_iff _).mpr
        (AlgebraicGeometry.isGeometricallyUnibranchRing_of_normal inferInstance)
    have hcontra : (1 : ℕ∞) = 2 := hone.symm.trans hbr
    simp at hcontra
  -- the delta invariant is squeezed between the branch bound and the base-change inequality
  have hle : Ring.deltaInvariant (X.presheaf.stalk x) ≤ 1 := by
    have h := AlgebraicGeometry.deltaInvariant_stalk_le_baseChange k K
      (X ↘ AlgebraicGeometry.Spec (.of k)) x xbar hxbar
    rwa [hdeltaB] at h
  have hge := Ring.deltaInvariant_ge_numberOfGeometricBranches_sub_one
    (X.presheaf.stalk x) hNagA hdim
  have hbrA : numberOfGeometricBranchesOfLocalRing (X.presheaf.stalk x) = 2 := hbr
  rw [hbrA, show (2 : ℕ∞) - 1 = 1 from rfl] at hge
  exact ⟨hred, le_antisymm hle hge, hbr⟩

/-- **A node whose residue field is separable over the base field has a nodal local ring.**

This is the implication from condition (1) to condition (2) of Stacks Tag 0C4D, for a point whose
residue field is separable over `k`.  Separability is itself a consequence of being a node
(`Stacks.Curves.isSeparableExtension_residueField_of_isNode`), which removes the hypothesis;
`Stacks.Curves.isNode_iff_isNodalAlgebra_stalk` is the resulting unconditional equivalence. -/
theorem isNodalAlgebra_stalk_of_isNode_of_isSeparableExtension
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) :
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    Algebra.IsSeparableExtension k (X.residueField x) → IsNode k X x →
      IsNodalAlgebra k (X.presheaf.stalk x) := by
  intro kToStalk hsep hnode
  obtain ⟨hred, hdelta, hbr⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode k X hX x
      hnode
  exact (isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches k X hX
    x).mpr ⟨hsep, hred, hdelta, hbr⟩

/-- **Conditions (1), (2), (3) and (6) of Stacks Tag 0C4D are equivalent at a point with
separable residue field, as soon as condition (2) implies condition (1).**

The hypothesis `h₂₁` — that a nodal local ring makes the point a node — is **not proved here**.
Everything else is supplied: condition (1) implies condition (2) by
`Stacks.Curves.isNodalAlgebra_stalk_of_isNode_of_isSeparableExtension`, condition (1) is
equivalent to condition (3) by `Stacks.Curves.isNode_iff_forall_isOrdinaryDoublePoint`, and
condition (2) to condition (6) by
`Stacks.Curves.isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches`. -/
theorem isNode_tfae_of_isSeparableExtension
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X)) :
    let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    let c₁ : Prop := IsNode k X x
    let c₂ : Prop := IsNodalAlgebra k (X.presheaf.stalk x)
    let c₃ : Prop :=
      (let K := AlgebraicClosure k
       let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
         AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
       let Y := (pullback f g : Scheme.{u})
       let p : Y ⟶ X := pullback.fst f g
       let q : Y ⟶ AlgebraicGeometry.Spec (.of K) := pullback.snd f g
       letI : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
       ∀ xbar : Y, p.base xbar = x → IsOrdinaryDoublePoint K Y xbar)
    let c₆ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        _root_.IsReduced (X.presheaf.stalk x) ∧
          Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
            AlgebraicGeometry.numberOfGeometricBranches X x = 2
    Algebra.IsSeparableExtension k (X.residueField x) → (c₂ → c₁) →
      List.TFAE [c₁, c₂, c₃, c₆] := by
  intro f kToStalk c₁ c₂ c₃ c₆ hsep h₂₁
  tfae_have 1 → 2 := isNodalAlgebra_stalk_of_isNode_of_isSeparableExtension k X hX x hsep
  tfae_have 2 → 1 := h₂₁
  tfae_have 1 ↔ 3 :=
    ⟨forall_isOrdinaryDoublePoint_of_isNode k X x, isNode_of_forall_isOrdinaryDoublePoint k X x hx⟩
  tfae_have 2 ↔ 4 :=
    isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches k X hX x
  tfae_finish

end Stacks.Curves

end
