module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeFieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.NodeNormalizationSeparable
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.DeltaInvariantSeparableFieldChange
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationSeparableResidue

/-!
# A nodal local ring makes the point a node

Let `k` be a field, let `X` be a one-dimensional scheme locally of finite type over `k` and let
`x` be a point whose local ring is a nodal `k`-algebra.  Then `x` is a node.

## Main results

* `Stacks.Curves.isNode_of_isNodalAlgebra_stalk` — condition (2) of Stacks Tag 0C4D implies
  condition (1).

## Implementation notes

The source proves this by checking the numerical form of the node condition at a point of
`X_{k̄}` above `x`.  Reducedness ascends because `X` is geometrically reduced at `x`, which is
Stacks Tag 0C3P fed with the separability of the residue fields of the normalization above `x`
(`Stacks.Curves.isSeparableExtension_residueField_normalization_of_isNodalAlgebra`); the delta
invariant is unchanged by the same separability hypothesis, which is Stacks Tag 0C3Y; and the
number of geometric branches is unchanged by any extension of the ground field.  Over the
algebraic closure the four numerical conditions are the node condition.

Both points are closed, because the local ring at a point with two geometric branches is
one-dimensional while the scheme is, and a point whose local ring has the dimension of the
scheme is closed.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C3P](https://stacks.math.columbia.edu/tag/0C3P)
* [Stacks Project, Tag 0C3Y](https://stacks.math.columbia.edu/tag/0C3Y)
* [Stacks Project, Tag 0C40](https://stacks.math.columbia.edu/tag/0C40)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Curves

/-- A local ring of Krull dimension zero is geometrically unibranch. -/
private alias isGeometricallyUnibranchRing_of_ringKrullDim_eq_zero' :=
    Stacks.Curves.isGeometricallyUnibranchRing_of_ringKrullDim_eq_zero

/-- A point of a one-dimensional scheme with two geometric branches has a one-dimensional local
ring: a local ring of dimension zero is geometrically unibranch. -/
private alias ringKrullDim_stalk_eq_one_of_two_geometricBranches' :=
    Stacks.Curves.ringKrullDim_stalk_eq_one_of_two_geometricBranches

/-- A point with two geometric branches on a one-dimensional scheme is closed: its local ring has
the dimension of the scheme. -/
private lemma isClosed_of_two_geometricBranches
    (Z : Scheme.{u}) (hZ : topologicalKrullDim Z = 1) (z : Z)
    (hbr : AlgebraicGeometry.numberOfGeometricBranches Z z = 2) : IsClosed ({z} : Set Z) := by
  have hbound (w : Z) : Order.coheight w ≤ 1 := by
    have h := Order.coheight_le_krullDim w
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Z))] at h
    exact WithBot.coe_le_coe.mp (h.trans hZ.le)
  have hzco : Order.coheight z = 1 := by
    have h := ringKrullDim_stalk_eq_one_of_two_geometricBranches' Z z hZ hbr
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_inj.mp h
  apply isClosed_of_closure_subset
  intro w hw
  have hwz : w ≤ z := specializes_iff_mem_closure.mpr hw
  refine Set.mem_singleton_iff.mpr ?_
  by_contra hne
  have hlt := Order.coheight_strictAnti (show w < z from ⟨hwz, fun hzw ↦
    hne ((hzw : Specializes w z).antisymm (hwz : Specializes z w)).eq⟩)
    (lt_of_le_of_lt (hbound z) (by simp : (1 : ℕ∞) < ⊤))
  rw [hzco] at hlt
  exact (not_lt_of_ge (hbound w)) hlt

/-- **Condition (2) of Stacks Tag 0C4D implies condition (1), over an arbitrary field.**

If the local ring at a point of a one-dimensional scheme locally of finite type over `k` is a
nodal `k`-algebra, then the point is a node. -/
@[stacks 0C4D "clause (2) implies clause (1), over an arbitrary base field"]
theorem isNode_of_isNodalAlgebra_stalk
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) :
    letI : Algebra k (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x trivial).hom.toAlgebra
    IsNodalAlgebra k (X.presheaf.stalk x) → IsNode k X x := by
  intro hnodal
  let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
  let K := AlgebraicClosure k
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback f g : Scheme.{u})
  let p : Y ⟶ X := pullback.fst f g
  let q : Y ⟶ AlgebraicGeometry.Spec (.of K) := pullback.snd f g
  let : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
  have hlftY : LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f g))
  -- the numerical form of the nodal condition at `x`
  obtain ⟨hsepκ, hred, hdelta, hbr⟩ :=
    (isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches k X hX x).mp hnodal
  have hdimA : ringKrullDim (X.presheaf.stalk x) = 1 :=
    ringKrullDim_stalk_eq_one_of_two_geometricBranches' X x hX hbr
  have hx : IsClosed ({x} : Set X) := isClosed_of_two_geometricBranches X hX x hbr
  -- the separability input for Tags 0C3P and 0C3Y
  have hsepnorm := isSeparableExtension_residueField_normalization_of_isNodalAlgebra k f x hnodal
  -- a point of the base change above `x`
  obtain ⟨xbar, hxbar, -⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x
      (IsLocalRing.closedPoint K) (Subsingleton.elim _ _)
  have hdimY : topologicalKrullDim Y = 1 :=
    (AlgebraicGeometry.topologicalKrullDim_baseChange k K p q f
      (IsPullback.of_hasPullback f g)).trans hX
  -- reducedness ascends by geometric reducedness at `x`
  have hredY : _root_.IsReduced (Y.presheaf.stalk xbar) :=
    AlgebraicGeometry.isGeometricallyReducedAt_of_normalization_residueField_isSeparable
      k f x hred hdimA hsepnorm K xbar hxbar
  -- the number of geometric branches is unchanged
  have hbrY : AlgebraicGeometry.numberOfGeometricBranches Y xbar = 2 :=
    (AlgebraicGeometry.numberOfGeometricBranches_baseChange_fieldExtension k K X f x xbar
      hxbar).symm.trans hbr
  have hdimB : ringKrullDim (Y.presheaf.stalk xbar) = 1 :=
    ringKrullDim_stalk_eq_one_of_two_geometricBranches' Y xbar hdimY hbrY
  -- the delta invariant is unchanged
  have hdeltaY : Ring.deltaInvariant (Y.presheaf.stalk xbar) = 1 :=
    (AlgebraicGeometry.deltaInvariant_stalk_baseChange k K f x xbar hxbar hred hdimA hsepnorm
      hdimB).symm.trans hdelta
  have hy : IsClosed ({xbar} : Set Y) := isClosed_of_two_geometricBranches Y hdimY xbar hbrY
  -- over the algebraic closure the numerical conditions are the nodal-algebra condition
  let KToStalk : K →+* Y.presheaf.stalk xbar :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (Y ↘ AlgebraicGeometry.Spec (.of K)).appTop ≫
      Y.presheaf.germ ⊤ xbar trivial).hom
  let : Algebra K (Y.presheaf.stalk xbar) := KToStalk.toAlgebra
  let : Algebra K (Y.residueField xbar) := ((Y.residue xbar).hom.comp KToStalk).toAlgebra
  have hnodalY : IsNodalAlgebra K (Y.presheaf.stalk xbar) :=
    (isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches K Y hdimY
      xbar).mpr ⟨Algebra.isSeparableExtension_of_perfectField K _, hredY, hdeltaY, hbrY⟩
  exact ⟨hx, xbar, hxbar,
    (isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk K Y xbar).mpr ⟨hy, hnodalY⟩⟩

/-- **Conditions (1) and (2) of Stacks Tag 0C4D agree at a point whose residue field is
separable over the base field.**

Separability of `κ(x)/k` is a clause of condition (2); it is assumed here, and discharged in
`Stacks.Curves.isSeparableExtension_residueField_of_isNode`, which makes
`Stacks.Curves.isNode_iff_isNodalAlgebra_stalk` the unconditional equivalence.  Everything else
is proved: condition (1) with separability gives condition (2) by
`Stacks.Curves.isNodalAlgebra_stalk_of_isNode_of_isSeparableExtension`, and condition (2) gives
condition (1) by `Stacks.Curves.isNode_of_isNodalAlgebra_stalk`, over an arbitrary field. -/
@[stacks 0C4D "clauses (1) and (2), at a point whose residue field is separable over the base \
field"]
theorem isNode_iff_isNodalAlgebra_stalk_of_isSeparableExtension
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) :
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x trivial).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    Algebra.IsSeparableExtension k (X.residueField x) →
      (IsNode k X x ↔ IsNodalAlgebra k (X.presheaf.stalk x)) := by
  intro kToStalk hsep
  exact ⟨isNodalAlgebra_stalk_of_isNode_of_isSeparableExtension k X hX x hsep,
    isNode_of_isNodalAlgebra_stalk k X hX x⟩

/-- **The four conditions of Stacks Tag 0C4D that do not mention the Fitting ideal are
equivalent, over an arbitrary field, at a point whose residue field is separable over the base
field.**

Conditions (1), (2), (3) and (6) of the tag.  The hypothesis `c₂ → c₁` of
`Stacks.Curves.isNode_tfae_of_isSeparableExtension` is discharged by
`Stacks.Curves.isNode_of_isNodalAlgebra_stalk`; what remains assumed is separability of
`κ(x)/k`, which is a clause of conditions (2), (4), (5) and (6).  That hypothesis is discharged
in `Stacks.Curves.isNode_tfae`, the same equivalence with no hypothesis beyond closedness of the
point. -/
@[stacks 0C4D "clauses (1), (2), (3) and (6), at a point whose residue field is separable over \
the base field"]
theorem isNode_tfae_of_isSeparableExtension_residueField
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
    Algebra.IsSeparableExtension k (X.residueField x) → List.TFAE [c₁, c₂, c₃, c₆] := by
  intro f kToStalk c₁ c₂ c₃ c₆ hsep
  exact isNode_tfae_of_isSeparableExtension k X hX x hx hsep
    (isNode_of_isNodalAlgebra_stalk k X hX x)

/-- **All six conditions of Stacks Tag 0C4D are equivalent over an arbitrary field as soon as
the two equivalences involving the first Fitting ideal are.**

The six propositions of the list are the six conditions of the tag.  This improves
`Stacks.Curves.isNode_tfae_of_residual_equivalences`, which asks in addition for the equivalence
of conditions (1) and (2): that equivalence now follows, because condition (2) implies condition
(1) over an arbitrary field (`Stacks.Curves.isNode_of_isNodalAlgebra_stalk`) and because
condition (4) carries the separability of `κ(x)/k` that takes condition (1) back to condition
(2).

The two remaining hypotheses are **not proved here**.  They are the equivalence of condition (1)
with condition (4) and the exchange of reducedness for depth one in the presence of the
Fitting-ideal condition. -/
theorem isNode_tfae_of_fittingIdeal_equivalences
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X)) :
    let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    let omega := f.relativeDifferentials
    let fittingCondition : Prop :=
      AlgebraicGeometry.IdealSheafData.stalk (AlgebraicGeometry.fittingIdeal omega 1) x =
        maximalIdeal (X.presheaf.stalk x)
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
    let c₄ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        _root_.IsReduced (X.presheaf.stalk x) ∧ fittingCondition
    let c₅ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x) = 1 ∧
          fittingCondition
    let c₆ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        _root_.IsReduced (X.presheaf.stalk x) ∧
          Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
            AlgebraicGeometry.numberOfGeometricBranches X x = 2
    (c₁ ↔ c₄) → (c₄ ↔ c₅) → List.TFAE [c₁, c₂, c₃, c₄, c₅, c₆] := by
  intro f kToStalk omega fittingCondition c₁ c₂ c₃ c₄ c₅ c₆ h₁₄ h₄₅
  refine isNode_tfae_of_residual_equivalences k X hX x hx ?_ h₁₄ h₄₅
  exact ⟨fun h => isNodalAlgebra_stalk_of_isNode_of_isSeparableExtension k X hX x
      (h₁₄.mp h).1 h,
    isNode_of_isNodalAlgebra_stalk k X hX x⟩

end Stacks.Curves

end
