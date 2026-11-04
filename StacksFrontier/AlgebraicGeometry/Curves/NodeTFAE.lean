module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.Curves.NodeFibreTransitive
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative
public import StacksFrontier.RingTheory.Depth.Defs.Defs

/-!
# The equivalent characterizations of a node on a curve

Let `k` be a field, let `X` be a one-dimensional scheme locally of finite type over `k` and let
`x` be a closed point of `X`.  Six conditions on `x` are classically equivalent: that `x` be a
node; that the local ring `𝒪_{X,x}` be a nodal `k`-algebra; that every point of `X_{k̄}` above
`x` be an ordinary double point; two conditions on the first Fitting ideal of `Ω_{X/k}`, one
asking in addition that `𝒪_{X,x}` be reduced and one that it have depth one; and that the
residue field be separable while `𝒪_{X,x}` is reduced of delta invariant one with two geometric
branches.

This file collects what is available about those six conditions.  The first and third are
equivalent over an arbitrary field, and so are the second and sixth; over an algebraically
closed field all four of those are equivalent.  Over an arbitrary field the two pairs are joined
by an equivalence that is proved downstream of this file, and the conditions on the Fitting ideal
are joined to them by two more; those residual equivalences appear as hypotheses of
`Stacks.Curves.isNode_tfae_of_isNode_iff_isNodalAlgebra_stalk` and
`Stacks.Curves.isNode_tfae_of_residual_equivalences`, which carry everything else.

## Main results

* `Stacks.Curves.isNode_iff_forall_isOrdinaryDoublePoint` — over an arbitrary field, a closed
  point is a node exactly when every point of the base change to the algebraic closure above it
  is an ordinary double point.
* `Stacks.Curves.isNode_tfae_of_isNode_iff_isNodalAlgebra_stalk` — the four conditions not
  mentioning the Fitting ideal are equivalent over an arbitrary field as soon as the first two of
  them are.
* `Stacks.Curves.isNode_tfae_of_isAlgClosed` — those four conditions are equivalent over an
  algebraically closed field.
* `Stacks.Curves.isNode_tfae_of_residual_equivalences` — all six conditions are equivalent over an
  arbitrary field as soon as three named equivalences among them are.

## Implementation notes

The `k`-algebra structure on `𝒪_{X,x}` is the one induced by the germ at `x` of the structure
morphism, and the `k`-algebra structure on `κ(x)` is induced from it along the residue map; these
are the structures `Stacks.Curves.IsNodalAlgebra` is applied to throughout the node files.  The
sheaf of relative differentials is `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, which is
by definition the module of differentials of the inverse-image structure map, and its Fitting
ideal sheaf is `AlgebraicGeometry.fittingIdeal`; the Fitting condition is the equality of the
stalk of that ideal sheaf with the maximal ideal.

`AlgebraicGeometry.Spec` is written out in full because a root-level `Spec` for topological
specialization is in scope through `StacksFrontier.AlgebraicGeometry.Properties.Dimension`.

Three equivalences are stated as hypotheses rather than proved *in this file*.  Two of them are
proved downstream, in `StacksFrontier.AlgebraicGeometry.Curves.NodeNodalAlgebraAscent`, and so is
the third, in `StacksFrontier.AlgebraicGeometry.Curves.NodeFittingIdealClosedPoint`; none of the
three can be imported here, each importing this file.

* `𝒪_{X,x}` is a nodal algebra exactly when `x` is a node.  Over an algebraically closed field
  this is `Stacks.Curves.isNode_iff_isNodalAlgebra_stalk_of_isAlgClosed`.  Over an arbitrary
  field the implication from the nodal algebra to the node is
  `Stacks.Curves.isNode_of_isNodalAlgebra_stalk`: it is checked at a point `x̄` of `X_{k̄}` above
  `x` in the numerical form, reducedness ascending because `X` is geometrically reduced at `x`
  (Tag 0C3P), the delta invariant being unchanged (Tag 0C3Y) and the number of geometric
  branches being unchanged (Tag 0C40); the separability of the residue fields of the
  normalization above `x` that the first two of those require is Tag 0C4A, carried to the
  normalization morphism by
  `Stacks.Curves.isSeparableExtension_residueField_normalization_of_isNodalAlgebra`.  The
  converse implication holds as soon as `κ(x)/k` is separable
  (`Stacks.Curves.isNodalAlgebra_stalk_of_isNode_of_isSeparableExtension`), so what is left of
  this equivalence is exactly the separability clause: over an algebraically closed field it
  holds automatically, and over an arbitrary field it is
  `Stacks.Curves.isSeparableExtension_residueField_of_isNode`, by a base change to `k^{1/p}`
  rather than by the route the source takes.  The equivalence itself is therefore
  `Stacks.Curves.isNode_iff_isNodalAlgebra_stalk`.
* `x` is a node exactly when `κ(x)/k` is separable, `𝒪_{X,x}` is reduced and the first Fitting
  ideal of `Ω_{X/k}` generates the maximal ideal.  This is
  `Stacks.Curves.isNode_tfae_of_isClosed`, at the far end of the chain: it needs the Jacobian
  criterion of Tag 0C4C in a chart presented at the point, which asks for `κ(x) = k`, and then
  a base change to `k̄` to reach an arbitrary closed point.  Granting it, the previous item
  follows in full: `Stacks.Curves.isNode_tfae_of_fittingIdeal_equivalences` takes only this
  hypothesis and the next, where `Stacks.Curves.isNode_tfae_of_residual_equivalences` below
  takes three.
* The reducedness clause of the previous condition may be exchanged for depth one.  This comes
  with the previous item, from the same theorem.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C1W](https://stacks.math.columbia.edu/tag/0C1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Curves

/-- **A closed point of a scheme locally of finite type over an arbitrary field is a node
exactly when every point of the base change to the algebraic closure above it is an ordinary
double point.**

This is the equivalence of conditions (1) and (3) of Stacks Tag 0C4D, over an arbitrary field.
The definition of a node asks only that *some* point above `x` be an ordinary double point; the
two agree because the automorphisms of the algebraic closure act transitively on the points
above `x`, which is `Stacks.Curves.forall_isOrdinaryDoublePoint_of_isNode`. -/
@[stacks 0C4D "clauses (1) and (3)"]
theorem isNode_iff_forall_isOrdinaryDoublePoint
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
    (IsNode k X x ↔
      (let K := AlgebraicClosure k
       let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
         AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
       let Y := (pullback f g : Scheme.{u})
       let p : Y ⟶ X := pullback.fst f g
       let q : Y ⟶ AlgebraicGeometry.Spec (.of K) := pullback.snd f g
       letI : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
       ∀ xbar : Y, p.base xbar = x → IsOrdinaryDoublePoint K Y xbar)) :=
  ⟨forall_isOrdinaryDoublePoint_of_isNode k X x, isNode_of_forall_isOrdinaryDoublePoint k X x hx⟩

/-- **The four conditions of Stacks Tag 0C4D that do not mention the Fitting ideal are
equivalent over an arbitrary field as soon as the first two of them are.**

Conditions (1), (2), (3) and (6) of the tag: that `x` be a node, that `𝒪_{X,x}` be a nodal
`k`-algebra, that every point of `X_{k̄}` above `x` be an ordinary double point, and that
`κ(x)/k` be separable with `𝒪_{X,x}` reduced of delta invariant one and with two geometric
branches.

The hypothesis `h₁₂` is the equivalence of conditions (1) and (2).  It is not proved in this
file, but it is no longer an open input: its backward half is
`Stacks.Curves.isNode_of_isNodalAlgebra_stalk` and its forward half holds as soon as `κ(x)/k`
is separable, so `Stacks.Curves.isNode_tfae_of_isSeparableExtension_residueField` discharges
`h₁₂` outright at a point with separable residue field.  Both live downstream of this file,
which they import.  Everything else is supplied here — (1) is equivalent to (3) by
`Stacks.Curves.isNode_iff_forall_isOrdinaryDoublePoint` and (2) to (6) by
`Stacks.Curves.isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches`. -/
theorem isNode_tfae_of_isNode_iff_isNodalAlgebra_stalk
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X)) :
    let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) :=
      ((X.residue x).hom.comp kToStalk).toAlgebra
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
        IsReduced (X.presheaf.stalk x) ∧
          Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
            AlgebraicGeometry.numberOfGeometricBranches X x = 2
    (c₁ ↔ c₂) → List.TFAE [c₁, c₂, c₃, c₆] := by
  intro f kToStalk c₁ c₂ c₃ c₆ h₁₂
  tfae_have 1 ↔ 2 := h₁₂
  tfae_have 1 ↔ 3 := isNode_iff_forall_isOrdinaryDoublePoint k X x hx
  tfae_have 2 ↔ 4 :=
    isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches k X hX x
  tfae_finish

/-- **The four conditions of Stacks Tag 0C4D that do not mention the Fitting ideal are
equivalent over an algebraically closed field.**

Conditions (1), (2), (3) and (6) of the tag.  The equivalence of (1) and (2) over an
algebraically closed field is
`Stacks.Curves.isNode_iff_isNodalAlgebra_stalk_of_isAlgClosed`, which is the only hypothesis of
`Stacks.Curves.isNode_tfae_of_isNode_iff_isNodalAlgebra_stalk`. -/
@[stacks 0C4D "clauses (1), (2), (3) and (6), for an algebraically closed base field"]
theorem isNode_tfae_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X)) :
    let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) :=
      ((X.residue x).hom.comp kToStalk).toAlgebra
    List.TFAE [
      IsNode k X x,
      IsNodalAlgebra k (X.presheaf.stalk x),
      (let K := AlgebraicClosure k
       let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
         AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
       let Y := (pullback f g : Scheme.{u})
       let p : Y ⟶ X := pullback.fst f g
       let q : Y ⟶ AlgebraicGeometry.Spec (.of K) := pullback.snd f g
       letI : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
       ∀ xbar : Y, p.base xbar = x → IsOrdinaryDoublePoint K Y xbar),
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        IsReduced (X.presheaf.stalk x) ∧
          Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
            AlgebraicGeometry.numberOfGeometricBranches X x = 2] :=
  isNode_tfae_of_isNode_iff_isNodalAlgebra_stalk k X hX x hx
    (isNode_iff_isNodalAlgebra_stalk_of_isAlgClosed k X x hx)

/-- **All six conditions of Stacks Tag 0C4D are equivalent over an arbitrary field as soon as
three named equivalences among them are.**

The six propositions of the list are exactly the six conditions of the tag: that `x` be a node;
that `𝒪_{X,x}` be a nodal `k`-algebra; that every point of `X_{k̄}` above `x` be an ordinary
double point; that `κ(x)/k` be separable with `𝒪_{X,x}` reduced and the first Fitting ideal of
`Ω_{X/k}` generating the maximal ideal; the same with reducedness replaced by depth one; and
that `κ(x)/k` be separable with `𝒪_{X,x}` reduced of delta invariant one and with two geometric
branches.

The three hypotheses are not proved here, and nothing in this file bears on their truth.  The
first of them — the equivalence of conditions (1) and (2) — is *implied* by the second, so
`Stacks.Curves.isNode_tfae_of_fittingIdeal_equivalences`, downstream of this file, states the
same conclusion on the last two hypotheses alone; this version is kept because it is what the
files between here and there consume.  What the theorem carries is the rest of the tag:
condition (1) is equivalent to condition (3) over an arbitrary field, and condition (2) to
condition (6), so the six conditions fall into four classes and three equivalences join them.
The classes are chosen to match the source, which proves (1), (3), (4), (5) equivalent first
and then joins (2) = (6) to them. -/
theorem isNode_tfae_of_residual_equivalences
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X)) :
    let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) :=
      ((X.residue x).hom.comp kToStalk).toAlgebra
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
        IsReduced (X.presheaf.stalk x) ∧ fittingCondition
    let c₅ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x) = 1 ∧
          fittingCondition
    let c₆ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        IsReduced (X.presheaf.stalk x) ∧
          Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
            AlgebraicGeometry.numberOfGeometricBranches X x = 2
    (c₁ ↔ c₂) → (c₁ ↔ c₄) → (c₄ ↔ c₅) → List.TFAE [c₁, c₂, c₃, c₄, c₅, c₆] := by
  intro f kToStalk omega fittingCondition c₁ c₂ c₃ c₄ c₅ c₆ h₁₂ h₁₄ h₄₅
  tfae_have 1 ↔ 2 := h₁₂
  tfae_have 1 ↔ 4 := h₁₄
  tfae_have 4 ↔ 5 := h₄₅
  tfae_have 1 ↔ 3 := isNode_iff_forall_isOrdinaryDoublePoint k X x hx
  tfae_have 2 ↔ 6 :=
    isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches k X hX x
  tfae_finish

end Stacks.Curves

end
