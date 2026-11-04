module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeFieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.NodeLocalRingDepth
public import StacksFrontier.AlgebraicGeometry.Curves.NodeNodalAlgebraAscent
public import StacksFrontier.AlgebraicGeometry.Variety.RationalMap.MaximalIdealFieldChange
public import StacksFrontier.FieldTheory.Separable.PthRootsTensorLocal

/-!
# The residue field at a node is separable over the base field

Let `k` be a field, let `X` be a one-dimensional scheme locally of finite type over `k` and let
`x` be a node of `X`.  Then `κ(x)/k` is separable.

## Main results

* `Stacks.Curves.isField_specialFibre_of_isNode` — at a node the maximal ideal of `𝒪_{X,x}`
  generates the maximal ideal of `𝒪_{X_K,y}` for every extension `K/k` and every point `y`
  above `x`.
* `Stacks.Curves.isSeparableExtension_residueField_of_isNode` — the residue field at a node is
  separable over the base field.
* `Stacks.Curves.isNode_iff_isNodalAlgebra_stalk` — conditions (1) and (2) of Stacks Tag 0C4D
  are equivalent over an arbitrary field.
* `Stacks.Curves.isNode_tfae` — conditions (1), (2), (3) and (6) of Stacks Tag 0C4D are
  equivalent over an arbitrary field, with no hypothesis beyond closedness of the point.
* `Stacks.Curves.isNode_tfae_of_fittingIdeal_equivalence` — all six conditions of Stacks
  Tag 0C4D are equivalent over an arbitrary field as soon as condition (1) is equivalent to
  condition (4) and condition (5) implies condition (4).

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C3X](https://stacks.math.columbia.edu/tag/0C3X)
* [Stacks Project, Tag 0C56](https://stacks.math.columbia.edu/tag/0C56)
* [Stacks Project, Tag 0C4Y](https://stacks.math.columbia.edu/tag/0C4Y)
* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

namespace Stacks.Curves

/-- **At a node the maximal ideal of `𝒪_{X,x}` generates the maximal ideal of `𝒪_{X_K,y}`.**

The point `y` is again a node over `K` (Stacks Tag 0C56), so both delta invariants are one; the
sharpened form of Stacks Tag 0C3X then bounds the length of the special fibre by one, and a
local ring of length one over itself is a field. -/
theorem isField_specialFibre_of_isNode
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X = 1)
    (y : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u}))
    (hnode :
      letI : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨f⟩
      IsNode k X ((pullback.fst f
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)) :
    IsField
      ((pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk y ⧸
        Ideal.map
          ((pullback.fst f
            (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom
          (maximalIdeal
            (X.presheaf.stalk
              ((pullback.fst f
                (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)))) := by
  let : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨f⟩
  have hlftX : LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType f)
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback f g : Scheme.{u})
  let p : Y ⟶ X := pullback.fst f g
  let q : Y ⟶ AlgebraicGeometry.Spec (.of K) := pullback.snd f g
  let : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
  have hlftY : LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f g))
  have hY : topologicalKrullDim Y = 1 :=
    (AlgebraicGeometry.topologicalKrullDim_baseChange k K p q f
      (IsPullback.of_hasPullback f g)).trans hX
  -- the delta invariant at `x`
  obtain ⟨-, hdeltaA, -⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode k X hX
      (p.base y) hnode
  -- `y` is a node over `K`, so the delta invariant there is one as well
  have hnodeY : IsNode K Y y :=
    (isNode_iff_of_fieldExtension k K X f hX (p.base y) y rfl).mp hnode
  obtain ⟨-, hdeltaB, -⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode K Y hY
      y hnodeY
  -- the sharpened inequality bounds the length of the special fibre
  have hle := AlgebraicGeometry.deltaInvariant_mul_length_specialFibre_stalk_le_baseChange
    k K f y
  rw [hdeltaA, hdeltaB, one_mul] at hle
  have hne : Module.length (Y.presheaf.stalk y)
      (Y.presheaf.stalk y ⧸
        Ideal.map (p.stalkMap y).hom (maximalIdeal (X.presheaf.stalk (p.base y)))) ≠ 0 := by
    rw [ne_eq, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial]
    exact Ideal.Quotient.nontrivial_iff.mpr
      (IsLocalRing.map_maximalIdeal_lt_top (p.stalkMap y).hom).ne
  have hone : Module.length (Y.presheaf.stalk y)
      (Y.presheaf.stalk y ⧸
        Ideal.map (p.stalkMap y).hom (maximalIdeal (X.presheaf.stalk (p.base y)))) = 1 :=
    le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
  have hsimple := Module.length_eq_one_iff.mp hone
  have hmax : (Ideal.map (p.stalkMap y).hom
      (maximalIdeal (X.presheaf.stalk (p.base y)))).IsMaximal :=
    Ideal.isMaximal_def.mpr (isSimpleModule_iff_isCoatom.mp hsimple)
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax

/-- **The residue field at a node is separable over the base field.**

This is the clause of conditions (2), (4), (5) and (6) of Stacks Tag 0C4D that conditions (1)
and (3) do not display, and the source obtains it from the closed subscheme cut out by the first
Fitting ideal of `Ω_{X/k}`.  The route here is different and stays inside the delta invariant.

Base change to `k^{1/p}`.  At a node the maximal ideal of `𝒪_{X,x}` generates the maximal ideal
upstairs (`Stacks.Curves.isField_specialFibre_of_isNode`), so the special fibre of the map on
local rings is a field.  That special fibre is the localization of `κ(x) ⊗_k k^{1/p}` at the
prime cut out by the chosen point (Stacks Tag 0C4Y), so a nonzero reduced *flat* algebra over
`κ(x) ⊗_k k^{1/p}` exists, which forces `κ(x) ⊗_k k^{1/p}` itself to be reduced — every element
of it is a unit or nilpotent, so its maximal ideal acts as zero and flatness upgrades to
faithful flatness.  Reducedness of `κ(x) ⊗_k k^{1/p}` is separability of `κ(x)/k` by Stacks
Tag 030W. -/
@[stacks 0C4D "the separability of the residue field extension, from condition (1), over an \
arbitrary base field"]
theorem isSeparableExtension_residueField_of_isNode
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) :
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    IsNode k X x → Algebra.IsSeparableExtension k (X.residueField x) := by
  intro kToStalk hnode
  let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
  let g : AlgebraicGeometry.Spec (.of (AdjoinPthRoots k)) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinPthRoots k)))
  obtain ⟨y, hxy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x
    (IsLocalRing.closedPoint (AdjoinPthRoots k)) (Subsingleton.elim _ _)
  subst hxy
  let : Algebra k (X.presheaf.stalk ((pullback.fst f g).base y)) := kToStalk.toAlgebra
  let : Algebra k (X.residueField ((pullback.fst f g).base y)) :=
    ((X.residue ((pullback.fst f g).base y)).hom.comp kToStalk).toAlgebra
  have hfield := isField_specialFibre_of_isNode k (AdjoinPthRoots k) X f hX y hnode
  let : Field _ := hfield.toField
  let p₀ := RingHom.ker (Scheme.Pullback.ofPointTensor y).hom
  have : p₀.IsPrime := RingHom.ker_isPrime _
  let eResid :
      (X.residueField ((pullback.fst f g).base y) ⊗[k] AdjoinPthRoots k) ≃+*
        (Scheme.Pullback.Triplet.ofPoint y).tensor :=
    (residuePushoutTensorIso f ((pullback.fst f g).base y) ≪≫
      residueBaseChangeTensorIso f y).commRingCatIsoToRingEquiv
  let q := p₀.comap eResid.toRingHom
  have : q.IsPrime := Ideal.comap_isPrime _ _
  let eLoc : Localization.AtPrime q ≃+* Localization.AtPrime p₀ :=
    Localization.localRingEquiv q p₀ eResid rfl
  have : IsReduced (Localization.AtPrime q) :=
    isReduced_of_ringEquiv
      (eLoc.trans (specialFibreRingEquiv k (AdjoinPthRoots k) f y).symm) inferInstance
  exact Algebra.isSeparableExtension_of_flat_isReduced k
    (X.residueField ((pullback.fst f g).base y)) (Localization.AtPrime q)

/-- **Conditions (1) and (2) of Stacks Tag 0C4D agree over an arbitrary field.**

A point of a one-dimensional scheme locally of finite type over `k` is a node exactly when its
local ring is a nodal `k`-algebra.  Separability of `κ(x)/k`, the one clause of condition (2)
that condition (1) does not display, is supplied by
`Stacks.Curves.isSeparableExtension_residueField_of_isNode`. -/
@[stacks 0C4D "clauses (1) and (2), over an arbitrary base field"]
theorem isNode_iff_isNodalAlgebra_stalk
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) :
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    (IsNode k X x ↔ IsNodalAlgebra k (X.presheaf.stalk x)) := by
  intro kToStalk
  exact ⟨fun hnode => isNodalAlgebra_stalk_of_isNode_of_isSeparableExtension k X hX x
      (isSeparableExtension_residueField_of_isNode k X hX x hnode) hnode,
    isNode_of_isNodalAlgebra_stalk k X hX x⟩

/-- **The four conditions of Stacks Tag 0C4D that do not mention the first Fitting ideal are
equivalent over an arbitrary field.**

Conditions (1), (2), (3) and (6) of the tag, at a closed point of a one-dimensional scheme
locally of finite type over an arbitrary field, with no hypothesis beyond closedness of the
point.  Each of the four implies that `κ(x)/k` is separable — conditions (2) and (6) say so
outright, and conditions (1) and (3) by
`Stacks.Curves.isSeparableExtension_residueField_of_isNode` — and under that separability the
four are already known to be equivalent. -/
@[stacks 0C4D "clauses (1), (2), (3) and (6), over an arbitrary base field"]
theorem isNode_tfae
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
    List.TFAE [c₁, c₂, c₃, c₆] := by
  intro f kToStalk c₁ c₂ c₃ c₆
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
  have hsep₁ : c₁ → Algebra.IsSeparableExtension k (X.residueField x) :=
    isSeparableExtension_residueField_of_isNode k X hX x
  have hsep₂ : c₂ → Algebra.IsSeparableExtension k (X.residueField x) :=
    fun h => hsep₁ (isNode_of_isNodalAlgebra_stalk k X hX x h)
  have hsep₃ : c₃ → Algebra.IsSeparableExtension k (X.residueField x) :=
    fun h => hsep₁ (isNode_of_forall_isOrdinaryDoublePoint k X x hx h)
  tfae_have 1 → 2 := fun h =>
    ((isNode_tfae_of_isSeparableExtension_residueField k X hX x hx (hsep₁ h)).out 1 2).mp h
  tfae_have 2 → 3 := fun h =>
    ((isNode_tfae_of_isSeparableExtension_residueField k X hX x hx (hsep₂ h)).out 2 3).mp h
  tfae_have 3 → 4 := fun h =>
    ((isNode_tfae_of_isSeparableExtension_residueField k X hX x hx (hsep₃ h)).out 3 4).mp h
  tfae_have 4 → 1 := fun h =>
    ((isNode_tfae_of_isSeparableExtension_residueField k X hX x hx h.1).out 4 1).mp h
  tfae_finish

/-- **All six conditions of Stacks Tag 0C4D are equivalent over an arbitrary field as soon as
condition (1) is equivalent to condition (4) and condition (5) implies condition (4).**

This improves `Stacks.Curves.isNode_tfae_of_fittingIdeal_equivalences`, which asks for the full
equivalence of conditions (4) and (5): the implication from (4) to (5) now follows, because
condition (4) gives condition (1) and a node has a local ring of depth one
(`Stacks.Curves.ringKrullDim_stalk_eq_one_and_depth_eq_one_of_isNode`) whose residue field
extension is separable (`Stacks.Curves.isSeparableExtension_residueField_of_isNode`), while the
Fitting-ideal clause is carried along unchanged.

What remains assumed is not proved here: that condition (1) is equivalent to condition (4),
and that the Fitting-ideal condition together with depth one recovers condition (4).  Both are
statements about the first Fitting ideal of `Ω_{X/k}`, which is the part of the source's proof
that goes through a finite presentation of the local ring; both are discharged at an arbitrary
closed point by `Stacks.Curves.isNode_tfae_of_isClosed`, downstream of this file. -/
theorem isNode_tfae_of_fittingIdeal_equivalence
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
    (c₁ ↔ c₄) → (c₅ → c₄) → List.TFAE [c₁, c₂, c₃, c₄, c₅, c₆] := by
  intro f kToStalk omega fittingCondition c₁ c₂ c₃ c₄ c₅ c₆ h₁₄ h₅₄
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
  tfae_have 1 ↔ 2 := isNode_iff_isNodalAlgebra_stalk k X hX x
  tfae_have 1 ↔ 4 := h₁₄
  tfae_have 1 → 5 := fun h =>
    ⟨isSeparableExtension_residueField_of_isNode k X hX x h,
      (ringKrullDim_stalk_eq_one_and_depth_eq_one_of_isNode k X hX x h).2,
      (h₁₄.mp h).2.2⟩
  tfae_have 5 → 4 := h₅₄
  tfae_have 1 ↔ 3 :=
    ⟨forall_isOrdinaryDoublePoint_of_isNode k X x, isNode_of_forall_isOrdinaryDoublePoint k X x hx⟩
  tfae_have 2 ↔ 6 :=
    isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches k X hX x
  tfae_finish

/-- The map from the ground field to the residue field at a point of a scheme over it, written
as the composite through the residue field of the image point of `Spec k` that the base-change
package uses. -/
theorem fieldToResidue_eq (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
    fieldToResidue f x =
      (CommRingCat.ofHom (algebraMap k (f.base x).asIdeal.ResidueField)) ≫
        (Scheme.Spec.residueFieldIso (.of k) (f.base x)).inv ≫ f.residueFieldMap x := by
  let : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
  rw [fieldToResidue_eq_residueFieldMap]
  rw [show (specFieldResidueIso k (f.base x)).inv =
    (CommRingCat.ofHom (algebraMap k (f.base x).asIdeal.ResidueField)) ≫
      (Scheme.Spec.residueFieldIso (.of k) (f.base x)).inv from rfl]
  simp

end Stacks.Curves

end
