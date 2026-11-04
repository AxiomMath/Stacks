module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.Additive
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackDimensionField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An algebraic stack of negative dimension: the classifying stack of `𝐆ₐ`

The last assertion of Stacks 0AFR is existential: *the dimension of an algebraic stack can be a
negative integer, in contrast to what happens for schemes or algebraic spaces.* This file exhibits
a witness over every field `k`: the classifying stack `B𝐆ₐ = [Spec k/𝐆ₐ]` of the additive group
is a locally Noetherian algebraic stack of dimension `-1`.

## Main results

* `AlgebraicGeometry.Space.smooth_additiveGroupBaseChange_hom`: `𝐆ₐ` is smooth over every base.
* `AlgebraicGeometry.Space.topologicalKrullDim_additiveGroupBaseChange_field`: `𝐆ₐ` over a field
  has dimension `1`.
* `AlgebraicGeometry.Stack.exists_dimension_classifyingStack_additiveGroup_eq_neg_one`:
  **Stacks 0AFR**, the classifying stack of `𝐆ₐ` over a field has a model in the 2-category of
  algebraic stacks, and every model is locally Noetherian of dimension `-1`.
* `AlgebraicGeometry.Stack.exists_algebraicStack_dimension_lt_zero`: **Stacks 0AFR**, over every
  field there is a locally Noetherian algebraic stack of negative dimension.

## Implementation notes

`𝐆ₐ` over `k` is the base change `𝐀¹_ℤ ×_ℤ Spec k`, which is `Spec (ℤ[X] ⊗_ℤ k) ≅ Spec k[X]`; its
dimension is `dim k[X] = dim k + 1 = 1`. It is smooth because `𝐀¹_ℤ ⟶ Spec ℤ` is, a polynomial
algebra being smooth, and smoothness is stable under base change. The group algebraic space over
`Spec k` it defines is represented by it, so its smoothness and its dimension are those of the
scheme, and `AlgebraicGeometry.Stack.dimension_classifyingStack_eq_neg_of_isSmooth` gives
`dim B𝐆ₐ = -1`.

The contrast with algebraic spaces is the type of their dimension: the dimension of an algebraic
space (Stacks 04N6) lies in `WithBot ℕ∞`, so it is never a negative integer, and for an algebraic
stack represented by an algebraic space the dimension of Stacks 0AFN is that dimension, by
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_zero_of_representing`.

## References

* [Stacks Project, Tag 0AFR](https://stacks.math.columbia.edu/tag/0AFR)
* [Stacks Project, Tag 022V](https://stacks.math.columbia.edu/tag/022V)
* [Stacks Project, Tag 043L](https://stacks.math.columbia.edu/tag/043L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

/-- The structure map of `𝐆ₐ` is the spectrum of the algebra map `ℤ → ℤ[X]`. -/
private theorem additiveGroup_hom_eq_spec_map :
    (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) =
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ)))) := rfl

/-- **The additive group scheme is smooth over every base.** The affine line over the integers is
smooth, a polynomial algebra being smooth, and smoothness is stable under base change. -/
@[sga "3 I 4.4.4" "G_a,S is smooth over S"]
theorem smooth_additiveGroupBaseChange_hom (S : Scheme.{u}) :
    Smooth (pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S)) := by
  have h : Smooth (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) := by
    rw [additiveGroup_hom_eq_spec_map, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr (by constructor <;> infer_instance)
  infer_instance

/-- **The additive group scheme over a field has dimension `1`.** It is the spectrum of
`ℤ[X] ⊗_ℤ k ≅ k[X]`, whose Krull dimension is `dim k + 1 = 1`. -/
theorem topologicalKrullDim_additiveGroupBaseChange_field (k : Type u) [Field k] :
    topologicalKrullDim (additiveGroupBaseChange (Spec (.of k))) = 1 := by
  let : Algebra (ULift.{u} ℤ) k :=
    ((Int.castRingHom k).comp ULift.ringEquiv.toRingHom).toAlgebra
  have h2 : specULiftZIsTerminal.from (Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) k)) :=
    specULiftZIsTerminal.hom_ext _ _
  let e := (pullback.congrHom additiveGroup_hom_eq_spec_map h2).trans
    (pullbackSpecIso (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ)) k)
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]
  have hk1 : ringKrullDim (Polynomial k) = 1 := by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    rfl
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans
    ((ringKrullDim_eq_of_ringEquiv ((polyEquivTensor (ULift.{u} ℤ) k).toRingEquiv.trans
      (Algebra.TensorProduct.comm (ULift.{u} ℤ) k
        (Polynomial (ULift.{u} ℤ))).toRingEquiv)).symm.trans hk1)

variable {k : Type u} [Field k] (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))

/-- The additive group algebraic space `𝐆ₐ` over the spectrum of a field. -/
noncomputable abbrev additiveGroupOverField :
    GroupAlgebraicSpace C (Spec (.of k)) hk (terminalSpace C (Spec (.of k)) hk).obj
      (terminalSpace C (Spec (.of k)) hk).property :=
  additiveGroupSpace C (Spec (.of k)) hk _ (terminalSpace C (Spec (.of k)) hk).property

/-- The additive group algebraic space over a field is smooth. -/
@[sga "3 I 4.4.4" "special case"]
theorem isSmooth_additiveGroupOverField :
    IsSmooth C (Spec (.of k)) hk (additiveGroupOverField C hk).obj.X.hom :=
  (isSmooth_hom_iff_smooth_of_iso_yoneda _ _
    (GroupAlgebraicSpace.ofGroupSchemeInSiteIsoYoneda (additiveGroupSiteObject C _ hk)
      (additiveGroupSiteObjectGrpObj C _ hk))).2
    (smooth_additiveGroupBaseChange_hom (Spec (.of k)))

/-- The additive group algebraic space over a field has dimension `1`. -/
theorem dimension_additiveGroupOverField :
    dimension C (Spec (.of k)) hk (additiveGroupOverField C hk).obj.X.left
      (additiveGroupOverField C hk).property = ((1 : ℕ) : WithBot ℕ∞) :=
  (dimension_eq_of_iso C (Spec (.of k)) hk (isAlgebraicSpace_yoneda C _ hk _) _
    (GroupAlgebraicSpace.ofGroupSchemeInSiteIsoYoneda (additiveGroupSiteObject C _ hk)
      (additiveGroupSiteObjectGrpObj C _ hk))).symm.trans
    ((dimension_yoneda_eq_topologicalKrullDim C _ hk _).trans
      (topologicalKrullDim_additiveGroupBaseChange_field k))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {k : Type u} [Field k] (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))

/-- **Stacks 0AFR: the classifying stack of `𝐆ₐ` has dimension `-1`.** Over every field `k`, the
classifying stack `B𝐆ₐ = [Spec k/𝐆ₐ]` has a model in the 2-category of algebraic stacks, and every
model is locally Noetherian of dimension `-1`. -/
@[stacks 0AFR "the dimension of an algebraic stack can be a negative integer: over every field \
the classifying stack of the additive group is constructed and has dimension `-1`"]
theorem exists_dimension_classifyingStack_additiveGroup_eq_neg_one :
    (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (classifyingStack C hk (Space.additiveGroupOverField C hk)).val.p 𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver
          (classifyingStack C hk (Space.additiveGroupOverField C hk)).val.p 𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN = ((-1 : ℤ) : EInt) := by
  obtain ⟨m, hm, hex, hall⟩ := dimension_classifyingStack_eq_neg_of_isSmooth.{u, w} C hk
    (Space.additiveGroupOverField C hk) (Space.isSmooth_additiveGroupOverField C hk)
  obtain rfl : m = 1 := by
    exact_mod_cast hm.symm.trans (Space.dimension_additiveGroupOverField C hk)
  exact ⟨hex, hall⟩

/-- **Stacks 0AFR: the dimension of an algebraic stack can be a negative integer.** Over every
field `k` there is a locally Noetherian algebraic stack of dimension `-1`, namely a model of the
classifying stack of the additive group. -/
@[stacks 0AFR "the dimension of an algebraic stack can be a negative integer: a locally \
Noetherian algebraic stack of dimension `-1` exists over every field"]
theorem exists_algebraicStack_dimension_lt_zero :
    ∃ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
      (hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬),
      dimension C (Spec (.of k)) hk 𝒬 hN = ((-1 : ℤ) : EInt) ∧
        dimension C (Spec (.of k)) hk 𝒬 hN < 0 := by
  obtain ⟨⟨𝒬, ⟨e⟩⟩, hall⟩ := exists_dimension_classifyingStack_additiveGroup_eq_neg_one.{u, w} C hk
  obtain ⟨hN, hdim⟩ := hall 𝒬 e
  refine ⟨𝒬, hN, hdim, ?_⟩
  rw [hdim, show (0 : EInt) = ((0 : ℤ) : EInt) from rfl, WithBotTop.coe_lt_coe]
  omega

end AlgebraicGeometry.Stack

end
