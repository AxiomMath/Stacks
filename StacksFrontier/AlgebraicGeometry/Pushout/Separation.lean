module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Pushout.Coproduct

/-!
# Separatedness of a pushout along a closed immersion and an integral morphism

If the two schemes glued in a pushout `Y ⨿_Z X` along a closed immersion and an integral
morphism are separated, then so is the pushout, and the same holds for separatedness over the
base, for quasi-separatedness, and for quasi-separatedness over the base.

## Main results

* `AlgebraicGeometry.pushoutScheme_isSeparated`
* `AlgebraicGeometry.pushoutToBase_isSeparated`
* `AlgebraicGeometry.pushoutScheme_quasiSeparatedSpace`
* `AlgebraicGeometry.pushoutToBase_quasiSeparated`

## Implementation notes

All four statements descend the property along the surjective universally closed morphism
`AlgebraicGeometry.pushoutCoprodDesc` from the coproduct `Y ⨿ X`, using the descent results of
[Stacks Project, Tag 09MQ].  What has to be checked in each case is the property *for the
coproduct*, which is where the two hypotheses are consumed.

For the two relative statements the structure morphism of the coproduct is factored as
`coprod.map pY pX` followed by the codiagonal `S ⨿ S ⟶ S`; the first factor is handled by
`AlgebraicGeometry.IsZariskiLocalAtTarget.coprodMap` and the second is affine.  For the absolute
quasi-separated statement the underlying space of the coproduct is the topological sum, and
quasi-separatedness of a sum is proved directly: an intersection of two retrocompact opens is
the union of the images of the corresponding intersections in the two summands.

`IsZariskiLocalAtTarget @QuasiSeparated` is not found by `inferInstance` on this Mathlib
revision and is fed as a term built from the affine-property instance, as in
`StacksFrontier.AlgebraicGeometry.Pushout.Gluing`.

## References

* [Stacks Project, Tag 0E26](https://stacks.math.columbia.edu/tag/0E26)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 09MQ](https://stacks.math.columbia.edu/tag/09MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0E26.** If both schemes being glued are separated, then the pushout
along a closed immersion and an integral morphism is separated. -/
@[stacks 0E26 "separated"]
instance pushoutScheme_isSeparated
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    [s.X.IsSeparated] [s.Y.IsSeparated] :
    (pushoutScheme s).IsSeparated := by
  have : (s.Y ⨿ s.X).IsSeparated := by
    let fY : s.Y ⟶ (⊤_ Scheme.{u}) := terminal.from s.Y
    let fX : s.X ⟶ (⊤_ Scheme.{u}) := terminal.from s.X
    let codiag : (⊤_ Scheme.{u}) ⨿ (⊤_ Scheme.{u}) ⟶ (⊤_ Scheme.{u}) := coprod.desc (𝟙 _) (𝟙 _)
    have := IsSeparated.of_isAffineHom codiag
    have : IsSeparated (coprod.map fY fX) :=
      IsZariskiLocalAtTarget.coprodMap fY fX inferInstance inferInstance
    apply Scheme.IsSeparated.mk
    rw [show terminal.from (s.Y ⨿ s.X) = coprod.map fY fX ≫ codiag from
      terminalIsTerminal.hom_ext _ _]
    infer_instance
  exact Scheme.isSeparated_of_surjective_universallyClosed (pushoutCoprodDesc s)

/-- **Stacks Project, Tag 0E26.** If both schemes being glued are separated over the base, then
the pushout along a closed immersion and an integral morphism is separated over the base. -/
@[stacks 0E26 "separated_over_s"]
instance pushoutToBase_isSeparated
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    [IsSeparated s.pX] [IsSeparated s.pY] :
    IsSeparated (pushoutToBase s) := by
  let q : s.Y ⨿ s.X ⟶ s.S := coprod.desc s.pY s.pX
  have hq : IsSeparated q := by
    let codiag : s.S ⨿ s.S ⟶ s.S := coprod.desc (𝟙 s.S) (𝟙 s.S)
    have := IsSeparated.of_isAffineHom codiag
    have : IsSeparated (coprod.map s.pY s.pX) :=
      IsZariskiLocalAtTarget.coprodMap s.pY s.pX inferInstance inferInstance
    rw [show q = coprod.map s.pY s.pX ≫ codiag by apply coprod.hom_ext <;> simp [q, codiag]]
    infer_instance
  let src : Over s.S := Over.mk q
  let tgt : Over s.S := Over.mk (pushoutToBase s)
  let f : src ⟶ tgt := Over.homMk (pushoutCoprodDesc s) (by
    apply coprod.hom_ext <;> simp [src, tgt, q, pushoutToBase])
  have : Surjective f.left := inferInstanceAs (Surjective (pushoutCoprodDesc s))
  have : UniversallyClosed f.left := inferInstanceAs (UniversallyClosed (pushoutCoprodDesc s))
  have : IsSeparated src.hom := hq
  exact isSeparated_of_surjective_universallyClosed f

private theorem quasiSeparatedSpace_sum {α β : Type u} [TopologicalSpace α]
    [TopologicalSpace β] [QuasiSeparatedSpace α] [QuasiSeparatedSpace β] :
    QuasiSeparatedSpace (α ⊕ β) := by
  rw [quasiSeparatedSpace_iff]
  intro U V hU hUc hV hVc
  have key {γ : Type u} [TopologicalSpace γ] [QuasiSeparatedSpace γ] {i : γ → α ⊕ β}
      (hi : Topology.IsClosedEmbedding i) :=
    QuasiSeparatedSpace.inter_isCompact _ _ (hU.preimage hi.continuous)
      (hi.isCompact_preimage hUc) (hV.preimage hi.continuous) (hi.isCompact_preimage hVc)
  rw [show U ∩ V = Sum.inl '' (Sum.inl ⁻¹' U ∩ Sum.inl ⁻¹' V) ∪
      Sum.inr '' (Sum.inr ⁻¹' U ∩ Sum.inr ⁻¹' V) by ext (x | x) <;> simp]
  exact ((key .inl).image continuous_inl).union ((key .inr).image continuous_inr)

/-- **Stacks Project, Tag 0E26.** If both schemes being glued are quasi-separated, then the
pushout along a closed immersion and an integral morphism is quasi-separated. -/
@[stacks 0E26 "quasi_separated"]
instance pushoutScheme_quasiSeparatedSpace
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    [QuasiSeparatedSpace s.X] [QuasiSeparatedSpace s.Y] :
    QuasiSeparatedSpace (pushoutScheme s) := by
  have : QuasiSeparatedSpace (s.Y ⨿ s.X : Scheme.{u}) :=
    (quasiSeparatedSpace_congr (AlgebraicGeometry.coprodMk s.Y s.X)).mp
      (quasiSeparatedSpace_sum (α := s.Y) (β := s.X))
  exact quasiSeparatedSpace_of_surjective_universallyClosed (pushoutCoprodDesc s)

/-- **Stacks Project, Tag 0E26.** If both schemes being glued are quasi-separated over the
base, then the pushout along a closed immersion and an integral morphism is quasi-separated
over the base. -/
@[stacks 0E26 "quasi_separated_over_s"]
instance pushoutToBase_quasiSeparated
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    [QuasiSeparated s.pX] [QuasiSeparated s.pY] :
    QuasiSeparated (pushoutToBase s) := by
  let codiag : s.S ⨿ s.S ⟶ s.S := coprod.desc (𝟙 s.S) (𝟙 s.S)
  have : IsZariskiLocalAtTarget @QuasiSeparated :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat
  have : QuasiSeparated (coprod.map s.pY s.pX) :=
    IsZariskiLocalAtTarget.coprodMap s.pY s.pX inferInstance inferInstance
  have hsource : QuasiSeparated (coprod.desc s.pY s.pX) := by
    rw [show coprod.desc s.pY s.pX = coprod.map s.pY s.pX ≫ codiag by
      apply coprod.hom_ext <;> simp [codiag]]
    infer_instance
  let src : Over s.S := Over.mk (coprod.desc s.pY s.pX)
  let tgt : Over s.S := Over.mk (pushoutToBase s)
  let f : src ⟶ tgt := Over.homMk (pushoutCoprodDesc s) (by simp [src, tgt, pushoutToBase])
  have : QuasiSeparated src.hom := hsource
  have : Surjective f.left := inferInstanceAs (Surjective (pushoutCoprodDesc s))
  have : UniversallyClosed f.left := inferInstanceAs (UniversallyClosed (pushoutCoprodDesc s))
  exact quasiSeparated_of_surjective_universallyClosed f

end AlgebraicGeometry

end
