module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.DeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionAntitone
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints

/-!
# Points of maximal delta-dimension

In Situation 0EDT, let `X` be good over the base and let `T` be a closed set of points of `X`.
**Stacks 0EE6** says that a point of `T` at which the induced dimension function attains the
delta-dimension bound of `T` is a generic point of an irreducible component of `T`.

## Main results

* `AlgebraicGeometry.Space.isGenericPoint_of_deltaDimensionClosed_le`: **Stacks 0EE6.**

## Implementation notes

The proof is the source's.  The point lies in some irreducible component of `T`, whose generic
point specializes to it; the delta-dimension bound caps the value of the induced dimension
function at that generic point by `k`; and if the two points differed, the strict antitonicity of
the induced dimension function along nontrivial specializations would make the value at the point
strictly below `k`, contradicting the hypothesis that it equals `k`.

The generic points exist because the points of a good algebraic space are quasi-sober,
`AlgebraicGeometry.Space.quasiSober_points_of_isGood`, and a closed subset of a quasi-sober space
is quasi-sober; that instance is installed here exactly as it is inside
`AlgebraicGeometry.Space.deltaDimensionClosed`, so the supremum unfolds by `rfl`.

The antitonicity is `AlgebraicGeometry.Space.lt_inducedDimensionValue_of_specializes`, whose
decency hypotheses are discharged from the situation: for `X` by
`AlgebraicGeometry.Space.isDecentSpace_of_isGood`, and for the base by
`AlgebraicGeometry.Space.isDecentSpace_of_isAbsolutelyQuasiSeparated`.

## References

* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EE6.** A point of a closed set of points at which the induced dimension function
attains the delta-dimension bound is a generic point of an irreducible component of that set. -/
@[stacks 0EE6]
theorem isGenericPoint_of_deltaDimensionClosed_le (f : X ⟶ D.space) (hf : D.IsGood f)
    (T : Set (points D.site D.base D.base_mem X)) (hT : IsClosed T)
    (t : points D.site D.base D.base_mem X) (ht : t ∈ T) (k : ℤ)
    (hbound : deltaDimensionClosed D f hf T hT ≤ (k : EInt))
    (hdim : inducedDimensionValue D.site D.base D.base_mem D.delta f t = k) :
    ∃ Z : irreducibleComponents T, IsGenericPoint (⟨t, ht⟩ : T) Z.1 := by
  classical
  have hanti : ∀ ⦃x y : points D.site D.base D.base_mem X⦄, x ⤳ y → x ≠ y →
      inducedDimensionValue D.site D.base D.base_mem D.delta f y <
        inducedDimensionValue D.site D.base D.base_mem D.delta f x :=
    lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hf.1
      (isDecentSpace_of_isGood D f hf) D.isAlgebraicSpace
      (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
        D.isAlgebraicSpace D.quasiSeparated)
      D.locallyNoetherian D.universallyCatenary D.delta f hf.2.2
  have _hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D f hf
  have _hTsober : QuasiSober T := hT.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨W, hW, hsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({(⟨t, ht⟩ : T)} : Set T))
      (isIrreducible_iff_closure.mpr isIrreducible_singleton)
  have hη : IsGenericPoint hW.1.genericPoint W := by
    simpa [isClosed_of_mem_irreducibleComponents W hW] using
      hW.1.isGenericPoint_genericPoint_closure
  have hbound' :
      (⨆ Z : irreducibleComponents T,
        (inducedDimensionValue D.site D.base D.base_mem D.delta f
          Z.2.1.genericPoint.1 : EInt)) ≤ (k : EInt) := hbound
  have hηle :
      inducedDimensionValue D.site D.base D.base_mem D.delta f hW.1.genericPoint.1 ≤ k :=
    WithBotTop.coe_le_coe.mp ((le_iSup _ (⟨W, hW⟩ : irreducibleComponents T)).trans hbound')
  by_cases hηt : hW.1.genericPoint = (⟨t, ht⟩ : T)
  · exact ⟨⟨W, hW⟩, by simpa [hηt] using hη⟩
  · have hlt := hanti ((hη.specializes (hsub (subset_closure rfl))).map continuous_subtype_val)
      (fun h => hηt (Subtype.ext h))
    rw [hdim] at hlt
    omega

end AlgebraicGeometry.Space

end
