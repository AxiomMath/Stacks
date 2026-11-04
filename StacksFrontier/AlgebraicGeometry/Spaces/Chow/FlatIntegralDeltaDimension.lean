module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatInverseImageDeltaDimension

/-!
# The δ-dimension of a space flat over an irreducible one

In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be a morphism over the base which
is flat of relative dimension `r`, and assume `|Y|` is irreducible and `X` is nonempty. Then

  `dim_δ(X) = dim_δ(Y) + r`.

This is the first clause of Stacks 0EP5 for the closed set `T = |Y|`: the inverse image of `|Y|`
is `|X|`, and `|Y|` has a single irreducible component, which `f` meets because `X` is nonempty.

## Main results

* `AlgebraicGeometry.Space.deltaDimensionClosed_univ_eq_add_of_isFlat`: the identity above.

## References

* [Stacks Project, Tag 0EP5](https://stacks.math.columbia.edu/tag/0EP5)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **The δ-dimension of a nonempty space flat of relative dimension `r` over an irreducible
one.** In Situation 0EDT let `f : X ⟶ Y` be a morphism of good algebraic spaces over the base
which is flat of relative dimension `r`. If `|Y|` is irreducible of δ-dimension `n` and `X` is
nonempty, then `dim_δ(X) = n + r`. -/
theorem deltaDimensionClosed_univ_eq_add_of_isFlat (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y} (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    [IrreducibleSpace (points D.site D.base D.base_mem Y)]
    (hXne : Nonempty (points D.site D.base D.base_mem X)) {n : ℤ}
    (hn : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)) :
    deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((n + r : ℤ) : EInt) := by
  obtain ⟨x⟩ := hXne
  have h := deltaDimensionClosed_preimage_eq_iSup_add D sX hX sY hY hbase r hflat hr Set.univ
    isClosed_univ ⟨x, Set.mem_univ _⟩
  rw [deltaDimensionClosed_congr D sX hX (Set.preimage_univ) _ isClosed_univ] at h
  rw [h]
  have hirr : IrreducibleSpace (Set.univ : Set (points D.site D.base D.base_mem Y)) :=
    Subtype.irreducibleSpace (IrreducibleSpace.isIrreducible_univ _)
  have hval : ∀ C : irreducibleComponents (Set.univ : Set (points D.site D.base D.base_mem Y)),
      (Subtype.val '' (C : Set (Set.univ : Set (points D.site D.base D.base_mem Y)))) =
        Set.univ := fun ⟨C, hC⟩ => by
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hC
    subst hC
    rw [Set.image_univ, Subtype.range_coe]
  have hterm : ∀ C : irreducibleComponents (Set.univ : Set (points D.site D.base D.base_mem Y)),
      (⨆ _ : (pointsMap D.site D.base D.base_mem X f ⁻¹'
          (Subtype.val '' (C : Set (Set.univ : Set (points D.site D.base D.base_mem Y))))).Nonempty,
        deltaDimensionClosed D sY hY (closure (Subtype.val '' (C : Set
          (Set.univ : Set (points D.site D.base D.base_mem Y))))) isClosed_closure) =
        (n : EInt) := fun C => by
    have hne : (pointsMap D.site D.base D.base_mem X f ⁻¹'
        (Subtype.val '' (C : Set (Set.univ : Set (points D.site D.base D.base_mem Y))))).Nonempty :=
      ⟨x, by rw [hval C]; exact Set.mem_univ _⟩
    rw [iSup_pos hne, ← hn]
    exact deltaDimensionClosed_congr D sY hY (by rw [hval C, closure_univ]) _ _
  have : Nonempty (irreducibleComponents (Set.univ : Set (points D.site D.base D.base_mem Y))) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; exact Set.mem_singleton _⟩⟩
  rw [iSup_congr hterm, iSup_const, Stacks.Chow.coe_add_coe_eq_coe_add]

end AlgebraicGeometry.Space

end
