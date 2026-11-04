module

public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The relative diagonal of a representable transformation

Let `a : F ⟶ G` be a representable morphism of presheaves on the big fppf site of a scheme
`S`.  Stacks 05L9 asserts that the relative diagonal `F ⟶ F ×[G] F` is again representable.

It follows from the *cancellation* property of representability, which holds for the
morphisms relatively representable along any fully faithful functor `F : C ⥤ D` preserving
fibre products, out of a category `C` with fibre products: if `v` and `u ≫ v` are relatively
representable, so is `u`. For a multiplicative property stable under base change, the
of-postcomposition property is equivalent to the property passing to relative diagonals
(`CategoryTheory.MorphismProperty.hasOfPostcompProperty_iff_le_diagonal`).

## Main results

* `CategoryTheory.Functor.relativelyRepresentable.hasOfPostcompProperty`: cancellation.
* `CategoryTheory.Functor.relativelyRepresentable.diagonal`: the relative diagonal of a
  relatively representable morphism is relatively representable.
* `AlgebraicGeometry.Space.relativelyRepresentable_diagonal_of_representable` is Stacks 05L9
  itself, the case of presheaves on the big fppf site of a scheme.

## References

* [Stacks Project, Tag 05L9](https://stacks.math.columbia.edu/tag/05L9)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Functor.relativelyRepresentable

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- **Cancellation of relative representability.** Let `F : C ⥤ D` be fully faithful and
preserve fibre products, with `C` having fibre products.  If `v : Y ⟶ Z` and `u ≫ v` are
relatively representable along `F`, then so is `u : X ⟶ Y`. -/
instance hasOfPostcompProperty [F.Full] [F.Faithful] [HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan F] :
    F.relativelyRepresentable.HasOfPostcompProperty F.relativelyRepresentable where
  of_postcomp u v hv huv a k := by
    have hw : (huv.fst (k ≫ v) ≫ u) ≫ v = F.map (huv.snd (k ≫ v)) ≫ k ≫ v := by
      rw [Category.assoc]; exact huv.w (k ≫ v)
    have hk : k ≫ v = F.map (𝟙 a) ≫ k ≫ v := by simp
    set w := hv.lift (huv.fst (k ≫ v) ≫ u) (huv.snd (k ≫ v)) hw
    set σ := hv.lift k (𝟙 a) hk
    have hwfst : F.map w ≫ hv.fst (k ≫ v) = huv.fst (k ≫ v) ≫ u := hv.lift_fst _ _ _
    have hwsnd : w ≫ hv.snd (k ≫ v) = huv.snd (k ≫ v) := hv.lift_snd _ _ _
    have hσfst : F.map σ ≫ hv.fst (k ≫ v) = k := hv.lift_fst _ _ _
    have hbot : IsPullback (huv.fst (k ≫ v)) (F.map w) u (hv.fst (k ≫ v)) :=
      IsPullback.of_bot (by rw [← F.map_comp, hwsnd]; exact huv.isPullback (k ≫ v))
        hwfst.symm (hv.isPullback (k ≫ v))
    have htop : IsPullback (F.map (pullback.fst w σ)) (F.map (pullback.snd w σ))
        (F.map w) (F.map σ) :=
      F.map_isPullback (IsPullback.of_hasPullback w σ)
    refine ⟨Limits.pullback w σ, pullback.snd w σ,
      F.map (pullback.fst w σ) ≫ huv.fst (k ≫ v), ?_⟩
    have := htop.paste_horiz hbot
    rwa [hσfst] at this

/-- The relative diagonal of a relatively representable morphism is relatively
representable. -/
theorem diagonal [F.Full] [F.Faithful] [HasPullbacks C] [HasPullbacks D]
    [PreservesLimitsOfShape WalkingCospan F] {X Y : D} {f : X ⟶ Y}
    (hf : F.relativelyRepresentable f) :
    F.relativelyRepresentable (pullback.diagonal f) :=
  MorphismProperty.diagonal_iff.mp
    ((MorphismProperty.hasOfPostcompProperty_iff_le_diagonal (P := F.relativelyRepresentable)
      (Q := F.relativelyRepresentable)).mp inferInstance f hf)

end CategoryTheory.Functor.relativelyRepresentable

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05L9.** The relative diagonal of a representable morphism of presheaves on the
big fppf site over `S` is representable. -/
theorem relativelyRepresentable_diagonal_of_representable
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : yoneda.relativelyRepresentable a) :
    yoneda.relativelyRepresentable (pullback.diagonal a) :=
  ha.diagonal

end AlgebraicGeometry.Space

end
