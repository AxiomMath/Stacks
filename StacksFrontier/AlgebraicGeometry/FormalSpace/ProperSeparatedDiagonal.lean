module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Proper
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM

/-!
# A proper morphism of formal algebraic spaces is separated

Let `S` be a scheme contained in a big fppf site `B`. A proper morphism `f : X ⟶ Y` of formal
algebraic spaces over `S` (Definition 0AM6) is representable by algebraic spaces, and each of its
base changes `X ×_Y T ⟶ T` along a scheme `T` over `Y` is a proper, in particular separated,
morphism of algebraic spaces. This file shows that `f` is then separated in the sense of
Stacks 0ARN: its relative diagonal `Δ_f : X ⟶ X ×_Y X` is a closed immersion.

## Main results

* `AlgebraicGeometry.FormalSpace.IsProper.isSeparatedMorphism`: a proper morphism of formal
  algebraic spaces is separated.

## Implementation notes

The base change of `Δ_f` along a morphism `T ⟶ X ×_Y X` from a scheme is a base change of the
relative diagonal of `X ×_Y T ⟶ T`, where `T ⟶ Y` is the composite through either projection
(`CategoryTheory.Limits.isPullback_diagonal_pullback_snd`). Separatedness of that base change
makes its relative diagonal a closed immersion relative to the universe-lifted Yoneda
embedding, hence so is the base change of `Δ_f`. The argument runs on the underlying
presheaves, and the comparison of the relative diagonal of the sheaf morphism with that of the
presheaf morphism is the isomorphism by which the forgetful functor preserves fibre products.

## References

* [Stacks Project, Tag 0AM6](https://stacks.math.columbia.edu/tag/0AM6)
* [Stacks Project, Tag 0ARN](https://stacks.math.columbia.edu/tag/0ARN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A proper morphism of formal algebraic spaces is separated.** Let `f : X ⟶ Y` be a proper
morphism of fppf sheaves on the big fppf site of `S` (Definition 0AM6). Then the relative
diagonal `Δ_f : X ⟶ X ×_Y X` is a closed immersion, that is, `f` is separated in the sense of
Stacks 0ARN. -/
theorem IsProper.isSeparatedMorphism {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hf : IsProper B S hS f) : IsSeparatedMorphism B S hS f := by
  obtain ⟨hrep, hprop⟩ := hf
  let R := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let L := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  -- The relative diagonal of the underlying morphism of presheaves.
  have hbc : ∀ (U : BigFppfOver B S hS) (g : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj),
      R.relative (uliftYoneda.{u + 1}) (pullback.diagonal (pullback.snd f.hom g)) := by
    intro U g
    have hs : Space.IsSeparatedULift.{u + 1} B S hS (pullback.fst g f.hom) := (hprop U g).1
    rw [← pullbackSymmetry_hom_comp_fst f.hom g]
    exact MorphismProperty.RespectsIso.precomp (R.relative (uliftYoneda.{u + 1})).diagonal
      (pullbackSymmetry f.hom g).hom _ hs
  -- A point `a` of `X ×_Y X` over a scheme `U` factors as `b ≫ c` through the relative
  -- self-product over `U` of the base change of `f` along `g = a ≫ pr₁ ≫ f`, and the relative
  -- diagonal of that base change is a base change of the relative diagonal of `f` along `c`.
  have hpre : R.relative (uliftYoneda.{u + 1}) (pullback.diagonal f.hom) := by
    apply MorphismProperty.relative.of_exists
    intro U a
    let g := a ≫ pullback.fst f.hom f.hom ≫ f.hom
    let s : (uliftYoneda.{u + 1}).obj U ⟶ pullback f.hom g :=
      pullback.lift (a ≫ pullback.fst f.hom f.hom) (𝟙 _) (by simp [g])
    let t : (uliftYoneda.{u + 1}).obj U ⟶ pullback f.hom g :=
      pullback.lift (a ≫ pullback.snd f.hom f.hom) (𝟙 _) (by
        simp only [g, Category.id_comp, Category.assoc]
        rw [pullback.condition])
    let b : (uliftYoneda.{u + 1}).obj U ⟶
        pullback (pullback.snd f.hom g) (pullback.snd f.hom g) :=
      pullback.lift s t (by simp only [s, t, pullback.lift_snd])
    let c := pullback.map (pullback.snd f.hom g) (pullback.snd f.hom g) f.hom f.hom
      (pullback.fst f.hom g) (pullback.fst f.hom g) g pullback.condition.symm
      pullback.condition.symm
    have hbc' : b ≫ c = a := by
      apply pullback.hom_ext <;>
        simp only [b, c, s, t, Category.assoc, pullback.map, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.lift_fst]
    let hp := hbc U g
    let r := hp.rep
    refine ⟨r.pullback b, r.fst b ≫ pullback.fst f.hom g, r.snd b, ?_, hp.property_snd b⟩
    have hc : IsPullback (r.fst b ≫ pullback.fst f.hom g) ((uliftYoneda.{u + 1}).map (r.snd b))
        (pullback.diagonal f.hom) (b ≫ c) :=
      (r.isPullback b).paste_horiz (isPullback_diagonal_pullback_snd f.hom g)
    rwa [hbc'] at hc
  -- The relative diagonal of the sheaf morphism, read on presheaves.
  have hdiag : (pullback.diagonal f).hom =
      pullback.diagonal f.hom ≫ (PreservesPullback.iso L f f).inv := by
    rw [Iso.eq_comp_inv]
    apply pullback.hom_ext <;>
    · simp only [Category.assoc, PreservesPullback.iso_hom]
      first
        | erw [pullbackComparison_comp_fst]
        | erw [pullbackComparison_comp_snd]
      erw [← L.map_comp]
      simp
      rfl
  have hsh : R.relative (uliftYoneda.{u + 1}) (pullback.diagonal f).hom := by
    rw [hdiag]
    exact MorphismProperty.RespectsIso.postcomp _ _ _ hpre
  exact ⟨fun U ξ ↦ Space.isAlgebraicSpaceULift_of_iso B S hS
      ((hsh.rep.isPullback ξ).isoPullback ≪≫ pullbackSymmetry _ ξ)
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (hsh.rep.pullback ξ)),
    fun U ξ ↦ (MorphismProperty.relative_isStableUnderBaseChange R).of_isPullback
      (IsPullback.of_hasPullback ξ (pullback.diagonal f).hom).flip hsh⟩

end AlgebraicGeometry.FormalSpace

end
