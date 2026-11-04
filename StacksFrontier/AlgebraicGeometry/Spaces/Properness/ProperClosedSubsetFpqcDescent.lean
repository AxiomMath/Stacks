module

public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Properness of a closed subset over the base descends along an fpqc covering

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, locally
of finite type, and let `T` be a closed subset of `|X|`.  If `{g i : Y i ⟶ Y}` is an fpqc covering
and, in cartesian squares `X i = Y i ×_Y X`, the inverse image of `T` in `|X i|` is proper over
`Y i` (Stacks 0CZD), then `T` is proper over `Y`.

The reduced induced closed subspace `Z` on `T` pulls back to a closed subspace of `X i` whose
points are the inverse image of `T`; being proper over `Y i` does not depend on which closed
subspace with those points is used
(`AlgebraicGeometry.Space.exists_isProper_closedSubspace_iff_forall`), so `Z ×_Y Y i ⟶ Y i` is
proper for every `i`, and properness descends along the fpqc covering by Stacks 0422.

## Main results

* `AlgebraicGeometry.Space.isProperOver_of_isFpqcCovering_of_isPullback`: the descent statement.

## References

* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 0CZF](https://stacks.math.columbia.edu/tag/0CZF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **Properness of a closed subset over the base descends along an fpqc covering.** -/
theorem isProperOver_of_isFpqcCovering_of_isPullback {I : Type v} {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) {Yi Xi : I → AlgebraicSpaces B S hS}
    (g : ∀ i, Yi i ⟶ Y) (hg : IsFpqcCovering B S hS fun i => (g i).hom)
    (g' : ∀ i, Xi i ⟶ X) (f' : ∀ i, Xi i ⟶ Yi i) (sq : ∀ i, IsPullback (g' i) (f' i) f (g i))
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (h : ∀ i, IsProperOver B S hS (Xi i).2 (Yi i).2 (f' i).hom
      ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback (sq i) hf)
      (pointsMap B S hS (Xi i).1 (g' i).hom ⁻¹' T)
      (isClosed_preimage_pointsMap B S hS (Xi i).2 X.2 (g' i).hom hT)) :
    IsProperOver B S hS X.2 Y.2 f.hom hf T hT := by
  set Z := reducedClosedSubspace B S hS X.1 X.property T hT with hZdef
  have hZc : IsClosedSubspace B S hS Z :=
    isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent B S hS X.1 X.2 T hT
      (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS)
  let Zs : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZc.1⟩
  let zf : Zs ⟶ Y := ObjectProperty.homMk (Z.ι ≫ f.hom)
  show properProperty B S hS zf
  have hloc := proper_isLocalAtTarget_fpqc.{u, v} B S hS
  refine hloc.of_forall_pullbackSnd (R := Presieve.ofArrows Yi g)
    ⟨I, Yi, g, rfl, Y.2, fun i => (Yi i).2, hg⟩ ?_
  rintro U k _ ⟨i⟩
  -- the inverse image of `Z` in `X i`
  set Q := Z.preimage (g' i).hom with hQdef
  have hQc : IsClosedSubspace B S hS Q :=
    isClosedSubspace_preimage B S hS (g' i).hom Z X.2 (Xi i).2 hZc
  let Qs : AlgebraicSpaces B S hS := ⟨Q.toFunctor, hQc.1⟩
  have hsqQ : IsPullback (Z.fromPreimage (g' i).hom) Q.ι Z.ι (g' i).hom :=
    Subfunctor.isPullback_preimage (g' i).hom Z
  have hpullQ : IsPullback
      (ObjectProperty.homMk (Z.fromPreimage (g' i).hom) : Qs ⟶ Zs)
      (ObjectProperty.homMk Q.ι : Qs ⟶ Xi i) (ObjectProperty.homMk Z.ι : Zs ⟶ X) (g' i) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) hsqQ
  have hbig : IsPullback (ObjectProperty.homMk (Z.fromPreimage (g' i).hom) : Qs ⟶ Zs)
      ((ObjectProperty.homMk Q.ι : Qs ⟶ Xi i) ≫ f' i) zf (g i) :=
    hpullQ.paste_vert (sq i)
  -- `Q ⟶ Y i` is proper
  have hQT : Set.range (pointsMap B S hS Q.toFunctor Q.ι) =
      pointsMap B S hS (Xi i).1 (g' i).hom ⁻¹' T := by
    rw [hQdef, range_pointsMap_ι_preimage B S hS (Xi i).2 X.2 (g' i).hom Z hZc.1,
      range_pointsMap_ι_reducedClosedSubspace]
  obtain ⟨W, hW, hWT, hWproper⟩ := (isProper_reducedClosedSubspace_iff_exists B S hS (Xi i).2
    (Yi i).2 (f' i).hom _ _ _).1 (h i)
  have hQproper : IsProper B S hS (Q.ι ≫ (f' i).hom) :=
    isProper_ι_comp_of_isProper_ι_comp B S hS (Xi i).2 (Yi i).2 _
      ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback (sq i) hf) _
      (isClosed_preimage_pointsMap B S hS (Xi i).2 X.2 (g' i).hom hT) W hW hWT hWproper Q hQc hQT
  have hP : properProperty B S hS ((ObjectProperty.homMk Q.ι : Qs ⟶ Xi i) ≫ f' i) := hQproper
  have : HasPullback zf (g i) := hbig.hasPullback
  have e : pullback.snd zf (g i) =
      hbig.isoPullback.inv ≫ ((ObjectProperty.homMk Q.ι : Qs ⟶ Xi i) ≫ f' i) := by
    simp
  rw [e]
  exact MorphismProperty.RespectsIso.precomp _ _ _ hP

end AlgebraicGeometry.Space

end
