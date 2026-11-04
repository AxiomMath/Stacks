module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.MorphismDescent

/-!
# The gluing morphism of the descent datum of the inductive step of Stacks 04DZ

Let `f : X ⟶ Y` be a universal homeomorphism, let `w : W ⟶ Y` be étale, let `p : U ⟶ X` be
étale, let `q : V ⟶ W` be étale, and suppose the base change of `V` along `X ×_Y W ⟶ W` is
identified with `U ×_X (X ×_Y W)` over `X ×_Y W`. That is the data the split of the inductive
step of the second proof of Stacks Project, Tag 04DZ produces.

The descent datum for `V` relative to `w : W ⟶ Y` which the source then descends needs a gluing
morphism `V ×_Y W ⟶ W ×_Y V` over `W ×_Y W`. This file produces it.

## The shape of the argument

Over `X` everything is computable. The identification of the base changes gives an isomorphism

```
Φ : V ×_Y X ≅ U ×_X (X ×_Y W)
```

— the left-hand side is `V ×_W (X ×_Y W)`, because the `W`-coordinate of a point of `V ×_Y X` is
determined by its `V`-coordinate — and under `Φ` a point of `V ×_Y X` becomes a pair consisting
of a point `u` of `U` and a point of `X ×_Y W`. Replacing the `W`-coordinate of the latter by any
other point `w₂` of `W` over the same point of `Y`, and applying `Φ⁻¹`, produces a new point of
`V` lying over `w₂`. That is the action of `w₂` on a point of `V`, and it is the gluing morphism
read on points — except that it has been defined only in the presence of an auxiliary point
of `X`.

The auxiliary point is removed by the full faithfulness of base change along `f`: the action is a
morphism `(V ×_Y W) ×_Y X ⟶ (W ×_Y V) ×_Y X` over `X` between the base changes along `f` of two
schemes étale over `Y`, so `Stacks.Etale.exists_hom_of_pullbackHom_of_universalHomeomorphism`
descends it to a morphism `V ×_Y W ⟶ W ×_Y V` over `Y`. That it is a morphism over `W ×_Y W`,
which is the content of the two displayed equations, is then checked after base change along `f`
by `AlgebraicGeometry.eq_of_comp_eq_of_surjective_of_etale`, the projection
`(V ×_Y W) ×_Y X ⟶ V ×_Y W` being surjective because `f` is.

## Main results

* `Stacks.Etale.exists_gluing_hom_of_isoBaseChange` — the gluing morphism, together with the two
  equations saying that it lies over `W ×_Y W`.

## Implementation notes

The whole construction is carried out at the single universal point of `(V ×_Y W) ×_Y X`, so no
naturality of the action in a test scheme is needed and no auxiliary definition is introduced:
the action is a concrete composite of `CategoryTheory.Limits.pullback.lift` terms.

What is *not* produced here is the inverse of the gluing morphism, nor its cocycle condition;
those are the remaining content of the descent step
`Stacks.Etale.EtaleDescentAlongAffineEtaleSurjection`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

/-- **The gluing morphism of the descent datum of the inductive step of Stacks Project,
Tag 04DZ.** Let `f : X ⟶ Y` be a universal homeomorphism, let `w : W ⟶ Y`, `p : U ⟶ X` and
`q : V ⟶ W` be étale, and let `e` identify the base change of `V` along `X ×_Y W ⟶ W` with
`U ×_X (X ×_Y W)` over `X ×_Y W`. Then there is a morphism `V ×_Y W ⟶ W ×_Y V` of schemes over
`W ×_Y W`.

This is the gluing morphism of the descent datum for `V` relative to `w : W ⟶ Y` which the
source descends; the two displayed equations say exactly that it lies over `W ×_Y W`. -/
theorem exists_gluing_hom_of_isoBaseChange {X Y W U V : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] (w : W ⟶ Y) [Etale w] (p : U ⟶ X) [Etale p] (q : V ⟶ W) [Etale q]
    (e : pullback q (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd q (pullback.snd f w)) :
    ∃ b : pullback (q ≫ w) w ⟶ pullback w (q ≫ w),
      b ≫ pullback.fst w (q ≫ w) = pullback.fst (q ≫ w) w ≫ q ∧
      b ≫ pullback.snd w (q ≫ w) ≫ q = pullback.snd (q ≫ w) w := by
  have hfsurj : Surjective f :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp inferInstance).2.2
  -- the two cartesian squares over which everything is computed
  have hM : IsPullback (pullback.snd f w) (pullback.fst f w) w f :=
    (IsPullback.of_hasPullback f w).flip
  have hA : IsPullback (pullback.fst p (pullback.fst f w))
      (pullback.snd p (pullback.fst f w)) p (pullback.fst f w) := IsPullback.of_hasPullback _ _
  have hVX := IsPullback.of_bot' (IsPullback.of_hasPullback (q ≫ w) f) hM
  -- `V ×_Y X ≅ U ×_X (X ×_Y W)`
  set Φ : pullback (q ≫ w) f ≅ pullback p (pullback.fst f w) := hVX.isoPullback ≪≫ e with hΦ
  have hΦsnd : Φ.hom ≫ pullback.snd p (pullback.fst f w) =
      hVX.isoPullback.hom ≫ pullback.snd q (pullback.snd f w) := by
    rw [hΦ, Iso.trans_hom, Category.assoc, he]
  have hQ1 : Φ.hom ≫ pullback.snd p (pullback.fst f w) ≫ pullback.fst f w =
      pullback.snd (q ≫ w) f := by
    rw [← Category.assoc, hΦsnd, hVX.isoPullback_hom_snd]
    exact hM.lift_snd _ _ _
  have hQ2 : Φ.hom ≫ pullback.snd p (pullback.fst f w) ≫ pullback.snd f w =
      pullback.fst (q ≫ w) f ≫ q := by
    rw [← Category.assoc, hΦsnd, hVX.isoPullback_hom_snd]
    exact hM.lift_fst _ _ _
  have hR1 : Φ.inv ≫ pullback.fst (q ≫ w) f ≫ q =
      pullback.snd p (pullback.fst f w) ≫ pullback.snd f w := by
    rw [← hQ2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  -- the two schemes étale over `Y` between which the gluing morphism goes
  set v₁ : pullback (q ≫ w) w ⟶ Y := pullback.snd (q ≫ w) w ≫ w with hv₁
  set v₂ : pullback w (q ≫ w) ⟶ Y := pullback.fst w (q ≫ w) ≫ w with hv₂
  have _ : Etale v₁ := by rw [hv₁]; infer_instance
  have _ : Etale v₂ := by rw [hv₂]; infer_instance
  have _ : Surjective (pullback.fst v₁ f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback v₁ f).flip hfsurj
  -- the universal point of `(V ×_Y W) ×_Y X`
  have hwx : (pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w) ≫ w = pullback.snd v₁ f ≫ f := by
    rw [Category.assoc, ← hv₁]
    exact pullback.condition
  have hvx : (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ (q ≫ w) =
      pullback.snd v₁ f ≫ f := by
    rwa [Category.assoc, pullback.condition, ← Category.assoc]
  -- the point of `U ×_X (X ×_Y W)` with the `W`-coordinate replaced
  have huu : (pullback.lift (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w)
          (pullback.snd v₁ f) hvx ≫ Φ.hom ≫ pullback.fst p (pullback.fst f w)) ≫ p =
      hM.lift (pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w) (pullback.snd v₁ f) hwx ≫
        pullback.fst f w :=
    calc (pullback.lift (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) (pullback.snd v₁ f) hvx
            ≫ Φ.hom ≫ pullback.fst p (pullback.fst f w)) ≫ p
        = pullback.lift (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) (pullback.snd v₁ f) hvx ≫
            (Φ.hom ≫ pullback.snd p (pullback.fst f w) ≫ pullback.fst f w) := by
          simp only [Category.assoc]
          rw [hA.w]
      _ = pullback.snd v₁ f := by rw [hQ1, pullback.lift_snd]
      _ = hM.lift (pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w) (pullback.snd v₁ f) hwx ≫
            pullback.fst f w := (hM.lift_snd _ _ _).symm
  -- the action of the second point of `W` on the point of `V`
  have hact : (hA.lift _ _ huu ≫ Φ.inv ≫ pullback.fst (q ≫ w) f) ≫ q =
      pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w :=
    calc (hA.lift _ _ huu ≫ Φ.inv ≫ pullback.fst (q ≫ w) f) ≫ q
        = hA.lift _ _ huu ≫ (pullback.snd p (pullback.fst f w) ≫ pullback.snd f w) := by
          simp only [Category.assoc]
          rw [hR1]
      _ = pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w := by
          rw [← Category.assoc, hA.lift_snd, hM.lift_fst]
  have hin : ((pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q) ≫ w =
      (hA.lift _ _ huu ≫ Φ.inv ≫ pullback.fst (q ≫ w) f) ≫ (q ≫ w) :=
    calc ((pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q) ≫ w
        = (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ (q ≫ w) := Category.assoc _ _ _
      _ = pullback.snd v₁ f ≫ f := hvx
      _ = ((hA.lift _ _ huu ≫ Φ.inv ≫ pullback.fst (q ≫ w) f) ≫ q) ≫ w := by
          rw [hact, hwx]
      _ = (hA.lift _ _ huu ≫ Φ.inv ≫ pullback.fst (q ≫ w) f) ≫ (q ≫ w) := Category.assoc _ _ _
  have hout : pullback.lift ((pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q)
        (hA.lift _ _ huu ≫ Φ.inv ≫ pullback.fst (q ≫ w) f) hin ≫ v₂ =
      pullback.snd v₁ f ≫ f := by
    rwa [hv₂, ← Category.assoc, pullback.lift_fst, Category.assoc]
  set α : pullback v₁ f ⟶ pullback v₂ f :=
    pullback.lift (pullback.lift ((pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q)
      (hA.lift _ _ huu ≫ Φ.inv ≫ pullback.fst (q ≫ w) f) hin) (pullback.snd v₁ f) hout with hα
  have hαsnd : α ≫ pullback.snd v₂ f = pullback.snd v₁ f := by
    rw [hα, pullback.lift_snd]
  -- full faithfulness of base change along `f` removes the auxiliary point of `X`
  obtain ⟨b, hb₁, hb₂⟩ :=
    exists_hom_of_pullbackHom_of_universalHomeomorphism f v₁ v₂ α hαsnd
  -- a morphism into `W` is determined after base change along `f`, since `w` is étale
  have key : ∀ (y : pullback w (q ≫ w) ⟶ W) (z : pullback (q ≫ w) w ⟶ W),
      y ≫ w = v₂ → z ≫ w = v₁ → pullback.fst v₁ f ≫ b ≫ y = pullback.fst v₁ f ≫ z → b ≫ y = z :=
    fun y z hy hz h => _root_.AlgebraicGeometry.eq_of_comp_eq_of_surjective_of_etale w
      (pullback.fst v₁ f) _ _ (by rw [Category.assoc, hy, hb₁, hz]) h
  refine ⟨b, key _ _ hv₂.symm (by rw [hv₁, Category.assoc, ← pullback.condition]) ?_,
    key _ _ (by rw [hv₂, Category.assoc, ← pullback.condition]) hv₁.symm ?_⟩
  · calc pullback.fst v₁ f ≫ b ≫ pullback.fst w (q ≫ w)
        = (α ≫ pullback.fst v₂ f) ≫ pullback.fst w (q ≫ w) := by
          rw [← Category.assoc, hb₂]
      _ = (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q := by
          rw [hα, pullback.lift_fst, pullback.lift_fst]
      _ = pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w ≫ q := Category.assoc _ _ _
  · calc pullback.fst v₁ f ≫ b ≫ pullback.snd w (q ≫ w) ≫ q
        = ((α ≫ pullback.fst v₂ f) ≫ pullback.snd w (q ≫ w)) ≫ q := by
          simp only [← Category.assoc]
          rw [hb₂]
      _ = (hA.lift _ _ huu ≫ Φ.inv ≫ pullback.fst (q ≫ w) f) ≫ q := by
          rw [hα, pullback.lift_fst, pullback.lift_snd]
      _ = pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w := hact

end Stacks.Etale

end

end
