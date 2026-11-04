module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineGluingAction

/-!
# The gluing isomorphism of the descent datum of the inductive step of Stacks 04DZ

Let `f : X ⟶ Y` be a universal homeomorphism, let `w : W ⟶ Y` be étale, let `p : U ⟶ X` be
étale, let `q : V ⟶ W` be étale, and suppose the base change of `V` along `X ×_Y W ⟶ W` is
identified with `U ×_X (X ×_Y W)` over `X ×_Y W`. That is the data the split of the inductive
step of the second proof of Stacks Project, Tag 04DZ produces.

The descent datum for `V` relative to `w : W ⟶ Y` which the source then descends needs a gluing
*isomorphism* `V ×_Y W ≅ W ×_Y V` over `W ×_Y W`. This file produces it, together with the
computation of its action on generalized points.

## The shape of the argument

Over `X` the gluing map is the action
`Stacks.Etale.gluingAct`: a point of `V ×_Y W` paired with a point of `X` over the same point of
`Y` is carried to the pair consisting of the point of `W` beneath the point of `V` and the result
of acting on it by the second point of `W`. Evaluated at the universal point of
`(V ×_Y W) ×_Y X`, that is a morphism `α` of `X`-schemes between the base changes along `f` of
two schemes étale over `Y`, so Stacks Project, Tag 0BTY —
`Stacks.Etale.exists_hom_of_pullbackHom_of_universalHomeomorphism` — descends it to a morphism
`V ×_Y W ⟶ W ×_Y V` over `Y`.

Interchanging the two factors produces in the same way the morphism in the other direction, and
the two composites are the identity because the corresponding composites over `X` are: that is
where the unit law `Stacks.Etale.gluingAct_self` and the composition law
`Stacks.Etale.gluingAct_gluingAct` are used, and it is why the action had to be a function of a
generalized point. The identities over `Y` follow because `V ×_Y W ⟶ Y` is étale and
`(V ×_Y W) ×_Y X ⟶ V ×_Y W` is surjective, by
`AlgebraicGeometry.eq_of_comp_eq_of_surjective_of_etale`.

## Main results

* `Stacks.Etale.exists_gluing_iso_of_isoBaseChange` — the gluing isomorphism, the two equations
  saying that it lies over `W ×_Y W`, and the identification of its action on a generalized point
  with `Stacks.Etale.gluingAct`.

## Implementation notes

The last clause is what makes the isomorphism usable: the cocycle condition of the descent datum
is a statement about the action on generalized points of a test scheme which carries no point of
`X`, and it is proved by pulling back along the surjection from a test scheme which does. The
clause is stated with `CategoryTheory.Limits.pullback.lift`, which is
`AlgebraicGeometry.DescentDatum.actPullback` unfolded, so that no `CategoryTheory.Over` datum
appears in it.

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

/-- The first projection of a pullback along a surjective morphism is surjective. -/
private theorem surjective_fst_of_surjective {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : X ⟶ Y)
    (hf : Surjective f) : Surjective (pullback.fst g f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
    (IsPullback.of_hasPullback g f).flip hf

/-- The two compatibilities over `Y` of the universal point of `(V ×_Y W) ×_Y X`. -/
private theorem comp_eq_snd_comp_of_pullback_snd_comp {X Y W V : Scheme.{u}} (f : X ⟶ Y)
    (w : W ⟶ Y) (q : V ⟶ W) :
    (pullback.fst (pullback.snd (q ≫ w) w ≫ w) f ≫ pullback.snd (q ≫ w) w) ≫ w =
        pullback.snd (pullback.snd (q ≫ w) w ≫ w) f ≫ f ∧
      (pullback.fst (pullback.snd (q ≫ w) w ≫ w) f ≫ pullback.fst (q ≫ w) w) ≫ q ≫ w =
        pullback.snd (pullback.snd (q ≫ w) w ≫ w) f ≫ f := by
  have hw : (pullback.fst (pullback.snd (q ≫ w) w ≫ w) f ≫ pullback.snd (q ≫ w) w) ≫ w =
      pullback.snd (pullback.snd (q ≫ w) w ≫ w) f ≫ f := by
    rw [Category.assoc]
    exact pullback.condition
  refine ⟨hw, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact hw

/-- **Isomorphisms descend along a universal homeomorphism.** An isomorphism over `X` between
the base changes along a universal homeomorphism `f : X ⟶ Y` of two schemes étale over `Y` is the
base change of an isomorphism over `Y`. -/
theorem exists_iso_of_pullbackIso_of_universalHomeomorphism {X Y V W : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] (v : V ⟶ Y) (w : W ⟶ Y) [Etale v] [Etale w]
    (α : pullback v f ≅ pullback w f) (hα : α.hom ≫ pullback.snd w f = pullback.snd v f) :
    ∃ b : V ≅ W, b.hom ≫ w = v ∧ pullback.fst v f ≫ b.hom = α.hom ≫ pullback.fst w f := by
  have hf : Surjective f :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp inferInstance).2.2
  have := surjective_fst_of_surjective v f hf
  have := surjective_fst_of_surjective w f hf
  obtain ⟨b, hb₁, hb₂⟩ := exists_hom_of_pullbackHom_of_universalHomeomorphism f v w α.hom hα
  obtain ⟨b', hb₁', hb₂'⟩ := exists_hom_of_pullbackHom_of_universalHomeomorphism f w v α.inv
    (by rw [Iso.inv_comp_eq, hα])
  refine ⟨⟨b, b', ?_, ?_⟩, hb₁, hb₂⟩
  · refine eq_of_comp_eq_of_surjective_of_etale v (pullback.fst v f) _ _ ?_ ?_
    · rw [Category.assoc, hb₁', hb₁, Category.id_comp]
    · rw [reassoc_of% hb₂, hb₂', α.hom_inv_id_assoc, Category.comp_id]
  · refine eq_of_comp_eq_of_surjective_of_etale w (pullback.fst w f) _ _ ?_ ?_
    · rw [Category.assoc, hb₁, hb₁', Category.id_comp]
    · rw [reassoc_of% hb₂', hb₂, α.inv_hom_id_assoc, Category.comp_id]

/-- An endomorphism of `(V ×_Y W) ×_Y X` over `X` which replaces the point of `W` by the point of
`W` beneath the point of `V`, and acts on the point of `V` by `Stacks.Etale.gluingAct`, is an
involution. -/
theorem comp_self_eq_id_of_comp_eq_gluingAct {X Y W U V : Scheme.{u}} (f : X ⟶ Y) (w : W ⟶ Y)
    (p : U ⟶ X) (q : V ⟶ W)
    (e : pullback q (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd q (pullback.snd f w)) :
    ∀ (β : pullback (pullback.snd (q ≫ w) w ≫ w) f ⟶ pullback (pullback.snd (q ≫ w) w ≫ w) f)
      (h₁ : (pullback.fst (pullback.snd (q ≫ w) w ≫ w) f ≫ pullback.fst (q ≫ w) w) ≫ q ≫ w =
        pullback.snd (pullback.snd (q ≫ w) w ≫ w) f ≫ f)
      (h₂ : pullback.snd (pullback.snd (q ≫ w) w ≫ w) f ≫ f =
        (pullback.fst (pullback.snd (q ≫ w) w ≫ w) f ≫ pullback.snd (q ≫ w) w) ≫ w),
      β ≫ pullback.snd _ f = pullback.snd _ f →
      β ≫ pullback.fst _ f ≫ pullback.snd (q ≫ w) w =
        (pullback.fst _ f ≫ pullback.fst (q ≫ w) w) ≫ q →
      β ≫ pullback.fst _ f ≫ pullback.fst (q ≫ w) w =
        gluingAct f w p q e he (pullback.fst _ f ≫ pullback.fst (q ≫ w) w) (pullback.snd _ f)
          (pullback.fst _ f ≫ pullback.snd (q ≫ w) w) h₁ h₂ →
      β ≫ β = 𝟙 _ := by
  set v₁ : pullback (q ≫ w) w ⟶ Y := pullback.snd (q ≫ w) w ≫ w
  intro β h₁ h₂ hβx hβw hβv
  have hu : pullback.snd v₁ f ≫ f = ((pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q) ≫ w :=
    ((Category.assoc _ _ _).trans h₁).symm
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
  · calc (β ≫ β) ≫ pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w
        = β ≫ gluingAct f w p q e he (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w)
            (pullback.snd v₁ f) (pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w) h₁ h₂ := by
          rw [Category.assoc, hβv]
      _ = gluingAct f w p q e he
            (gluingAct f w p q e he (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w)
              (pullback.snd v₁ f) (pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w) h₁ h₂)
            (pullback.snd v₁ f) ((pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q)
            (gluingAct_comp_proj_comp f w p q e he _ _ _ h₁ h₂) hu := by
          rw [comp_gluingAct f w p q e he β _ _ _ h₁ h₂
            (by rw [hβv, hβx]; exact gluingAct_comp_proj_comp f w p q e he _ _ _ h₁ h₂)
            (by rw [hβx, hβw]; exact hu)]
          exact gluingAct_congr f w p q e he hβv hβx hβw _ _ _ _
      _ = pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w :=
          (gluingAct_gluingAct f w p q e he _ _ _ _ h₁ h₂ hu _).trans
            (gluingAct_self f w p q e he _ _ h₁ hu)
      _ = 𝟙 _ ≫ pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w := (Category.id_comp _).symm
  · calc (β ≫ β) ≫ pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w
        = β ≫ (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q := by rw [Category.assoc, hβw]
      _ = pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w := by
          rw [← Category.assoc, hβv]
          exact gluingAct_comp_proj f w p q e he _ _ _ h₁ h₂
      _ = 𝟙 _ ≫ pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w := (Category.id_comp _).symm
  · rw [Category.assoc, hβx, hβx, Category.id_comp]

/-- **The gluing involution over `X`.** The endomorphism of `(V ×_Y W) ×_Y X` over `X` carrying a
point `(v, w₂, x)` to `(gluingAct v x w₂, v ≫ q, x)` is an involution. -/
theorem exists_involution_comp_eq_gluingAct {X Y W U V : Scheme.{u}} (f : X ⟶ Y) (w : W ⟶ Y)
    (p : U ⟶ X) (q : V ⟶ W)
    (e : pullback q (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd q (pullback.snd f w)) :
    ∃ β : pullback (pullback.snd (q ≫ w) w ≫ w) f ⟶ pullback (pullback.snd (q ≫ w) w ≫ w) f,
      β ≫ β = 𝟙 _ ∧ β ≫ pullback.snd _ f = pullback.snd _ f ∧
      β ≫ pullback.fst _ f ≫ pullback.snd (q ≫ w) w =
        (pullback.fst _ f ≫ pullback.fst (q ≫ w) w) ≫ q ∧
      ∀ h₁ h₂, β ≫ pullback.fst _ f ≫ pullback.fst (q ≫ w) w =
        gluingAct f w p q e he (pullback.fst _ f ≫ pullback.fst (q ≫ w) w) (pullback.snd _ f)
          (pullback.fst _ f ≫ pullback.snd (q ≫ w) w) h₁ h₂ := by
  set v₁ : pullback (q ≫ w) w ⟶ Y := pullback.snd (q ≫ w) w ≫ w with hv₁
  obtain ⟨hw₁, hvx₁⟩ := comp_eq_snd_comp_of_pullback_snd_comp f w q
  have hu₁ : pullback.snd v₁ f ≫ f = ((pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q) ≫ w :=
    ((Category.assoc _ _ _).trans hvx₁).symm
  set β : pullback v₁ f ⟶ pullback v₁ f := pullback.lift (pullback.lift
      (gluingAct f w p q e he (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) (pullback.snd v₁ f)
        (pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w) hvx₁ hw₁.symm)
      ((pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q)
      ((gluingAct_comp_proj_comp f w p q e he _ _ _ hvx₁ hw₁.symm).trans hu₁))
    (pullback.snd v₁ f) ((pullback.lift_snd_assoc _ _ _ w).trans hu₁.symm) with hβ
  have hβx : β ≫ pullback.snd v₁ f = pullback.snd v₁ f := by rw [hβ, pullback.lift_snd]
  have hβw : β ≫ pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w =
      (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q := by
    rw [hβ, pullback.lift_fst_assoc, pullback.lift_snd]
  have hβv : β ≫ pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w =
      gluingAct f w p q e he (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) (pullback.snd v₁ f)
        (pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w) hvx₁ hw₁.symm := by
    rw [hβ, pullback.lift_fst_assoc, pullback.lift_fst]
  exact ⟨β, comp_self_eq_id_of_comp_eq_gluingAct f w p q e he β hvx₁ hw₁.symm hβx hβw hβv, hβx,
    hβw, fun _ _ => hβv⟩

/-- A morphism `b` of `V ×_Y W` which acts by `Stacks.Etale.gluingAct` on the universal point of
`(V ×_Y W) ×_Y X` acts by `Stacks.Etale.gluingAct` on every point of `V ×_Y W` accompanied by a
point of `X` over the same point of `Y`. -/
theorem pullback_lift_comp_eq_gluingAct {X Y W U V : Scheme.{u}} (f : X ⟶ Y) (w : W ⟶ Y)
    (p : U ⟶ X) (q : V ⟶ W)
    (e : pullback q (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd q (pullback.snd f w))
    (b : pullback (q ≫ w) w ⟶ pullback (q ≫ w) w)
    (hu₁ : (pullback.fst (pullback.snd (q ≫ w) w ≫ w) f ≫ pullback.fst (q ≫ w) w) ≫ q ≫ w =
      pullback.snd (pullback.snd (q ≫ w) w ≫ w) f ≫ f)
    (hu₂ : pullback.snd (pullback.snd (q ≫ w) w ≫ w) f ≫ f =
      (pullback.fst (pullback.snd (q ≫ w) w ≫ w) f ≫ pullback.snd (q ≫ w) w) ≫ w)
    (hb : pullback.fst (pullback.snd (q ≫ w) w ≫ w) f ≫ b ≫ pullback.fst (q ≫ w) w =
      gluingAct f w p q e he (pullback.fst (pullback.snd (q ≫ w) w ≫ w) f ≫ pullback.fst (q ≫ w) w)
        (pullback.snd (pullback.snd (q ≫ w) w ≫ w) f)
        (pullback.fst (pullback.snd (q ≫ w) w ≫ w) f ≫ pullback.snd (q ≫ w) w) hu₁ hu₂)
    {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (w₂ : Z ⟶ W) (h₁ : v ≫ q ≫ w = x ≫ f)
    (h₂ : x ≫ f = w₂ ≫ w) :
    pullback.lift v w₂ (h₁.trans h₂) ≫ b ≫ pullback.fst (q ≫ w) w =
      gluingAct f w p q e he v x w₂ h₁ h₂ := by
  set v₁ : pullback (q ≫ w) w ⟶ Y := pullback.snd (q ≫ w) w ≫ w
  have hz : pullback.lift v w₂ (h₁.trans h₂) ≫ v₁ = x ≫ f :=
    (pullback.lift_snd_assoc _ _ _ w).trans h₂.symm
  have hzf : pullback.lift (pullback.lift v w₂ (h₁.trans h₂)) x hz ≫ pullback.fst v₁ f =
      pullback.lift v w₂ (h₁.trans h₂) := pullback.lift_fst _ _ _
  have hzx : pullback.lift (pullback.lift v w₂ (h₁.trans h₂)) x hz ≫ pullback.snd v₁ f = x :=
    pullback.lift_snd _ _ _
  have hzv : pullback.lift (pullback.lift v w₂ (h₁.trans h₂)) x hz ≫
      pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w = v := by
    rw [← Category.assoc, hzf, pullback.lift_fst]
  have hzw : pullback.lift (pullback.lift v w₂ (h₁.trans h₂)) x hz ≫
      pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w = w₂ := by
    rw [← Category.assoc, hzf, pullback.lift_snd]
  calc pullback.lift v w₂ (h₁.trans h₂) ≫ b ≫ pullback.fst (q ≫ w) w
      = pullback.lift (pullback.lift v w₂ (h₁.trans h₂)) x hz ≫ pullback.fst v₁ f ≫ b ≫
          pullback.fst (q ≫ w) w := by rw [reassoc_of% hzf]
    _ = pullback.lift (pullback.lift v w₂ (h₁.trans h₂)) x hz ≫
          gluingAct f w p q e he (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w)
            (pullback.snd v₁ f) (pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w) hu₁ hu₂ := by
        rw [hb]
    _ = gluingAct f w p q e he v x w₂ h₁ h₂ := by
        rw [comp_gluingAct f w p q e he _ _ _ _ hu₁ hu₂ (by rw [hzv, hzx]; exact h₁)
          (by rw [hzx, hzw]; exact h₂)]
        exact gluingAct_congr f w p q e he hzv hzx hzw _ _ _ _

/-- **The gluing isomorphism of the descent datum of the inductive step of Stacks Project,
Tag 04DZ.** Let `f : X ⟶ Y` be a universal homeomorphism, let `w : W ⟶ Y`, `p : U ⟶ X` and
`q : V ⟶ W` be étale, and let `e` identify the base change of `V` along `X ×_Y W ⟶ W` with
`U ×_X (X ×_Y W)` over `X ×_Y W`. Then there is an isomorphism `V ×_Y W ≅ W ×_Y V` of schemes
over `W ×_Y W` whose action on a generalized point is `Stacks.Etale.gluingAct`.

The two displayed equations say exactly that the isomorphism lies over `W ×_Y W`; the third
clause computes it on a point of `V ×_Y W` which is accompanied by a point of `X` over the same
point of `Y`. -/
theorem exists_gluing_iso_of_isoBaseChange {X Y W U V : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] (w : W ⟶ Y) [Etale w] (p : U ⟶ X) [Etale p] (q : V ⟶ W) [Etale q]
    (e : pullback q (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd q (pullback.snd f w)) :
    ∃ i : pullback (q ≫ w) w ≅ pullback w (q ≫ w),
      i.hom ≫ pullback.fst w (q ≫ w) = pullback.fst (q ≫ w) w ≫ q ∧
      i.hom ≫ pullback.snd w (q ≫ w) ≫ q = pullback.snd (q ≫ w) w ∧
      ∀ {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (w₂ : Z ⟶ W)
        (h₁ : v ≫ q ≫ w = x ≫ f) (h₂ : x ≫ f = w₂ ≫ w),
        pullback.lift v w₂ (h₁.trans h₂) ≫ i.hom ≫ pullback.snd w (q ≫ w) =
          gluingAct f w p q e he v x w₂ h₁ h₂ := by
  have hfsurj : Surjective f :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp inferInstance).2.2
  set v₁ : pullback (q ≫ w) w ⟶ Y := pullback.snd (q ≫ w) w ≫ w with hv₁
  have : Etale v₁ := by
    rw [hv₁]
    infer_instance
  have := surjective_fst_of_surjective v₁ f hfsurj
  obtain ⟨hw₁, hvx₁⟩ := comp_eq_snd_comp_of_pullback_snd_comp f w q
  obtain ⟨β, hββ, hβx, hβw, hβv⟩ : ∃ β : pullback v₁ f ⟶ pullback v₁ f, β ≫ β = 𝟙 _ ∧
      β ≫ pullback.snd v₁ f = pullback.snd v₁ f ∧
      β ≫ pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w =
        (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) ≫ q ∧
      β ≫ pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w =
        gluingAct f w p q e he (pullback.fst v₁ f ≫ pullback.fst (q ≫ w) w) (pullback.snd v₁ f)
          (pullback.fst v₁ f ≫ pullback.snd (q ≫ w) w) hvx₁ hw₁.symm :=
    (exists_involution_comp_eq_gluingAct f w p q e he).imp fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 _ _⟩
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b : pullback (q ≫ w) w ≅ pullback (q ≫ w) w,
      b.hom ≫ v₁ = v₁ ∧ pullback.fst v₁ f ≫ b.hom = β ≫ pullback.fst v₁ f :=
    exists_iso_of_pullbackIso_of_universalHomeomorphism f v₁ v₁ ⟨β, β, hββ, hββ⟩ hβx
  refine ⟨b ≪≫ pullbackSymmetry _ _, ?_, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
    refine eq_of_comp_eq_of_surjective_of_etale w (pullback.fst v₁ f) _ _ ?_ ?_
    · simp only [Category.assoc]
      rw [← hv₁, hb₁, hv₁]
      exact pullback.condition.symm
    · rw [reassoc_of% hb₂, hβw, Category.assoc]
  · rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd_assoc]
    refine eq_of_comp_eq_of_surjective_of_etale w (pullback.fst v₁ f) _ _ ?_ ?_
    · simp only [Category.assoc]
      rw [pullback.condition, ← hv₁, hb₁]
    · rw [reassoc_of% hb₂, reassoc_of% hβv]
      exact gluingAct_comp_proj f w p q e he _ _ _ hvx₁ hw₁.symm
  · intro Z v x w₂ h₁ h₂
    rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact pullback_lift_comp_eq_gluingAct f w p q e he b.hom hvx₁ hw₁.symm
      (((reassoc_of% hb₂) _).trans hβv) v x w₂ h₁ h₂

end Stacks.Etale

end

end
