module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFppfFamilyEffective
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.EffectiveCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineGluingIso
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent

/-!
# Descending the scheme over `W` of the inductive step of Stacks 04DZ

Let `f : X ⟶ Y` be a universal homeomorphism, let `w : W ⟶ Y` be étale and surjective with `W`
affine, let `p : U ⟶ X` be étale, let `q : V ⟶ W` be étale with `V` affine, and let the base
change of `V` along `X ×_Y W ⟶ W` be identified with `U ×_X (X ×_Y W)` over `X ×_Y W`. This file
descends `V` along `w`.

The gluing isomorphism of `Stacks.Etale.exists_gluing_iso_of_isoBaseChange` satisfies the cocycle
condition, because on generalized points it is the action
`Stacks.Etale.gluingAct` and acting twice is acting once; a test scheme carrying no point of `X`
is handled by pulling back along the surjection from one that does. So the isomorphism is the
gluing isomorphism of a descent datum for `V` relative to `w`, and that datum is effective by
effectivity of affine descent along an fppf covering, Stacks Project, Tag 0245: `V ⟶ W` is an
affine morphism and `w` is surjective, flat and locally of finite presentation.

What comes out is a scheme `V₀` over `Y`, étale by fppf descent of étaleness, with an
isomorphism `W ×_Y V₀ ≅ V` over `W` which is equivariant: the action carries the point
`(v₀, w₁)` of `W ×_Y V₀` to `(v₀, w₂)`. That equivariance is the input the final comparison
`V₀ ×_Y X ≅ U` consumes.

## Main results

* `Stacks.Etale.exists_etale_descent_of_isoBaseChange` — the statement above.

## Implementation notes

The cocycle condition is stated in the form
`AlgebraicGeometry.DescentDatum.ActPullbackLaw`, which
`AlgebraicGeometry.DescentDatum.ofPullbackIso` consumes, and the action it refers to is
`AlgebraicGeometry.DescentDatum.actPullback`; that is
`CategoryTheory.Limits.pullback.lift` followed by the gluing isomorphism and a projection, so it
agrees with the third clause of `Stacks.Etale.exists_gluing_iso_of_isoBaseChange` on the nose.

Equivariance is read off the isomorphism of descent data by
`AlgebraicGeometry.DescentData.hom_comm_gluingPullbackIso`, which states it on the literal
fibre products. The canonical datum's action is computed by
`AlgebraicGeometry.DescentData.canonicalFunctor_gluingPullbackIso_hom_snd_projection` — it
preserves the coordinate in `V₀` — together with
`AlgebraicGeometry.DescentData.gluingPullbackIso_hom_snd_structureMap`, which gives the
coordinate in `W`; the two coordinates determine a point by
`AlgebraicGeometry.DescentData.canonical_hom_ext`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

/-- **The gluing isomorphism of the inductive step of Stacks Project, Tag 04DZ satisfies the
cocycle condition.** Let `f : X ⟶ Y` be a universal homeomorphism, let `w : W ⟶ Y` and
`p : U ⟶ X` and `q : V ⟶ W` be étale, and let `e` identify the base change of `V` along
`X ×_Y W ⟶ W` with `U ×_X (X ×_Y W)` over `X ×_Y W`. Then the gluing isomorphism of
`Stacks.Etale.exists_gluing_iso_of_isoBaseChange` satisfies the cocycle condition in the form
`AlgebraicGeometry.DescentDatum.ActPullbackLaw`.

A test scheme carrying no point of `X` is handled by pulling back along the surjection from one
that does, which is legitimate because `V` is étale over `W`. -/
theorem exists_gluing_iso_actPullbackLaw_of_isoBaseChange {X Y W U V : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] (w : W ⟶ Y) [Etale w] (p : U ⟶ X) [Etale p] (q : V ⟶ W) [Etale q]
    (e : pullback q (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd q (pullback.snd f w)) :
    ∃ i : pullback (q ≫ w) w ≅ pullback w (q ≫ w),
      i.hom ≫ pullback.fst w (q ≫ w) = pullback.fst (q ≫ w) w ≫ q ∧
      i.hom ≫ pullback.snd w (q ≫ w) ≫ q = pullback.snd (q ≫ w) w ∧
      DescentDatum.ActPullbackLaw (f := w) (Over.mk q) i.hom ∧
      ∀ {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (w₂ : Z ⟶ W)
        (h₁ : v ≫ q ≫ w = x ≫ f) (h₂ : x ≫ f = w₂ ≫ w),
        pullback.lift v w₂ (h₁.trans h₂) ≫ i.hom ≫ pullback.snd w (q ≫ w) =
          gluingAct f w p q e he v x w₂ h₁ h₂ := by
  obtain ⟨i, hi₁, hi₂, hact⟩ := exists_gluing_iso_of_isoBaseChange f w p q e he
  have hactP : ∀ {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (w₂ : Z ⟶ W)
      (h₁ : v ≫ q ≫ w = x ≫ f) (h₂ : x ≫ f = w₂ ≫ w) (h : v ≫ q ≫ w = w₂ ≫ w),
      DescentDatum.actPullback (f := w) (Over.mk q) i.hom v w₂ h =
        gluingAct f w p q e he v x w₂ h₁ h₂ := fun v x w₂ h₁ h₂ _ ↦ hact v x w₂ h₁ h₂
  have hcoc : DescentDatum.ActPullbackLaw (f := w) (Over.mk q) i.hom := by
    intro Z v x y hv₀ hxy hvx
    have hv : v ≫ q ≫ w = x ≫ w := hv₀
    have hsurj : Surjective f :=
      ((universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp
        inferInstance).2.2
    have _ : Surjective (pullback.fst (v ≫ q ≫ w) f) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
        (IsPullback.of_hasPullback (v ≫ q ≫ w) f).flip hsurj
    have hkf : pullback.fst (v ≫ q ≫ w) f ≫ v ≫ q ≫ w =
        pullback.snd (v ≫ q ≫ w) f ≫ f := pullback.condition
    have ha₁ : (pullback.fst (v ≫ q ≫ w) f ≫ v) ≫ q ≫ w =
        pullback.snd (v ≫ q ≫ w) f ≫ f := (Category.assoc _ _ _).trans hkf
    have ha₂ : pullback.snd (v ≫ q ≫ w) f ≫ f =
        (pullback.fst (v ≫ q ≫ w) f ≫ x) ≫ w := by
      rw [← hkf, Category.assoc, hv]
    have ha₃ : pullback.snd (v ≫ q ≫ w) f ≫ f =
        (pullback.fst (v ≫ q ≫ w) f ≫ y) ≫ w := by
      rw [← hkf, Category.assoc, hv, hxy]
    have hg₁ := gluingAct_comp_proj_comp f w p q e he _ _ _ ha₁ ha₂
    refine _root_.AlgebraicGeometry.eq_of_comp_eq_of_surjective_of_etale q
      (pullback.fst (v ≫ q ≫ w) f) _ _ ?_ ?_
    · exact (DescentDatum.actPullback_comp_hom (f := w) (Over.mk q) i.hom hi₂ _ y hvx).trans
        (DescentDatum.actPullback_comp_hom (f := w) (Over.mk q) i.hom hi₂ v y
          (hv₀.trans hxy)).symm
    refine DescentDatum.comp_actPullback_act_act (Over.mk q) i.hom _ v x y hv₀ hxy hvx
      (ha₁.trans ha₂) (ha₂.symm.trans ha₃) (DescentDatum.actPullback_comp_hom_comp (Over.mk q)
        i.hom hi₂ _ _ _ (ha₁.trans ha₂) (ha₂.symm.trans ha₃)) ?_
    rw [DescentDatum.actPullback_congr (Over.mk q) i.hom (hactP _ _ _ ha₁ ha₂ (ha₁.trans ha₂))
      rfl _ (hg₁.trans ha₃), hactP _ _ _ hg₁ ha₃ (hg₁.trans ha₃),
      gluingAct_gluingAct f w p q e he _ _ _ _ ha₁ ha₂ ha₃ hg₁, hactP _ _ _ ha₁ ha₃]
  exact ⟨i, hi₁, hi₂, hcoc, hact⟩

/-- **The action of the canonical descent datum of a scheme over `Y`, on generalized points.**
The canonical descent datum of `A₀ : Over Y` relative to `w : W ⟶ Y` has underlying scheme
`A₀ ×_Y W`, and its gluing isomorphism replaces the coordinate in `W` while preserving the
coordinate in `A₀`. -/
theorem actPullback_canonicalFunctor_eq {Y W : Scheme.{u}} (w : W ⟶ Y) (A₀ : Over Y)
    {Z : Scheme.{u}} (v₀ : Z ⟶ A₀.left) (w₁ x₂ : Z ⟶ W) (h₁ : v₀ ≫ A₀.hom = w₁ ≫ w)
    (h₂ : w₁ ≫ w = x₂ ≫ w)
    (hc : (pullback.lift v₀ w₁ h₁ ≫ (DescentData.canonicalObjIso w A₀).inv.left) ≫
      (((DescentData.canonicalFunctor w).obj A₀).obj ()).hom ≫ w = x₂ ≫ w) :
    DescentDatum.actPullback (f := w) (((DescentData.canonicalFunctor w).obj A₀).obj ())
        (((DescentData.canonicalFunctor w).obj A₀).gluingPullbackIso () ()).hom
        (pullback.lift v₀ w₁ h₁ ≫ (DescentData.canonicalObjIso w A₀).inv.left) x₂ hc =
      pullback.lift v₀ x₂ (h₁.trans h₂) ≫ (DescentData.canonicalObjIso w A₀).inv.left := by
  have hKstr : (DescentData.canonicalObjIso w A₀).inv.left ≫
      (((DescentData.canonicalFunctor w).obj A₀).obj ()).hom = pullback.snd A₀.hom w := by
    simpa only [Over.pullback_obj_hom] using Over.w (DescentData.canonicalObjIso w A₀).inv
  have hKK : (DescentData.canonicalObjIso w A₀).inv.left ≫
      (DescentData.canonicalObjIso w A₀).hom.left = 𝟙 _ := by
    simpa only [Over.comp_left, Over.id_left] using
      congrArg Over.Hom.left (DescentData.canonicalObjIso w A₀).inv_hom_id
  have hKproj : (DescentData.canonicalObjIso w A₀).inv.left ≫
      DescentData.canonicalProjection w A₀ = pullback.fst A₀.hom w := by
    rw [DescentData.canonicalProjection, ← Category.assoc, hKK, Category.id_comp]
  refine DescentData.canonical_hom_ext w A₀ ?_ ?_
  · rw [DescentDatum.actPullback, Category.assoc, Category.assoc,
      DescentData.canonicalFunctor_gluingPullbackIso_hom_snd_projection w A₀,
      ← Category.assoc, pullback.lift_fst, Category.assoc, hKproj, pullback.lift_fst,
      Category.assoc, hKproj, pullback.lift_fst]
  · rw [DescentDatum.actPullback_comp_hom _ _ (DescentData.gluingPullbackIso_hom_snd_structureMap
      w ((DescentData.canonicalFunctor w).obj A₀)), Category.assoc, hKstr, pullback.lift_snd]

/-- A morphism is étale if its base change along a surjective, flat, locally finitely presented
morphism is étale. -/
private theorem etale_of_etale_pullback_snd {A W Y : Scheme.{u}} (g : A ⟶ Y) (w : W ⟶ Y)
    [Surjective w] [Flat w] [LocallyOfFinitePresentation w] [Etale (pullback.snd g w)] :
    Etale g := by
  have : MorphismProperty.DescendsAlong (@Etale.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
  have hw : (@Surjective.{u} ⊓ @Flat ⊓ @LocallyOfFinitePresentation :
      MorphismProperty Scheme.{u}) w := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.DescendsAlong.of_isPullback (IsPullback.of_hasPullback g w).flip hw
    inferInstance

/-- **The descent of the scheme over `W` produced by the split of the inductive step of Stacks
Project, Tag 04DZ.** Let `f : X ⟶ Y` be a universal homeomorphism, let `w : W ⟶ Y` be étale and
surjective with `W` affine, let `p : U ⟶ X` be étale, let `q : V ⟶ W` be étale with `V` affine,
and let `e` identify the base change of `V` along `X ×_Y W ⟶ W` with `U ×_X (X ×_Y W)` over
`X ×_Y W`. Then there are a scheme `V₀` étale over `Y` and an isomorphism `V₀ ×_Y W ≅ V` over
`W` under which the gluing action replaces the coordinate in `W`. -/
theorem exists_etale_descent_of_isoBaseChange {X Y W U V : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] (w : W ⟶ Y) [Etale w] [Surjective w] [IsAffine W] (p : U ⟶ X)
    [Etale p] (q : V ⟶ W) [Etale q] [IsAffine V]
    (e : pullback q (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd q (pullback.snd f w)) :
    ∃ (V₀ : Scheme.{u}) (q₀ : V₀ ⟶ Y) (_ : Etale q₀) (Ψ : pullback q₀ w ≅ V),
      Ψ.hom ≫ q = pullback.snd q₀ w ∧
      ∀ {Z : Scheme.{u}} (v₀ : Z ⟶ V₀) (w₁ x₂ : Z ⟶ W) (x : Z ⟶ X)
        (h₁ : v₀ ≫ q₀ = w₁ ≫ w) (hx : x ≫ f = w₁ ≫ w) (h₂ : x ≫ f = x₂ ≫ w)
        (hg : (pullback.lift v₀ w₁ h₁ ≫ Ψ.hom) ≫ q ≫ w = x ≫ f),
        gluingAct f w p q e he (pullback.lift v₀ w₁ h₁ ≫ Ψ.hom) x x₂ hg h₂ =
          pullback.lift v₀ x₂ (h₁.trans (hx.symm.trans h₂)) ≫ Ψ.hom := by
  obtain ⟨i, hi₁, hi₂, hcoc, hact⟩ :=
    exists_gluing_iso_actPullbackLaw_of_isoBaseChange f w p q e he
  obtain ⟨A₀, ⟨ξ⟩⟩ : DescentData.IsEffective
      (DescentDatum.ofPullbackIso (f := w) (Over.mk q) i hi₁ hi₂ hcoc) :=
    DescentDatum.isEffective_of_isAffineHom_of_locallyOfFinitePresentation _
      (_root_.AlgebraicGeometry.isAffineHom_of_isAffine q)
  have hcomm := DescentData.hom_comm_gluingPullbackIso w ξ.hom
  rw [DescentDatum.ofPullbackIso_gluingPullbackIso_hom] at hcomm
  set cS := (((DescentData.canonicalFunctor w).obj A₀).obj ()).hom with hcS
  set ψ₁ : (((DescentData.canonicalFunctor w).obj A₀).obj ()).left ⟶ V :=
    (ξ.hom.hom ()).left with hψ₁
  set CGl : pullback (cS ≫ w) w ⟶ pullback w (cS ≫ w) :=
    (((DescentData.canonicalFunctor w).obj A₀).gluingPullbackIso () ()).hom with hCGl
  set K' : pullback A₀.hom w ⟶ (((DescentData.canonicalFunctor w).obj A₀).obj ()).left :=
    (DescentData.canonicalObjIso w A₀).inv.left with hK'
  have hψq : ψ₁ ≫ q = cS := Over.w (ξ.hom.hom ())
  have hKstr : K' ≫ cS = pullback.snd A₀.hom w :=
    Over.w (DescentData.canonicalObjIso w A₀).inv
  -- the comparison isomorphism `A₀ ×_Y W ≅ V`
  set ΨO : (Over.pullback w).obj A₀ ≅ Over.mk q :=
    (DescentData.canonicalObjIso w A₀).symm ≪≫
      (DescentData.evaluation (f := fun _ : Unit ↦ w) ()).mapIso ξ with hΨO
  set Ψ : pullback A₀.hom w ≅ V := (Over.forget W).mapIso ΨO with hΨdef
  have hΨhom : Ψ.hom = K' ≫ ψ₁ := rfl
  have hΨq : Ψ.hom ≫ q = pullback.snd A₀.hom w := Over.w ΨO.hom
  -- the descended morphism is étale, by fppf descent of étaleness
  have hsnd : Etale (pullback.snd A₀.hom w) := by
    rw [← hΨq]
    infer_instance
  refine ⟨A₀.left, A₀.hom, etale_of_etale_pullback_snd A₀.hom w, Ψ, hΨq, ?_⟩
  intro Z v₀ w₁ x₂ x h₁ hx h₂ hg
  have hw₁₂ : w₁ ≫ w = x₂ ≫ w := hx.symm.trans h₂
  have hKw₁ : (pullback.lift v₀ w₁ h₁ ≫ K') ≫ cS = w₁ := by
    rw [Category.assoc, hKstr, pullback.lift_snd]
  have hc : (pullback.lift v₀ w₁ h₁ ≫ K') ≫ cS ≫ w = x₂ ≫ w := by
    rwa [← Category.assoc, hKw₁]
  have hm₂ : w ≫ 𝟙 Y = 𝟙 W ≫ w := by rw [Category.comp_id, Category.id_comp]
  have hm₁ : (cS ≫ w) ≫ 𝟙 Y = ψ₁ ≫ q ≫ w := by
    rw [Category.comp_id, ← hψq, Category.assoc]
  have hcomm₂ : pullback.map (cS ≫ w) w (q ≫ w) w ψ₁ (𝟙 W) (𝟙 Y) hm₁ hm₂ ≫ i.hom =
      CGl ≫ pullback.map w (cS ≫ w) w (q ≫ w) (𝟙 W) ψ₁ (𝟙 Y) hm₂ hm₁ := hcomm
  have hmap₂ : pullback.map w (cS ≫ w) w (q ≫ w) (𝟙 W) ψ₁ (𝟙 Y) hm₂ hm₁ ≫
      pullback.snd w (q ≫ w) = pullback.snd w (cS ≫ w) ≫ ψ₁ := pullback.lift_snd _ _ _
  have hLeq : pullback.lift (pullback.lift v₀ w₁ h₁ ≫ Ψ.hom) x₂ (hg.trans h₂) =
      pullback.lift (pullback.lift v₀ w₁ h₁ ≫ K') x₂ hc ≫
        pullback.map (cS ≫ w) w (q ≫ w) w ψ₁ (𝟙 W) (𝟙 Y) hm₁ hm₂ := by
    refine pullback.hom_ext ?_ ?_
    · simp only [pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id, hΨhom]
      refine Eq.trans ?_ (Category.assoc _ _ _)
      exact (congrArg (fun m ↦ m ≫ ψ₁)
        (pullback.lift_fst (pullback.lift v₀ w₁ h₁ ≫ K') x₂ hc)).symm
    · simp only [pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id, hΨhom]
  have hactC : DescentDatum.actPullback (f := w) (((DescentData.canonicalFunctor w).obj A₀).obj ())
      (((DescentData.canonicalFunctor w).obj A₀).gluingPullbackIso () ()).hom
      (pullback.lift v₀ w₁ h₁ ≫ K') x₂ hc =
      pullback.lift (pullback.lift v₀ w₁ h₁ ≫ K') x₂ hc ≫ CGl ≫
        pullback.snd w (cS ≫ w) := rfl
  have hcan := actPullback_canonicalFunctor_eq w A₀ v₀ w₁ x₂ h₁ hw₁₂ hc
  calc gluingAct f w p q e he (pullback.lift v₀ w₁ h₁ ≫ Ψ.hom) x x₂ hg h₂
      = pullback.lift (pullback.lift v₀ w₁ h₁ ≫ Ψ.hom) x₂ (hg.trans h₂) ≫ i.hom ≫
          pullback.snd w (q ≫ w) := (hact _ x x₂ hg h₂).symm
    _ = pullback.lift (pullback.lift v₀ w₁ h₁ ≫ K') x₂ hc ≫
          (pullback.map (cS ≫ w) w (q ≫ w) w ψ₁ (𝟙 W) (𝟙 Y) hm₁ hm₂ ≫ i.hom) ≫
            pullback.snd w (q ≫ w) := by
        rw [hLeq]
        simp only [Category.assoc]
    _ = pullback.lift (pullback.lift v₀ w₁ h₁ ≫ K') x₂ hc ≫ CGl ≫
          pullback.snd w (cS ≫ w) ≫ ψ₁ := by
        rw [hcomm₂]
        simp only [Category.assoc]
        rw [hmap₂]
    _ = DescentDatum.actPullback (f := w)
          (((DescentData.canonicalFunctor w).obj A₀).obj ())
          (((DescentData.canonicalFunctor w).obj A₀).gluingPullbackIso () ()).hom
          (pullback.lift v₀ w₁ h₁ ≫ K') x₂ hc ≫ ψ₁ := by
        rw [hactC]
        simp only [Category.assoc]
    _ = (pullback.lift v₀ x₂ (h₁.trans hw₁₂) ≫ K') ≫ ψ₁ :=
        congrArg (· ≫ ψ₁) hcan
    _ = pullback.lift v₀ x₂ (h₁.trans (hx.symm.trans h₂)) ≫ Ψ.hom := by
        rw [hΨhom, Category.assoc]

end Stacks.Etale

end

end
