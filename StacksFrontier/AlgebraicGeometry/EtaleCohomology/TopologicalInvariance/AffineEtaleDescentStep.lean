module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentHomEtaleSurjection
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineEtaleDescentDatum
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineInductiveStep
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The descent step of the second proof of Stacks 04DZ

This file proves `Stacks.Etale.EtaleDescentAlongAffineEtaleSurjection`, the one statement to
which `StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineInductiveStep`
reduced the affine case of Stacks Project, Tag 04E0, and so proves that affine case,
`Stacks.Etale.EssSurjAffineEtalePullback`, outright.

The scheme `V₀` étale over `Y` is produced by
`Stacks.Etale.exists_etale_descent_of_isoBaseChange`, together with an identification
`V₀ ×_Y W ≅ V` over `W` which is equivariant for the gluing action. What is left is the
comparison `V₀ ×_Y X ≅ U` over `X`, which the source leaves as a chain of isomorphisms to be
descended.

That comparison is a morphism of schemes étale over `X`, and `X ×_Y W ⟶ X` is a surjective étale
covering of `X`; so both it and its inverse descend from that covering, by
`AlgebraicGeometry.exists_hom_of_pullbackFst_comp_eq_of_etale_surjective`. Over the covering the
comparison is read off the gluing action: a point of `V₀ ×_Y X` together with a point of `W` over
the same point of `Y` names a point of `V₀ ×_Y W`, hence by the identification a point of `V`,
hence by `e` a point of `U`. The compatibility that the descent asks for is exactly that this
point of `U` does not depend on the chosen point of `W`, and that is what equivariance gives: two
points of `W` over one point of `Y` are related by the action, and the action does not change the
point of `U`.

## Main results

* `Stacks.Etale.uCoord_lift_eq_of_gluingEquivariant` — the point of `U` named by a point of `V₀`
  does not depend on the auxiliary point of `W`.
* `Stacks.Etale.vCoord_comp_inv_eq_of_gluingEquivariant` — the point of `V₀` named by a point of
  `U` does not depend on the auxiliary point of `W`.
* `Stacks.Etale.etaleDescentAlongAffineEtaleSurjection` —
  `Stacks.Etale.EtaleDescentAlongAffineEtaleSurjection`.
* `Stacks.Etale.isEquivalence_etalePullback_of_integral_universallyInjective_surjective` —
  **Stacks Project, Tag 04DZ**: base change along an integral, universally injective and
  surjective morphism is an equivalence of small étale sites.

## Implementation notes

The two comparison morphisms are descended separately and shown to be mutually inverse by
`AlgebraicGeometry.eq_of_comp_eq_of_surjective_of_etale`: both composites are morphisms over `X`
into the source of an étale morphism, so it is enough to check them after restriction to the
covering, where the two round trips of `Stacks.Etale.uCoord_vCoord` and
`Stacks.Etale.vCoord_uCoord` compute them.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04E0](https://stacks.math.columbia.edu/tag/04E0)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

variable {X Y W U V V₀ : Scheme.{u}} (f : X ⟶ Y) (w : W ⟶ Y) (p : U ⟶ X) (q : V ⟶ W)
  (q₀ : V₀ ⟶ Y) (e : pullback q (pullback.snd f w) ≅ pullback p (pullback.fst f w))
  (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd q (pullback.snd f w))
  (Ψ : pullback q₀ w ≅ V) (hΨq : Ψ.hom ≫ q = pullback.snd q₀ w)
  (hequiv : ∀ {Z : Scheme.{u}} (v₀ : Z ⟶ V₀) (w₁ x₂ : Z ⟶ W) (x : Z ⟶ X)
    (h₁ : v₀ ≫ q₀ = w₁ ≫ w) (hx : x ≫ f = w₁ ≫ w) (h₂ : x ≫ f = x₂ ≫ w)
    (hg : (pullback.lift v₀ w₁ h₁ ≫ Ψ.hom) ≫ q ≫ w = x ≫ f),
    gluingAct f w p q e he (pullback.lift v₀ w₁ h₁ ≫ Ψ.hom) x x₂ hg h₂ =
      pullback.lift v₀ x₂ (h₁.trans (hx.symm.trans h₂)) ≫ Ψ.hom)

include hΨq in
/-- The point of `V₀` beneath a point of `V` lies over the point of `W` beneath it. -/
theorem comp_inv_fst_comp_proj {Z : Scheme.{u}} (vv : Z ⟶ V) (w₁ : Z ⟶ W)
    (hq₁ : vv ≫ q = w₁) : (vv ≫ Ψ.inv ≫ pullback.fst q₀ w) ≫ q₀ = w₁ ≫ w := by
  subst hq₁
  simp only [Category.assoc, pullback.condition, ← hΨq, Iso.inv_hom_id_assoc]

include hΨq in
/-- **A point of `V` is the point named by its coordinate in `V₀` and the point of `W` beneath
it.** -/
theorem lift_comp_hom_eq {Z : Scheme.{u}} (vv : Z ⟶ V) (w₁ : Z ⟶ W) (hq₁ : vv ≫ q = w₁)
    (hv₀ : (vv ≫ Ψ.inv ≫ pullback.fst q₀ w) ≫ q₀ = w₁ ≫ w) :
    pullback.lift (vv ≫ Ψ.inv ≫ pullback.fst q₀ w) w₁ hv₀ ≫ Ψ.hom = vv := by
  have hΨinv : Ψ.inv ≫ pullback.snd q₀ w = q := by rw [← hΨq, Iso.inv_hom_id_assoc]
  have hfact : pullback.lift (vv ≫ Ψ.inv ≫ pullback.fst q₀ w) w₁ hv₀ = vv ≫ Ψ.inv := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]
      simp only [Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, hΨinv, hq₁]
  rw [hfact, Category.assoc, Iso.inv_hom_id, Category.comp_id]

include he hequiv in
/-- **The point of `U` named by a point of `V₀` and an auxiliary point of `X` does not depend on
the auxiliary point of `W`.** This is the compatibility that the descent of the comparison
morphism `V₀ ×_Y X ⟶ U` along the covering `X ×_Y W ⟶ X` asks for. -/
theorem uCoord_lift_eq_of_gluingEquivariant {Z : Scheme.{u}} (v₀ : Z ⟶ V₀) (w₁ w₂ : Z ⟶ W)
    (x : Z ⟶ X) (h₁ : v₀ ≫ q₀ = w₁ ≫ w) (h₂ : v₀ ≫ q₀ = w₂ ≫ w) (hx : x ≫ f = w₁ ≫ w)
    (hg₁ : (pullback.lift v₀ w₁ h₁ ≫ Ψ.hom) ≫ q ≫ w = x ≫ f)
    (hg₂ : (pullback.lift v₀ w₂ h₂ ≫ Ψ.hom) ≫ q ≫ w = x ≫ f) :
    uCoord f w p q e (pullback.lift v₀ w₂ h₂ ≫ Ψ.hom) x hg₂ =
      uCoord f w p q e (pullback.lift v₀ w₁ h₁ ≫ Ψ.hom) x hg₁ := by
  have hxw₂ : x ≫ f = w₂ ≫ w := hx.trans (h₁.symm.trans h₂)
  have hga : gluingAct f w p q e he (pullback.lift v₀ w₁ h₁ ≫ Ψ.hom) x w₂ hg₁ hxw₂ ≫ q ≫ w =
      x ≫ f := gluingAct_comp_proj_comp f w p q e he _ _ _ hg₁ hxw₂
  exact (uCoord_congr f w p q e (hequiv v₀ w₁ w₂ x h₁ hx hxw₂ hg₁).symm rfl hg₂ hga).trans
    (uCoord_gluingAct f w p q e he _ x w₂ hg₁ hxw₂ hga)

include he hΨq hequiv in
/-- **The point of `V₀` named by a point of `U` and the point of `X` beneath it does not depend
on the auxiliary point of `W`.** This is the compatibility that the descent of the comparison
morphism `U ⟶ V₀ ×_Y X` along the covering `X ×_Y W ⟶ X` asks for. -/
theorem vCoord_comp_inv_eq_of_gluingEquivariant {Z : Scheme.{u}} (uu : Z ⟶ U) (x : Z ⟶ X)
    (w₁ w₂ : Z ⟶ W) (hx₁ : x ≫ f = w₁ ≫ w) (hx₂ : x ≫ f = w₂ ≫ w) (hu : uu ≫ p = x) :
    vCoord f w p q e uu x w₂ hx₂ hu ≫ Ψ.inv ≫ pullback.fst q₀ w =
      vCoord f w p q e uu x w₁ hx₁ hu ≫ Ψ.inv ≫ pullback.fst q₀ w := by
  have hq₁ : vCoord f w p q e uu x w₁ hx₁ hu ≫ q = w₁ :=
    vCoord_comp_proj f w p q e he uu x w₁ hx₁ hu
  have hv₀ : ((vCoord f w p q e uu x w₁ hx₁ hu) ≫ Ψ.inv ≫ pullback.fst q₀ w) ≫ q₀ =
      w₁ ≫ w := comp_inv_fst_comp_proj w q q₀ Ψ hΨq _ w₁ hq₁
  have hfact' : pullback.lift (vCoord f w p q e uu x w₁ hx₁ hu ≫ Ψ.inv ≫ pullback.fst q₀ w) w₁
      hv₀ ≫ Ψ.hom = vCoord f w p q e uu x w₁ hx₁ hu :=
    lift_comp_hom_eq w q q₀ Ψ hΨq _ w₁ hq₁ hv₀
  have hgx : (pullback.lift (vCoord f w p q e uu x w₁ hx₁ hu ≫ Ψ.inv ≫ pullback.fst q₀ w) w₁
      hv₀ ≫ Ψ.hom) ≫ q ≫ w = x ≫ f := by
    rw [hfact', ← Category.assoc, hq₁]
    exact hx₁.symm
  have huc : uCoord f w p q e (vCoord f w p q e uu x w₁ hx₁ hu) x
      (by rw [← Category.assoc, hq₁]; exact hx₁.symm) = uu :=
    uCoord_vCoord f w p q e he uu x w₁ hx₁ hu _
  have hact : gluingAct f w p q e he
      (pullback.lift (vCoord f w p q e uu x w₁ hx₁ hu ≫ Ψ.inv ≫ pullback.fst q₀ w) w₁ hv₀ ≫
        Ψ.hom) x w₂ hgx hx₂ = vCoord f w p q e uu x w₂ hx₂ hu := by
    rw [gluingAct]
    refine vCoord_congr f w p q e ?_ rfl rfl _ _ _ _
    exact (uCoord_congr f w p q e hfact' rfl _ _).trans huc
  have hgl := hequiv (vCoord f w p q e uu x w₁ hx₁ hu ≫ Ψ.inv ≫ pullback.fst q₀ w) w₁ w₂ x hv₀
    (hx₁) hx₂ hgx
  rw [hact] at hgl
  rw [hgl, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]

/-- **The descent step of the second proof of Stacks Project, Tag 04DZ.** -/
theorem etaleDescentAlongAffineEtaleSurjection :
    EtaleDescentAlongAffineEtaleSurjection.{u} := by
  intro X Y f _ W w hw _ hwsurj U p _ _ V q _ _ e he
  obtain ⟨V₀, q₀, hq₀, Ψ, hΨq, hequiv⟩ := exists_etale_descent_of_isoBaseChange f w p q e he
  have _ : Surjective (pullback.fst f w) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback f w).flip hwsurj
  have _ : Etale (pullback.fst f w) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
      (IsPullback.of_hasPullback f w).flip hw
  have hmcond : pullback.fst f w ≫ f = pullback.snd f w ≫ w := pullback.condition
  have hlift : ∀ {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (v₀ : Z ⟶ V₀) (w₁ : Z ⟶ W)
      (h : v₀ ≫ q₀ = w₁ ≫ w) (h' : (k ≫ v₀) ≫ q₀ = (k ≫ w₁) ≫ w),
      k ≫ pullback.lift v₀ w₁ h = pullback.lift (k ≫ v₀) (k ≫ w₁) h' := by
    intro Z Z' k v₀ w₁ h h'
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hΨqw : ∀ {Z : Scheme.{u}} (v₀ : Z ⟶ V₀) (w₁ : Z ⟶ W) (h : v₀ ≫ q₀ = w₁ ≫ w),
      (pullback.lift v₀ w₁ h ≫ Ψ.hom) ≫ q = w₁ := by
    intro Z v₀ w₁ h
    rw [Category.assoc, hΨq, pullback.lift_snd]
  set a : pullback q₀ f ⟶ X := pullback.snd q₀ f with ha
  set a₀ : pullback q₀ f ⟶ V₀ := pullback.fst q₀ f with ha₀
  have _ : Etale a := by rw [ha]; infer_instance
  have hacond : a₀ ≫ q₀ = a ≫ f := by rw [ha₀, ha]; exact pullback.condition
  -- the `V₀`-point and the `W`-point attached to a point of `A ×_X (X ×_Y W)`
  have hdata₃ : ∀ {Z : Scheme.{u}} (x : Z ⟶ X) (m : Z ⟶ pullback f w),
      x = m ≫ pullback.fst f w → x ≫ f = (m ≫ pullback.snd f w) ≫ w := by
    intro Z x m hm
    rw [hm, Category.assoc, hmcond, Category.assoc]
  have hdata : ∀ {Z : Scheme.{u}} (α : Z ⟶ pullback q₀ f) (m : Z ⟶ pullback f w),
      α ≫ a = m ≫ pullback.fst f w →
      (α ≫ a₀) ≫ q₀ = (m ≫ pullback.snd f w) ≫ w := by
    intro Z α m hm
    rw [Category.assoc, hacond, ← Category.assoc]
    exact hdata₃ _ m hm
  have hdata₂ : ∀ {Z : Scheme.{u}} (α : Z ⟶ pullback q₀ f) (m : Z ⟶ pullback f w)
      (hm : α ≫ a = m ≫ pullback.fst f w),
      (pullback.lift (α ≫ a₀) (m ≫ pullback.snd f w) (hdata α m hm) ≫ Ψ.hom) ≫ q ≫ w =
        (α ≫ a) ≫ f := by
    intro Z α m hm
    calc (pullback.lift (α ≫ a₀) (m ≫ pullback.snd f w) (hdata α m hm) ≫ Ψ.hom) ≫ q ≫ w
        = ((pullback.lift (α ≫ a₀) (m ≫ pullback.snd f w) (hdata α m hm) ≫ Ψ.hom) ≫ q) ≫ w :=
          (Category.assoc _ _ _).symm
      _ = (m ≫ pullback.snd f w) ≫ w := by rw [hΨqw]
      _ = (α ≫ a) ≫ f := (hdata₃ _ m hm).symm
  -- the comparison morphism over the covering
  set k₁ := pullback.fst a (pullback.fst f w) with hk₁
  set k₂ := pullback.snd a (pullback.fst f w) with hk₂
  have hkcond : k₁ ≫ a = k₂ ≫ pullback.fst f w := by rw [hk₁, hk₂]; exact pullback.condition
  set β := uCoord f w p q e
    (pullback.lift (k₁ ≫ a₀) (k₂ ≫ pullback.snd f w) (hdata k₁ k₂ hkcond) ≫ Ψ.hom)
    (k₁ ≫ a) (hdata₂ k₁ k₂ hkcond) with hβdef
  have hβp : β ≫ p = k₁ ≫ a :=
    uCoord_comp_proj f w p q e he _ (k₁ ≫ a) (hdata₂ k₁ k₂ hkcond)
  have hβcomp : ∀ {Z : Scheme.{u}} (z : Z ⟶ pullback a (pullback.fst f w))
      (α : Z ⟶ pullback q₀ f) (m : Z ⟶ pullback f w) (hα : z ≫ k₁ = α) (hm : z ≫ k₂ = m)
      (hc : α ≫ a = m ≫ pullback.fst f w),
      z ≫ β = uCoord f w p q e
        (pullback.lift (α ≫ a₀) (m ≫ pullback.snd f w) (hdata α m hc) ≫ Ψ.hom) (α ≫ a)
        (hdata₂ α m hc) := by
    intro Z z α m hα hm hc
    have hxa : z ≫ k₁ ≫ a₀ = α ≫ a₀ := by rw [← Category.assoc, hα]
    have hxm : z ≫ k₂ ≫ pullback.snd f w = m ≫ pullback.snd f w := by
      rw [← Category.assoc, hm]
    have hxx : z ≫ k₁ ≫ a = α ≫ a := by rw [← Category.assoc, hα]
    have h1 : z ≫ (pullback.lift (k₁ ≫ a₀) (k₂ ≫ pullback.snd f w) (hdata k₁ k₂ hkcond) ≫
        Ψ.hom) = pullback.lift (α ≫ a₀) (m ≫ pullback.snd f w) (hdata α m hc) ≫ Ψ.hom := by
      rw [← Category.assoc, hlift z (k₁ ≫ a₀) (k₂ ≫ pullback.snd f w) (hdata k₁ k₂ hkcond)
        (by rw [hxa, hxm]; exact hdata α m hc)]
      exact congrArg (fun t ↦ t ≫ Ψ.hom) (pullback.hom_ext
        (by rw [pullback.lift_fst, pullback.lift_fst, hxa])
        (by rw [pullback.lift_snd, pullback.lift_snd, hxm]))
    have hcu : (z ≫ (pullback.lift (k₁ ≫ a₀) (k₂ ≫ pullback.snd f w) (hdata k₁ k₂ hkcond) ≫
        Ψ.hom)) ≫ q ≫ w = (z ≫ (k₁ ≫ a)) ≫ f := by
      rw [h1, hxx]
      exact hdata₂ α m hc
    rw [hβdef, comp_uCoord f w p q e z _ (k₁ ≫ a) (hdata₂ k₁ k₂ hkcond) hcu]
    exact uCoord_congr f w p q e h1 hxx _ _
  have hkc : ∀ {Z : Scheme.{u}} (t : Z ⟶ pullback a (pullback.fst f w)),
      (t ≫ k₁) ≫ a = (t ≫ k₂) ≫ pullback.fst f w := by
    intro Z t
    rw [Category.assoc, Category.assoc, hkcond]
  have hcomp : pullback.fst k₁ k₁ ≫ β = pullback.snd k₁ k₁ ≫ β := by
    have hj : pullback.fst k₁ k₁ ≫ k₁ = pullback.snd k₁ k₁ ≫ k₁ := pullback.condition
    have hc₁ := hkc (pullback.fst k₁ k₁)
    have hc₂ := hkc (pullback.snd k₁ k₁)
    have hc₃ : (pullback.fst k₁ k₁ ≫ k₁) ≫ a =
        (pullback.snd k₁ k₁ ≫ k₂) ≫ pullback.fst f w := by
      rw [hj]
      exact hc₂
    rw [hβcomp (pullback.fst k₁ k₁) _ _ rfl rfl hc₁,
      hβcomp (pullback.snd k₁ k₁) _ _ rfl rfl hc₂]
    refine Eq.trans (uCoord_lift_eq_of_gluingEquivariant f w p q q₀ e he Ψ hequiv
      ((pullback.fst k₁ k₁ ≫ k₁) ≫ a₀) ((pullback.fst k₁ k₁ ≫ k₂) ≫ pullback.snd f w)
      ((pullback.snd k₁ k₁ ≫ k₂) ≫ pullback.snd f w) ((pullback.fst k₁ k₁ ≫ k₁) ≫ a)
      (hdata _ _ hc₁) (hdata _ _ hc₃) (hdata₃ _ _ hc₁) (hdata₂ _ _ hc₁)
      (hdata₂ _ _ hc₃)).symm ?_
    refine uCoord_congr f w p q e (congrArg (fun t ↦ t ≫ Ψ.hom) (pullback.hom_ext ?_ ?_)) ?_ _ _
    · rw [pullback.lift_fst, pullback.lift_fst, hj]
    · rw [pullback.lift_snd, pullback.lift_snd]
    · rw [hj]
  obtain ⟨γ, hγp, hγβ⟩ :=
    _root_.AlgebraicGeometry.exists_hom_of_pullbackFst_comp_eq_of_etale_surjective
      a p (pullback.fst f w) β hβp hcomp
  -- the comparison morphism in the other direction
  set l₁ := pullback.fst p (pullback.fst f w) with hl₁
  have hlcond : l₁ ≫ p =
      pullback.snd p (pullback.fst f w) ≫ pullback.fst f w := pullback.condition
  have hvdata : ∀ {Z : Scheme.{u}} (uu : Z ⟶ U) (m : Z ⟶ pullback f w)
      (hm : uu ≫ p = m ≫ pullback.fst f w),
      (vCoord f w p q e uu (uu ≫ p) (m ≫ pullback.snd f w) (hdata₃ _ m hm) rfl ≫ Ψ.inv ≫
        pullback.fst q₀ w) ≫ q₀ = (uu ≫ p) ≫ f := by
    intro Z uu m hm
    refine Eq.trans (comp_inv_fst_comp_proj w q q₀ Ψ hΨq _ (m ≫ pullback.snd f w)
      (vCoord_comp_proj f w p q e he uu (uu ≫ p) (m ≫ pullback.snd f w)
        (hdata₃ _ m hm) rfl)) ?_
    exact (hdata₃ _ m hm).symm
  set β' := pullback.lift
    (vCoord f w p q e (l₁)
      (l₁ ≫ p)
      (pullback.snd p (pullback.fst f w) ≫ pullback.snd f w)
      (hdata₃ _ (pullback.snd p (pullback.fst f w)) hlcond)
      rfl ≫ Ψ.inv ≫ pullback.fst q₀ w)
    (l₁ ≫ p)
    (hvdata (l₁) (pullback.snd p (pullback.fst f w)) hlcond)
    with hβ'def
  have hβ'a : β' ≫ a = l₁ ≫ p := by
    rw [hβ'def, ha]
    exact pullback.lift_snd _ _ _
  have hβ'a₀ : β' ≫ a₀ = vCoord f w p q e (l₁)
      (l₁ ≫ p)
      (pullback.snd p (pullback.fst f w) ≫ pullback.snd f w)
      (hdata₃ _ (pullback.snd p (pullback.fst f w)) hlcond)
      rfl ≫ Ψ.inv ≫ pullback.fst q₀ w := by
    rw [hβ'def, ha₀]
    exact pullback.lift_fst _ _ _
  have hβ'comp : ∀ {Z : Scheme.{u}} (z : Z ⟶ pullback p (pullback.fst f w)) (uu : Z ⟶ U)
      (m : Z ⟶ pullback f w) (hu : z ≫ l₁ = uu)
      (hm : z ≫ pullback.snd p (pullback.fst f w) = m)
      (hc : uu ≫ p = m ≫ pullback.fst f w),
      z ≫ β' ≫ a₀ = vCoord f w p q e uu (uu ≫ p) (m ≫ pullback.snd f w)
        (hdata₃ _ m hc) rfl ≫ Ψ.inv ≫ pullback.fst q₀ w := by
    intro Z z uu m hu hm hc
    have hxu : z ≫ l₁ ≫ p = uu ≫ p := by
      rw [← Category.assoc, hu]
    have hxm : z ≫ pullback.snd p (pullback.fst f w) ≫ pullback.snd f w =
        m ≫ pullback.snd f w := by rw [← Category.assoc, hm]
    rw [hβ'a₀, ← Category.assoc, comp_vCoord f w p q e z _ _ _ _ rfl
      (by rw [hxu, hxm]; exact hdata₃ _ m hc) (Category.assoc _ _ _)]
    exact congrArg (fun t ↦ t ≫ Ψ.inv ≫ pullback.fst q₀ w)
      (vCoord_congr f w p q e hu hxu hxm _ _ _ _)
  have hlc : ∀ {Z : Scheme.{u}} (t : Z ⟶ pullback p (pullback.fst f w)),
      (t ≫ l₁) ≫ p = (t ≫ pullback.snd p (pullback.fst f w)) ≫ pullback.fst f w := by
    intro Z t
    rw [Category.assoc, Category.assoc, hlcond]
  have hβ'c : pullback.fst l₁ l₁ ≫ β' = pullback.snd l₁ l₁ ≫ β' := by
    have hj : pullback.fst l₁ l₁ ≫ l₁ = pullback.snd l₁ l₁ ≫ l₁ := pullback.condition
    have hc₁ := hlc (pullback.fst l₁ l₁)
    have hc₂ := hlc (pullback.snd l₁ l₁)
    have hc₃ : (pullback.fst l₁ l₁ ≫ l₁) ≫ p =
        (pullback.snd l₁ l₁ ≫ pullback.snd p (pullback.fst f w)) ≫ pullback.fst f w := by
      rw [hj]
      exact hc₂
    refine pullback.hom_ext ?_ ?_
    · rw [← ha₀, Category.assoc, Category.assoc, hβ'comp _ _ _ rfl rfl hc₁,
        hβ'comp _ _ _ rfl rfl hc₂]
      refine Eq.trans (vCoord_comp_inv_eq_of_gluingEquivariant f w p q q₀ e he Ψ hΨq hequiv
        (pullback.fst l₁ l₁ ≫ l₁) ((pullback.fst l₁ l₁ ≫ l₁) ≫ p)
        ((pullback.fst l₁ l₁ ≫ pullback.snd p (pullback.fst f w)) ≫ pullback.snd f w)
        ((pullback.snd l₁ l₁ ≫ pullback.snd p (pullback.fst f w)) ≫ pullback.snd f w)
        (hdata₃ _ _ hc₁) (hdata₃ _ _ hc₃) rfl).symm ?_
      exact congrArg (fun t ↦ t ≫ Ψ.inv ≫ pullback.fst q₀ w)
        (vCoord_congr f w p q e hj (by rw [hj]) rfl _ _ _ _)
    · rw [← ha, Category.assoc, Category.assoc, hβ'a]
      simp only [← Category.assoc]
      rw [hj]
  obtain ⟨δ, hδa, hδβ'⟩ :=
    _root_.AlgebraicGeometry.exists_hom_of_pullbackFst_comp_eq_of_etale_surjective
      p a (pullback.fst f w) β' hβ'a hβ'c
  rw [← hl₁] at hδβ'
  -- the two composites are the identity
  have hδγ : δ ≫ γ = 𝟙 U := by
    refine _root_.AlgebraicGeometry.eq_of_comp_eq_of_surjective_of_etale p
      (l₁) _ _ ?_ ?_
    · rw [Category.assoc, hγp, hδa, Category.id_comp]
    · have hn : β' ≫ a = pullback.snd p (pullback.fst f w) ≫ pullback.fst f w :=
        hβ'a.trans hlcond
      set n := pullback.lift β' (pullback.snd p (pullback.fst f w)) hn with hndef
      have hnk₁ : n ≫ k₁ = β' := by rw [hndef, hk₁]; exact pullback.lift_fst _ _ _
      have hnk₂ : n ≫ k₂ = pullback.snd p (pullback.fst f w) := by
        rw [hndef, hk₂]; exact pullback.lift_snd _ _ _
      have hq₁ : vCoord f w p q e (l₁)
            (l₁ ≫ p)
            (pullback.snd p (pullback.fst f w) ≫ pullback.snd f w)
            (hdata₃ _
              (pullback.snd p (pullback.fst f w)) hlcond) rfl ≫ q =
          pullback.snd p (pullback.fst f w) ≫ pullback.snd f w :=
        vCoord_comp_proj f w p q e he _ _ _ _ rfl
      calc l₁ ≫ δ ≫ γ
          = n ≫ β := by rw [← Category.assoc, hδβ', ← hnk₁, Category.assoc, hγβ]
        _ = uCoord f w p q e (pullback.lift (β' ≫ a₀)
              (pullback.snd p (pullback.fst f w) ≫ pullback.snd f w)
              (hdata β' (pullback.snd p (pullback.fst f w)) hn) ≫ Ψ.hom) (β' ≫ a)
              (hdata₂ β' (pullback.snd p (pullback.fst f w)) hn) :=
            hβcomp n β' (pullback.snd p (pullback.fst f w)) hnk₁ hnk₂ hn
        _ = uCoord f w p q e (vCoord f w p q e (l₁)
              (l₁ ≫ p)
              (pullback.snd p (pullback.fst f w) ≫ pullback.snd f w)
              (hdata₃ _
                (pullback.snd p (pullback.fst f w)) hlcond) rfl)
              (l₁ ≫ p)
              (by rw [← Category.assoc, hq₁]
                  exact (hdata₃ _
                    (pullback.snd p (pullback.fst f w)) hlcond).symm) := by
            refine uCoord_congr f w p q e ?_ hβ'a _ _
            refine Eq.trans ?_ (lift_comp_hom_eq w q q₀ Ψ hΨq _ _ hq₁
              (comp_inv_fst_comp_proj w q q₀ Ψ hΨq _ _ hq₁))
            exact congrArg (fun t ↦ t ≫ Ψ.hom) (pullback.hom_ext
              ((pullback.lift_fst _ _ _).trans (hβ'a₀.trans (pullback.lift_fst _ _ _).symm))
              ((pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm))
        _ = l₁ := uCoord_vCoord f w p q e he _ _ _ _ rfl _
        _ = l₁ ≫ 𝟙 U := (Category.comp_id _).symm
  have hγδ : γ ≫ δ = 𝟙 (pullback q₀ f) := by
    refine _root_.AlgebraicGeometry.eq_of_comp_eq_of_surjective_of_etale a k₁ _ _ ?_ ?_
    · rw [Category.assoc, hδa, hγp, Category.id_comp]
    · have hm : β ≫ p = k₂ ≫ pullback.fst f w := hβp.trans hkcond
      set m := pullback.lift β k₂ hm with hmdef
      have hml₁ : m ≫ l₁ = β := by
        rw [hmdef]; exact pullback.lift_fst _ _ _
      have hml₂ : m ≫ pullback.snd p (pullback.fst f w) = k₂ := by
        rw [hmdef]; exact pullback.lift_snd _ _ _
      have hvv : vCoord f w p q e β (β ≫ p) (k₂ ≫ pullback.snd f w)
            (hdata₃ _ k₂ hm) rfl =
          pullback.lift (k₁ ≫ a₀) (k₂ ≫ pullback.snd f w) (hdata k₁ k₂ hkcond) ≫ Ψ.hom := by
        refine Eq.trans ?_ (vCoord_uCoord f w p q e he (pullback.lift (k₁ ≫ a₀)
          (k₂ ≫ pullback.snd f w) (hdata k₁ k₂ hkcond) ≫ Ψ.hom) (k₁ ≫ a)
          (hdata₂ k₁ k₂ hkcond) ?_ ?_)
        · exact vCoord_congr f w p q e hβdef hβp
            (hΨqw (k₁ ≫ a₀) (k₂ ≫ pullback.snd f w) (hdata k₁ k₂ hkcond)).symm _ _ _ _
        · rw [hΨqw]
          exact hdata₃ _ _ hkcond
        · exact uCoord_comp_proj f w p q e he _ (k₁ ≫ a) (hdata₂ k₁ k₂ hkcond)
      rw [← Category.assoc, hγβ, ← hml₁, Category.assoc, hδβ', Category.comp_id]
      refine pullback.hom_ext ?_ ?_
      · show (m ≫ β') ≫ a₀ = k₁ ≫ a₀
        rw [Category.assoc, hβ'comp m β k₂ hml₁ hml₂ hm, hvv, Category.assoc,
          Iso.hom_inv_id_assoc, pullback.lift_fst]
      · show (m ≫ β') ≫ a = k₁ ≫ a
        rw [Category.assoc, hβ'a, ← Category.assoc, hml₁, hβp]
  exact ⟨V₀, q₀, hq₀, ⟨γ, δ, hγδ, hδγ⟩, hγp⟩

/-- **Topological invariance of the small étale site, Stacks Project, Tag 04DZ.** Let
`f : X ⟶ Y` be integral, universally injective and surjective. Then `V ↦ X ×_Y V` is an
equivalence from the category of schemes étale over `Y` to the category of schemes étale over
`X`.

The reduction to the affine case,
`Stacks.Etale.exists_etale_pullback_iso_of_essSurjAffine`, is
supplied with that affine case (Stacks Project, Tag 04E0), obtained here from
`Stacks.Etale.essSurjAffineEtalePullback_of_etaleDescent` and the descent step
`Stacks.Etale.etaleDescentAlongAffineEtaleSurjection`. -/
@[stacks 04DZ "base change `V ↦ X ×_Y V` along an integral, universally injective and surjective
morphism `f : X ⟶ Y` is an equivalence `Y_étale ⥤ X_étale`: full faithfulness is Tag 0BTY, and
essential surjectivity is glued, by Schemes 01JA and 01JC, from the affine case, the induction
`Stacks.Etale.essSurjAffineEtalePullback_of_etaleDescent` of the source's second proof on a
bound for the degree of the fibres, descending at each step by Tag 0245 as
`Stacks.Etale.etaleDescentAlongAffineEtaleSurjection`.",
  ega "IV 18.1.2" "more general",
  sga "1 IX 4.10",
  sga "4 VIII 1.1" "partial"]
theorem isEquivalence_etalePullback_of_integral_universallyInjective_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ f).IsEquivalence :=
  have : UniversalHomeomorphism f :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  etalePullback_isEquivalence_of_forall_exists_pullback_iso f
    (exists_etale_pullback_iso_of_essSurjAffine
      (essSurjAffineEtalePullback_of_etaleDescent etaleDescentAlongAffineEtaleSurjection) f)

end Stacks.Etale

end

end
