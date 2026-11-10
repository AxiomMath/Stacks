module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CartesianSquareDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification

/-!
# Quotients of relations cartesian over a presentation

Let `U` be an algebraic space over `S` with a surjective étale atlas `a : V ⟶ U` and kernel pair
`s, t : R ⇉ V`, and let `p : M ⟶ V` be an étale morphism of objects of the site. A pair
`f₁, f₂ : Q ⇉ M` together with `k : Q ⟶ R` such that both squares

```
Q --f₁--> M        Q --f₂--> M
|         |        |         |
k         p        k         p
v         v        v         v
R --s---> V        R --t---> V
```

are cartesian is a descent datum for `M` relative to the atlas, once the normalisation and
cocycle conditions hold. Then `f₁, f₂` is an étale equivalence relation on `M`, its quotient `W`
is an algebraic space, and `W ⟶ U` is an étale morphism along which the atlas pulls back to
`M ⟶ W`: the descent datum is effective. This is the effectivity of étale descent for algebraic
spaces étale over `U`, in the form in which a descent datum arises from an étale presentation.

## Main results

* `AlgebraicGeometry.Space.equivalenceRelationOfIsPullback`: a kernel pair is an internal
  equivalence relation.
* `AlgebraicGeometry.Space.exists_quotient_of_isPullback_relation`: the quotient of a relation
  cartesian over a presentation, with its étale morphism to `U` and the cartesian square.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 07VZ](https://stacks.math.columbia.edu/tag/07VZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u v w

namespace AlgebraicGeometry.Space

/-- **A kernel pair is an internal equivalence relation.** -/
noncomputable def equivalenceRelationOfIsPullback {C : Type v} [Category.{w} C] [HasPullbacks C]
    {R U F : C} {s t : R ⟶ U} {f : U ⟶ F} (h : IsPullback s t f f) :
    EquivalenceRelation s t where
  right_cancellation _ a b h₁ h₂ := h.hom_ext h₁ h₂
  r := h.lift (𝟙 U) (𝟙 U) rfl
  reflexivity₁ := h.lift_fst _ _ _
  reflexivity₂ := h.lift_snd _ _ _
  s := h.lift t s h.w.symm
  symmetry₁ := h.lift_fst _ _ _
  symmetry₂ := h.lift_snd _ _ _
  c := pullback.cone t s
  isLimit := pullback.isLimit t s
  t := h.lift (pullback.fst t s ≫ s) (pullback.snd t s ≫ t) (by
    simp only [Category.assoc, h.w]
    rw [← Category.assoc, pullback.condition, Category.assoc, h.w])
  transitivity₁ := h.lift_fst _ _ _
  transitivity₂ := h.lift_snd _ _ _

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The quotient of a relation cartesian over a presentation.** Let `a : V ⟶ U` be a surjective
étale atlas of an algebraic space with kernel pair `s, t : R ⇉ V`, let `p : M ⟶ V` be étale, and
let `f₁, f₂ : Q ⇉ M` lie over `s, t` along `k : Q ⟶ R` with both squares cartesian. If the
normalisation and cocycle conditions hold, then `f₁, f₂` presents an algebraic space `W` with a
surjective étale atlas `q : M ⟶ W` whose kernel pair is `f₁, f₂`, and an étale morphism
`w : W ⟶ U` along which `a` pulls back to `q`. -/
theorem exists_quotient_of_isPullback_relation
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    {V R M Q : BigFppfOver B S hS} {a : yoneda.obj V ⟶ U}
    (ha_et : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    {s t : R ⟶ V} (hR : IsPullback (yoneda.map s) (yoneda.map t) a a)
    {p : M ⟶ V} (hp : Etale ((BigFppfOver.toScheme B S hS).map p))
    {k : Q ⟶ R} {f₁ f₂ : Q ⟶ M}
    (h₁ : IsPullback (yoneda.map f₁) (yoneda.map k) (yoneda.map p) (yoneda.map s))
    (h₂ : IsPullback (yoneda.map f₂) (yoneda.map k) (yoneda.map p) (yoneda.map t))
    (hr : ∃ ρ : M ⟶ Q, ρ ≫ f₁ = 𝟙 M ∧ ρ ≫ f₂ = 𝟙 M)
    (hs : ∃ σ : Q ⟶ Q, σ ≫ f₁ = f₂ ∧ σ ≫ f₂ = f₁)
    (ht : ∃ τ : pullback f₂ f₁ ⟶ Q,
      τ ≫ f₁ = pullback.fst f₂ f₁ ≫ f₁ ∧ τ ≫ f₂ = pullback.snd f₂ f₁ ≫ f₂) :
    ∃ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q : yoneda.obj M ⟶ W) (w : W ⟶ U),
      IsAlgebraicSpace B S hS W ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      IsPullback (yoneda.map f₁) (yoneda.map f₂) q q ∧
      IsPullback q (yoneda.map p) w a ∧ IsEtale B S hS w := by
  classical
  have hf₁_et := (presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance f₁).mp
    (presheaf_of_isPullback B S hS h₁.flip (presheaf_of_isPullback B S hS hR.flip ha_et))
  have hf₂_et := (presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance f₂).mp
    (presheaf_of_isPullback B S hS h₂.flip (presheaf_of_isPullback B S hS hR ha_et))
  have hP := (IsPullback.of_hasPullback f₂ f₁).map yoneda
  have hrel : IsEquivalenceRelation (yoneda.map f₁) (yoneda.map f₂) := by
    obtain ⟨ρ, hρ₁, hρ₂⟩ := hr
    obtain ⟨σ, hσ₁, hσ₂⟩ := hs
    obtain ⟨τ, hτ₁, hτ₂⟩ := ht
    refine Stacks.Descent.isEquivalenceRelation_of_isPullback
      (equivalenceRelationOfIsPullback hR) h₁ h₂ hP.cone hP.isLimit
      ⟨yoneda.map ρ, by rw [← CategoryTheory.Functor.map_comp, hρ₁, CategoryTheory.Functor.map_id],
        by rw [← CategoryTheory.Functor.map_comp, hρ₂, CategoryTheory.Functor.map_id]⟩
      ⟨yoneda.map σ, by rw [← CategoryTheory.Functor.map_comp, hσ₁],
        by rw [← CategoryTheory.Functor.map_comp, hσ₂]⟩
      ⟨yoneda.map τ,
        (show yoneda.map τ ≫ yoneda.map f₁ = yoneda.map (pullback.fst f₂ f₁) ≫ yoneda.map f₁ by
          simpa using congrArg yoneda.map hτ₁),
        (show yoneda.map τ ≫ yoneda.map f₂ = yoneda.map (pullback.snd f₂ f₁) ≫ yoneda.map f₂ by
          simpa using congrArg yoneda.map hτ₂)⟩
  have hEER : IsEtaleEquivalenceRelation (relation B S hS f₂ f₁) :=
    isEtaleEquivalenceRelation_of_yoneda B S hS f₂ f₁ (Iso.refl _)
      (by simpa using hrel) hf₁_et hf₂_et
  let W := (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS f₂ f₁)).obj
  have hW : IsAlgebraicSpace B S hS W := isAlgebraicSpace_quotient_unconditional B S hS f₂ f₁
  let q := quotientMap B S hS f₂ f₁
  have hq_surj := quotientMap_surjective_unconditional B S hS f₂ f₁
  have hq_et := quotientMap_etale_unconditional B S hS f₂ f₁
  have hker : IsPullback (yoneda.map f₁) (yoneda.map f₂) q q := quotientMap_isPullback B S hS f₂ f₁
  have hk : yoneda.map f₁ ≫ (yoneda.map p ≫ a) = yoneda.map f₂ ≫ (yoneda.map p ≫ a) := by
    rw [← Category.assoc, ← Category.assoc, h₁.w, h₂.w, Category.assoc, Category.assoc, hR.w]
  obtain ⟨w, hw, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS hW.isSheaf q hker
    hq_surj hq_et hU.isSheaf (yoneda.map p ≫ a) hk
  have houter : IsPullback (yoneda.map f₁ ≫ yoneda.map p) (yoneda.map f₂) a (q ≫ w) := by
    rw [hw, h₁.w]
    exact h₂.flip.paste_horiz hR
  have hcart : IsPullback (yoneda.map p) q a w :=
    isPullback_right_of_isPullback_of_surjective_etale B S hS
      (isAlgebraicSpace_yoneda B S hS Q) (isAlgebraicSpace_yoneda B S hS M)
      (isAlgebraicSpace_yoneda B S hS M) hW (isAlgebraicSpace_yoneda B S hS V) hU hw.symm
      hker houter (isSurjective_of_presheafSurjective B S hS _ hq_surj)
      ((isEtale_iff_presheaf_of_yoneda B S hS q).mpr hq_et)
  exact ⟨W, q, w, hW, hq_surj, hq_et, hker, hcart.flip,
    (isEtale_iff_holdsOnEveryEtaleChart B S hS hW hU w).mpr
      ((holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _ etale_isEtaleLocalOnSourceAndTarget
        hW hU w).mpr ⟨M, V, q, a, p, hq_et, ha_et, hq_surj, hw.symm, hp⟩)⟩

end AlgebraicGeometry.Space

end
