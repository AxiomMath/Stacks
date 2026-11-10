module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# Smoothness descends along an étale surjective cover of the source

Let `S` be a scheme contained in a big fppf site `B` and consider a commutative square of
presheaves on the big fppf site of `S` with values in `Type (u + 1)`
```
X' --g'--> W'
|a         |ψ
X  --g---> W
```
with `a` surjective and étale after every represented base change, `ψ` representable by
algebraic spaces and étale, and `g`, `g'` representable by algebraic spaces. If `g'` is smooth
(Stacks 03XZ), so is `g`: over a scheme `T ⟶ W` an étale chart of `T ×_W W'`, followed by an
étale chart of its base change of `g'`, gives an étale surjective chart of `T ×_W X` which is
smooth over `T`, and smoothness is étale local on the source (Stacks 03MJ).

## Main results

* `AlgebraicGeometry.Space.hasPropertyULift_isSmoothULift_of_etale_cover`: the statement above.

## References

* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Given a commutative square `a ≫ g = g' ≫ ψ`, a map `ξ : T ⟶ W` and `y : Y ⟶ T ×_W W'`, the
pullback `Y ×_{W'} X'` maps to `(T ×_W X) ×_X X'` by a pullback of `y` over `T ×_W W'`. -/
theorem exists_isPullback_pullback_of_comm {C : Type*} [Category C] [HasPullbacks C]
    {X' X W' W T Y : C} (a : X' ⟶ X) (g : X ⟶ W) (g' : X' ⟶ W') (ψ : W' ⟶ W)
    (w : a ≫ g = g' ≫ ψ) (ξ : T ⟶ W) (y : Y ⟶ pullback ξ ψ) :
    ∃ (m : pullback (y ≫ pullback.snd ξ ψ) g' ⟶ pullback (pullback.snd ξ g) a)
      (k : pullback (pullback.snd ξ g) a ⟶ pullback ξ ψ),
      IsPullback m (pullback.fst (y ≫ pullback.snd ξ ψ) g') k y ∧
      m ≫ pullback.fst (pullback.snd ξ g) a ≫ pullback.fst ξ g =
        pullback.fst (y ≫ pullback.snd ξ ψ) g' ≫ y ≫ pullback.fst ξ ψ := by
  let p₁ := pullback.fst (pullback.snd ξ g) a
  let p₂ := pullback.snd (pullback.snd ξ g) a
  have hPa : IsPullback p₂ (p₁ ≫ pullback.fst ξ g) (g' ≫ ψ) ξ := by
    rw [← w]
    exact (IsPullback.of_hasPullback (pullback.snd ξ g) a).flip.paste_vert
      (IsPullback.of_hasPullback ξ g).flip
  let k : pullback (pullback.snd ξ g) a ⟶ pullback ξ ψ :=
    pullback.lift (p₁ ≫ pullback.fst ξ g) (p₂ ≫ g')
      (by simpa only [Category.assoc] using hPa.w.symm)
  have hk : k ≫ pullback.fst ξ ψ = p₁ ≫ pullback.fst ξ g := pullback.lift_fst _ _ _
  have hk' : k ≫ pullback.snd ξ ψ = p₂ ≫ g' := pullback.lift_snd _ _ _
  have hsq₁ : IsPullback p₂ k g' (pullback.snd ξ ψ) :=
    IsPullback.of_bot (v₂₁ := pullback.fst ξ ψ) (v₂₂ := ψ) (h₃₁ := ξ) (by rwa [hk]) hk'.symm
      (IsPullback.of_hasPullback ξ ψ).flip
  let m : pullback (y ≫ pullback.snd ξ ψ) g' ⟶ pullback (pullback.snd ξ g) a :=
    hsq₁.lift (pullback.snd _ g') (pullback.fst _ g' ≫ y) (by
      rw [Category.assoc]
      exact (pullback.condition (f := y ≫ pullback.snd ξ ψ) (g := g')).symm)
  have hmp : m ≫ p₂ = pullback.snd _ g' := hsq₁.lift_fst _ _ _
  have hmk : m ≫ k = pullback.fst _ g' ≫ y := hsq₁.lift_snd _ _ _
  refine ⟨m, k, IsPullback.of_right ?_ hmk hsq₁, ?_⟩
  · rw [hmp]
    exact (IsPullback.of_hasPullback _ g').flip
  · rw [← hk, ← Category.assoc, hmk, Category.assoc]

/-- **Smoothness descends along an étale surjective cover of the source.** In a commutative
square `a ≫ g = g' ≫ ψ` with `a` surjective and étale after every represented base change and
`ψ` representable étale, smoothness of `g'` implies smoothness of `g`. -/
theorem hasPropertyULift_isSmoothULift_of_etale_cover
    {X' X W' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (a : X' ⟶ X) (g : X ⟶ W) (g' : X' ⟶ W') (ψ : W' ⟶ W) (w : a ≫ g = g' ≫ ψ)
    (haE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) a)
    (haS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) a)
    (hg : IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g)
    (hg' : IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g')
    (hsm : HasPropertyULift.{u + 1} B S hS (fun _ _ f ↦ IsSmoothULift.{u + 1} B S hS f.hom) g' hg')
    (hψ : IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS ψ)
    (hψe : HasPropertyULift.{u + 1} B S hS (fun _ _ f ↦ IsEtaleULift.{u + 1} B S hS f.hom) ψ hψ) :
    HasPropertyULift.{u + 1} B S hS (fun _ _ f ↦ IsSmoothULift.{u + 1} B S hS f.hom) g hg := by
  classical
  intro T ξ
  let Sch := BigFppfOver.toScheme B S hS
  let Yo := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  change HoldsOnEveryEtaleChartULift.{u + 1} B S hS (@AlgebraicGeometry.Smooth.{u})
    (pullback.fst ξ g)
  -- an étale chart `Y₀` of `T ×_W W'`, étale over `T`
  obtain ⟨Y₀, y, hyS, hyE⟩ := (hψ T ξ).exists_atlas
  have hyT := hψe T ξ Y₀ y hyE
  obtain ⟨hY, hhY⟩ : ∃ hY : Y₀ ⟶ T, Yo.map hY = y ≫ pullback.fst ξ ψ :=
    ⟨Yo.preimage _, Yo.map_preimage _⟩
  have hYet : AlgebraicGeometry.Etale (Sch.map hY) :=
    (relative_etale_uliftYoneda_map_iff B S hS hY).mp (by rwa [hhY])
  -- an étale chart `X₀` of `Y₀ ×_{W'} X'`, smooth over `Y₀`
  let η : Yo.obj Y₀ ⟶ W' := y ≫ pullback.snd ξ ψ
  obtain ⟨X₀, x, hxS, hxE⟩ := (hg' Y₀ η).exists_atlas
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : X₀ ⟶ Y₀, Yo.map h₁ = x ≫ pullback.fst η g' :=
    ⟨Yo.preimage _, Yo.map_preimage _⟩
  have hh₁sm : AlgebraicGeometry.Smooth (Sch.map h₁) :=
    (hsm Y₀ η : HoldsOnEveryEtaleChartULift.{u + 1} B S hS (@AlgebraicGeometry.Smooth.{u})
      (pullback.fst η g')) X₀ Y₀ x (𝟙 _) h₁ hxE (relative_id_etale B S hS Y₀)
      (by rw [Category.comp_id, hh₁]; rfl)
  have hsm₀ : AlgebraicGeometry.Smooth (Sch.map (h₁ ≫ hY)) := by
    rw [Sch.map_comp]
    infer_instance
  obtain ⟨m₁, k, hm₁, hcomm⟩ := exists_isPullback_pullback_of_comm a g g' ψ w ξ y
  have hp₁ : IsPullback (pullback.fst (pullback.snd ξ g) a) (pullback.snd (pullback.snd ξ g) a)
    (pullback.snd ξ g) a := IsPullback.of_hasPullback _ _
  let a₀ : Yo.obj X₀ ⟶ pullback ξ g := x ≫ m₁ ≫ pullback.fst (pullback.snd ξ g) a
  have ha₀ : ∀ (Q : MorphismProperty (BigFppfOver B S hS)) [Q.IsStableUnderComposition],
      Q.relative Yo x → Q.relative Yo y → Q.relative Yo a → Q.relative Yo a₀ :=
    fun Q _ hx hy ha ↦ relative_comp B S hS hx (relative_comp B S hS
      (relative_of_isPullback B S hS hm₁ hy) (relative_of_isPullback B S hS hp₁ ha))
  have ha₀E := ha₀ _ hxE hyE haE
  have ha₀S := ha₀ _ hxS hyS haS
  have hsq : Yo.map (h₁ ≫ hY) ≫ 𝟙 _ = a₀ ≫ pullback.fst ξ g := by
    rw [Category.comp_id, Yo.map_comp, hh₁, hhY]
    change (x ≫ pullback.fst (y ≫ pullback.snd ξ ψ) g') ≫ y ≫ pullback.fst ξ ψ =
      x ≫ m₁ ≫ pullback.fst (pullback.snd ξ g) a ≫ pullback.fst ξ g
    rw [Category.assoc, hcomm]
  exact holdsOnEveryEtaleChartULift_of_surjectiveChart B S hS (@AlgebraicGeometry.Smooth.{u})
    isEtaleLocalOnSourceAndTarget_smooth (hg T ξ) (isAlgebraicSpaceULift_uliftYoneda B S hS T)
    X₀ T a₀ (𝟙 _) (h₁ ≫ hY) ha₀E (relative_id_etale B S hS T) ha₀S hsq hsm₀

end AlgebraicGeometry.Space
