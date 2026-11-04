module

public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutChartTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceSections
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The base change of an atlas along a point, on the big fppf site

Let `𝒵` be a category fibred in groupoids over the big fppf site of `S`, `f₀ : U₀ ⟶ 𝒵` a
1-morphism out of the category represented by a scheme `U₀`, and `w` an object of `𝒵` over `A`.
The 2-fibre product of the point `A ⟶ 𝒵` named by `w` with `f₀` is
`AlgebraicGeometry.Stack.ThickeningPushout.chartSquare`. When `f₀` is representable by algebraic
spaces, its apex is represented by an algebraic space `V`
(`AlgebraicGeometry.Stack.ThickeningPushout.exists_chartSpace`); the sections of `V` are then the
triples of `StacksFrontier/AlgebraicGeometry/Stacks/ThickeningPushoutChartTriples.lean`, and the two
projections of the 2-fibre product induce on representing presheaves the maps `V ⟶ h_A` and
`V ⟶ h_{U₀}` reading off the two morphisms of a triple
(`AlgebraicGeometry.Stack.ThickeningPushout.chartFst_app_tripSection`,
`AlgebraicGeometry.Stack.ThickeningPushout.chartSnd_app_tripSection`). This is the algebraic
space `Y ×_𝒵 W` of the proof of Stacks 07WN.

## References

* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.Stack.ThickeningPushout

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  {U₀ : BigFppfOver B S hS} (f₀ : schemeFibredCategory B S hS U₀ ⟶ 𝒵)

/-- The point of `𝒵` named by an object `w` over `A`: the 2-Yoneda 1-morphism `A ⟶ 𝒵`. -/
noncomputable def pointHom {A : BigFppfOver B S hS} (w : 𝒵.val.p.Fiber A) :
    schemeFibredCategory B S hS A ⟶ 𝒵 :=
  Bicategory.InducedBicategory.mkHom
    (TwoYoneda.liftBased 𝒵.val.p 𝒵.isFiberedInGroupoids A w)

/-- The 2-fibre product of the point named by `w` with `f₀`. -/
noncomputable abbrev chartSquare {A : BigFppfOver B S hS} (w : 𝒵.val.p.Fiber A) :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} (pointHom 𝒵 w) f₀

/-- **The base change of an atlas along a point is an algebraic space.** -/
theorem exists_chartSpace (hf₀ : IsRepresentableByAlgebraicSpaces B S hS f₀.hom)
    {A : BigFppfOver B S hS} (w : 𝒵.val.p.Fiber A) :
    ∃ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS F ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver (chartSquare 𝒵 f₀ w).pt.val.p
        (presheafOfCategories (F ⋙ typeToCat)).p) :=
  isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
    (schemeFibredCategory B S hS U₀) 𝒵 (schemeFibredCategory B S hS A) f₀ (pointHom 𝒵 w)
    (chartSquare 𝒵 f₀ w)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _) hf₀
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS A)

variable {𝒵 f₀} {A : BigFppfOver B S hS} {w : 𝒵.val.p.Fiber A}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (e : StacksRepresentableCFG.EquivalenceOver (chartSquare 𝒵 f₀ w).pt.val.p
    (presheafOfCategories (F ⋙ typeToCat)).p)

/-- The first projection, on representing presheaves. -/
noncomputable abbrev chartFst : F ⟶ yoneda.obj A :=
  representingMap B S hS (chartSquare 𝒵 f₀ w).pt (schemeFibredCategory B S hS A) F (yoneda.obj A)
    e (PresheafOfCategories.sliceElementsEquivalenceOver A) (chartSquare 𝒵 f₀ w).fst

/-- The second projection, on representing presheaves. -/
noncomputable abbrev chartSnd : F ⟶ yoneda.obj U₀ :=
  representingMap B S hS (chartSquare 𝒵 f₀ w).pt (schemeFibredCategory B S hS U₀) F
    (yoneda.obj U₀) e (PresheafOfCategories.sliceElementsEquivalenceOver U₀)
    (chartSquare 𝒵 f₀ w).snd

/-- The first projection reads off the first morphism of a triple. -/
lemma chartFst_app_tripSection {T : BigFppfOver B S hS}
    (τ : Trip 𝒵.val.p f₀.hom.toFunctor (TwoYoneda.liftFunctor 𝒵.val.p 𝒵.isFiberedInGroupoids A w)
      T) :
    (chartFst e).app (op T) (tripSection e τ) = τ.1 :=
  morphismSpaceEquiv_app_sectionOfObj B S hS _ _ F (yoneda.obj A) e _ _ τ.obj rfl

/-- The second projection reads off the second morphism of a triple. -/
lemma chartSnd_app_tripSection {T : BigFppfOver B S hS}
    (τ : Trip 𝒵.val.p f₀.hom.toFunctor (TwoYoneda.liftFunctor 𝒵.val.p 𝒵.isFiberedInGroupoids A w)
      T) :
    (chartSnd e).app (op T) (tripSection e τ) = τ.2.1 :=
  morphismSpaceEquiv_app_sectionOfObj B S hS _ _ F (yoneda.obj U₀) e _ _ τ.obj rfl

/-! ### The atlas of an algebraic stack -/

/-- **The presentation of an algebraic stack, unpacked.** An algebraic stack `𝒵` has a 1-morphism
`f₀` out of the category represented by a scheme, representable by algebraic spaces, surjective
and smooth in the sense of Stacks 03YK. -/
theorem exists_atlas_of_isAlgebraicStack.{w'} (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h𝒵 : IsAlgebraicStack.{u, w'} B S hS 𝒵) :
    ∃ (U₀ : BigFppfOver B S hS)
      (f₀ : schemeFibredCategory B S hS U₀ ⟶ CatFiberedInGroupoids.mk 𝒵 (Classical.choose h𝒵))
      (hf₀ : IsRepresentableByAlgebraicSpaces B S hS f₀.hom),
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS) f₀ hf₀ ∧
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
        f₀ hf₀ := by
  obtain ⟨-, -, U, pres, hrep, hprop⟩ := Classical.choose_spec h𝒵
  exact ⟨U, Bicategory.InducedBicategory.mkHom pres, hrep,
    fun V y hy G hG he => (hprop V y hy G hG he).2,
    fun V y hy G hG he => (hprop V y hy G hG he).1⟩

/-- **The base change of a smooth surjective atlas along a point is smooth and surjective.** -/
theorem chartFst_smooth_surjective (hf₀ : IsRepresentableByAlgebraicSpaces B S hS f₀.hom)
    (hsm : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS) f₀
      hf₀)
    (hsu : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      f₀ hf₀)
    {A : BigFppfOver B S hS} (w : 𝒵.val.p.Fiber A) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver (chartSquare 𝒵 f₀ w).pt.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Space.IsSmooth B S hS (chartFst e) ∧ Space.IsSurjective B S hS (chartFst e) :=
  ⟨prop_representingMap_of_hasRelativeProperty B S hS (Space.smoothMorphismProperty B S hS) f₀
      hf₀ hsm (schemeFibredCategory B S hS A) (pointHom 𝒵 w) (chartSquare 𝒵 f₀ w)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      F (yoneda.obj A) hF (isAlgebraicSpace_yoneda B S hS A) e
      (PresheafOfCategories.sliceElementsEquivalenceOver A),
    prop_representingMap_of_hasRelativeProperty B S hS (Space.surjectiveMorphismProperty B S hS)
      f₀ hf₀ hsu (schemeFibredCategory B S hS A) (pointHom 𝒵 w) (chartSquare 𝒵 f₀ w)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      F (yoneda.obj A) hF (isAlgebraicSpace_yoneda B S hS A) e
      (PresheafOfCategories.sliceElementsEquivalenceOver A)⟩

/-- **An étale chart of the base change of the atlas, read as a triple.** An étale surjective
scheme chart `a : V₁ ⟶ V` of the algebraic space representing the base change of `f₀` along the
point `w` names a triple `(t, s, γ)` over `V₁`; its first morphism `t : V₁ ⟶ A` is the composite
of `a` with `V ⟶ A`, hence smooth and surjective when `f₀` is. -/
theorem exists_chartTriple (hf₀ : IsRepresentableByAlgebraicSpaces B S hS f₀.hom)
    (hsm : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS) f₀
      hf₀)
    (hsu : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      f₀ hf₀)
    {A : BigFppfOver B S hS} (w : 𝒵.val.p.Fiber A) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver (chartSquare 𝒵 f₀ w).pt.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    ∃ (V₁ : BigFppfOver B S hS) (a : yoneda.obj V₁ ⟶ F)
      (τ : Trip 𝒵.val.p f₀.hom.toFunctor
        (TwoYoneda.liftFunctor 𝒵.val.p 𝒵.isFiberedInGroupoids A w) V₁),
      Space.IsEtale B S hS a ∧ a.app (op V₁) (𝟙 V₁) = tripSection e τ ∧
      yoneda.map τ.1 = a ≫ chartFst e ∧
      Smooth ((BigFppfOver.toScheme B S hS).map τ.1) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map τ.1) := by
  obtain ⟨hsmF, hsuF⟩ := chartFst_smooth_surjective hf₀ hsm hsu w hF e
  obtain ⟨V₁, a, hasurj, haetale⟩ := hF.exists_atlas
  have hae : Space.IsEtale B S hS a := (Space.isEtale_iff_presheaf_of_yoneda B S hS a).2 haetale
  obtain ⟨τ, hτ⟩ := tripSection_surjective e V₁ (a.app (op V₁) (𝟙 V₁))
  have hmap : yoneda.map τ.1 = a ≫ chartFst e := yonedaEquiv.injective <| by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_apply, ← hτ]
    exact (chartFst_app_tripSection e τ).symm
  refine ⟨V₁, a, τ, hae, hτ.symm, hmap, ?_, ?_⟩
  · refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Smooth.isEtaleLocalOnSourceAndTarget τ.1).1 ?_
    rw [hmap]
    exact Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS V₁) hF
      (isAlgebraicSpace_yoneda B S hS A) a _ (Space.isSmooth_of_isEtale B S hS hF hae) hsmF
  · refine (Space.presheaf_yoneda_map_iff B S hS
      (inferInstance : MorphismProperty.IsStableUnderBaseChange
        (@Surjective.{u} : MorphismProperty Scheme.{u})) τ.1).1 ?_
    refine (Space.surjective_yonedaMap_iff_surjective_pointsMap B S hS _).2 ?_
    rw [hmap]
    exact Space.isSurjective_comp B S hS
      ((Space.surjective_iff_surjective_pointsMap B S hS F hF V₁ a).1 hasurj) hsuF

end AlgebraicGeometry.Stack.ThickeningPushout

end
