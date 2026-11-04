module

public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeEffectiveDescent

/-! # Every fibred category over a site has a stackification

Let `(𝒞, J)` be a site and let `q : 𝒴 ⥤ 𝒞` be a fibred category. There are a stack
`q' : 𝒴' ⥤ 𝒞` over `(𝒞, J)` and a 1-morphism of fibred categories over `𝒞` `G : 𝒴 ⥤ 𝒴'` such that

1. for every object `U` of `𝒞` and all objects `x`, `y` of the fibre `𝒴_U`, the induced map of
   presheaves `Mor(x, y) ⟶ Mor(G x, G y)` on `𝒞/U` identifies the target with the sheafification
   of the source, i.e. is locally injective and locally surjective, and
2. for every object `U` of `𝒞` and every object `x'` of the fibre `𝒴'_U` there is a covering
   sieve of `U` along each of whose arrows `f : V ⟶ U` the restriction `x'|_V` lies in the
   essential image of the functor `𝒴_V ⥤ 𝒴'_V` induced by `G`.

The witness is `q' = CategoryTheory.Functor.stageThreeProj q J` and
`G = CategoryTheory.Functor.toStageThree q J`. That the pair is unique up to unique
2-isomorphism is `CategoryTheory.Functor.Stackification.restrict_isEquivalence`.

## Main results

* `CategoryTheory.Functor.isStackification_toStageThree`: the two clauses, and that the target is
  a stack, for the explicit witness.
* `CategoryTheory.Functor.exists_isStackification`: the existence of a stackification.

## Implementation notes

The explicit form `isStackification_toStageThree` produces the hypotheses `q'.IsStack J`, `hmor`
and `hobj` in the unfolded shape that results about a given stackification take, which the
existential statement cannot supply.

The base hom universe is independent of the hom universe of the total category, so a site with
smaller hom types can be used after raising the morphisms of the fibred category with `ULiftHom`.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe w t₁ t₂ vb

section Stackification

variable {𝒞 : Type t₁} [Category.{vb} 𝒞] {𝒴 : Type t₂} [Category.{max t₁ t₂ w vb} 𝒴]
  (q : 𝒴 ⥤ 𝒞) [q.IsFibered] (J : GrothendieckTopology 𝒞)

/-- The fibred category `q' = stageThreeProj q J` is a stack over `(𝒞, J)`, and the 1-morphism
`G = toStageThree q J : 𝒴 ⥤ StageThree q J` of fibred categories over `𝒞` induces locally
injective and locally surjective maps of morphism presheaves, and every object of a fibre of
`StageThree q J` is, along a covering sieve of the base, in the essential image of the induced
functor on fibres. -/
theorem isStackification_toStageThree :
    (q.stageThreeProj J).IsStack J ∧
      (∀ (U : 𝒞) (x y : q.Fiber U),
          Presheaf.IsLocallyInjective (J.over U)
              ((isFibredOneMorphism_toStageThree q J).morPresheafMap x y) ∧
            Presheaf.IsLocallySurjective (J.over U)
              ((isFibredOneMorphism_toStageThree q J).morPresheafMap x y)) ∧
        ∀ (U : 𝒞) (x' : (q.stageThreeProj J).Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄,
          R.arrows f →
            (fiberFunctorOfCompEq (isFibredOneMorphism_toStageThree q J).comp_eq V).essImage
              (pullbackFiber (q.stageThreeProj J) x' f) :=
  ⟨isStack_stageThreeProj q J,
    fun U x y ↦ isLocallyBijective_morPresheafMap_toStageThree q J U x y,
    fun U x' ↦ essImage_pullbackFiber_toStageThree q J U x'⟩

/-- Let `(𝒞, J)` be a site and let `q : 𝒴 ⥤ 𝒞` be a fibred category. There exist
a stack `q' : 𝒴' ⥤ 𝒞` over `(𝒞, J)` and a 1-morphism `G : 𝒴 ⥤ 𝒴'` of fibred categories over `𝒞`
such that

1. for every `U` and all `x`, `y` in the fibre `𝒴_U` the map `Mor(x, y) ⟶ Mor(G x, G y)` of
   presheaves on `𝒞/U` exhibits its target as the sheafification of its source, and
2. every object of a fibre of `𝒴'` is, along a covering sieve of the base, in the essential image
   of the functor induced by `G` on fibres.

The objects and morphisms of `𝒴'` live in `Type (max t₁ t₂ w vb)`, the morphism universe of
`𝒴`. -/
@[stacks 02ZN]
theorem exists_isStackification :
    ∃ (𝒴' : Type (max t₁ t₂ w vb)) (inst : Category.{max t₁ t₂ w vb} 𝒴'),
      letI := inst
      ∃ (q' : 𝒴' ⥤ 𝒞) (instq : q'.IsFibered),
        letI := instq
        ∃ (G : 𝒴 ⥤ 𝒴') (hG : q.IsFibredOneMorphism q' G),
          q'.IsStack J ∧
            (∀ (U : 𝒞) (x y : q.Fiber U),
                Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y) ∧
                  Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y)) ∧
              ∀ (U : 𝒞) (x' : q'.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
                (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber q' x' f) :=
  ⟨q.StageThree J, inferInstance, q.stageThreeProj J, inferInstance, q.toStageThree J,
    isFibredOneMorphism_toStageThree q J, isStackification_toStageThree q J⟩

end Stackification

end CategoryTheory.Functor
