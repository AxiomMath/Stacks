module

public import StacksFrontier.CategoryTheory.Sites.Stackification.Stackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.Uniqueness

/-! # Stacks 02ZN: the stackification exists and is determined up to unique 2-isomorphism

Let `(𝒞, J)` be a site and let `q : 𝒴 ⥤ 𝒞` be a fibred category. Stacks 02ZN asserts that there
are a stack `q' : 𝒴' ⥤ 𝒞` and a 1-morphism `G : 𝒴 ⥤ 𝒴'` of fibred categories over `𝒞` satisfying

1. for every `U` and all `x`, `y` in the fibre `𝒴_U` the induced map `Mor(x, y) ⟶ Mor(G x, G y)`
   of presheaves on `𝒞/U` identifies the target with the sheafification of the source, and
2. every object of a fibre of `𝒴'` is, locally on the base, in the essential image of `G` on
   fibres,

and that `𝒴'` is determined up to unique 2-isomorphism by these conditions. The existence is
`CategoryTheory.Functor.exists_isStackification`; this file adds the determinacy and assembles the
complete statement.

"Determined up to unique 2-isomorphism" is read in the 2-category of fibred categories over `𝒞`:
for every other stack `r : 𝒳 ⥤ 𝒞` with a 1-morphism `F : 𝒴 ⥤ 𝒳` satisfying (1) and (2) there are
a 1-morphism `H : 𝒴' ⥤ 𝒳` over `𝒞`, which is an equivalence over `𝒞`, and a 2-isomorphism
`α : G ⋙ H ≅ F`; and any other pair `(H', α')` of this kind is related to `(H, α)` by exactly one
2-isomorphism `β : H ≅ H'` compatible with `α` and `α'`.

## Main results

* `CategoryTheory.Functor.Stackification.exists_isEquivalenceOver_and_existsUnique_iso`: two
  stackifications of one fibred category are equivalent over `𝒞` compatibly with the two
  1-morphisms, by a comparison unique up to unique 2-isomorphism.
* `CategoryTheory.Functor.exists_isStackification_and_unique`: Stacks 02ZN, existence together
  with the determinacy up to unique 2-isomorphism.

## Implementation notes

2-morphisms are those of `CategoryTheory.Functor.FibredMor`, the morphism category
`Mor_{Fib/𝒞}` of Stacks 02ZG: natural transformations whose components lie over identities. The
comparison is the preimage of `F` under restriction along `G`, an equivalence of morphism
categories by Stacks 04W9 (`CategoryTheory.Functor.Stackification.restrict_isEquivalence`).

## References

* [Stacks 02ZN](https://stacks.math.columbia.edu/tag/02ZN).
* [Stacks 04W9](https://stacks.math.columbia.edu/tag/04W9).
-/

@[expose] public section

namespace CategoryTheory.Functor

/-! ### Determinacy up to unique 2-isomorphism -/

namespace Stackification

universe vb' v u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{vb'} 𝒞] {𝒜 : Type u₂} [Category.{v} 𝒜]
  {ℬ : Type u₃} [Category.{v} ℬ] {𝒳 : Type u₄} [Category.{v} 𝒳]
  {p : 𝒜 ⥤ 𝒞} {p' : ℬ ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} [p.IsFibered] [p'.IsFibered] [q.IsFibered]
  {G : 𝒜 ⥤ ℬ} {F : 𝒜 ⥤ 𝒳} (J : GrothendieckTopology 𝒞)

/-- **Two stackifications are equivalent, by a comparison unique up to unique 2-isomorphism.**
Let `G : 𝒜 ⥤ ℬ` and `F : 𝒜 ⥤ 𝒳` be 1-morphisms of fibred categories over `𝒞` into stacks `p'` and
`q`, both satisfying clauses (1) and (2) of Stacks 02ZN. Then there are a 1-morphism `H : ℬ ⥤ 𝒳`
of fibred categories over `𝒞` which is an equivalence of `p'` with `q` over `𝒞`, and a
2-isomorphism `α : G ⋙ H ≅ F` (an isomorphism in `Mor_{Fib/𝒞}(𝒜, 𝒳)`), such that for every
1-morphism `H'` with a 2-isomorphism `α' : G ⋙ H' ≅ F` there is exactly one 2-isomorphism
`β : H ≅ H'` whose whiskering by `G`, followed by `α'`, is `α`.

The comparison is the preimage of `F` under restriction along `G`, which is an equivalence of
morphism categories by Stacks 04W9; uniqueness of `β` is faithfulness of restriction, and `H` is
an equivalence over `𝒞` by
`CategoryTheory.Functor.Stackification.nonempty_isEquivalenceOver_of_natIso`. -/
theorem exists_isEquivalenceOver_and_existsUnique_iso (hG : p.IsFibredOneMorphism p' G)
    (hF : p.IsFibredOneMorphism q F)
    (hGmor : ∀ (U : 𝒞) (a b : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap a b))
    (hGobj : ∀ (U : 𝒞) (x : p'.Fiber U), ∃ R ∈ J U,
      ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x f))
    (hFmor : ∀ (U : 𝒞) (a b : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hF.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) (hF.morPresheafMap a b))
    (hFobj : ∀ (U : 𝒞) (x : q.Fiber U), ∃ R ∈ J U,
      ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (fiberFunctorOfCompEq hF.comp_eq V).essImage (pullbackFiber q x f))
    (hp' : p'.IsStack J) (hq : q.IsStack J) :
    ∃ H : FibredMor p' q, Nonempty (IsEquivalenceOver p' q H.functor) ∧
      ∃ α : (restrictMor hG).obj H ≅ ⟨F, hF⟩,
        ∀ (H' : FibredMor p' q) (α' : (restrictMor hG).obj H' ≅ ⟨F, hF⟩),
          ∃! β : H ≅ H', (restrictMor hG).mapIso β ≪≫ α' = α := by
  let R := restrictMor (q := q) hG
  have : R.IsEquivalence :=
    restrict_isEquivalence hG hGmor hq.isMorSheaf hGobj hq.hasEffectiveDescent
  let H : FibredMor p' q := R.objPreimage ⟨F, hF⟩
  let α : R.obj H ≅ ⟨F, hF⟩ := R.objObjPreimageIso ⟨F, hF⟩
  let e : G ⋙ H.functor ≅ F :=
    { hom := α.hom.trans
      inv := α.inv.trans
      hom_inv_id := congrArg FibredMor.Hom.trans α.hom_inv_id
      inv_hom_id := congrArg FibredMor.Hom.trans α.inv_hom_id }
  refine ⟨H, nonempty_isEquivalenceOver_of_natIso hG H.isFibredOneMorphism J hF e
    (fun a ↦ α.hom.isHomLift a) hGmor hGobj hFmor hFobj hp' hq, α, fun H' α' ↦
      ⟨R.preimageIso (α ≪≫ α'.symm), by ext; simp [R], fun β hβ ↦ ?_⟩⟩
  ext
  apply R.map_injective
  rw [← cancel_mono α'.hom]
  simpa [R] using congrArg Iso.hom hβ

end Stackification

section Stackification

universe w t₁ t₂ vb

variable {𝒞 : Type t₁} [Category.{vb} 𝒞] {𝒴 : Type t₂} [Category.{max t₁ t₂ w vb} 𝒴]
  (q : 𝒴 ⥤ 𝒞) [q.IsFibered] (J : GrothendieckTopology 𝒞)

universe u

/-- **Stacks 02ZN.** Let `(𝒞, J)` be a site and let `q : 𝒴 ⥤ 𝒞` be a fibred category. There exist
a stack `q' : 𝒴' ⥤ 𝒞` over `(𝒞, J)` and a 1-morphism `G : 𝒴 ⥤ 𝒴'` of fibred categories over `𝒞`
such that

1. for every `U` and all `x`, `y` in the fibre `𝒴_U` the map `Mor(x, y) ⟶ Mor(G x, G y)` of
   presheaves on `𝒞/U` exhibits its target as the sheafification of its source (it is locally
   injective and locally surjective), and
2. every object of a fibre of `𝒴'` is, along a covering sieve of the base, in the essential image
   of the functor induced by `G` on fibres.

Moreover `𝒴'` is determined up to unique 2-isomorphism by these conditions: for every stack
`r : 𝒳 ⥤ 𝒞` and 1-morphism `F : 𝒴 ⥤ 𝒳` of fibred categories over `𝒞` satisfying (1) and (2) there
are a 1-morphism `H : 𝒴' ⥤ 𝒳` which is an equivalence of `q'` with `r` over `𝒞` and a
2-isomorphism `α : G ⋙ H ≅ F`, and every other such pair `(H', α')` is related to `(H, α)` by
exactly one 2-isomorphism `β : H ≅ H'` with `(G ◁ β) ≫ α' = α`.

The objects and morphisms of `𝒴'` live in `Type (max t₁ t₂ w vb)`, the morphism universe of `𝒴`;
the competing stack `𝒳` may live in any universe and has the same morphism universe as `𝒴`. -/
@[stacks 02ZN "Mor(x, y) → Mor(G x, G y) identifying the target with the sheafification of the \
source is read as local injectivity and local surjectivity of the map of presheaves on 𝒞/U, a \
covering {U_i → U} as a covering sieve, and 'unique up to unique 2-isomorphism' as: a comparison \
1-morphism with a 2-isomorphism G ⋙ H ≅ F exists, is an equivalence over 𝒞, and is unique up to \
exactly one compatible 2-isomorphism"]
theorem exists_isStackification_and_unique :
    ∃ (𝒴' : Type (max t₁ t₂ w vb)) (inst : Category.{max t₁ t₂ w vb} 𝒴'),
      letI := inst
      ∃ (q' : 𝒴' ⥤ 𝒞) (instq : q'.IsFibered),
        letI := instq
        ∃ (G : 𝒴 ⥤ 𝒴') (hG : q.IsFibredOneMorphism q' G),
          q'.IsStack J ∧
            (∀ (U : 𝒞) (x y : q.Fiber U),
                Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y) ∧
                  Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y)) ∧
              (∀ (U : 𝒞) (x' : q'.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
                (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber q' x' f)) ∧
              ∀ (𝒳 : Type u) [Category.{max t₁ t₂ w vb} 𝒳] (r : 𝒳 ⥤ 𝒞) [r.IsFibered]
                (F : 𝒴 ⥤ 𝒳) (hF : q.IsFibredOneMorphism r F), r.IsStack J →
                (∀ (U : 𝒞) (x y : q.Fiber U),
                  Presheaf.IsLocallyInjective (J.over U) (hF.morPresheafMap x y) ∧
                    Presheaf.IsLocallySurjective (J.over U) (hF.morPresheafMap x y)) →
                (∀ (U : 𝒞) (x : r.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
                  (fiberFunctorOfCompEq hF.comp_eq V).essImage (pullbackFiber r x f)) →
                ∃ H : FibredMor q' r, Nonempty (IsEquivalenceOver q' r H.functor) ∧
                  ∃ α : (restrictMor hG).obj H ≅ ⟨F, hF⟩,
                    ∀ (H' : FibredMor q' r) (α' : (restrictMor hG).obj H' ≅ ⟨F, hF⟩),
                      ∃! β : H ≅ H', (restrictMor hG).mapIso β ≪≫ α' = α := by
  obtain ⟨hst, hmor, hobj⟩ := isStackification_toStageThree q J
  exact ⟨q.StageThree J, inferInstance, q.stageThreeProj J, inferInstance, q.toStageThree J,
    isFibredOneMorphism_toStageThree q J, hst, hmor, hobj,
    fun _ _ _ _ _ hF hr hFmor hFobj ↦
      Stackification.exists_isEquivalenceOver_and_existsUnique_iso J
        (isFibredOneMorphism_toStageThree q J) hF hmor hobj hFmor hFobj hst hr⟩

end Stackification

end CategoryTheory.Functor

end
