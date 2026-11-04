module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackCongruence

/-! # Two stackifications of one fibred category, compared by a given 1-morphism

Let `(𝒞, J)` be a site, `p : 𝒮 ⥤ 𝒞` a fibred category over it, and let `F : 𝒮 ⥤ 𝒮'` and
`G : 𝒮 ⥤ 𝒮''` be 1-morphisms of fibred categories over `𝒞` which both exhibit their target as a
stackification of `𝒮` in the sense of Stacks 02ZN, the targets `q : 𝒮' ⥤ 𝒞` and `r : 𝒮'' ⥤ 𝒞`
being stacks. Then `q` and `r` are equivalent over `𝒞`.

The point of this file is that the equivalence is produced *with a prescribed forward
1-morphism*: given in addition a 1-morphism `H : 𝒮' ⥤ 𝒮''` over `𝒞` and a vertical natural
isomorphism `α : F ⋙ H ≅ G`, the equivalence returned has `H` itself as its forward functor. A
consumer which has already built the comparison `H` by hand — on a presentation of `𝒮'` by
objects and morphisms, say — therefore learns that *that* functor is an equivalence, rather than
merely that some equivalence exists.

## Main definitions

* `CategoryTheory.Functor.Stackification.liftVerticalIso` extends a vertical natural isomorphism
  between the restrictions along a stackification of two 1-morphisms into a stack to a vertical
  natural isomorphism of the 1-morphisms themselves.

## Main results

* `CategoryTheory.Functor.Stackification.essImage_fiberFunctor_of_essImage`: for a source fibred
  in groupoids, an object of a fibre of the target which lies in the essential image of a
  1-morphism already lies in the essential image of the functor induced on that fibre;
* `CategoryTheory.Functor.Stackification.equivalenceOverOfStackifications`: two stackifications of
  one fibred category are equivalent over the base, by a given comparison 1-morphism.

## Implementation notes

`CategoryTheory.Functor.equivalenceOverOfUniversalMorphisms` already gives an equivalence between
two stackifications, but its forward functor is the one chosen by essential surjectivity of
restriction, about which nothing else is known. Here the forward functor is an input, and the
quasi-inverse is the one chosen by essential surjectivity of restriction along `G`; the unit and
counit are obtained by extending the vertical isomorphisms visible after restriction along `F`
respectively `G`, which is what `liftVerticalIso` is for. The coherence conditions of
`CategoryTheory.StacksRepresentableCFG.EquivalenceOver` are discharged by
`CategoryTheory.Functor.equivalenceOverOfFibredMor`, the unit and counit being assembled as
isomorphisms of the morphism categories with `CategoryTheory.Functor.FibredMor.isoMk`.

As in `StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyUniqueness`, the
hypothesis "`F` exhibits `𝒮'` as the stackification of `𝒮`" is stated as the unfolded clauses of
Stacks 02ZN — local injectivity and local surjectivity of the maps of morphism presheaves, and
local essential surjectivity on fibres — so that the result is usable against any concrete
construction of a stackification. The three total categories share one hom universe, the sharing
being forced by `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`.

## References

* [Stacks 02ZN](https://stacks.math.columbia.edu/tag/02ZN);
* [Stacks 04W9](https://stacks.math.columbia.edu/tag/04W9);
* [Stacks 04WM](https://stacks.math.columbia.edu/tag/04WM).
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor.Stackification

universe v₁ v u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮]
  {𝒮' : Type u₃} [Category.{v} 𝒮'] {𝒮'' : Type u₄} [Category.{v} 𝒮'']
  {p : 𝒮 ⥤ 𝒞} {q : 𝒮' ⥤ 𝒞} {r : 𝒮'' ⥤ 𝒞}
  [p.IsFibered] [q.IsFibered] [r.IsFibered]
  {J : GrothendieckTopology 𝒞} {F : 𝒮 ⥤ 𝒮'}

omit [p.IsFibered] [q.IsFibered] in
/-- **The essential image of a 1-morphism, read in a fibre.** Let `F` be a functor strictly over
`𝒞` whose source is fibred in groupoids. An object `x` of the fibre of the target over `U` whose
underlying object lies in the essential image of `F` lies in the essential image of the functor
`F` induces on the fibres over `U`: an isomorphism `F.obj z ≅ x.val` in the total category can be
straightened to a vertical one, by transporting `z` into the fibre over `U` along the isomorphism
of `𝒞` that the given one covers. -/
theorem essImage_fiberFunctor_of_essImage (hp : p.IsFiberedInGroupoids)
    (hF : F ⋙ q = p) {U : 𝒞} (x : q.Fiber U) (hx : F.essImage x.val) :
    (fiberFunctorOfCompEq hF U).essImage x := by
  obtain ⟨z, ⟨β⟩⟩ := hx
  have hpgz : q.obj (F.obj z) = p.obj z := CategoryTheory.Functor.congr_obj hF z
  let c : p.obj z ≅ U := eqToIso hpgz.symm ≪≫ q.mapIso β ≪≫ eqToIso x.property
  obtain ⟨y, hy, βzy, hlift⟩ := hp.exists_iso_lift c
  let e : F.obj y ≅ x.val := (F.mapIso βzy).symm ≪≫ β
  have hβ : q.IsHomLift c.hom β.hom :=
    IsHomLift.of_fac' q c.hom β.hom hpgz x.property (by simp [c])
  have hmap : q.IsHomLift c.hom (F.mapIso βzy).hom :=
    isHomLift_map_of_comp_eq hF c.hom βzy.hom
  have hinv : q.IsHomLift c.inv (F.mapIso βzy).inv :=
    IsHomLift.inv_lift_inv q c (F.mapIso βzy)
  have he : q.IsHomLift (𝟙 U) e.hom := by
    have h : q.IsHomLift (c.inv ≫ c.hom) ((F.mapIso βzy).inv ≫ β.hom) := inferInstance
    simpa [e] using h
  exact ⟨⟨y, hy⟩, ⟨{ hom := ⟨e.hom, he⟩
                     inv := ⟨e.inv, IsHomLift.lift_id_inv q U e⟩
                     hom_inv_id := Fiber.hom_ext e.hom_inv_id
                     inv_hom_id := Fiber.hom_ext e.inv_hom_id }⟩⟩

/-- **Extending a vertical isomorphism along a stackification.** Let `F` exhibit `q` as a
stackification of `p` in the sense of Stacks 02ZN, and let `K`, `L` be two 1-morphisms from `q`
to a stack `r`. A vertical natural isomorphism `F ⋙ K ≅ F ⋙ L` of the restrictions extends to a
vertical natural isomorphism `K ≅ L`, because restriction along `F` is fully faithful on morphism
categories by Stacks 04W9. -/
def liftVerticalIso (hF : p.IsFibredOneMorphism q F)
    (hmor : ∀ U (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hF.morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (J.over U) (hF.morPresheafMap x y))
    (hobj : ∀ U (y : q.Fiber U), ∃ R ∈ J U, ∀ ⦃V⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hF.comp_eq V).essImage (pullbackFiber q y f))
    (hr : r.IsStack J) {K L : 𝒮' ⥤ 𝒮''}
    (hK : q.IsFibredOneMorphism r K) (hL : q.IsFibredOneMorphism r L)
    (α : F ⋙ K ≅ F ⋙ L)
    (hα : ∀ a, r.IsHomLift (𝟙 (p.obj a)) (α.hom.app a)) :
    {e : K ≅ L // ∀ a, r.IsHomLift (𝟙 (q.obj a)) (e.hom.app a)} := by
  let R := restrictMor (q := r) hF
  have : R.Full := restrict_full hF hmor hr.isMorSheaf hobj
  have : R.Faithful := restrict_faithful hF hr.isMorSheaf hobj
  let K' : FibredMor q r := ⟨K, hK⟩
  let L' : FibredMor q r := ⟨L, hL⟩
  let a : R.obj K' ≅ R.obj L' := FibredMor.isoMk α hα
  let e : K' ≅ L' := R.preimageIso a
  exact ⟨fibredMorNatIso e, e.hom.isHomLift⟩

/-- **Two stackifications of one fibred category are equivalent over the base, by a given
comparison.** Let `F : 𝒮 ⥤ 𝒮'` and `G : 𝒮 ⥤ 𝒮''` both exhibit their target as a stackification
of `p : 𝒮 ⥤ 𝒞` in the sense of Stacks 02ZN, the targets `q` and `r` being stacks fibred in
groupoids. Given a 1-morphism `H : 𝒮' ⥤ 𝒮''` over `𝒞` and a vertical natural isomorphism
`α : F ⋙ H ≅ G`, the functor `H` is an equivalence `q ≃ r` over `𝒞`: the quasi-inverse is the
1-morphism `K` corresponding to `F` under restriction along `G`, and the unit and counit are the
extensions along `F` respectively `G` of the vertical isomorphisms `α` and the comparison
`G ⋙ K ≅ F` supply after restriction. -/
def equivalenceOverOfStackifications
    (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
    (sq : q.IsStack J) (sr : r.IsStack J)
    {G : 𝒮 ⥤ 𝒮''} (hF : p.IsFibredOneMorphism q F) (hG : p.IsFibredOneMorphism r G)
    (hmorF : ∀ U (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hF.morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (J.over U) (hF.morPresheafMap x y))
    (hmorG : ∀ U (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y))
    (hobjF : ∀ U (y : q.Fiber U), ∃ R ∈ J U, ∀ ⦃V⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hF.comp_eq V).essImage (pullbackFiber q y f))
    (hobjG : ∀ U (y : r.Fiber U), ∃ R ∈ J U, ∀ ⦃V⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber r y f))
    (H : 𝒮' ⥤ 𝒮'') (hH : q.IsFibredOneMorphism r H) (α : F ⋙ H ≅ G)
    (hα : ∀ a, r.IsHomLift (𝟙 (p.obj a)) (α.hom.app a)) :
    StacksRepresentableCFG.EquivalenceOver q r := by
  let R := restrictMor (q := q) hG
  have : R.IsEquivalence :=
    restrict_isEquivalence hG hmorG sq.isMorSheaf hobjG sq.hasEffectiveDescent
  let K : FibredMor r q := R.objPreimage ⟨F, hF⟩
  let β₀ : R.obj K ≅ (⟨F, hF⟩ : FibredMor p q) := R.objObjPreimageIso ⟨F, hF⟩
  let β : G ⋙ K.functor ≅ F := fibredMorNatIso β₀
  have hβ : ∀ a, q.IsHomLift (𝟙 (p.obj a)) (β.hom.app a) := β₀.hom.isHomLift
  let u : F ⋙ (H ⋙ K.functor) ≅ F ⋙ 𝟭 𝒮' :=
    (Functor.associator F H K.functor).symm ≪≫ Functor.isoWhiskerRight α K.functor ≪≫
      β ≪≫ (Functor.rightUnitor F).symm
  have hu (a : 𝒮) : q.IsHomLift (𝟙 (p.obj a)) (u.hom.app a) := by
    have := hα a
    have := isHomLift_map_of_comp_eq K.isFibredOneMorphism.comp_eq
      (𝟙 (p.obj a)) (α.hom.app a)
    have := hβ a
    have h : q.IsHomLift (𝟙 (p.obj a) ≫ 𝟙 (p.obj a))
        (K.functor.map (α.hom.app a) ≫ β.hom.app a) := inferInstance
    simpa [u] using h
  let unit := liftVerticalIso hF hmorF hobjF sq (hH.comp K.isFibredOneMorphism)
    (hq.isFibredOneMorphism (Functor.id_comp q)) u hu
  let c : G ⋙ (K.functor ⋙ H) ≅ G ⋙ 𝟭 𝒮'' :=
    (Functor.associator G K.functor H).symm ≪≫ Functor.isoWhiskerRight β H ≪≫
      α ≪≫ (Functor.rightUnitor G).symm
  have hc (a : 𝒮) : r.IsHomLift (𝟙 (p.obj a)) (c.hom.app a) := by
    have := hβ a
    have := isHomLift_map_of_comp_eq hH.comp_eq (𝟙 (p.obj a)) (β.hom.app a)
    have := hα a
    have h : r.IsHomLift (𝟙 (p.obj a) ≫ 𝟙 (p.obj a))
        (H.map (β.hom.app a) ≫ α.hom.app a) := inferInstance
    simpa [c] using h
  let counit := liftVerticalIso hG hmorG hobjG sr (K.isFibredOneMorphism.comp hH)
    (hr.isFibredOneMorphism (Functor.id_comp r)) c hc
  exact equivalenceOverOfFibredMor ⟨H, hH⟩ K
    (FibredMor.isoMk unit.val unit.property).symm
    (FibredMor.isoMk counit.val counit.property)

end CategoryTheory.Functor.Stackification

end
