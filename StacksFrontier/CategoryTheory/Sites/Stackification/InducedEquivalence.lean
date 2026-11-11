module

public import StacksFrontier.CategoryTheory.Sites.Stackification.Stackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.Uniqueness
public import StacksFrontier.CategoryTheory.Sites.Stackification.TransportAlongEquivalenceOver
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification.Coverings

/-!
# A 1-morphism inducing an equivalence of stackifications

Let `(𝒞, J)` be a site and let `F : 𝒳 ⥤ 𝒴` be a 1-morphism of fibred categories over `𝒞`. Choose
stackifications `G : 𝒳 ⥤ 𝒳'` and `H : 𝒴 ⥤ 𝒴'` in the sense of Stacks 02ZN. The 1-morphism `F`
*induces an equivalence of stackifications* when there is a 1-morphism `E : 𝒳' ⥤ 𝒴'` over `𝒞`
which is an equivalence over `𝒞` and is compatible with `F`, that is, comes with a vertical
2-isomorphism `F ⋙ H ≅ G ⋙ E`. By the universal property of stackification (Stacks 0435) such
an `E` is the 1-morphism of stackifications induced by `F`, determined up to 2-isomorphism.

This file shows that, when `𝒴` is fibred in groupoids, such an `F` itself satisfies the two
local clauses of Stacks 02ZN: the induced maps of morphism presheaves are locally injective and
locally surjective, and every object of a fibre of `𝒴` is, along a covering sieve, in the
essential image of `F` on fibres.

## Main definitions

* `CategoryTheory.Functor.IsFibredOneMorphism.IsStackification`: a 1-morphism `G : 𝒳 ⥤ 𝒳'`
  exhibits `𝒳'` as a stackification of `𝒳`, Stacks 02ZN: `𝒳'` is a stack and the two clauses of
  Stacks 02ZN hold for `G`.

## Main results

* `CategoryTheory.Functor.IsFibredOneMorphism.isStackification_toStageThree`: the stackification
  constructed in the library is one.
* `CategoryTheory.Functor.Stackification.isLocallyBijective_morPresheafMap_of_isEquivalenceOver`
  and `CategoryTheory.Functor.Stackification.locally_essImage_of_isEquivalenceOver`: a
  1-morphism inducing an equivalence of stackifications satisfies the two clauses of
  Stacks 02ZN.

## Implementation notes

Both clauses are obtained by cancelling `H`. The composite `G ⋙ E` satisfies the two clauses,
because `G` does and `E` is an equivalence over `𝒞`; they transport across the vertical
2-isomorphism to `F ⋙ H`. For the first clause, the map of morphism presheaves of `F ⋙ H` is that
of `F` followed by that of `H`, and the second is locally injective, so local injectivity and
local surjectivity of the composite descend to the map of `F`. For the second clause, an object
`y` of a fibre of `𝒴` has `H y` locally isomorphic to images of `F ⋙ H`; by local surjectivity of
the maps of morphism presheaves of `H`, such an isomorphism is locally the image of a morphism of
a fibre of `𝒴`, which is an isomorphism because `𝒴` is fibred in groupoids.

All the total categories share one hom universe with the base, which is what
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` and
`CategoryTheory.locallyEssSurj_comp` require.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 0435](https://stacks.math.columbia.edu/tag/0435)
* [Stacks Project, Tag 06WQ](https://stacks.math.columbia.edu/tag/06WQ)
-/

@[expose] public section

namespace CategoryTheory.Functor

open CategoryTheory

namespace IsFibredOneMorphism

section IsStackification

universe vb v u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {𝒳' : Type u₃} [Category.{v} 𝒳'] {p : 𝒳 ⥤ 𝒞} {p' : 𝒳' ⥤ 𝒞} [p.IsFibered] [p'.IsFibered]
  {G : 𝒳 ⥤ 𝒳'}

/-- **Stacks 02ZN: `G` exhibits `p'` as a stackification of `p`.** The target `p'` is a stack,
for every `U` and all `x`, `y` in the fibre over `U` the induced map of presheaves
`Mor(x, y) ⟶ Mor(G x, G y)` on `𝒞/U` identifies its target with the sheafification of its
source — it is locally injective and locally surjective — and every object of a fibre of `p'` is,
along a covering sieve of the base, in the essential image of the functor induced by `G` on
fibres. -/
structure IsStackification (hG : p.IsFibredOneMorphism p' G) (J : GrothendieckTopology 𝒞) :
    Prop where
  /-- The target is a stack. -/
  isStack : p'.IsStack J
  /-- Clause (1) of Stacks 02ZN. -/
  isLocallyBijective_morPresheafMap : ∀ (U : 𝒞) (x y : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y)
  /-- Clause (2) of Stacks 02ZN. -/
  locally_essImage : ∀ (U : 𝒞) (x' : p'.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄,
    R.arrows f → (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x' f)

end IsStackification

universe w t₁ t₂ vb in
/-- The stackification constructed in the library, `CategoryTheory.Functor.toStageThree`, is a
stackification in the sense of `CategoryTheory.Functor.IsFibredOneMorphism.IsStackification`. -/
theorem isStackification_toStageThree {𝒞 : Type t₁} [Category.{vb} 𝒞] {𝒴 : Type t₂}
    [Category.{max t₁ t₂ w vb} 𝒴] (q : 𝒴 ⥤ 𝒞) [q.IsFibered] (J : GrothendieckTopology 𝒞) :
    (isFibredOneMorphism_toStageThree q J).IsStackification J :=
  have h := _root_.CategoryTheory.Functor.isStackification_toStageThree q J
  ⟨h.1, h.2.1, h.2.2⟩

end IsFibredOneMorphism

namespace Stackification

universe v u₁ u₂ u₃ u₄ u₅

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {𝒴 : Type u₃} [Category.{v} 𝒴] {𝒳' : Type u₄} [Category.{v} 𝒳']
  {𝒴' : Type u₅} [Category.{v} 𝒴']
  {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {p' : 𝒳' ⥤ 𝒞} {q' : 𝒴' ⥤ 𝒞}
  [p.IsFibered] [q.IsFibered] [p'.IsFibered] [q'.IsFibered]
  {F : 𝒳 ⥤ 𝒴} {G : 𝒳 ⥤ 𝒳'} {H : 𝒴 ⥤ 𝒴'} {E : 𝒳' ⥤ 𝒴'}
  (J : GrothendieckTopology 𝒞)

omit [q.IsFibered] in
/-- **Clause (1) of Stacks 02ZN transports along an equivalence over the site on the target.** If
the maps of morphism presheaves induced by `G` are locally injective and locally surjective, then
so are those induced by `G ⋙ E` for an equivalence `E` over the site: the map of `E` is bijective
over every object. -/
theorem isLocallyBijective_morPresheafMap_comp_of_isEquivalenceOver_right
    (hG : p.IsFibredOneMorphism p' G) (hE : p'.IsFibredOneMorphism q' E)
    (hEeq : IsEquivalenceOver p' q' E)
    (hGmor : ∀ (U : 𝒞) (a b : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap a b))
    (U : 𝒞) (a b : p.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) ((hG.comp hE).morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) ((hG.comp hE).morPresheafMap a b) := by
  rw [← IsFibredOneMorphism.morPresheafMap_comp hG hE a b]
  have hbij := bijective_morPresheafMap_app_of_isEquivalenceOver hE hEeq
    ((fiberFunctorOfCompEq hG.comp_eq U).obj a) ((fiberFunctorOfCompEq hG.comp_eq U).obj b)
  have : Presheaf.IsLocallyInjective (J.over U) (hE.morPresheafMap
      ((fiberFunctorOfCompEq hG.comp_eq U).obj a) ((fiberFunctorOfCompEq hG.comp_eq U).obj b)) :=
    Presheaf.isLocallyInjective_of_injective _ _ fun g => (hbij g).1
  have : Presheaf.IsLocallySurjective (J.over U) (hE.morPresheafMap
      ((fiberFunctorOfCompEq hG.comp_eq U).obj a) ((fiberFunctorOfCompEq hG.comp_eq U).obj b)) :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun g => (hbij g).2
  obtain ⟨_, _⟩ := hGmor U a b
  exact ⟨inferInstance, inferInstance⟩

omit [p'.IsFibered] in
/-- **Clause (1) of Stacks 02ZN cancels.** If the maps of morphism presheaves induced by `F ⋙ H`
are locally injective and locally surjective, and those induced by `H` are locally injective,
then those induced by `F` are locally injective and locally surjective. -/
theorem isLocallyBijective_morPresheafMap_of_comp (hF : p.IsFibredOneMorphism q F)
    (hH : q.IsFibredOneMorphism q' H)
    (hHmor : ∀ (U : 𝒞) (a b : q.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hH.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) (hH.morPresheafMap a b))
    (hFHmor : ∀ (U : 𝒞) (a b : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) ((hF.comp hH).morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) ((hF.comp hH).morPresheafMap a b))
    (U : 𝒞) (a b : p.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) (hF.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) (hF.morPresheafMap a b) := by
  have fac := IsFibredOneMorphism.morPresheafMap_comp hF hH a b
  obtain ⟨_, _⟩ := hFHmor U a b
  obtain ⟨_, -⟩ := hHmor U ((fiberFunctorOfCompEq hF.comp_eq U).obj a)
    ((fiberFunctorOfCompEq hF.comp_eq U).obj b)
  exact ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_fac (J.over U) fac,
    Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac (J.over U) _
      fac⟩

omit [p'.IsFibered] in
/-- **Clause (2) of Stacks 02ZN cancels, one object at a time.** Let `𝒴` be fibred in groupoids
and let the maps of morphism presheaves induced by `H` be locally injective and locally
surjective. If `H z` is in the essential image of `F ⋙ H` on the fibre over `V`, then `z` is,
along a covering sieve of `V`, in the essential image of `F` on fibres.

An isomorphism `H (F a) ≅ H z` is, along a covering sieve, the image under `H` of a morphism
`(F a)|_W ⟶ z|_W` of the fibre over `W`, which is an isomorphism because `𝒴` is fibred in
groupoids, and `(F a)|_W` is isomorphic to `F (a|_W)`. -/
theorem locally_essImage_of_essImage_comp (hq : q.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F) (hH : q.IsFibredOneMorphism q' H)
    (hHmor : ∀ (U : 𝒞) (a b : q.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hH.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) (hH.morPresheafMap a b))
    {V : 𝒞} (z : q.Fiber V)
    (h : (fiberFunctorOfCompEq (hF.comp hH).comp_eq V).essImage
      ((fiberFunctorOfCompEq hH.comp_eq V).obj z)) :
    ∃ R ∈ J V, ∀ ⦃W : 𝒞⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (fiberFunctorOfCompEq hF.comp_eq W).essImage (pullbackFiber q z g) := by
  obtain ⟨a, ⟨φ⟩⟩ := h
  obtain ⟨R, hR, hlift⟩ := exists_covering_lift (J := J) hH hHmor
    (a := (fiberFunctorOfCompEq hF.comp_eq V).obj a) (b := z) φ.hom
  refine ⟨R, hR, fun W g hg => ?_⟩
  obtain ⟨u, -⟩ := hlift g hg
  have hu : q.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map u) := u.2
  have := hq.isStronglyCartesian_homLift (𝟙 W) (Fiber.fiberInclusion.map u)
  have hiso : IsIso (Fiber.fiberInclusion.map u) :=
    IsStronglyCartesian.isIso_of_base_isIso q (𝟙 W) (Fiber.fiberInclusion.map u)
  exact ⟨pullbackFiber p a g, ⟨(hF.mapPullbackFiberIso a g).symm ≪≫
    Fiber.isoMk (@asIso _ _ _ _ (Fiber.fiberInclusion.map u) hiso) hu⟩⟩

omit [p.IsFibered] [q.IsFibered] in
/-- **Clause (2) of Stacks 02ZN transports along an equivalence over the site on the target.**
If every object of a fibre of `p'` is locally in the essential image of `G` on fibres, every
object of a fibre of `q'` is locally in the essential image of `G ⋙ E`, for an equivalence `E`
over the site. -/
theorem locally_essImage_comp_of_isEquivalenceOver_right
    (hG : p.IsFibredOneMorphism p' G) (hE : p'.IsFibredOneMorphism q' E)
    (hEeq : IsEquivalenceOver p' q' E)
    (hGobj : ∀ (U : 𝒞) (x : p'.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x f))
    (U : 𝒞) (x : q'.Fiber U) :
    ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq (hG.comp hE).comp_eq V).essImage (pullbackFiber q' x f) :=
  locallyEssSurj_comp hG hE J hGobj (fun U _ => ⟨⊤, J.top_mem U, fun V _ _ =>
    have := essSurj_fiberFunctorOfCompEq_of_isEquivalenceOver hE.comp_eq hEeq V
    EssSurj.mem_essImage (fiberFunctorOfCompEq hE.comp_eq V) _⟩) U x

variable {J}

/-- **A 1-morphism inducing an equivalence of stackifications satisfies clause (1) of
Stacks 02ZN.** Let `G : 𝒳 ⥤ 𝒳'` and `H : 𝒴 ⥤ 𝒴'` be stackifications and let `E : 𝒳' ⥤ 𝒴'` be an
equivalence over the site with a vertical 2-isomorphism `F ⋙ H ≅ G ⋙ E`. Then the maps of
morphism presheaves induced by `F` are locally injective and locally surjective. -/
theorem isLocallyBijective_morPresheafMap_of_isEquivalenceOver
    (hF : p.IsFibredOneMorphism q F) (hG : p.IsFibredOneMorphism p' G)
    (hH : q.IsFibredOneMorphism q' H) (hGst : hG.IsStackification J)
    (hHst : hH.IsStackification J) (hE : p'.IsFibredOneMorphism q' E)
    (hEeq : IsEquivalenceOver p' q' E) (α : F ⋙ H ≅ G ⋙ E)
    (hα : ∀ a : 𝒳, q'.IsHomLift (𝟙 (p.obj a)) (α.hom.app a)) (U : 𝒞) (a b : p.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) (hF.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) (hF.morPresheafMap a b) :=
  isLocallyBijective_morPresheafMap_of_comp J hF hH hHst.isLocallyBijective_morPresheafMap
    (isLocallyBijective_morPresheafMap_of_natIso hF hH J (hG.comp hE) α hα
      (isLocallyBijective_morPresheafMap_comp_of_isEquivalenceOver_right J hG hE hEeq
        hGst.isLocallyBijective_morPresheafMap)) U a b

/-- **A 1-morphism inducing an equivalence of stackifications satisfies clause (2) of
Stacks 02ZN**, when its target is fibred in groupoids. Let `G : 𝒳 ⥤ 𝒳'` and `H : 𝒴 ⥤ 𝒴'` be
stackifications and let `E : 𝒳' ⥤ 𝒴'` be an equivalence over the site with a vertical
2-isomorphism `F ⋙ H ≅ G ⋙ E`. Then every object of a fibre of `𝒴` is, along a covering sieve,
in the essential image of `F` on fibres. -/
theorem locally_essImage_of_isEquivalenceOver (hq : q.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F) (hG : p.IsFibredOneMorphism p' G)
    (hH : q.IsFibredOneMorphism q' H) (hGst : hG.IsStackification J)
    (hHst : hH.IsStackification J) (hE : p'.IsFibredOneMorphism q' E)
    (hEeq : IsEquivalenceOver p' q' E) (α : F ⋙ H ≅ G ⋙ E)
    (hα : ∀ a : 𝒳, q'.IsHomLift (𝟙 (p.obj a)) (α.hom.app a)) (U : 𝒞) (y : q.Fiber U) :
    ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hF.comp_eq V).essImage (pullbackFiber q y f) := by
  classical
  obtain ⟨S, hS, hSess⟩ := locally_essImage_comp_of_isEquivalenceOver_right J hG hE hEeq
    hGst.locally_essImage U ((fiberFunctorOfCompEq hH.comp_eq U).obj y)
  have hloc : ∀ ⦃V : 𝒞⦄ ⦃k : V ⟶ U⦄, S.arrows k → ∃ T ∈ J V, ∀ ⦃W : 𝒞⦄ ⦃g : W ⟶ V⦄,
      T.arrows g → (fiberFunctorOfCompEq hF.comp_eq W).essImage
        (pullbackFiber q (pullbackFiber q y k) g) := by
    intro V k hk
    obtain ⟨a, ⟨ι⟩⟩ := hSess hk
    refine locally_essImage_of_essImage_comp J hq hF hH hHst.isLocallyBijective_morPresheafMap
      (pullbackFiber q y k) ⟨a, ⟨?_⟩⟩
    exact IsFibredOneMorphism.natIsoFiber (hF.comp hH) (hG.comp hE) α hα a ≪≫ ι ≪≫
      hH.mapPullbackFiberIso y k
  choose T hT hTess using hloc
  refine ⟨Sieve.bind S.arrows T, J.bind_covering hS hT, ?_⟩
  rintro W _ ⟨V, g, k, hk, hg, rfl⟩
  obtain ⟨a, ⟨ι⟩⟩ := hTess hk hg
  exact ⟨a, ⟨ι ≪≫ pullbackFiberCompIso y k g⟩⟩

end Stackification

end CategoryTheory.Functor
