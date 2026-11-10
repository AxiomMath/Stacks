module

public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty
public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackEquivalence

/-!
# Full faithfulness of a 1-morphism out of a stackification (Stacks 04WQ)

Let `(𝒞, J)` be a site, let `p : 𝒜 ⥤ 𝒞` be a fibred category, let `G : 𝒜 ⥤ ℬ` be a 1-morphism of
fibred categories over `𝒞` exhibiting `p' : ℬ ⥤ 𝒞` as the stackification of `p` — that is,
satisfying the two clauses of **Stacks 02ZN**: the induced maps of morphism presheaves are locally
injective and locally surjective, and every object of a fibre of `p'` is, locally on the base, in
the essential image of `G` on fibres — and let `H : ℬ ⥤ 𝒳` be a 1-morphism into a stack `q`.

Then `H` is fully faithful as soon as the composite `G ⋙ H` is *locally fully faithful*, i.e. its
own induced maps of morphism presheaves are locally injective and locally surjective. This is the
combination of **Stacks 04WQ** (a 1-morphism of stacks is fully faithful exactly when it induces
isomorphisms on the sheaves of morphisms) with the morphism half of the universal property of
stackification, **Stacks 0435**, and it is what reduces full faithfulness of an *extension along a
stackification* to a statement about the 1-morphism being extended.

The reduction is genuine: the hypothesis is about the fibres of `p` alone, so a consumer never has
to handle an object of `p'` that is only locally presented. That local-to-global step is done once,
here, and it is done at the level of presheaves rather than by gluing morphisms of fibres, so no
compatibility condition on a chosen family has to be verified.

## Main results

* `CategoryTheory.Presheaf.isIso_of_isLocallyBijective`: a locally bijective map of sheaves of
  types is an isomorphism, and `CategoryTheory.Presheaf.isIso_of_isLocallyBijective_fac`: two
  locally bijective maps out of one presheaf into sheaves identify those sheaves.
* `CategoryTheory.Functor.Stackification.isIso_morPresheafMap_of_extension`: the map of morphism
  presheaves induced by `H` is an isomorphism, between *any* two objects of *any* fibre of `p'`.
* `CategoryTheory.Functor.Stackification.full_of_extension` and `.faithful_of_extension`:
  **Stacks 04WQ** for the extension — `H` is full and faithful.
* `CategoryTheory.Functor.Stackification.isLocallyBijective_morPresheafMap_of_natIso`: the
  hypothesis may be checked for any 1-morphism related to `G ⋙ H` by a vertical 2-isomorphism,
  which is the shape the universal property of stackification (Stacks 0436) delivers.

## Implementation notes

**Where the three steps are.** At objects in the image of `G` the conclusion is immediate from the
composition law for the maps of morphism presheaves,
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap_comp`: the two outer maps of the
factorisation `Mor(x, y) ⟶ Mor(G x, G y) ⟶ Mor(H G x, H G y)` are locally bijective by hypothesis
and the two targets are sheaves, so the middle map is an isomorphism. At a general pair of objects
of a fibre the map is shown to be locally injective and locally surjective *directly*, each over
the sieve of the slice induced by the covering sieve on which both objects are presented, and then
the two sheaf conditions finish it. Local injectivity and local surjectivity are the two halves
that require no coherence between the local choices, which is why this route is shorter than
gluing a family of morphisms of fibres.

**The morphism universes.** `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` has one
morphism universe for its source and its target, because its value is a morphism of presheaves of
types; the base's is independent. All three fibred categories here therefore share one morphism
universe, while the base's is free, which is the configuration
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap_comp` and
`CategoryTheory.Comma.bijective_fiberFunctor_map_of_bijective_app` are stated at.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 0435](https://stacks.math.columbia.edu/tag/0435)
* [Stacks Project, Tag 04WQ](https://stacks.math.columbia.edu/tag/04WQ)
-/

@[expose] public section

namespace CategoryTheory

open Opposite

namespace Presheaf

universe w v u

variable {𝒟 : Type u} [Category.{v} 𝒟] {P Q T : 𝒟ᵒᵖ ⥤ Type w}

/-- **Two locally bijective maps out of one presheaf into sheaves identify those sheaves.** The
map through which one factors the other — unique by
`CategoryTheory.Presheaf.existsUnique_hom_of_isLocallyBijective` — is an isomorphism, its inverse
being the map factoring the other way. -/
theorem isIso_of_isLocallyBijective_fac (K : GrothendieckTopology 𝒟) (φ : P ⟶ Q) (ψ : P ⟶ T)
    [IsLocallyInjective K φ] [IsLocallySurjective K φ]
    [IsLocallyInjective K ψ] [IsLocallySurjective K ψ]
    (hQ : IsSheaf K Q) (hT : IsSheaf K T) {χ : Q ⟶ T} (hχ : φ ≫ χ = ψ) :
    IsIso χ := by
  obtain ⟨χ', hχ', -⟩ := existsUnique_hom_of_isLocallyBijective K ψ φ hQ
  obtain ⟨_, -, huniqQ⟩ := existsUnique_hom_of_isLocallyBijective K φ φ hQ
  obtain ⟨_, -, huniqT⟩ := existsUnique_hom_of_isLocallyBijective K ψ ψ hT
  refine ⟨χ', ?_, ?_⟩
  · rw [huniqQ (χ ≫ χ') (show φ ≫ χ ≫ χ' = φ by rw [← Category.assoc, hχ, hχ']),
      huniqQ (𝟙 Q) (Category.comp_id φ)]
  · rw [huniqT (χ' ≫ χ) (show ψ ≫ χ' ≫ χ = ψ by rw [← Category.assoc, hχ', hχ]),
      huniqT (𝟙 T) (Category.comp_id ψ)]

/-- **A locally bijective map of sheaves of types is an isomorphism.** This is
`CategoryTheory.Presheaf.isIso_of_isLocallyBijective_fac` with the identity of the source as the
second locally bijective map; it needs no universe hypothesis, because no sheafification functor
is formed. -/
theorem isIso_of_isLocallyBijective (K : GrothendieckTopology 𝒟) (φ : Q ⟶ T)
    [IsLocallyInjective K φ] [IsLocallySurjective K φ] (hQ : IsSheaf K Q) (hT : IsSheaf K T) :
    IsIso φ :=
  isIso_of_isLocallyBijective_fac K (𝟙 Q) φ hQ hT (Category.id_comp φ)

end Presheaf

namespace Functor

universe v u₂ u₃

/-- **Bijectivity of a functor's action on a hom-set transports along isomorphisms** of the source
and of the target. -/
theorem bijective_map_of_isos {A : Type u₂} [Category.{v} A] {Bb : Type u₃} [Category.{v} Bb]
    (K : A ⥤ Bb) {a b x y : A} (ι : a ≅ x) (κ : b ≅ y)
    (h : Function.Bijective (fun m : a ⟶ b => K.map m)) :
    Function.Bijective (fun n : x ⟶ y => K.map n) := by
  have key : (fun n : x ⟶ y => K.map n) =
      (Iso.homCongr (K.mapIso ι) (K.mapIso κ)) ∘ (fun m : a ⟶ b => K.map m) ∘
        (Iso.homCongr ι κ).symm := by
    funext n
    simp [Iso.homCongr, Functor.map_comp]
  rw [key]
  exact (Iso.homCongr (K.mapIso ι) (K.mapIso κ)).bijective.comp
    (h.comp (Iso.homCongr ι κ).symm.bijective)

namespace Stackification

universe vb u₁ u₄

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒜 : Type u₂} [Category.{v} 𝒜]
  {ℬ : Type u₃} [Category.{v} ℬ] {𝒳 : Type u₄} [Category.{v} 𝒳]
  {p : 𝒜 ⥤ 𝒞} {p' : ℬ ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} [p.IsFibered] [p'.IsFibered] [q.IsFibered]
  {G : 𝒜 ⥤ ℬ} {H : ℬ ⥤ 𝒳}
  (hG : p.IsFibredOneMorphism p' G) (hH : p'.IsFibredOneMorphism q H)
  (J : GrothendieckTopology 𝒞)

/-- Over every object `g` of the slice there is a covering sieve all of whose members lie over
both of two covering sieves of the base. -/
private theorem exists_mem_over_arrows_inf {U : 𝒞} {Rx Ry : Sieve U} (hRx : Rx ∈ J U)
    (hRy : Ry ∈ J U) (g : Over U) :
    ∃ S ∈ (J.over U) g, ∀ ⦃g₂ : Over U⦄ (k : g₂ ⟶ g), S.arrows k →
      Rx.arrows g₂.hom ∧ Ry.arrows g₂.hom := by
  refine ⟨_, J.overEquiv_symm_mem_over g ((Rx ⊓ Ry).pullback g.hom)
    (J.pullback_stable _ (J.intersection_covering hRx hRy)), fun g₂ k hk => ?_⟩
  have h1 : (Rx ⊓ Ry).arrows (k.left ≫ g.hom) := (Sieve.overEquiv_symm_iff _ k).1 hk
  rwa [Over.w k] at h1

/-- If `H` induces an isomorphism of morphism presheaves, it is bijective on hom-sets of the
fibre. -/
private theorem bijective_fiberFunctor_map_of_isIso {U : 𝒞} (x y : p'.Fiber U)
    [IsIso (hH.morPresheafMap x y)] :
    Function.Bijective (fun m : x ⟶ y => (fiberFunctorOfCompEq hH.comp_eq U).map m) := by
  refine Comma.bijective_fiberFunctor_map_of_bijective_app hH _ _ ?_
  rw [← isIso_iff_bijective]
  infer_instance

section

variable
  (hGmor : ∀ (U : 𝒞) (a b : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap a b))
  (hFmor : ∀ (U : 𝒞) (a b : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) ((hG.comp hH).morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) ((hG.comp hH).morPresheafMap a b))
  (hp' : ∀ (U : 𝒞) (x y : p'.Fiber U), IsMorSheaf p' J U x y)
  (hq : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y)

include hGmor hFmor hp' hq

/-- **At objects in the image of `G` the map of morphism presheaves induced by `H` is an
isomorphism.** The map induced by `G ⋙ H` factors through the one induced by `G`, by the
composition law; both are locally bijective by hypothesis and both targets are sheaves. -/
theorem isIso_morPresheafMap_of_image (U : 𝒞) (a b : p.Fiber U) :
    IsIso (hH.morPresheafMap ((fiberFunctorOfCompEq hG.comp_eq U).obj a)
      ((fiberFunctorOfCompEq hG.comp_eq U).obj b)) := by
  obtain ⟨_, _⟩ := hGmor U a b
  obtain ⟨_, _⟩ := hFmor U a b
  exact Presheaf.isIso_of_isLocallyBijective_fac (J.over U) (hG.morPresheafMap a b)
    ((hG.comp hH).morPresheafMap a b) (hp' U _ _) (hq U _ _)
    (IsFibredOneMorphism.morPresheafMap_comp hG hH a b)

/-- **At objects of a fibre of `p'` that lie in the essential image of `G` on that fibre, the
functor induced by `H` on the fibre is bijective on hom-sets.** -/
theorem bijective_fiberFunctor_map_of_essImage {V : 𝒞} {z y : p'.Fiber V}
    (hz : (fiberFunctorOfCompEq hG.comp_eq V).essImage z)
    (hy : (fiberFunctorOfCompEq hG.comp_eq V).essImage y) :
    Function.Bijective (fun m : z ⟶ y => (fiberFunctorOfCompEq hH.comp_eq V).map m) := by
  obtain ⟨a, ⟨ι⟩⟩ := hz
  obtain ⟨b, ⟨κ⟩⟩ := hy
  refine bijective_map_of_isos _ ι κ ?_
  have := isIso_morPresheafMap_of_image hG hH J hGmor hFmor hp' hq V a b
  exact bijective_fiberFunctor_map_of_isIso hH _ _

end

section

variable
  (hbij : ∀ {V : 𝒞} {z y : p'.Fiber V},
    (fiberFunctorOfCompEq hG.comp_eq V).essImage z →
    (fiberFunctorOfCompEq hG.comp_eq V).essImage y →
    Function.Bijective (fun m : z ⟶ y => (fiberFunctorOfCompEq hH.comp_eq V).map m))
  (hGobj : ∀ (U : 𝒞) (x : p'.Fiber U), ∃ R ∈ J U,
    ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x f))

include hbij hGobj

omit [p.IsFibered] in
/-- **The map of morphism presheaves induced by `H` is locally injective**, between any two objects
of any fibre of `p'`: over the sieve of the slice induced by a covering sieve on which both objects
are presented, two sections with the same image restrict to morphisms of a fibre between presented
objects, whose images agree by naturality. -/
theorem isLocallyInjective_morPresheafMap_of_essImage (U : 𝒞) (x y : p'.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) (hH.morPresheafMap x y) := by
  constructor
  intro X s t hst
  obtain ⟨Rx, hRx, hRx'⟩ := hGobj U x
  obtain ⟨Ry, hRy, hRy'⟩ := hGobj U y
  obtain ⟨S, hS, hS'⟩ := exists_mem_over_arrows_inf J hRx hRy X.unop
  refine (J.over U).superset_covering ?_ hS
  intro g₂ k hk
  change (morPresheaf p' x y).map k.op s = (morPresheaf p' x y).map k.op t
  have hs : (hH.morPresheafMap x y).app (op g₂) ((morPresheaf p' x y).map k.op s)
      = (hH.morPresheafMap x y).app (op g₂) ((morPresheaf p' x y).map k.op t) := by
    rw [NatTrans.naturality_apply (hH.morPresheafMap x y) k.op s,
      NatTrans.naturality_apply (hH.morPresheafMap x y) k.op t, hst]
  rw [IsFibredOneMorphism.morPresheafMap_app, IsFibredOneMorphism.morPresheafMap_app] at hs
  exact (hbij (hRx' (hS' k hk).1) (hRy' (hS' k hk).2)).1 ((cancel_mono _).1 ((cancel_epi _).1 hs))

omit [p.IsFibered] in
/-- **The map of morphism presheaves induced by `H` is locally surjective**, between any two
objects of any fibre of `p'`: over the same sieve, the restriction of a section of the target is,
after conjugating by the comparison isomorphisms, a morphism of a fibre between presented objects,
and so is in the image. No compatibility between the local preimages is needed. -/
theorem isLocallySurjective_morPresheafMap_of_essImage (U : 𝒞) (x y : p'.Fiber U) :
    Presheaf.IsLocallySurjective (J.over U) (hH.morPresheafMap x y) := by
  constructor
  intro g n
  obtain ⟨Rx, hRx, hRx'⟩ := hGobj U x
  obtain ⟨Ry, hRy, hRy'⟩ := hGobj U y
  obtain ⟨S, hS, hS'⟩ := exists_mem_over_arrows_inf J hRx hRy g
  refine (J.over U).superset_covering ?_ hS
  intro g₂ k hk
  obtain ⟨m, hm⟩ := (hbij (hRx' (hS' k hk).1) (hRy' (hS' k hk).2)).2
    ((hH.mapPullbackFiberIso x g₂.hom).inv ≫
      (morPresheaf q ((fiberFunctorOfCompEq hH.comp_eq U).obj x)
        ((fiberFunctorOfCompEq hH.comp_eq U).obj y)).map k.op n ≫
      (hH.mapPullbackFiberIso y g₂.hom).hom)
  refine ⟨m, ?_⟩
  dsimp only at hm
  rw [IsFibredOneMorphism.morPresheafMap_app, hm]
  simp

end

section

variable
  (hGmor : ∀ (U : 𝒞) (a b : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap a b))
  (hGobj : ∀ (U : 𝒞) (x : p'.Fiber U), ∃ R ∈ J U,
    ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x f))
  (hFmor : ∀ (U : 𝒞) (a b : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) ((hG.comp hH).morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) ((hG.comp hH).morPresheafMap a b))
  (hp' : ∀ (U : 𝒞) (x y : p'.Fiber U), IsMorSheaf p' J U x y)
  (hq : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y)

include hGmor hGobj hFmor hp' hq

/-- **The map of morphism presheaves induced by `H` is an isomorphism**, between any two objects of
any fibre of `p'` — not only between presented ones. This is condition (2) of **Stacks 04WQ** for
the extension. -/
theorem isIso_morPresheafMap_of_extension (U : 𝒞) (x y : p'.Fiber U) :
    IsIso (hH.morPresheafMap x y) := by
  have hbij := fun {V : 𝒞} {z w : p'.Fiber V} hz hw =>
    bijective_fiberFunctor_map_of_essImage hG hH J hGmor hFmor hp' hq (z := z) (y := w) hz hw
  have h1 := isLocallyInjective_morPresheafMap_of_essImage hG hH J hbij hGobj U x y
  have h2 := isLocallySurjective_morPresheafMap_of_essImage hG hH J hbij hGobj U x y
  exact Presheaf.isIso_of_isLocallyBijective (J.over U) _ (hp' U x y) (hq U _ _)

/-- The functor induced by `H` on every fibre is bijective on every hom-set. -/
theorem bijective_fiberFunctor_map_of_extension (U : 𝒞) (x y : p'.Fiber U) :
    Function.Bijective (fun m : x ⟶ y => (fiberFunctorOfCompEq hH.comp_eq U).map m) := by
  have := isIso_morPresheafMap_of_extension hG hH J hGmor hGobj hFmor hp' hq U x y
  exact bijective_fiberFunctor_map_of_isIso hH _ _

/-- **Stacks 04WQ for an extension along a stackification: `H` is faithful.** -/
theorem faithful_of_extension : H.Faithful :=
  Comma.faithful_of_fiber_faithful hH fun U => ⟨fun {x y} _ _ hmn =>
    (bijective_fiberFunctor_map_of_extension hG hH J hGmor hGobj hFmor hp' hq U x y).1 hmn⟩

/-- **Stacks 04WQ for an extension along a stackification: `H` is full.** -/
theorem full_of_extension : H.Full :=
  Comma.full_of_fiber_full hH fun U => ⟨fun {x y} ψ =>
    (bijective_fiberFunctor_map_of_extension hG hH J hGmor hGobj hFmor hp' hq U x y).2 ψ⟩

end

omit [p'.IsFibered] in
/-- **The hypothesis on `G ⋙ H` may be checked on any 1-morphism related to it by a vertical
2-isomorphism**, which is the shape in which the universal property of stackification
(Stacks 0436) produces the comparison. -/
theorem isLocallyBijective_morPresheafMap_of_natIso {F : 𝒜 ⥤ 𝒳}
    (hF : p.IsFibredOneMorphism q F) (α : G ⋙ H ≅ F)
    (hα : ∀ a : 𝒜, q.IsHomLift (𝟙 (p.obj a)) (α.hom.app a))
    (hmor : ∀ (U : 𝒞) (a b : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hF.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) (hF.morPresheafMap a b))
    (U : 𝒞) (a b : p.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) ((hG.comp hH).morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) ((hG.comp hH).morPresheafMap a b) := by
  obtain ⟨_, _⟩ := hmor U a b
  rw [(Iso.eq_comp_inv (morPresheafFiberIso q
    (IsFibredOneMorphism.natIsoFiber (hG.comp hH) hF α hα a)
    (IsFibredOneMorphism.natIsoFiber (hG.comp hH) hF α hα b))).2
    (IsFibredOneMorphism.morPresheafMap_natIso (hG.comp hH) hF α hα a b)]
  exact ⟨inferInstance, inferInstance⟩

end Stackification

end Functor

end CategoryTheory

end
