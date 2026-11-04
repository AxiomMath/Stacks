module

public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackFibred
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyUniqueness

/-! # The pullback `f⁻¹𝒮` of a stack along a morphism of sites

Let `f : 𝒟 ⟶ 𝒞` be a morphism of sites given by a continuous functor `u : 𝒞 ⥤ 𝒟` satisfying the
hypotheses and conclusions of Sites 00X6, and let `𝒮` be a stack over `(𝒞, J)`. Stacks 04WJ writes
`f⁻¹𝒮` for the stackification over `(𝒟, K)` of the fibred category `u_p 𝒮` of Stacks 04WG, and
calls it the *pullback of `𝒮` along `f`*.

The stackification is taken as data: `f⁻¹𝒮` is defined relative to a category `q : 𝒳 ⥤ 𝒟`
over `𝒟` and a functor `G : u_p 𝒮 ⥤ 𝒳`, together with the hypotheses that `q` is a stack over
`(𝒟, K)`, that `G` is a 1-morphism of fibred categories over `𝒟`, and that `G` satisfies the two
clauses of Stacks 02ZN. Given those, `Comma.pullbackStack` is `q` and `Comma.pullbackStackMap` is
`G`.

## Main definitions

* `CategoryTheory.Comma.pullbackStack`, the structure functor `f⁻¹𝒮 ⥤ 𝒟` of the pullback of `𝒮`
  along `f` (Stacks 04WJ);
* `CategoryTheory.Comma.pullbackStackMap`, the canonical 1-morphism `u_p 𝒮 ⥤ f⁻¹𝒮` exhibiting
  `f⁻¹𝒮` as the stackification (Stacks 04WJ);
* `CategoryTheory.Comma.pullbackStackEquivalence`, the equivalence of morphism categories
  expressing the universal property of `f⁻¹𝒮`.

## Main results

* `CategoryTheory.Comma.isFibered_pullbackProj_of_preservesFiniteLimits`, that the hypotheses of
  Sites 00X6 are enough for Stacks 04WG, so that `u_p 𝒮` is a fibred category over `𝒟`;
* `CategoryTheory.Comma.pullbackStack_isStack` and
  `CategoryTheory.Comma.isFibered_pullbackStack`, that `f⁻¹𝒮` is a stack, hence a fibred category,
  over `(𝒟, K)`;
* `CategoryTheory.Comma.isFibredOneMorphism_pullbackStackMap`,
  `CategoryTheory.Comma.pullbackStackMap_locallyBijective` and
  `CategoryTheory.Comma.pullbackStackMap_locally_essImage`, that `u_p 𝒮 ⥤ f⁻¹𝒮` is a 1-morphism of
  fibred categories over `𝒟` satisfying the two clauses of Stacks 02ZN;
* `CategoryTheory.Comma.restrictMor_pullbackStack_isEquivalence`, the universal property: for every
  stack `t : 𝒯 ⥤ 𝒟` over `(𝒟, K)`, restriction along `u_p 𝒮 ⥤ f⁻¹𝒮` is an equivalence
  `Mor_{Stacks/𝒟}(f⁻¹𝒮, 𝒯) ≌ Mor_{Fib/𝒟}(u_p 𝒮, 𝒯)`.

## Implementation notes

The hypotheses on `u` are those of Sites 00X6 in the form
`CategoryTheory.Functor.isMorphismOfSites_of_preservesFiniteLimits` takes them: `u` continuous,
`𝒞` finitely complete and `u` left exact. They are equivalent to the literal hypotheses of 00X6
(a final object of `𝒞` sent to a final object of `𝒟`, and fibre products preserved) by
`CategoryTheory.Functor.isMorphismOfSites_of_isTerminal`, and they imply those of Stacks 04WF and
04WG. "Stackification" is spelled out from the two clauses of Stacks 02ZN: local bijectivity of
the induced maps of the morphism presheaves of Stacks 02ZB, and local essential surjectivity on
fibres. The hypotheses that `𝒮` is a stack over `(𝒞, J)` and that `u` is continuous are not used
to produce the functor; they are named binders of the definitions, as in Stacks 04WJ.

`𝒞 : Type u₁` with `Category.{v₁} 𝒞`, `𝒟 : Type u₂` with `Category.{vb} 𝒟` and `𝒮 : Type u₃` with
`Category.{v} 𝒮` have independent universes. The morphism presheaves of Stacks 02ZB force a single
hom universe on the two sides of a 1-morphism but not on the base. Here the 1-morphism is
`u_p 𝒮 ⥤ 𝒳`, and `u_p 𝒮` has homs in `Type (max u₂ u₃ vb v)`, so that is the hom universe of the
stackification `𝒳` and of the test stack `𝒯`; their object universes remain independent. In
particular `f⁻¹𝒮` can be formed over a big site, whose objects and morphisms live in different
universes.

## References

* [Stacks 04WJ](https://stacks.math.columbia.edu/tag/04WJ);
* [Stacks 04WG](https://stacks.math.columbia.edu/tag/04WG);
* [Stacks 02ZN](https://stacks.math.columbia.edu/tag/02ZN);
* [Stacks 04W9](https://stacks.math.columbia.edu/tag/04W9);
* [Stacks 00X6](https://stacks.math.columbia.edu/tag/00X6).
-/

@[expose] public section

namespace CategoryTheory

open Limits

namespace Comma

universe v vb v₁ u₁ u₂ u₃ u₄ u₅

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{vb} 𝒟]
  {𝒮 : Type u₃} [Category.{v} 𝒮]
  {J : GrothendieckTopology 𝒞} {K : GrothendieckTopology 𝒟}

section Fibered

variable (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u]

/-- **`u_p 𝒮` is a fibred category over `𝒟` under the hypotheses of Sites 00X6.** The hypotheses of
Sites 00X6 — `𝒞` has a final object sent by `u` to a final object and has fibre products preserved
by `u`, equivalently `𝒞` is finitely complete and `u` is left exact — imply the hypotheses of
Stacks 04WF and 04WG, which ask for nonempty finite limits in `𝒞` preserved by `u`. So Stacks 04WG
applies and `u_p 𝒮` is a fibred category over `𝒟`. -/
instance isFibered_pullbackProj_of_preservesFiniteLimits : (pullbackProj p u).IsFibered :=
  haveI : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  isFibered_pullbackProj p u fun _ => inferInstance

end Fibered

section Pullback

/-- **The pullback `f⁻¹𝒮` of the stack `𝒮` along the morphism of sites `f`** (Stacks 04WJ), given
as its structure functor over `𝒟`.

`f : 𝒟 ⟶ 𝒞` is the morphism of sites attached to the continuous functor `u : 𝒞 ⥤ 𝒟` by
Sites 00X6, `𝒮` is a stack over `(𝒞, J)`, and `f⁻¹𝒮` is the stackification over `(𝒟, K)` of the
fibred category `u_p 𝒮 = Comma.pullbackLocalization p u` of Stacks 04WG. The stackification is
supplied: `q : 𝒳 ⥤ 𝒟` is a stack over `(𝒟, K)` and `G : u_p 𝒮 ⥤ 𝒳` is a 1-morphism of fibred
categories over `𝒟` satisfying the two clauses of Stacks 02ZN — local bijectivity of the induced
maps of morphism presheaves, and local essential surjectivity on fibres. Relative to that data,
`f⁻¹𝒮` is `q`. -/
@[stacks 04WJ]
def pullbackStack (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) [p.IsFibered] [HasFiniteLimits 𝒞]
    [PreservesFiniteLimits u] [u.IsContinuous J K] {𝒳 : Type u₄} [Category.{max u₂ u₃ vb v} 𝒳]
    {q : 𝒳 ⥤ 𝒟} [q.IsFibered] {G : pullbackLocalization p u ⥤ 𝒳}
    (_hs : p.IsStack J) (_hq : q.IsStack K)
    (hG : (pullbackProj p u).IsFibredOneMorphism q G)
    (_hmor : ∀ (V : 𝒟) (x y : (pullbackProj p u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap x y))
    (_hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g)) :
    𝒳 ⥤ 𝒟 :=
  q

/-- **The canonical 1-morphism `u_p 𝒮 ⥤ f⁻¹𝒮`** (Stacks 04WJ), exhibiting the pullback of `𝒮`
along `f` as the stackification of `u_p 𝒮`. -/
@[stacks 04WJ]
def pullbackStackMap (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) [p.IsFibered] [HasFiniteLimits 𝒞]
    [PreservesFiniteLimits u] [u.IsContinuous J K] {𝒳 : Type u₄} [Category.{max u₂ u₃ vb v} 𝒳]
    {q : 𝒳 ⥤ 𝒟} [q.IsFibered] {G : pullbackLocalization p u ⥤ 𝒳}
    (_hs : p.IsStack J) (_hq : q.IsStack K)
    (hG : (pullbackProj p u).IsFibredOneMorphism q G)
    (_hmor : ∀ (V : 𝒟) (x y : (pullbackProj p u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap x y))
    (_hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g)) :
    pullbackLocalization p u ⥤ 𝒳 :=
  G

variable (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u]
  [u.IsContinuous J K]
  {𝒳 : Type u₄} [Category.{max u₂ u₃ vb v} 𝒳] {q : 𝒳 ⥤ 𝒟} [q.IsFibered]
  {G : pullbackLocalization p u ⥤ 𝒳}
  (hs : p.IsStack J) (hq : q.IsStack K)
  (hG : (pullbackProj p u).IsFibredOneMorphism q G)
  (hmor : ∀ (V : 𝒟) (x y : (pullbackProj p u).Fiber V),
    Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap x y))
  (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
    (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g))

/-- **`f⁻¹𝒮` is a fibred category over `𝒟`**, being a stack over `(𝒟, K)`. -/
instance isFibered_pullbackStack : (pullbackStack p u hs hq hG hmor hobj).IsFibered := hq.isFibered

/-- The pullback `f⁻¹𝒮` is the supplied stackification `q`. -/
@[simp]
lemma pullbackStack_eq : pullbackStack p u hs hq hG hmor hobj = q := rfl

/-- The canonical 1-morphism `u_p 𝒮 ⥤ f⁻¹𝒮` is the supplied functor `G`. -/
@[simp]
lemma pullbackStackMap_eq : pullbackStackMap p u hs hq hG hmor hobj = G := rfl

/-- **`f⁻¹𝒮` is a stack over `(𝒟, K)`.** -/
lemma pullbackStack_isStack : (pullbackStack p u hs hq hG hmor hobj).IsStack K := hq

/-- The canonical morphism `u_p 𝒮 ⥤ f⁻¹𝒮` is a 1-morphism of fibred categories over `𝒟`. -/
lemma isFibredOneMorphism_pullbackStackMap :
    (pullbackProj p u).IsFibredOneMorphism (pullbackStack p u hs hq hG hmor hobj)
      (pullbackStackMap p u hs hq hG hmor hobj) := hG

/-- **Clause (1) of Stacks 02ZN for `u_p 𝒮 ⥤ f⁻¹𝒮`**: the induced maps of the morphism presheaves
of Stacks 02ZB are locally injective and locally surjective, that is, they identify the morphism
presheaves of `f⁻¹𝒮` with the sheafifications of those of `u_p 𝒮`. -/
lemma pullbackStackMap_locallyBijective (V : 𝒟) (x y : (pullbackProj p u).Fiber V) :
    Presheaf.IsLocallyInjective (K.over V)
        ((isFibredOneMorphism_pullbackStackMap p u hs hq hG hmor hobj).morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (K.over V)
        ((isFibredOneMorphism_pullbackStackMap p u hs hq hG hmor hobj).morPresheafMap x y) :=
  hmor V x y

/-- **Clause (2) of Stacks 02ZN for `u_p 𝒮 ⥤ f⁻¹𝒮`**: every object of a fibre of `f⁻¹𝒮` is, along
a covering sieve of `K`, in the essential image of the induced functor on fibres. -/
lemma pullbackStackMap_locally_essImage (V : 𝒟) (x' : q.Fiber V) :
    ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq
          (isFibredOneMorphism_pullbackStackMap p u hs hq hG hmor hobj).comp_eq W).essImage
        (Functor.pullbackFiber (pullbackStack p u hs hq hG hmor hobj) x' g) :=
  hobj V x'

/-! ### The universal property of the pullback -/

variable {𝒯 : Type u₅} [Category.{max u₂ u₃ vb v} 𝒯] {t : 𝒯 ⥤ 𝒟}

/-- **The universal property of `f⁻¹𝒮`**, Stacks 04W9 for the stackification `u_p 𝒮 ⥤ f⁻¹𝒮`.
For every stack `t : 𝒯 ⥤ 𝒟` over `(𝒟, K)`, restriction along the canonical 1-morphism
`u_p 𝒮 ⥤ f⁻¹𝒮` is an equivalence from the category of 1-morphisms `f⁻¹𝒮 ⥤ 𝒯` of fibred
categories over `𝒟` onto the category of 1-morphisms `u_p 𝒮 ⥤ 𝒯`. -/
theorem restrictMor_pullbackStack_isEquivalence (ht : t.IsStack K) :
    (Functor.restrictMor (q := t)
      (isFibredOneMorphism_pullbackStackMap p u hs hq hG hmor hobj)).IsEquivalence :=
  have := ht.isFibered
  Functor.Stackification.restrict_isEquivalence hG hmor ht.isMorSheaf hobj ht.hasEffectiveDescent

/-- **The universal property of `f⁻¹𝒮` as an equivalence of morphism categories**,
`Mor_{Stacks/𝒟}(f⁻¹𝒮, 𝒯) ≌ Mor_{Fib/𝒟}(u_p 𝒮, 𝒯)`, whose functor is restriction along the
canonical 1-morphism `u_p 𝒮 ⥤ f⁻¹𝒮`. -/
noncomputable def pullbackStackEquivalence (ht : t.IsStack K) :
    Functor.FibredMor (pullbackStack p u hs hq hG hmor hobj) t ≌
      Functor.FibredMor (pullbackProj p u) t :=
  haveI := ht.isFibered
  Functor.Stackification.restrictEquivalence hG hmor ht.isMorSheaf hobj ht.hasEffectiveDescent

end Pullback

end Comma

end CategoryTheory
