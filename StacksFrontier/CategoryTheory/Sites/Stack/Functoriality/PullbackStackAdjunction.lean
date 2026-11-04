module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackAdjunction
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStack

/-! # The pullback of a stack is adjoint to the pushforward

Let `f : 𝒟 ⟶ 𝒞` be the morphism of sites given by a continuous functor `u : 𝒞 ⥤ 𝒟` satisfying the
conditions of Sites 00X6, let `p : 𝒮 ⥤ 𝒞` be a fibred category and let `q : 𝒯 ⥤ 𝒟` be a stack.
The pushforward `f_*𝒯 = u^p 𝒯` is the strict pullback of `u` and `q` (Stacks 04WB, a stack by
Stacks 04WC), and the pullback `f⁻¹𝒮` is the stackification of the fibred category `u_p 𝒮` of
Stacks 04WG (Stacks 04WJ). Stacks 04WK says that the two are adjoint at the level of the
2-categories of stacks:

`Mor_{Stacks/𝒞}(𝒮, f_*𝒯) ≃ Mor_{Stacks/𝒟}(f⁻¹𝒮, 𝒯)`.

This file proves that, in the form `04WI ∘ 04W9`, which is the source's own proof.

## Main results

* `CategoryTheory.Functor.equivalenceFibredMorStrictPullbackStackification`: the canonical
  equivalence of the two morphism categories (Stacks 04WK);
* `CategoryTheory.Functor.equivalenceFibredMorPushforwardPullbackStack`: the same equivalence
  written with the pushforward `f_*𝒯` named by Stacks 04WE and the pullback `f⁻¹𝒮` named by
  Stacks 04WJ, under the hypotheses of Sites 00X6 and with both `𝒮` and `𝒯` assumed to be stacks
  (Stacks 04WK);
* `CategoryTheory.Functor.equivalenceFibredMorStrictPullbackStackificationUniv` and
  `CategoryTheory.Functor.equivalenceFibredMorPushforwardPullbackStackUniv`: the same two
  equivalences with the hom universes of `𝒟` and `𝒮` free.

## Main definitions

* `CategoryTheory.Functor.FibredMor.basedEquivalence`: the identification of the morphism category
  `CategoryTheory.Functor.FibredMor` of Stacks 02ZG with the full subcategory of based functors
  cut out by `CategoryTheory.Functor.IsFibredOneMorphism`, which is the spelling of the same
  morphism category used in Stacks 04WI.

## Implementation notes

The statement is *conditional on being given a stackification*. Stacks 02ZN constructs, for every
fibred category over a site, a stackification; that construction is not yet assembled in this
tree, so — exactly as in
`StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyFunctor` (Stacks 0435) and
`StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid` (Stacks 04Y2) — a
1-morphism `G : u_p 𝒮 ⥤ 𝒮'` exhibiting `𝒮'` as the stackification of `u_p 𝒮` is *hypothesised*,
by the unfolded clauses of Stacks 02ZN: `hG` that `G` is a 1-morphism of fibred categories over
`𝒟`, `hmor` that the maps of morphism presheaves it induces are locally injective and locally
surjective, and `hobj` that every object of a fibre of `𝒮'` is locally in the essential image of
`G`. Once Stacks 02ZN is assembled it supplies `𝒮'`, `G`, `hmor` and `hobj`, and `𝒮' = f⁻¹𝒮` is
the pullback of Stacks 04WJ. The conclusion is data, an equivalence of categories, not the
assertion that one exists.

The proof is the composite of Stacks 04WI and Stacks 04W9 and nothing else: 04WI identifies
`Mor_{Fib/𝒞}(𝒮, u^p 𝒯)` with `Mor_{Fib/𝒟}(u_p 𝒮, 𝒯)`, and 04W9 identifies the latter with
`Mor_{Fib/𝒟}(𝒮', 𝒯)` by restriction along the stackification `G`. The only bookkeeping is
`CategoryTheory.Functor.FibredMor.basedEquivalence`: 04WI spells a morphism category as the full
subcategory of `CategoryTheory.BasedFunctor`s satisfying
`CategoryTheory.Functor.IsFibredOneMorphism`, while 04W9 spells it as
`CategoryTheory.Functor.FibredMor`. The two are the same data — a functor, a proof that it is
strictly over the base, and a proof that it preserves strongly cartesian morphisms, with the
morphisms of functors whose components lie over identities — so the comparison is an equivalence
all of whose structure maps are identities.

Faithfulness of the formalization. (1) Hypotheses. `p.IsFibered`, `HasNonemptyFiniteLimits 𝒞` and
`hu` are the content of Sites 00X6 that the statement uses: they are what make `u_p 𝒮` a fibred
category over `𝒟` (Stacks 04WG) and what Stacks 04WI needs. Continuity of `u` is not assumed: it
enters Stacks 04WK only to know that `f_*𝒯` is a stack (Stacks 04WC) and that `f⁻¹𝒮` exists
(Stacks 04WJ), and here the latter is hypothesised and the former is not used. That `𝒯` is a
stack is assumed, in the unbundled form `q.IsFibered`, `hqmor`, `hdesc` of Stacks 026F, because
Stacks 04W9 needs all three. That `𝒮` is a stack is *not* assumed: by Stacks 02ZG the morphism
category of two stacks over `𝒞` is the morphism category of the underlying fibred categories, so
the equivalence holds for `𝒮` merely fibred, and the statement is therefore stronger than the
source's. The specialization
`CategoryTheory.Functor.equivalenceFibredMorPushforwardPullbackStack` restores all of the source's
hypotheses: it assumes `𝒮` is a stack, spells Sites 00X6 as `Limits.HasFiniteLimits 𝒞`,
`Limits.PreservesFiniteLimits u` and `u.IsContinuous J K` as
`StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStack` (Stacks 04WJ) does, and names
the two sides `f_*𝒯` and `f⁻¹𝒮`. (2) The bases are the source's: the left-hand morphism category
is taken over `𝒞`, the
right-hand one over `𝒟`. (3) Both sides are `CategoryTheory.Functor.FibredMor`, the morphism
category of Stacks 02ZG, which for stacks is the morphism category of the 2-category of stacks by
Stacks 02ZG; it is not the hom-category of `CategoryTheory.BasedStack`, which bundles all of its
objects into one pair of universes and could not state the result at this generality.

Universes. The hom universes of `𝒟`, `𝒮`, `𝒯` and `𝒮'` are tied to one another because Stacks
04W9 has a single hom universe for the four categories involved in it, and `u_p 𝒮` is one of them:
`Comma (𝟭 𝒟) (p ⋙ u)` has homs in `Type (max v₂ v₃)` and its localization has homs in
`Type (max u₂ u₃ v₂ v₃)`, so the shared hom universe must absorb the object universes of `𝒟` and
`𝒮`. Writing it as `max u₂ u₃ w` for a free `w` is the least such choice. The base `𝒞` keeps an
independent universe pair, and the object universes of `𝒟`, `𝒮`, `𝒯` and `𝒮'` are independent.
No `UnivLE` hypothesis occurs.

The `Univ` forms of the two equivalences tie only the hom universes Stacks 04W9 needs tied: the
categories `u_p 𝒮`, `𝒯` and `𝒮'`, so `𝒯` and `𝒮'` carry `Category.{max u₂ u₃ v₂ v₃}` while the
hom universes `v₂` and `v₃` of `𝒟` and `𝒮` are free. A site whose morphisms are small, such as a
big site, then has hom universe `v₂` smaller than the shared one, which the forms above exclude.

## References

* [Stacks 04WK](https://stacks.math.columbia.edu/tag/04WK);
* [Stacks 04WI](https://stacks.math.columbia.edu/tag/04WI);
* [Stacks 04W9](https://stacks.math.columbia.edu/tag/04W9);
* [Stacks 04WJ](https://stacks.math.columbia.edu/tag/04WJ);
* [Stacks 02ZN](https://stacks.math.columbia.edu/tag/02ZN);
* [Sites 00X6](https://stacks.math.columbia.edu/tag/00X6).
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

namespace FibredMor

/-! ### The morphism category as a full subcategory of based functors -/

section Based

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  {𝒳 : Type u₃} [Category.{v₃} 𝒳] (p : 𝒮 ⥤ 𝒞) (q : 𝒳 ⥤ 𝒞)

/-- A 1-morphism of fibred categories over `𝒞`, read as a based functor satisfying
`Functor.IsFibredOneMorphism`. -/
@[implicit_reducible]
def toBased : FibredMor p q ⥤
    ObjectProperty.FullSubcategory
      (fun G : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q =>
        Functor.IsFibredOneMorphism p q G.toFunctor) where
  obj K := ⟨⟨K.functor, K.isFibredOneMorphism.comp_eq⟩, K.isFibredOneMorphism⟩
  map α := ⟨⟨α.trans, α.isHomLift⟩⟩

/-- A based functor satisfying `Functor.IsFibredOneMorphism`, read as an object of the morphism
category. -/
@[implicit_reducible]
def ofBased :
    ObjectProperty.FullSubcategory
        (fun G : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q =>
          Functor.IsFibredOneMorphism p q G.toFunctor) ⥤
      FibredMor p q where
  obj K := ⟨K.obj.toFunctor, K.property⟩
  map α := ⟨α.hom.toNatTrans, fun A => α.hom.isHomLift' A⟩

/-- **The morphism category `Mor_{Fib/𝒞}(𝒮, 𝒳)` of Stacks 02ZG is the full subcategory of the
category of based functors cut out by `Functor.IsFibredOneMorphism`.** Both are a functor `𝒮 ⥤ 𝒳`
together with a proof that it is strictly over `𝒞` and preserves strongly cartesian morphisms,
with the morphisms of functors whose components lie over identities as morphisms, so every
structure map of the equivalence is an identity. -/
def basedEquivalence : FibredMor p q ≌
    ObjectProperty.FullSubcategory
      (fun G : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q =>
        Functor.IsFibredOneMorphism p q G.toFunctor) where
  functor := toBased p q
  inverse := ofBased p q
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp K := by
    simp

end Based

end FibredMor

/-! ### The adjunction -/

section Adjunction

universe w v₁ u₁ u₂ u₃ u₄ u₅

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{max u₂ u₃ w} 𝒟]
  {𝒮 : Type u₃} [Category.{max u₂ u₃ w} 𝒮] {𝒯 : Type u₄} [Category.{max u₂ u₃ w} 𝒯]
  {𝒮' : Type u₅} [Category.{max u₂ u₃ w} 𝒮']
  (u : 𝒞 ⥤ 𝒟) (p : 𝒮 ⥤ 𝒞) (q : 𝒯 ⥤ 𝒟) {p' : 𝒮' ⥤ 𝒟}
  {K : GrothendieckTopology 𝒟} {G : Comma.pullbackLocalization p u ⥤ 𝒮'}
  [p.IsFibered] [q.IsFibered] [p'.IsFibered] [HasNonemptyFiniteLimits 𝒞]
  [(Comma.pullbackProj p u).IsFibered]

/-- **The pullback of a stack along `f` is adjoint to the pushforward along `f`** (Stacks 04WK).
Let `f : 𝒟 ⟶ 𝒞` be the morphism of sites given by a functor `u : 𝒞 ⥤ 𝒟` as in Sites 00X6, let
`p : 𝒮 ⥤ 𝒞` be a fibred category and let `q : 𝒯 ⥤ 𝒟` be a stack. Let `G : u_p 𝒮 ⥤ 𝒮'` exhibit
`𝒮'` as the stackification of the pullback `u_p 𝒮` of Stacks 04WG, in the sense of Stacks 02ZN, so
that `𝒮' = f⁻¹𝒮` is the pullback of Stacks 04WJ. Then the morphism category
`Mor_{Stacks/𝒞}(𝒮, f_*𝒯)` of 1-morphisms `𝒮 ⟶ f_*𝒯` over `𝒞` and their 2-morphisms is
canonically equivalent to the morphism category `Mor_{Stacks/𝒟}(f⁻¹𝒮, 𝒯)`, where `f_*𝒯 = u^p 𝒯`
is the pushforward of Stacks 04WB. The equivalence is the composite of Stacks 04WI, the same
adjunction at the level of fibred categories, with Stacks 04W9, restriction along the
stackification `G`.

This statement is *conditional on being given a stackification* `G`: its hypotheses are the
unfolded clauses of Stacks 02ZN, which that construction supplies once it is assembled. -/
@[stacks 04WK]
noncomputable def equivalenceFibredMorStrictPullbackStackification
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    (hG : (Comma.pullbackProj p u).IsFibredOneMorphism p' G)
    (hmor : ∀ (V : 𝒟) (x y : (Comma.pullbackProj p u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap x y))
    (hqmor : ∀ (V : 𝒟) (x y : q.Fiber V), IsMorSheaf q K V x y)
    (hobj : ∀ (V : 𝒟) (x' : p'.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃f : W ⟶ V⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq W).essImage (pullbackFiber p' x' f))
    (hdesc : HasEffectiveDescent q K) :
    FibredMor p (StrictPullback.structureFunctor u q) ≌ FibredMor p' q :=
  (FibredMor.basedEquivalence p (StrictPullback.structureFunctor u q)).trans
    ((equivalenceIsFibredOneMorphismStrictPullbackPullbackLocalization u p q hu).trans
      ((FibredMor.basedEquivalence (Comma.pullbackProj p u) q).symm.trans
        (Stackification.restrictEquivalence hG hmor hqmor hobj hdesc).symm))

end Adjunction

/-! ### The adjunction in the notation of Stacks 04WE and 04WJ -/

section Named

universe v v₁ u₁ u₄ u₅

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type v} [Category.{v} 𝒟]
  {𝒮 : Type v} [Category.{v} 𝒮] {𝒳 : Type u₄} [Category.{v} 𝒳] {𝒯 : Type u₅} [Category.{v} 𝒯]
  (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟) (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)
  [p.IsFibered] [Limits.HasFiniteLimits 𝒞] [Limits.PreservesFiniteLimits u] [u.IsContinuous J K]
  {q : 𝒳 ⥤ 𝒟} [q.IsFibered] {G : Comma.pullbackLocalization p u ⥤ 𝒳} {t : 𝒯 ⥤ 𝒟} [t.IsFibered]

/-- **Stacks 04WK**, written with the pushforward `f_*𝒯` of Stacks 04WE and the pullback `f⁻¹𝒮`
of Stacks 04WJ. Let `f : 𝒟 ⟶ 𝒞` be the morphism of sites attached by Sites 00X6 to a continuous
functor `u : 𝒞 ⥤ 𝒟` between a finitely complete `(𝒞, J)` and `(𝒟, K)` which is left exact, let
`𝒮` be a stack over `(𝒞, J)` and let `𝒯` be a stack over `(𝒟, K)`. Then

`Mor_{Stacks/𝒞}(𝒮, f_*𝒯) ≃ Mor_{Stacks/𝒟}(f⁻¹𝒮, 𝒯)`.

The pullback `f⁻¹𝒮` is represented by the supplied stackification of `u_p 𝒮`: the stack
`q : 𝒳 ⥤ 𝒟` and the 1-morphism `G : u_p 𝒮 ⥤ 𝒳` satisfying the clauses `hG`,
`hmor`, `hobj` of Stacks 02ZN. So this statement too is conditional on being given a
stackification, which Stacks 02ZN supplies once assembled.

The instance `[t.IsFibered]` is implied by `ht` and is taken separately only because the notation
`f_*𝒯` of Stacks 04WE needs it to elaborate. -/
@[stacks 04WK]
noncomputable def equivalenceFibredMorPushforwardPullbackStack
    (hs : p.IsStack J) (hq : q.IsStack K)
    (hG : (Comma.pullbackProj p u).IsFibredOneMorphism q G)
    (hmor : ∀ (V : 𝒟) (x y : (Comma.pullbackProj p u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap x y))
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (fiberFunctorOfCompEq hG.comp_eq W).essImage (pullbackFiber q x' g))
    (ht : t.IsStack K) :
    FibredMor p (pushforwardFibredCategory J K u t) ≌ FibredMor q t :=
  letI : p.IsFibered := hs.isFibered
  letI : q.IsFibered := hq.isFibered
  haveI : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  equivalenceFibredMorStrictPullbackStackification u p t (fun _ => inferInstance) hG hmor
    ht.isMorSheaf hobj ht.hasEffectiveDescent

end Named

/-! ### The adjunction, with free hom universes for `𝒟` and `𝒮` -/

section AdjunctionUniv

universe v₁ v₂ v₃ u₁ u₂ u₃ u₄ u₅

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮] {𝒯 : Type u₄} [Category.{max u₂ u₃ v₂ v₃} 𝒯]
  {𝒮' : Type u₅} [Category.{max u₂ u₃ v₂ v₃} 𝒮']
  (u : 𝒞 ⥤ 𝒟) (p : 𝒮 ⥤ 𝒞) (q : 𝒯 ⥤ 𝒟) {p' : 𝒮' ⥤ 𝒟}
  {K : GrothendieckTopology 𝒟} {G : Comma.pullbackLocalization p u ⥤ 𝒮'}
  [p.IsFibered] [q.IsFibered] [p'.IsFibered] [HasNonemptyFiniteLimits 𝒞]
  [(Comma.pullbackProj p u).IsFibered]

/-- **The pullback of a stack along `f` is adjoint to the pushforward along `f`** (Stacks 04WK),
with the hom universes of `𝒟` and `𝒮` free. Let `f : 𝒟 ⟶ 𝒞` be the morphism of sites given by a
functor `u : 𝒞 ⥤ 𝒟` as in Sites 00X6, let `p : 𝒮 ⥤ 𝒞` be a fibred category and let `q : 𝒯 ⥤ 𝒟` be a
stack. Let `G : u_p 𝒮 ⥤ 𝒮'` exhibit `𝒮'` as the stackification of the pullback `u_p 𝒮` of Stacks
04WG, in the sense of Stacks 02ZN, so that `𝒮' = f⁻¹𝒮` is the pullback of Stacks 04WJ. Then the
morphism category `Mor_{Stacks/𝒞}(𝒮, f_*𝒯)` of 1-morphisms `𝒮 ⟶ f_*𝒯` over `𝒞` and their
2-morphisms is canonically equivalent to the morphism category `Mor_{Stacks/𝒟}(f⁻¹𝒮, 𝒯)`, where
`f_*𝒯 = u^p 𝒯` is the pushforward of Stacks 04WB. The equivalence is the composite of Stacks 04WI,
the same adjunction at the level of fibred categories, with Stacks 04W9, restriction along the
stackification `G`.

This statement is *conditional on being given a stackification* `G`: its hypotheses are the
unfolded clauses of Stacks 02ZN, which that construction supplies once it is assembled. -/
noncomputable def equivalenceFibredMorStrictPullbackStackificationUniv
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    (hG : (Comma.pullbackProj p u).IsFibredOneMorphism p' G)
    (hmor : ∀ (V : 𝒟) (x y : (Comma.pullbackProj p u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap x y))
    (hqmor : ∀ (V : 𝒟) (x y : q.Fiber V), IsMorSheaf q K V x y)
    (hobj : ∀ (V : 𝒟) (x' : p'.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃f : W ⟶ V⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq W).essImage (pullbackFiber p' x' f))
    (hdesc : HasEffectiveDescent q K) :
    FibredMor p (StrictPullback.structureFunctor u q) ≌ FibredMor p' q :=
  (FibredMor.basedEquivalence p (StrictPullback.structureFunctor u q)).trans
    ((equivalenceIsFibredOneMorphismStrictPullbackPullbackLocalization u p q hu).trans
      ((FibredMor.basedEquivalence (Comma.pullbackProj p u) q).symm.trans
        (Stackification.restrictEquivalence hG hmor hqmor hobj hdesc).symm))

end AdjunctionUniv

/-! ### The adjunction in the notation of Stacks 04WE and 04WJ, with free hom universes -/

section NamedUniv

universe v₁ v₂ v₃ u₁ u₂ u₃ u₄ u₅

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮] {𝒳 : Type u₄} [Category.{max u₂ u₃ v₂ v₃} 𝒳]
  {𝒯 : Type u₅} [Category.{max u₂ u₃ v₂ v₃} 𝒯]
  (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟) (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)
  [p.IsFibered] [Limits.HasFiniteLimits 𝒞] [Limits.PreservesFiniteLimits u] [u.IsContinuous J K]
  {q : 𝒳 ⥤ 𝒟} [q.IsFibered] {G : Comma.pullbackLocalization p u ⥤ 𝒳} {t : 𝒯 ⥤ 𝒟} [t.IsFibered]

/-- **Stacks 04WK**, written with the pushforward `f_*𝒯` of Stacks 04WE and the pullback `f⁻¹𝒮` of
Stacks 04WJ, with the hom universes of `𝒟` and `𝒮` free. Let `f : 𝒟 ⟶ 𝒞` be the morphism of sites
attached by Sites 00X6 to a continuous functor `u : 𝒞 ⥤ 𝒟` between a finitely complete `(𝒞, J)` and
`(𝒟, K)` which is left exact, let `𝒮` be a stack over `(𝒞, J)` and let `𝒯` be a stack over
`(𝒟, K)`. Then

`Mor_{Stacks/𝒞}(𝒮, f_*𝒯) ≃ Mor_{Stacks/𝒟}(f⁻¹𝒮, 𝒯)`.

The pullback `f⁻¹𝒮` is represented by the supplied stackification of `u_p 𝒮`: the stack `q : 𝒳 ⥤ 𝒟`
and the 1-morphism `G : u_p 𝒮 ⥤ 𝒳` satisfying the clauses `hG`, `hmor`, `hobj` of Stacks 02ZN. So
this statement too is conditional on being given a stackification, which Stacks 02ZN supplies once
assembled.

The instance `[t.IsFibered]` is implied by `ht` and is taken separately only because the notation
`f_*𝒯` of Stacks 04WE needs it to elaborate. -/
noncomputable def equivalenceFibredMorPushforwardPullbackStackUniv
    (hs : p.IsStack J) (hq : q.IsStack K)
    (hG : (Comma.pullbackProj p u).IsFibredOneMorphism q G)
    (hmor : ∀ (V : 𝒟) (x y : (Comma.pullbackProj p u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap x y))
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (fiberFunctorOfCompEq hG.comp_eq W).essImage (pullbackFiber q x' g))
    (ht : t.IsStack K) :
    FibredMor p (pushforwardFibredCategory J K u t) ≌ FibredMor q t :=
  letI : p.IsFibered := hs.isFibered
  letI : q.IsFibered := hq.isFibered
  haveI : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  equivalenceFibredMorStrictPullbackStackificationUniv u p t (fun _ => inferInstance) hG hmor
    ht.isMorSheaf hobj ht.hasEffectiveDescent

end NamedUniv

end Functor

end CategoryTheory

end
