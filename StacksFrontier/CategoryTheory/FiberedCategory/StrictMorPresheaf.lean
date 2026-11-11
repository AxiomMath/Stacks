module

public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap

/-!
# The presheaf `Mor(x, y)` through a split model (Stacks 02ZA)

Stacks Remark 02ZA gives a second proof of Stacks 026A (that `Mor(x, y)` is a presheaf on `𝒞/U`)
for a category `p : 𝒮 ⥤ 𝒞` fibred in groupoids. By Stacks 004A (in the groupoid form Stacks
02XY, `CategoryTheory.Functor.exists_isFibredEquivalenceOver_presheafOfGroupoids`) `𝒮` is
equivalent to the fibred category of a contravariant functor `F : 𝒞 ⥤ Groupoids`. For that
fibred category `g^* ∘ f^* = (f ∘ g)^*` on the nose, so the restriction maps of `Mor(x, y)` need
no comparison isomorphisms `α_{g, f}` and the lemma is trivial; and `Mor(x, y)` is unchanged when
passing to an equivalent fibred category, by Stacks 042V.

The three ingredients are registered under 02ZA:

* `CategoryTheory.strictMorPresheaf` (in
  `StacksFrontier/CategoryTheory/FiberedCategory/Strictification.lean`): for an honest functor
  `F : 𝒞ᵒᵖ ⥤ Cat`, the presheaf `Mor(x, y)` on `𝒞/U` whose restriction maps are the functors
  `F(h)`, its presheaf axioms being `F.map_id` and `F.map_comp`;
* `CategoryTheory.Functor.IsFibredEquivalenceOver.isIso_morPresheafMap` (here): the map
  `Mor(x, y) ⟶ Mor(G x, G y)` of Stacks 042V along an equivalence `G` of fibred categories is an
  isomorphism of presheaves;
* `CategoryTheory.Functor.morPresheafIsoStrictMorPresheafGrpd` (here): for `p` fibred in
  groupoids, the presheaf `Mor(x, y)` of Stacks 02ZB is isomorphic to the strict presheaf
  `Mor((x, id), (y, id))` of the split model `splitPresheafGrpd p hp : 𝒞ᵒᵖ ⥤ Grpd` of 02XY. It
  is `CategoryTheory.Functor.morPresheafIsoStrictMorPresheaf`, which holds for every fibred
  category.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe v₁ v₂ u₁ u₂ u₃

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-! ### `Mor(x, y)` is unchanged along an equivalence of fibred categories -/

namespace IsFibredEquivalenceOver

variable {𝒴 : Type u₃} [Category.{v₂} 𝒴] {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {G : 𝒳 ⥤ 𝒴}

/-- The underlying functor of an equivalence of fibred categories is an equivalence of
categories. -/
lemma isEquivalence (hG : IsFibredEquivalenceOver p q G) : G.IsEquivalence := by
  obtain ⟨H, -, η, -, ε, -⟩ := hG.exists_inverse
  exact (Equivalence.mk G H η ε).isEquivalence_functor

/-- On the fibres, an equivalence of fibred categories is full. -/
lemma fiberFunctor_map_surjective (hG : IsFibredEquivalenceOver p q G) {V : 𝒞}
    {a b : p.Fiber V}
    (ψ : (fiberFunctorOfCompEq hG.isFibredOneMorphism.comp_eq V).obj a ⟶
      (fiberFunctorOfCompEq hG.isFibredOneMorphism.comp_eq V).obj b) :
    ∃ φ : a ⟶ b, (fiberFunctorOfCompEq hG.isFibredOneMorphism.comp_eq V).map φ = ψ := by
  have := hG.isEquivalence
  let u : G.obj a.1 ⟶ G.obj b.1 := Fiber.fiberInclusion.map ψ
  have hu : q.IsHomLift (𝟙 V) u := ψ.2
  have hψ : q.IsHomLift (𝟙 V) (G.map (G.preimage u)) := by
    rw [G.map_preimage]
    exact hu
  have : p.IsHomLift (𝟙 V) (G.preimage u) :=
    isHomLift_of_isHomLift_map hG.isFibredOneMorphism.comp_eq (𝟙 V) _
  exact ⟨⟨G.preimage u, this⟩, Fiber.hom_ext (G.map_preimage u)⟩

/-- On the fibres, an equivalence of fibred categories is faithful. -/
lemma fiberFunctor_map_injective (hG : IsFibredEquivalenceOver p q G) {V : 𝒞}
    {a b : p.Fiber V} {φ φ' : a ⟶ b}
    (h : (fiberFunctorOfCompEq hG.isFibredOneMorphism.comp_eq V).map φ =
      (fiberFunctorOfCompEq hG.isFibredOneMorphism.comp_eq V).map φ') : φ = φ' := by
  have := hG.isEquivalence
  exact Fiber.hom_ext (G.map_injective (congrArg Fiber.fiberInclusion.map h))

variable [p.IsFibered] [q.IsFibered]

/-- **`Mor(x, y)` is unchanged along an equivalence of fibred categories** (Stacks 02ZA, from
Stacks 042V). If `G : 𝒳 ⥤ 𝒴` is an equivalence in the 2-category of fibred categories over `𝒞`,
then the map of presheaves `Mor(x, y) ⟶ Mor(G x, G y)` of Stacks 042V is an isomorphism. -/
@[stacks 02ZA "Mor(x, y) is unchanged when passing to an equivalent fibred category: the map of \
  042V along an equivalence of fibred categories is an isomorphism of presheaves"]
theorem isIso_morPresheafMap (hG : IsFibredEquivalenceOver p q G) {U : 𝒞} (a b : p.Fiber U) :
    IsIso (hG.isFibredOneMorphism.morPresheafMap a b) := by
  suffices ∀ g, IsIso ((hG.isFibredOneMorphism.morPresheafMap a b).app g) from
    NatIso.isIso_of_isIso_app _
  intro g
  rw [isIso_iff_bijective]
  refine ⟨fun m m' hmm' => ?_, fun n => ?_⟩
  · simp only [IsFibredOneMorphism.morPresheafMap_app] at hmm'
    exact hG.fiberFunctor_map_injective ((cancel_mono _).1 ((cancel_epi _).1 hmm'))
  · obtain ⟨φ, hφ⟩ := hG.fiberFunctor_map_surjective
      ((hG.isFibredOneMorphism.mapPullbackFiberIso a g.unop.hom).inv ≫ n ≫
        (hG.isFibredOneMorphism.mapPullbackFiberIso b g.unop.hom).hom)
    refine ⟨φ, ?_⟩
    simp [IsFibredOneMorphism.morPresheafMap_app, hφ]

end IsFibredEquivalenceOver

/-! ### Stacks 02ZA -/

section Split

variable (p : 𝒳 ⥤ 𝒞) [p.IsFibered] {U : 𝒞}

/-- **Stacks 02ZA.** Let `p : 𝒳 ⥤ 𝒞` be fibred in groupoids, and let `x`, `y` be objects of the
fibre over `U`. By Stacks 02XY (the groupoid case of Stacks 004A) `p` is equivalent to the fibred
category of the functor `F = splitPresheafGrpd p hp : 𝒞ᵒᵖ ⥤ Grpd`, and the presheaf `Mor(x, y)`
of `p` is isomorphic to the presheaf `Mor((x, id), (y, id))` of that split model, whose
restriction maps are the functors `F(h)` and need no comparison isomorphisms. -/
@[stacks 02ZA "Mor(x, y) of a category fibred in groupoids is the strict Mor presheaf of the \
  split model F : 𝒞ᵒᵖ ⥤ Grpd of 004A, whose restriction maps are the functors F(h) with \
  g^* ∘ f^* = (f ∘ g)^* on the nose"]
noncomputable def morPresheafIsoStrictMorPresheafGrpd (hp : p.IsFiberedInGroupoids)
    (x y : p.Fiber U) :
    morPresheaf p x y ≅
      strictMorPresheaf (splitPresheafGrpd p hp ⋙ Grpd.forgetToCat)
        (SplitFiber.ofFiber p x) (SplitFiber.ofFiber p y) :=
  morPresheafIsoStrictMorPresheaf p x y

end Split

end Functor

end CategoryTheory
