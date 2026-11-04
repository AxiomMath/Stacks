module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-!
# 1-morphisms of fibred categories over a base

Fix a base category `𝒞`. A *category over `𝒞`* is a functor `p : 𝒳 ⥤ 𝒞`, its *structure
functor*. A *1-morphism of fibred categories over `𝒞`* from `p : 𝒳 ⥤ 𝒞` to `q : 𝒴 ⥤ 𝒞`
is a functor `G : 𝒳 ⥤ 𝒴` which is *strictly over `𝒞`*, meaning `G ⋙ q = p`, and which
*preserves strongly cartesian morphisms*: if `φ` is strongly cartesian for `p` over a
morphism `f` of `𝒞`, then `G.map φ` is strongly cartesian for `q` over the same `f`
(this makes sense precisely because `G` is strictly over `𝒞`). This is item (2) of
Stacks Definition 4.33.9.

Mathlib has `Functor.IsStronglyCartesian` and `Functor.IsFibered` but no predicate for a
morphism of fibred categories, so it is defined here as `Functor.IsFibredOneMorphism`,
once, as the shared vocabulary of the Section 4.33 and 4.34 results (the 2-fibre product
of Stacks 02XQ, the amelioration of Stacks 08NF, the inertia of Stacks 034H). Being
strictly over `𝒞` is already enough to transport the weaker predicate `IsHomLift` along
`G`, which is `isHomLift_map_of_comp_eq`.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- A functor `G` strictly over `𝒞` transports `IsHomLift` from the source structure
functor to the target one: if `φ` lies over `f` for `p`, then `G.map φ` lies over the
same `f` for `q`. -/
lemma isHomLift_map_of_comp_eq {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {G : 𝒳 ⥤ 𝒴} (hG : G ⋙ q = p)
    {R T : 𝒞} (f : R ⟶ T) {a b : 𝒳} (φ : a ⟶ b) [p.IsHomLift f φ] :
    q.IsHomLift f (G.map φ) := by
  subst hG
  obtain ⟨⟩ := ‹(G ⋙ q).IsHomLift f φ›
  exact IsHomLift.map (p := q) (G.map φ)

/-- A *1-morphism of fibred categories over `𝒞`* (Stacks Definition 4.33.9 (2)) from
`p : 𝒳 ⥤ 𝒞` to `q : 𝒴 ⥤ 𝒞`: a functor `G : 𝒳 ⥤ 𝒴` strictly over `𝒞` which preserves
strongly cartesian morphisms. -/
structure IsFibredOneMorphism (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (G : 𝒳 ⥤ 𝒴) : Prop where
  /-- `G` is strictly over `𝒞`. -/
  comp_eq : G ⋙ q = p
  /-- `G` preserves strongly cartesian morphisms. -/
  map_isStronglyCartesian : ∀ {R T : 𝒞} (f : R ⟶ T) {a b : 𝒳} (φ : a ⟶ b),
    p.IsStronglyCartesian f φ → q.IsStronglyCartesian f (G.map φ)

namespace IsFibredOneMorphism

variable {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {G : 𝒳 ⥤ 𝒴}

/-- A 1-morphism of fibred categories transports `IsHomLift` along `G`. -/
lemma map_isHomLift (hG : IsFibredOneMorphism p q G) {R T : 𝒞} (f : R ⟶ T) {a b : 𝒳}
    (φ : a ⟶ b) [p.IsHomLift f φ] : q.IsHomLift f (G.map φ) :=
  isHomLift_map_of_comp_eq hG.comp_eq f φ

/-- The identity functor is a 1-morphism of fibred categories over `𝒞`. -/
lemma id (p : 𝒳 ⥤ 𝒞) : IsFibredOneMorphism p p (𝟭 𝒳) where
  comp_eq := rfl
  map_isStronglyCartesian := by intros; assumption

/-- A composite of 1-morphisms of fibred categories over `𝒞` is a 1-morphism of fibred
categories over `𝒞`. -/
lemma comp {𝒵 : Type*} [Category 𝒵] {r : 𝒵 ⥤ 𝒞} {H : 𝒴 ⥤ 𝒵}
    (hG : IsFibredOneMorphism p q G) (hH : IsFibredOneMorphism q r H) :
    IsFibredOneMorphism p r (G ⋙ H) where
  comp_eq := by rw [Functor.assoc, hH.comp_eq, hG.comp_eq]
  map_isStronglyCartesian := by
    intro _ _ f _ _ φ h
    exact hH.map_isStronglyCartesian f (G.map φ) (hG.map_isStronglyCartesian f φ h)

end IsFibredOneMorphism

end CategoryTheory.Functor
