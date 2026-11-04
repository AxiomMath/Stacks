module

public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.BaseChangeShriek

/-!
# Compactly supported cohomology is independent of the compactification

Let `f : X ⟶ Y` be a separated morphism of finite type between Noetherian schemes. A
compactification of `X` over `Y` is an open immersion `j : X ⟶ X̄` with `X̄ ⟶ Y` proper, and the
construction of the previous section attaches to it the functor

`Rf_! = Rf̄_* ∘ Rj_! : D^b_{Coh}(𝒪_X) ⥤ Pro-D^b_{Coh}(𝒪_Y)`.

[Stacks, Tag 0G50] says that this is, up to isomorphism, independent of the compactification. The
argument is that the category of compactifications is cofiltered, so any two are dominated by a
third, and that a morphism of compactifications induces an isomorphism of the attached functors
by [Stacks, Tag 0G4X].

## Main definitions

* `CategoryTheory.Compactification`: the data a compactification contributes to the construction.
* `CategoryTheory.Compactification.shriekImage`: the functor `Rf_! = Rf̄_* ∘ Rj_!` it determines.

## Main results

* `CategoryTheory.Compactification.shriekImageIsoOfMorphism`: a morphism of compactifications
  induces an isomorphism of the attached functors; this is [Stacks, Tag 0G4X] followed by the
  functoriality of pushforward.
* `CategoryTheory.Compactification.shriekImageIso`: **Stacks 0G50**, the independence.

## Implementation notes

**What is assumed.** A compactification contributes exactly the data the construction uses: the
category `D^b_{Coh}(𝒪_{X̄})`, the restriction `j^*` with a Deligne system assignment (which is how
`Rj_!` exists at all, [Stacks, Tag 0G4N]), and the proper pushforward `Rf̄_*` with its right
adjoint `f̄^!`. A morphism of compactifications contributes `Rg_* ⊣ g^!` together with the two
compatibilities `j_2^* ≅ g^! ∘ j_1^*` and `g^! ∘ f̄_2^! ≅ f̄_1^!` that express `f̄_2 ∘ g = f̄_1`.
That the category of compactifications is cofiltered, which in the source is More on Flatness,
Theorem 38.33.8, is the hypothesis `CategoryTheory.IsCofiltered` on the index category.

The isomorphism produced is not canonical and the source does not claim it is: the assertion is
independence up to isomorphism, and the construction here depends on the chosen dominating
compactification `CategoryTheory.IsCofiltered.min`.

## References

* [Stacks Project, Tag 0G50](https://stacks.math.columbia.edu/tag/0G50)
* [Stacks Project, Tag 0G4X](https://stacks.math.columbia.edu/tag/0G4X)
* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u₁ u₂ u₃ u₄ w₁ w₂

namespace CategoryTheory

/-- The data one compactification `j : X ⟶ X̄` of `X` over `Y` contributes to the construction of
`Rf_!`: the bounded coherent derived category of `X̄`, the restriction `j^*` to `X` together with a
Deligne system assignment for it — which is what makes `Rj_!` exist, [Stacks, Tag 0G4N] — and the
proper pushforward `Rf̄_*` to `Y` with its right adjoint `f̄^!`. -/
public structure Compactification (𝒞 : Type u₁) [Category.{v} 𝒞] (𝒟 : Type u₂) [Category.{v} 𝒟]
    (ℳ : Type u₃) [Category.{v} ℳ] where
  /-- Restriction `j^* : D^b_{Coh}(𝒪_{X̄}) ⥤ D^b_{Coh}(𝒪_X)` along the open immersion. -/
  restrict : ℳ ⥤ 𝒞
  /-- The Deligne system assignment for `j^*`, which determines `Rj_!`. -/
  assignment : DeligneSystemAssignment restrict
  /-- The proper pushforward `Rf̄_* : D^b_{Coh}(𝒪_{X̄}) ⥤ D^b_{Coh}(𝒪_Y)`. -/
  direct : ℳ ⥤ 𝒟
  /-- Its right adjoint `f̄^!`. -/
  shriek : 𝒟 ⥤ ℳ
  /-- The adjunction, which holds because `f̄` is proper. -/
  adj : direct ⊣ shriek

namespace Compactification

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v} 𝒟]

/-- The functor `Rf_! = Rf̄_* ∘ Rj_! : D^b_{Coh}(𝒪_X) ⥤ Pro-D^b_{Coh}(𝒪_Y)` attached to a
compactification. -/
public def shriekImage {ℳ : Type u₃} [Category.{v} ℳ] (C : Compactification 𝒞 𝒟 ℳ) :
    𝒞 ⥤ ProSeq 𝒟 :=
  extensionByZero C.restrict C.assignment ⋙ ProSeq.pushforward C.adj

/-- A morphism `g : X̄₁ ⟶ X̄₂` of compactifications of `X` over `Y` induces an isomorphism of the
attached functors `Rf_!`:

`Rf̄_{2,*} ∘ Rj_{2,!} ≅ Rf̄_{2,*} ∘ Rg_* ∘ Rj_{1,!} ≅ Rf̄_{1,*} ∘ Rj_{1,!}`,

the first step being [Stacks, Tag 0G4X] and the second the identification `f̄_2 ∘ g = f̄_1`. -/
public def shriekImageIsoOfMorphism {ℳ₁ : Type u₃} [Category.{v} ℳ₁] {ℳ₂ : Type u₄}
    [Category.{v} ℳ₂] (C₁ : Compactification 𝒞 𝒟 ℳ₁) (C₂ : Compactification 𝒞 𝒟 ℳ₂)
    {gdirect : ℳ₁ ⥤ ℳ₂} {gshriek : ℳ₂ ⥤ ℳ₁} (adjg : gdirect ⊣ gshriek)
    (κ : C₂.restrict ≅ gshriek ⋙ C₁.restrict)
    (θ : C₂.shriek ⋙ gshriek ≅ C₁.shriek) :
    C₂.shriekImage ≅ C₁.shriekImage :=
  Functor.isoWhiskerRight
      (compactificationShriek adjg C₁.assignment C₂.assignment κ)
      (ProSeq.pushforward C₂.adj) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (extensionByZero C₁.restrict C₁.assignment)
      (ProSeq.pushforwardIso (adjg.comp C₂.adj) C₁.adj θ)

/-- **Stacks Project, Tag 0G50.** The functor `Rf_!` is, up to isomorphism, independent of the
choice of the compactification.

The compactifications of `X` over `Y` are the objects of a cofiltered category `𝒦`, each carrying
the data of a `CategoryTheory.Compactification`, and each morphism of `𝒦` induces an isomorphism
of the attached functors `Rf_!` — the isomorphism of [Stacks, Tag 0G4X], produced by
`CategoryTheory.Compactification.shriekImageIsoOfMorphism`. Any two compactifications are then
dominated by a third, and the two isomorphisms to it compose to one between them. -/
@[stacks 0G50 "the per-compactification data, the cofilteredness of the category of \
compactifications, and the isomorphisms attached to its morphisms by Tag 0G4X, supplied as data"]
public def shriekImageIso {𝒦 : Type w₁} [Category.{w₂} 𝒦] [IsCofiltered 𝒦] {ℳ : 𝒦 → Type u₃}
    [∀ c, Category.{v} (ℳ c)] (C : ∀ c, Compactification 𝒞 𝒟 (ℳ c))
    (e : ∀ {c c' : 𝒦}, (c ⟶ c') → ((C c').shriekImage ≅ (C c).shriekImage)) (c c' : 𝒦) :
    (C c).shriekImage ≅ (C c').shriekImage :=
  e (IsCofiltered.minToLeft c c') ≪≫ (e (IsCofiltered.minToRight c c')).symm

end Compactification

end CategoryTheory

end
