module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GoodDiagramExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SystemMorphismOfAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.LimitDescriptionIsomorphism

/-!
# Limit descriptions of spaces of finite type over a Noetherian limit

In Situation 0CP6, Stacks 0CPB remarks that Stacks 0CP7, 0CP9 and 0CPA together say that the
category of algebraic spaces quasi-separated and of finite type over `B = lim_i B_i` is equivalent
to the inverse systems over `(B_i)` produced by Stacks 0CP9 from a diagram as in Stacks 0CP8:

* every such `X ⟶ B` has a diagram (Stacks 0CP7), and for every diagram `X` is the limit of the
  system `(X_{i'})` of scheme-theoretic images (Stacks 0CP9);
* every morphism `X ⟶ Y` over `B` comes from a morphism of the image systems on a late tail, and
  two such agree at every late stage (Stacks 0CPA);
* for example the systems attached to two diagrams for the same `X` are isomorphic on a late tail.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.limitDescriptions_of_noetherianApproximation`:
  Stacks 0CPB, from the inputs of the staged Stacks 0CP7.

## References

* [Stacks Project, Tag 0CPB](https://stacks.math.columbia.edu/tag/0CPB)
* [Stacks Project, Tag 0CP7](https://stacks.math.columbia.edu/tag/0CP7)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- **Stacks 0CPB**, granted the input `h07SU` of the staged Stacks 0CP7. In Situation 0CP6, let
`pX : X ⟶ B` be quasi-separated and of finite type. Then:
1. `X` has a diagram as in Stacks 0CP8, and for every such diagram `X` is the limit of its
   system of scheme-theoretic images;
2. for every diagram of `X` and every diagram of a space `Y` over `B`, a morphism `X ⟶ Y` over
   `B` is the limit of a morphism of the image systems on a late tail, and two such morphisms
   agree at every late stage;
3. the image systems attached to two diagrams of `X` are isomorphic on a late tail, by morphisms
   of image systems inducing the identity of `X`. -/
theorem limitDescriptions_of_noetherianApproximation
    (D : NoetherianLimitSystem B S hS B.contains_terminal I)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (pX : X ⟶ D.limitCone.pt)
    (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsQuasiSeparated B S hS pX) (hXft : IsFiniteType B S hS pX)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z) :
    (Nonempty (GoodDiagram B S hS B.contains_terminal D pX) ∧
      ∀ G : GoodDiagram B S hS B.contains_terminal D pX, Nonempty (IsLimit (imageCone G))) ∧
    (∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pY : Y ⟶ D.limitCone.pt} (f : X ⟶ Y),
      f ≫ pY = pX → ∀ (GX : GoodDiagram B S hS B.contains_terminal D pX)
        (GY : GoodDiagram B S hS B.contains_terminal D pY),
      (∃ (i₀ : I) (hiX : GX.index ≤ i₀) (hiY : GY.index ≤ i₀),
        Nonempty (SystemMorphism GX GY f i₀ hiX hiY)) ∧
      ∀ {i₀ : I} {hiX : GX.index ≤ i₀} {hiY : GY.index ≤ i₀}
        (F G : SystemMorphism GX GY f i₀ hiX hiY),
        ∃ i₃ : I, i₀ ≤ i₃ ∧ ∀ j : Over (op i₀), i₃ ≤ j.left.unop →
          F.maps.app j = G.maps.app j) ∧
    ∀ G G' : GoodDiagram B S hS B.contains_terminal D pX,
      ∃ (a : I) (h : G.index ≤ a) (h' : G'.index ≤ a)
        (E : SystemMorphism G G' (𝟙 X) a h h') (E' : SystemMorphism G' G (𝟙 X) a h' h)
        (i₁ : I) (h₁ : a ≤ i₁), ∀ (i : I) (hi : i₁ ≤ i),
          E.maps.app (Over.mk (homOfLE (h₁.trans hi)).op) ≫
              E'.maps.app (Over.mk (homOfLE (h₁.trans hi)).op) = 𝟙 _ ∧
            E'.maps.app (Over.mk (homOfLE (h₁.trans hi)).op) ≫
              E.maps.app (Over.mk (homOfLE (h₁.trans hi)).op) = 𝟙 _ :=
  ⟨⟨nonempty_goodDiagram_of_noetherianApproximation D pX hX hXqs hXft h07SU,
      fun G => ⟨isLimit_imageCone_of_algebraicLimit G hX⟩⟩,
    fun f hf GX GY => exists_systemMorphism_and_eventually_eq hX hXqs f hf GX GY,
    fun G G' => SystemMorphism.exists_systemMorphism_inv_of_algebraicLimit hX hXqs G G'⟩

end GoodDiagram

end AlgebraicGeometry.Space

end
