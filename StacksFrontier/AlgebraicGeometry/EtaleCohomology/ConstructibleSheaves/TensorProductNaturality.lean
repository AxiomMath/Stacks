module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.TensorProduct
public import StacksFrontier.CategoryTheory.Sites.InverseImageTensorNaturality

/-!
# Naturality of the small étale inverse image/tensor comparison

`AlgebraicGeometry.smallEtaleSheafPullbackTensorIso` is the small étale instance of
`Stacks.InverseImageTensor.sheafPullbackTensorIso`: inverse image along a morphism of a big étale
site commutes with the tensor product of sheaves of `Λ`-modules. This file records its two
naturality squares, in the shape `CategoryTheory.Functor.mapBifunctorTotalIso` consumes as `hε₁`
and `hε₂`; each is the general statement of
`StacksFrontier.CategoryTheory.Sites.InverseImageTensorNaturality` read at the small étale site,
whose comma categories are filtered because small étale base change preserves finite limits.

## Main results

* `AlgebraicGeometry.smallEtaleSheafPullbackTensorIso_naturality_left` and
  `AlgebraicGeometry.smallEtaleSheafPullbackTensorIso_naturality_right` — **the two naturality
  squares of the small étale inverse image/tensor comparison.**

## References

* [Stacks Project, Tag 095I](https://stacks.math.columbia.edu/tag/095I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w

namespace AlgebraicGeometry

section SmallEtale

attribute [local instance] Sheaf.monoidalCategory

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (h : Z ⟶ X)
  (Λ : Type (max (u + 1) w)) [CommRing Λ]
  [((smallEtaleBaseChange B h).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B Z.obj Z.property)).IsRightAdjoint]

/-- The comma categories of the opposite of the small étale base change functor are filtered. -/
private theorem isFiltered_costructuredArrow_smallEtaleBaseChange_op :
    ∀ Y : (SmallEtale B Z.obj Z.property)ᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange B h).op Y) := fun Y =>
  IsFiltered.of_equivalence
    (structuredArrowOpEquivalence (smallEtaleBaseChange B h) (Opposite.unop Y))

/-- For a morphism `f : a ⟶ a'` of sheaves of `Λ`-modules on the small étale site of `X`, the
comparison isomorphism `smallEtaleSheafPullbackTensorIso B h Λ` is natural in the left tensor
factor: pulling back `f ▷ b` along `h` and then comparing agrees with comparing and then
tensoring the pullback of `f` with the pullback of `b`. -/
public theorem smallEtaleSheafPullbackTensorIso_naturality_left
    {a a' : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)}
    (f : a ⟶ a')
    (b : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) :
    ((smallEtaleBaseChange B h).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B Z.obj Z.property)).map
          (((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
            (ModuleCat.{max (u + 1) w} Λ))).map f).app b) ≫
        (smallEtaleSheafPullbackTensorIso B h Λ a' b).hom
      = (smallEtaleSheafPullbackTensorIso B h Λ a b).hom ≫
        ((curriedTensor (Sheaf (SmallEtale.topology B Z.obj Z.property)
              (ModuleCat.{max (u + 1) w} Λ))).map
            (((smallEtaleBaseChange B h).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
              (SmallEtale.topology B X.obj X.property)
              (SmallEtale.topology B Z.obj Z.property)).map f)).app
          (((smallEtaleBaseChange B h).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B Z.obj Z.property)).obj b) :=
  let := isFiltered_costructuredArrow_smallEtaleBaseChange_op B h
  Stacks.InverseImageTensor.sheafPullbackTensorIso_naturality_left (smallEtaleBaseChange B h) Λ
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property) f b

/-- For a morphism `g : b ⟶ b'` of sheaves of `Λ`-modules on the small étale site of `X`, the
comparison isomorphism `smallEtaleSheafPullbackTensorIso B h Λ` is natural in the right tensor
factor: pulling back `a ◁ g` along `h` and then comparing agrees with comparing and then
tensoring the pullback of `a` with the pullback of `g`. -/
public theorem smallEtaleSheafPullbackTensorIso_naturality_right
    (a : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))
    {b b' : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)}
    (g : b ⟶ b') :
    ((smallEtaleBaseChange B h).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B Z.obj Z.property)).map
          (((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
            (ModuleCat.{max (u + 1) w} Λ))).obj a).map g) ≫
        (smallEtaleSheafPullbackTensorIso B h Λ a b').hom
      = (smallEtaleSheafPullbackTensorIso B h Λ a b).hom ≫
        ((curriedTensor (Sheaf (SmallEtale.topology B Z.obj Z.property)
              (ModuleCat.{max (u + 1) w} Λ))).obj
            (((smallEtaleBaseChange B h).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
              (SmallEtale.topology B X.obj X.property)
              (SmallEtale.topology B Z.obj Z.property)).obj a)).map
          (((smallEtaleBaseChange B h).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B Z.obj Z.property)).map g) :=
  let := isFiltered_costructuredArrow_smallEtaleBaseChange_op B h
  Stacks.InverseImageTensor.sheafPullbackTensorIso_naturality_right (smallEtaleBaseChange B h) Λ
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property) a g

end SmallEtale

end AlgebraicGeometry

end
