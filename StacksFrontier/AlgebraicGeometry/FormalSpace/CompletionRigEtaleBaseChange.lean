module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChangeAdic

/-!
# Completion commutes with base change on the categories of Stacks 0AR5

Let `S` be a scheme contained in a big fppf site `B`, let `g : X₁ ⟶ X` be a morphism of locally
Noetherian algebraic spaces over `S`, let `T ⊆ |X|` be closed and let `T₁ = |g|⁻¹T`. The
right-hand category of Stacks 0AR5 for `X` and `T` consists of the rig-étale morphisms
`W ⟶ X_{/T}` with `W` a locally Noetherian formal algebraic space. Base change along
`g_{/T} : X_{1, /T_1} ⟶ X_{/T}` carries it to the corresponding category for `X₁` and `T₁`:
both completions are locally Noetherian by Stacks 0AQ1 (2), `g_{/T}` is adic because it is
representable by algebraic spaces, and Stacks 0GD1 applies.

**Stacks 0GDQ** says that the square formed by the two functors of Stacks 0AR5 (for `X`, `T`
and for `X₁`, `T₁`), base change along `g` on the finite-type modifications and base change
along `g_{/T}` on the rig-étale morphisms commutes. As in the source, this is because completion
along `T` commutes with fibre products (`AlgebraicGeometry.Space.completionBaseChangeSquareIso`).

## Main definitions

* `AlgebraicGeometry.FormalSpace.rigEtaleOverCompletionPullback`: base change along
  `X_{1, /T_1} ⟶ X_{/T}` from the right-hand category of Stacks 0AR5 for `X` and `T` to the one
  for `X₁` and `T₁`.
* `AlgebraicGeometry.FormalSpace.completionModificationFunctorBaseChangeIso`: **Stacks 0GDQ**.

## Main results

* `AlgebraicGeometry.FormalSpace.rigEtaleOverCompletionPullbackCompιIso`: followed by the
  inclusion into the sheaves over `X_{1, /T_1}`, that base change is the pullback functor along
  `X_{1, /T_1} ⟶ X_{/T}`.

## References

* [Stacks Project, Tag 0GDQ](https://stacks.math.columbia.edu/tag/0GDQ)
* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0AQ1](https://stacks.math.columbia.edu/tag/0AQ1)
* [Stacks Project, Tag 0AR5](https://stacks.math.columbia.edu/tag/0AR5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- **Base change over a completion.** For a morphism `g : X₁ ⟶ X` of locally Noetherian
algebraic spaces over `S` and a closed subset `T ⊆ |X|`, base change along
`X_{1, /T_1} ⟶ X_{/T}`, with `T₁ = |g|⁻¹T`, carries a rig-étale morphism `W ⟶ X_{/T}` with `W`
locally Noetherian to a rig-étale morphism `W ×_{X_{/T}} X_{1, /T_1} ⟶ X_{1, /T_1}` with locally
Noetherian source (Stacks 0GD1, `g_{/T}` being adic). -/
def rigEtaleOverCompletionPullback {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₁ ⟶ X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX₁sp : IsAlgebraicSpace B S hS X₁) (hXsp : IsAlgebraicSpace B S hS X)
    (hX₁ : Space.IsLocallyNoetherian B S hS X₁) (hX : Space.IsLocallyNoetherian B S hS X) :
    RigEtaleOverCompletion B S hS X T ⥤
      RigEtaleOverCompletion B S hS X₁ (Space.pointsMap B S hS X₁ g ⁻¹' T) :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ Over.pullback (Space.completionSheafMap B S hS g T)) fun W => by
    have hY := isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hXsp hX T hT
    have hZ := isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hX₁sp hX₁ _
      (hT.preimage (Space.continuous_pointsMap B S hS g))
    have hg := Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS hX₁sp hXsp g T
    have hN := isLocallyNoetherian_pullback_of_isRigEtale B S hS W.obj.hom
      (Space.completionSheafMap B S hS g T) W.property.2.1 hY hZ W.property.2.2 hg
    exact ⟨hN.1, hN, isRigEtale_pullback_snd_of_isLocallyNoetherian B S hS _ _ W.property.2.1 hY
      hZ W.property.2.2 hg⟩

/-- Base change over a completion, followed by the inclusion into the sheaves over
`X_{1, /T_1}`, is the pullback functor along `X_{1, /T_1} ⟶ X_{/T}`. -/
def rigEtaleOverCompletionPullbackCompιIso {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X₁ ⟶ X) (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX₁sp : IsAlgebraicSpace B S hS X₁) (hXsp : IsAlgebraicSpace B S hS X)
    (hX₁ : Space.IsLocallyNoetherian B S hS X₁) (hX : Space.IsLocallyNoetherian B S hS X) :
    rigEtaleOverCompletionPullback g T hT hX₁sp hXsp hX₁ hX ⋙
        ObjectProperty.ι (fun W : Over (Space.completionSheaf B S hS X₁
            (Space.pointsMap B S hS X₁ g ⁻¹' T)) =>
          IsFormalAlgebraicSpace B S hS W.left ∧ IsLocallyNoetherian B S hS W.left ∧
            IsRigEtale B S hS W.hom) ≅
      ObjectProperty.ι (fun W : Over (Space.completionSheaf B S hS X T) =>
          IsFormalAlgebraicSpace B S hS W.left ∧ IsLocallyNoetherian B S hS W.left ∧
            IsRigEtale B S hS W.hom) ⋙
        Over.pullback (Space.completionSheafMap B S hS g T) :=
  ObjectProperty.liftCompιIso _ _ _

/-- **Stacks 0GDQ.** Let `X` be a locally Noetherian algebraic space over `S`, let `T ⊆ |X|` be
closed with open complement `U`, and let `g : X₁ ⟶ X` be a morphism of algebraic spaces with `X₁`
locally Noetherian; write `T₁ = |g|⁻¹T` and `U₁ = g⁻¹U`. Then the square
```
  C_{X,T}   ⟶  C_{X_{/T}}
     ↓              ↓
  C_{X₁,T₁} ⟶  C_{X_{1,/T_1}}
```
commutes, where the horizontal arrows are the functors of Stacks 0AR5, the left vertical arrow is
base change along `g` and the right vertical arrow is base change along `X_{1, /T_1} ⟶ X_{/T}`.
Base change being defined by a universal property, commutativity is a natural isomorphism of the
two composite functors.

The proof is the source's: the completion functor `(h : Y ⟶ X) ↦ Y_{/T}` commutes with fibre
products. -/
@[stacks 0GDQ "the commutativity of the square as a natural isomorphism of the two composite \
functors, base change being defined by a universal property; the horizontal arrows are the \
functors of Stacks 0AR5 with the source's hypotheses, the left vertical arrow is base change \
along g on the finite-type modifications of Stacks 0AS2 and the right vertical arrow is base \
change along the completion of g"]
def completionModificationFunctorBaseChangeIso {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X₁ ⟶ X) (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX₁sp : IsAlgebraicSpace B S hS X₁) (hXsp : IsAlgebraicSpace B S hS X)
    (hX₁ : Space.IsLocallyNoetherian B S hS X₁) (hX : Space.IsLocallyNoetherian B S hS X) :
    Space.finiteTypeBaseChangePointsFunctor hX₁sp hXsp g T ⋙
        completionModificationFunctor (Space.pointsMap B S hS X₁ g ⁻¹' T)
          (hT.preimage (Space.continuous_pointsMap B S hS g)) hX₁sp hX₁ ≅
      completionModificationFunctor T hT hXsp hX ⋙
        rigEtaleOverCompletionPullback g T hT hX₁sp hXsp hX₁ hX :=
  Space.restrictedCompletionBaseChangeSquareIso B S hS g T
    (Space.finiteTypeBaseChangePointsFunctorCompιIso hX₁sp hXsp g T)
    (eqToIso (completionModificationFunctor_comp_ι T hT hXsp hX))
    (eqToIso (completionModificationFunctor_comp_ι _
      (hT.preimage (Space.continuous_pointsMap B S hS g)) hX₁sp hX₁))
    (rigEtaleOverCompletionPullbackCompιIso g T hT hX₁sp hXsp hX₁ hX)

end AlgebraicGeometry.FormalSpace

end
