module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism

/-!
# Cancelling an invertible morphism of ringed topoi on the right of a 2-isomorphism

Let `Θ : (Sh(A), O_A) ⟶ (Sh(B), O_B)` be a morphism of ringed topoi whose direct image
`Θ_* : Sh(A) ⥤ Sh(B)` is an equivalence and whose structure map is invertible, and let
`f, g : (Sh(B), O_B) ⟶ (Sh(C), O_C)`. A 2-isomorphism `f ∘ Θ ⟹ g ∘ Θ` then comes from a unique
2-isomorphism `f ⟹ g`; this file constructs it.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.cancelRightIso`: the underlying isomorphism
  `f_* ≅ g_*` of direct images, obtained by cancelling `Θ_*` from
  `Θ_* ⋙ f_* ≅ Θ_* ⋙ g_*`.
* `AlgebraicGeometry.RingedToposHom.TwoIso.cancelRight`: the 2-isomorphism `f ⟹ g` cancelled
  from a 2-isomorphism `f ∘ Θ ⟹ g ∘ Θ`.

## Main results

* `AlgebraicGeometry.RingedToposHom.TwoIso.cancelRightIso_hom_app`: the cancelled isomorphism
  of direct images has, at an object in the image of `Θ_*`, the component of the isomorphism it
  was cancelled from. This is what identifies the cancelled 2-isomorphism, and it is what the
  compatibility with the structure maps is proved from.

## Implementation notes

Cancellation of `Θ_*` happens in the functor category: precomposition with an equivalence
`Θ_* : Sh(A) ⥤ Sh(B)` is the functor underlying the equivalence
`CategoryTheory.Equivalence.congrLeft`, hence fully faithful, so an isomorphism
`Θ_* ⋙ f_* ≅ Θ_* ⋙ g_*` has a unique preimage `f_* ≅ g_*`. Fully faithfulness alone would give
a preimage of the underlying natural transformation; the equivalence is what makes it an
isomorphism and, more importantly, what makes
`AlgebraicGeometry.RingedToposHom.TwoIso.cancelRightIso_hom_app` available — without a component
equation relating the two isomorphisms there is nothing to prove the compatibility with the
structure maps from.

The compatibility itself is naturality of the cancelled isomorphism at the structure map
`Θ♯ : O_B ⟶ Θ_*O_A`, followed by cancelling the mono `g_*(Θ♯)`; the hypothesis that `Θ♯` is
invertible is used exactly there, and is not avoidable, since the 2-isomorphism `f ∘ Θ ⟹ g ∘ Θ`
only ever constrains the cancelled isomorphism after composing with `g_*(Θ♯)`.

## References

* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ w₁ v₂ u₂ w₂ v₃ u₃ w₃

namespace AlgebraicGeometry.RingedToposHom

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₂}}
  {C : RingedTopos.{v₃, u₃, w₃}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{w₂})]
  [C.J.HasSheafCompose (forget RingCat.{w₃})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

namespace TwoIso

variable (Θ : RingedToposHom A B) [Θ.toToposHom.pushforward.IsEquivalence]
  {f g : RingedToposHom B C}

/-- The isomorphism of direct images underlying the cancellation of `Θ` on the right.

Precomposition with the equivalence `Θ_*` is fully faithful, so the isomorphism
`Θ_* ⋙ f_* ≅ Θ_* ⋙ g_*` underlying a 2-isomorphism `f ∘ Θ ⟹ g ∘ Θ` has a preimage
`f_* ≅ g_*`. -/
noncomputable def cancelRightIso (s : TwoIso (comp f Θ) (comp g Θ)) :
    f.toToposHom.pushforward ≅ g.toToposHom.pushforward :=
  Functor.preimageIso
    (Θ.toToposHom.pushforward.asEquivalence.symm.congrLeft (E := C.Topos)).functor
    (X := f.toToposHom.pushforward) (Y := g.toToposHom.pushforward) s.e

/-- At an object of the shape `Θ_*Z`, the cancelled isomorphism of direct images has the
component of the isomorphism it was cancelled from. -/
theorem cancelRightIso_hom_app (s : TwoIso (comp f Θ) (comp g Θ)) (Z : A.Topos) :
    (cancelRightIso Θ s).hom.app (Θ.toToposHom.pushforward.obj Z) = s.e.hom.app Z :=
  congrArg (fun α : (comp f Θ).toToposHom.pushforward ⟶ (comp g Θ).toToposHom.pushforward =>
      α.app Z)
    (Functor.map_preimage
      (Θ.toToposHom.pushforward.asEquivalence.symm.congrLeft (E := C.Topos)).functor s.e.hom)

/-- **Cancelling an invertible morphism of ringed topoi on the right of a 2-isomorphism.** If
the direct image of `Θ` is an equivalence and the structure map of `Θ` is invertible, then a
2-isomorphism `f ∘ Θ ⟹ g ∘ Θ` is the right whiskering by `Θ` of a 2-isomorphism `f ⟹ g`. -/
noncomputable def cancelRight [IsIso (forgetFSharp Θ)]
    (s : TwoIso (comp f Θ) (comp g Θ)) : TwoIso f g where
  e := cancelRightIso Θ s
  commutes := by
    have hs := s.commutes
    rw [forgetFSharp_comp f Θ, forgetFSharp_comp g Θ,
      ← cancelRightIso_hom_app Θ s (A.forgetRing.obj A.O), Category.assoc,
      (cancelRightIso Θ s).hom.naturality (forgetFSharp Θ), ← Category.assoc] at hs
    exact (cancel_mono (g.toToposHom.pushforward.map (forgetFSharp Θ))).1 hs

end TwoIso

end AlgebraicGeometry.RingedToposHom

end
