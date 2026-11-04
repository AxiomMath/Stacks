module

public import StacksFrontier.AlgebraicGeometry.Stacks.FpqcDescent.QuasiAffineDiagonal

/-!
# Isomorphism spaces of pairs of slice points, as presheaves on the site of the base

For an algebraic stack `𝒳` over `S` with quasi-affine diagonal, an object `T` of the big fppf
site of `S` and two 1-morphisms `X₁ X₂ : 𝒮/T ⥤ 𝒳` over `𝒮`, the presheaf on the big fppf site of
`S` whose sections over `Z` are the pairs `(ψ : Z ⟶ T, m)` with `m : X₁ ψ ⟶ X₂ ψ` vertical is
represented by a quasi-affine morphism `Q ⟶ T` of the site.

This is the same statement as `AlgebraicGeometry.Stack.exists_pairIsomSpace_representing`, with the
two points read on the slice `𝒮/T` instead of on the big fppf site of `T`; the passage between the
two is the iterated-slice equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section RoundTrip

variable {C : Type*} [Category C] {X : C} (T : Over X)

/-- The iterated-slice round trip does not change the coproduct presheaf of a presheaf on a slice.
-/
noncomputable def overShriekRoundTripIso (G : (Over T)ᵒᵖ ⥤ Type*) :
    OverShriek.presheaf ((Over.iteratedSliceForward T).op ⋙ (Over.iteratedSliceBackward T).op ⋙ G) ≅
      OverShriek.presheaf G :=
  (OverShriek.presheafFunctorToOver ⋙ Over.forget _).mapIso
    ((Functor.associator (Over.iteratedSliceForward T).op (Over.iteratedSliceBackward T).op G).symm
      ≪≫ Functor.isoWhiskerRight (NatIso.op (Over.iteratedSliceEquiv T).unitIso) G ≪≫
      G.leftUnitor)

/-- The round-trip isomorphism `overShriekRoundTripIso T G` commutes with the projections of the
two coproduct presheaves to the Yoneda presheaf of `T`. -/
lemma overShriekRoundTripIso_hom_comp (G : (Over T)ᵒᵖ ⥤ Type*) :
    (overShriekRoundTripIso T G).hom ≫ OverShriek.presheafToYoneda G =
      OverShriek.presheafToYoneda _ :=
  Over.w ((OverShriek.presheafFunctorToOver).map
    ((Functor.associator (Over.iteratedSliceForward T).op (Over.iteratedSliceBackward T).op G).symm
      ≪≫ Functor.isoWhiskerRight (NatIso.op (Over.iteratedSliceEquiv T).unitIso) G ≪≫
      G.leftUnitor).hom)

end RoundTrip

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (T : BigFppfOver B S hS) {X₁ X₂ : Over T ⥤ 𝒳.val.obj}
  (h₁ : X₁ ⋙ 𝒳.val.p = Over.forget T) (h₂ : X₂ ⋙ 𝒳.val.p = Over.forget T)

/-- If `X₀` lies over `Over.forget T`, then its composite with `Over.iteratedSliceBackward T` lies
over `Over.map T.hom`. -/
lemma backward_comp_of_comp {X₀ : Over T ⥤ 𝒳.val.obj} (h : X₀ ⋙ 𝒳.val.p = Over.forget T) :
    (Over.iteratedSliceBackward T ⋙ X₀) ⋙ 𝒳.val.p = Over.map T.hom := by
  rw [Functor.assoc, h]
  exact Over.iteratedSliceBackward_forget T

/-- The presheaf on the big fppf site of `S` of pairs `(ψ : Z ⟶ T, m)` with `m : X₁ ψ ⟶ X₂ ψ`
vertical. -/
noncomputable abbrev slicePairIsom : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  OverShriek.presheaf (VertHom.presheaf 𝒳.isFiberedInGroupoids h₁ h₂)

/-- The isomorphism presheaf of the two points read on the big fppf site of `T`, transported to
the slice. -/
lemma pairIsomPresheaf_backward :
    pairIsomPresheaf B S hS 𝒳 T (backward_comp_of_comp 𝒳 T h₁) (backward_comp_of_comp 𝒳 T h₂) =
      (Over.iteratedSliceBackward T).op ⋙ VertHom.presheaf 𝒳.isFiberedInGroupoids h₁ h₂ :=
  rfl

/-- **The isomorphism presheaf of two slice points of an algebraic stack with quasi-affine diagonal
is represented by a quasi-affine morphism of the site.** -/
theorem exists_slicePairIsom_representing (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hΔ : IsQuasiAffineHom B S hS (diagonal.{u, u, u} B S hS 𝒳)) :
    ∃ (Q : BigFppfOver B S hS) (π : Q ⟶ T) (e : yoneda.obj Q ≅ slicePairIsom 𝒳 T h₁ h₂),
      e.hom ≫ OverShriek.presheafToYoneda _ = yoneda.map π ∧
        _root_.AlgebraicGeometry.IsQuasiAffineHom ((BigFppfOver.toScheme B S hS).map π) := by
  obtain ⟨Q, π, e, he, hq⟩ := exists_pairIsomSpace_representing B S hS 𝒳 T
    (backward_comp_of_comp 𝒳 T h₁) (backward_comp_of_comp 𝒳 T h₂) h𝒳 hΔ
  refine ⟨Q, π, e ≪≫ overShriekRoundTripIso T (VertHom.presheaf 𝒳.isFiberedInGroupoids h₁ h₂),
    ?_, hq⟩
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (e.hom ≫ ·)
    (overShriekRoundTripIso_hom_comp T (VertHom.presheaf 𝒳.isFiberedInGroupoids h₁ h₂))).trans ?_
  exact he

end AlgebraicGeometry.Stack

end
