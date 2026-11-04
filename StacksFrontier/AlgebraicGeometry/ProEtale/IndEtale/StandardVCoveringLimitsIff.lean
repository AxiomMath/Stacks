module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.StandardVCoveringLimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard V coverings as limits of ph and of h coverings, as two equivalences

A morphism `f : X ⟶ Y` of affine schemes is a standard V covering if and only if it is a
directed inverse limit, over `Y`, of affine schemes `Xᵢ` whose structure morphisms `Xᵢ ⟶ Y` are
ph coverings, and this holds if and only if it is such a limit with the `Xᵢ ⟶ Y` h coverings.

## Main results

* `AlgebraicGeometry.isStandardVCovering_limit_equivalences`: the two equivalences.

## Implementation notes

This is `AlgebraicGeometry.isStandardVCovering_limit_tfae_unconditional` with its list of three
equivalent conditions written out as the two equivalences `(1) ↔ (2)` and `(2) ↔ (3)`.

## References

* [Stacks Project, Tag 0EVP](https://stacks.math.columbia.edu/tag/0EVP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 0EVP.** Let `f : X ⟶ Y` be a morphism of affine schemes. Then `f` is a standard V
covering if and only if `X` is the limit of a directed inverse system of affine schemes `Xᵢ` over
`Y` with each `Xᵢ ⟶ Y` a ph covering, and that holds if and only if `X` is such a limit with each
`Xᵢ ⟶ Y` an h covering. -/
@[stacks 0EVP]
theorem isStandardVCovering_limit_equivalences {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) :
    (IsStandardVCovering (fun _ : Unit ↦ X) (fun _ ↦ f) ↔
      ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I)
          (_ : IsDirectedOrder I) (D : Iᵒᵖ ⥤ Scheme.{u})
          (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
          (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
          (_ : IsLimit (Cone.mk X p))
          (_ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone (Cone.mk X p).op)),
        (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
          (∀ i, IsAffine (D.obj i)) ∧
          (∀ i, IsPHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i))) ∧
    ((∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I)
          (_ : IsDirectedOrder I) (D : Iᵒᵖ ⥤ Scheme.{u})
          (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
          (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
          (_ : IsLimit (Cone.mk X p))
          (_ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone (Cone.mk X p).op)),
        (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
          (∀ i, IsAffine (D.obj i)) ∧
          (∀ i, IsPHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i))) ↔
      ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I)
          (_ : IsDirectedOrder I) (D : Iᵒᵖ ⥤ Scheme.{u})
          (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
          (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
          (_ : IsLimit (Cone.mk X p))
          (_ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone (Cone.mk X p).op)),
        (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
          (∀ i, IsAffine (D.obj i)) ∧
          (∀ i, IsHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i))) := by
  have h := isStandardVCovering_limit_tfae_unconditional f
  rw [List.tfae_cons_cons, List.tfae_cons_cons] at h
  exact ⟨h.1, h.2.1⟩

end AlgebraicGeometry

end
