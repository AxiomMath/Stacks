module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.Sheaves
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# The inverse-image comparisons as left-adjoint transports (Stacks 09WF)

Stacks 09WF describes sheaves on the total site of a simplicial site by a sheaf in every
simplicial degree together with transition maps, and packages the identity and composition
constraints as a lax section of a pseudofunctor of component categories. Building that
pseudofunctor means knowing that `φ ↦ f_φ⁻¹` satisfies the unitality and associativity laws
of a pseudofunctor, and the comparisons `canonicalIdentityComparison` and
`canonicalCompositionComparison` are defined as mates of the direct-image comparisons
`SimplicialSiteSituation.pushforwardId` and `.pushforwardCompSymm`.

This file identifies those two mates with Mathlib's transports of right-adjoint comparisons
along adjunctions, `Adjunction.leftAdjointIdIso` and `Adjunction.leftAdjointCompIso`. Mathlib
proves that those transports inherit the pseudofunctor unitality and associativity laws from
the corresponding laws for the right adjoints (`Adjunction.leftAdjointCompIso_comp_id`,
`Adjunction.leftAdjointCompIso_id_comp`, `Adjunction.leftAdjointCompIso_assoc`), so with the
identifications below the coherence of the inverse-image comparisons reduces to the coherence
of the direct-image comparisons.

## Main results

* `Adjunction.leftAdjointUniq_ofNatIsoRight`: the canonical isomorphism between two left
  adjoints, one of which has had its right adjoint transported along an isomorphism, is the
  conjugate of that isomorphism. This is the general statement behind both identifications.
* `SimplicialSiteSituation.canonicalIdentityComparison_eq_leftAdjointIdIso`: the inverse-image
  unit comparison is the left-adjoint transport of `pushforwardId`.
* `SimplicialSiteSituation.canonicalCompositionComparison_eq_leftAdjointCompIso`: the
  inverse-image compositor is the left-adjoint transport of `pushforwardCompSymm`.

## Implementation notes

`canonicalIdentityComparison` compares two left adjoints of the *identity* functor, obtained by
transporting the adjunction of `f_𝟙` along `pushforwardId`; `Adjunction.leftAdjointIdIso`
instead conjugates `pushforwardId` directly. The two agree, and the proof goes through the
`homEquiv` characterisation of `Adjunction.leftAdjointUniq` together with the unit triangle.

`canonicalCompositionComparison` has the transport on the *second* adjunction, which is the
shape of `Adjunction.leftAdjointUniq_ofNatIsoRight`, so there the identification is that
general lemma applied once.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory Functor

universe u

namespace CategoryTheory

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D]

/-- Transporting the right adjoint of one of two adjunctions along an isomorphism turns the
canonical isomorphism of their left adjoints into the conjugate of that isomorphism. -/
theorem leftAdjointUniq_ofNatIsoRight {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adjA : L₁ ⊣ R₁) (adjB : L₂ ⊣ R₂) (e : R₂ ≅ R₁) :
    leftAdjointUniq adjA (adjB.ofNatIsoRight e) =
      ((conjugateIsoEquiv adjA adjB).symm e.symm).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (adjA.homEquiv X _).injective
  rw [homEquiv_leftAdjointUniq_hom_app]
  simp only [ofNatIsoRight_unit, homEquiv_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv]
  exact unit_conjugateEquiv_symm adjB adjA e.hom X

end Adjunction

namespace SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- The transpose of the inverse-image unit comparison is the inverse of the direct-image unit
comparison. -/
theorem homEquiv_canonicalIdentityComparison_hom_app (n : SimplexCategory)
    (X : Sheaf (S.componentTopology n) (Type u)) :
    ((S.transitionMorphism (𝟙 n)).adj.homEquiv X _)
        ((canonicalIdentityComparison S n).hom.app X) = (S.pushforwardId n).inv.app X := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((S.transitionMorphism (𝟙 n)).adj.ofNatIsoRight (S.pushforwardId n))
    (Adjunction.id (C := Sheaf (S.componentTopology n) (Type u))) X
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  simp only [Adjunction.id_unit, NatTrans.id_app] at h
  simpa only [canonicalIdentityComparison, Functor.id_obj, Category.id_comp, Iso.app_inv] using
    (Iso.eq_comp_inv ((S.pushforwardId n).app X)).mpr h

/-- The inverse-image unit comparison is the left-adjoint transport of the direct-image unit
comparison `pushforwardId`. -/
theorem canonicalIdentityComparison_eq_leftAdjointIdIso (n : SimplexCategory) :
    canonicalIdentityComparison S n =
      Adjunction.leftAdjointIdIso (S.transitionMorphism (𝟙 n)).adj (S.pushforwardId n) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply ((S.transitionMorphism (𝟙 n)).adj.homEquiv X _).injective
  rw [homEquiv_canonicalIdentityComparison_hom_app]
  have hnat := (S.transitionMorphism (𝟙 n)).adj.unit.naturality ((S.pushforwardId n).inv.app X)
  simp only [Adjunction.leftAdjointIdIso_hom_app, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_comp, Functor.comp_map, Functor.id_map] at hnat ⊢
  rw [← reassoc_of% hnat, Adjunction.right_triangle_components, Category.comp_id]

/-- The inverse-image compositor is the left-adjoint transport of the direct-image compositor
`pushforwardCompSymm`. -/
theorem canonicalCompositionComparison_eq_leftAdjointCompIso
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    canonicalCompositionComparison S ψ φ =
      (Adjunction.leftAdjointCompIso (S.transitionMorphism ψ).adj
        (S.transitionMorphism φ).adj (S.transitionMorphism (ψ ≫ φ)).adj
        (S.pushforwardCompSymm ψ φ)).symm := by
  rw [canonicalCompositionComparison, Adjunction.leftAdjointUniq_ofNatIsoRight]
  rfl

end SimplicialSiteSituation

end CategoryTheory

end
