module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisonsOnHomotopyCategory

/-!
# Cancellation identities for the composition comparison over `DerivedCategory.Qh`

`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Qh` computes the value of the
composition comparison `(F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory`
at an object `DerivedCategory.Qh.obj J` coming from the homotopy category. This file records that
value as the two cancellation identities in which a diagram chase meets it, together with the
bookkeeping lemma such chases use.

## Main results

* `Stacks.DerivedCategoryComparisons.map_factorsh_inv_comp_compIso_inv_app_Qh` and
  `Stacks.DerivedCategoryComparisons.compIso_hom_comp_factorsh_app_Qh`: that value read as two
  cancellation identities, the shapes in which a chase meets the comparison — the first cancels
  the factor `G(F-factorisation)` off its front, the second cancels the two factors behind its
  inverse and leaves the factorisation of `F ⋙ G`.
* `Stacks.DerivedCategoryComparisons.pinning_aux`: a composite of five morphisms in any category
  is computed from the four identities its factors satisfy.

## Implementation notes

The lemmas are stated at variables because the composites they are applied to are well typed only
up to definitional equality: in the applications the endpoints of two consecutive factors are two
definitionally equal but syntactically distinct spellings of one object, which makes those
composites invisible to `rw` and `simp` but acceptable to the elaborator.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedCategoryComparisons

universe w₃ w₂ w₁

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-! ### Cancellations at variables -/

section Abstract

variable {D : Type*} [Category D]

/-- A morphism equal to the identity may be cancelled off the front of a composite. The point of
stating it at variables is that `w` carries no spelling: the composites this is applied to are
well typed only up to definitional equality, and a tactic may not build them. -/
private theorem eq_id_comp {X Y : D} (f : X ⟶ X) (hf : f = 𝟙 X) (w : X ⟶ Y) : f ≫ w = w := by
  rw [hf, Category.id_comp]

/-- A composite of three morphisms whose last two compose to a morphism with an identity
front is the identity. Stated at variables, for the reason given at `eq_id_comp`. -/
private theorem comp_assoc_eq_id {A X Y : D} (s : A ⟶ X) (pq : X ⟶ Y) (r : Y ⟶ A) (iv : X ⟶ A)
    (h : pq ≫ r = iv) (hid : s ≫ iv = 𝟙 A) : (s ≫ pq) ≫ r = 𝟙 A := by
  rw [Category.assoc, h, hid]

/-- A morphism whose composite with an invertible morphism is the identity is that morphism's
inverse. Stated at variables, for the reason given at `eq_id_comp`. -/
private theorem eq_inv_of_comp_eq_id {A B : D} (f : A ⟶ B) (g : B ⟶ A) [IsIso g]
    (h : f ≫ g = 𝟙 A) : f = CategoryTheory.inv g :=
  IsIso.eq_inv_of_inv_hom_id h

/-- **A composite of three morphisms, computed from the identities its factors satisfy.** Given
`ef = ei ≫ fh`, a factorisation `a ≫ ei = b ≫ r` of the front, a factorisation
`fh ≫ p ≫ q = r'` of the back, and `r ≫ r' = 𝟙`, the composite `a ≫ ef ≫ p` is `b` followed by
the inverse `qi` of `q`.

This is the bookkeeping of a pinning computation, stated at variables so that it is indifferent
to the spelling of the objects: in the application the endpoints of `r` and of `r'` are two
definitionally equal but syntactically distinct spellings of one object, which makes the
composites below invisible to `rw` and `simp` but perfectly acceptable to the elaborator. -/
theorem pinning_aux {A X Y Z' W N : D}
    (a : A ⟶ X) (ei : X ⟶ Y) (fh : Y ⟶ Z') (ef : X ⟶ Z') (p : Z' ⟶ W) (q : W ⟶ N)
    (qi : N ⟶ W) (b : A ⟶ N) (r : N ⟶ Y) (r' : Y ⟶ N)
    (hef : ei ≫ fh = ef) (h1 : a ≫ ei = b ≫ r) (h2 : fh ≫ p ≫ q = r')
    (h3 : r ≫ r' = 𝟙 N) (h4 : q ≫ qi = 𝟙 W) :
    a ≫ ef ≫ p = b ≫ qi := by
  have key : (a ≫ ef ≫ p) ≫ q = b := by
    subst hef
    simp only [Category.assoc]
    rw [h2, ← Category.assoc, h1, Category.assoc, h3, Category.comp_id]
  rw [← Category.comp_id (a ≫ ef ≫ p), ← h4, ← Category.assoc, key]

end Abstract

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

variable (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The composition comparison with the factorisation of `F` cancelled off its front.** The
inverse of `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` at `DerivedCategory.Qh`
begins with `G` applied to the factorisation of `F`; preceded by `G` applied to its inverse, what
is left is the factorisation of `G` followed by the inverse of that of `F ⋙ G`. -/
theorem map_factorsh_inv_comp_compIso_inv_app_Qh
    (J : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.inv.app J) ≫
        (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Qh.obj J) =
      G.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
        (F ⋙ G).mapDerivedCategoryFactorsh.inv.app J := by
  rw [mapDerivedCategoryCompIso_inv_app_Qh, ← Category.assoc]
  exact eq_id_comp _
    (by rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]) _

/-- **The composition comparison followed by the two factorisations behind its inverse.** The
inverse of `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` at `DerivedCategory.Qh`
is `G` applied to the factorisation of `F`, then the factorisation of `G`, then the inverse of
that of `F ⋙ G`; so the comparison itself, followed by the first two factors, is the
factorisation of `F ⋙ G`. -/
theorem compIso_hom_comp_factorsh_app_Qh (J : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Qh.obj J) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app J) ≫
          G.mapDerivedCategoryFactorsh.hom.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) =
      (F ⋙ G).mapDerivedCategoryFactorsh.hom.app J := by
  have hPQR : (G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app J) ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
      (F ⋙ G).mapDerivedCategoryFactorsh.inv.app J =
      (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Qh.obj J) :=
    (Category.assoc (G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app J))
        (G.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J))
        ((F ⋙ G).mapDerivedCategoryFactorsh.inv.app J)).trans
      (mapDerivedCategoryCompIso_inv_app_Qh F G J).symm
  have h1 : ((mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Qh.obj J) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app J) ≫
          G.mapDerivedCategoryFactorsh.hom.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
      (F ⋙ G).mapDerivedCategoryFactorsh.inv.app J = 𝟙 _ :=
    comp_assoc_eq_id _ _ _ _ hPQR (Iso.hom_inv_id_app _ _)
  refine (eq_inv_of_comp_eq_id _ ((F ⋙ G).mapDerivedCategoryFactorsh.inv.app J) h1).trans ?_
  simp

end Stacks.DerivedCategoryComparisons

end
