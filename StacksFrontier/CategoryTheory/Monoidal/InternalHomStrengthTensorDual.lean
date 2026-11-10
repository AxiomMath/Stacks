module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomStrength
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# The strength of an internal-hom adjunction at a dualizable tensor factor

For an adjunction `- ⊗ M ⊣ H` in a monoidal category `C`, the strength
`CategoryTheory.MonoidalCategory.internalHomStrength`, `K ⊗ H(L) ⟶ H(K ⊗ L)`, is the diagonal
morphism of [Stacks, Tag 0BYS] in its adjunction-theoretic form. It is invertible when the source
`M` of the internal Hom is dualizable (`isIso_internalHomStrength_of_source_dual`). This file
proves the other half of [Stacks, Tag 0ATN] in the same form: the strength is invertible when the
tensor factor `K` has a right dual.

## The argument

If `K` and `K'` form an exact pairing, then morphisms `T ⟶ K ⊗ Z` are morphisms `K' ⊗ T ⟶ Z`
(`CategoryTheory.tensorLeftHomEquiv`). Composing with the strength is therefore, after these
identifications and the adjunction, the reassociation
`((K' ⊗ T) ⊗ M ⟶ L) ≃ (K' ⊗ (T ⊗ M) ⟶ L)`, a bijection; by Yoneda the strength is invertible.

## Main results

* `CategoryTheory.MonoidalCategory.internalHomStrength_naturality_left`: the strength is natural
  in the tensor factor.
* `CategoryTheory.MonoidalCategory.isIso_internalHomStrength_of_dual`: the strength is an
  isomorphism when `K` has a right dual.

## References

* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- **The strength is natural in the tensor factor.** -/
theorem internalHomStrength_naturality_left {M : C} {H : C ⥤ C} (a : tensorRight M ⊣ H)
    {K K' : C} (φ : K ⟶ K') (L : C) :
    φ ▷ H.obj L ≫ internalHomStrength a K' L = internalHomStrength a K L ≫ H.map (φ ▷ L) := by
  apply (a.homEquiv _ _).symm.injective
  rw [a.homEquiv_naturality_left_symm, a.homEquiv_naturality_right_symm]
  simp only [internalHomStrength, Equiv.symm_apply_apply]
  change (φ ▷ H.obj L) ▷ M ≫ (α_ K' (H.obj L) M).hom ≫ K' ◁ a.counit.app L =
    ((α_ K (H.obj L) M).hom ≫ K ◁ a.counit.app L) ≫ φ ▷ L
  rw [associator_naturality_left_assoc, ← whisker_exchange, Category.assoc]
  rfl

/-- Composing with the strength, read through the duality of `K` and the adjunction: for
`g : K' ⊗ T ⟶ H(L)`, the morphism `T ⟶ K ⊗ H(L)` it corresponds to, followed by the strength, is
the transpose of the morphism `K' ⊗ (T ⊗ M) ⟶ L` obtained from the transpose of `g` by
reassociating. -/
theorem tensorLeftHomEquiv_comp_internalHomStrength {M : C} {H : C ⥤ C}
    (a : tensorRight M ⊣ H) (K K' : C) [ExactPairing K K'] (T L : C)
    (g : K' ⊗ T ⟶ H.obj L) :
    tensorLeftHomEquiv T K K' (H.obj L) g ≫ internalHomStrength a K L =
      a.homEquiv _ _ (tensorLeftHomEquiv (T ⊗ M) K K' L
        ((α_ K' T M).inv ≫ (a.homEquiv _ _).symm g)) := by
  apply (a.homEquiv _ _).symm.injective
  rw [a.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, internalHomStrength,
    Equiv.symm_apply_apply, a.homEquiv_counit]
  change ((λ_ T).inv ≫ η_ K K' ▷ T ≫ (α_ K K' T).hom ≫ K ◁ g) ▷ M ≫ (α_ K (H.obj L) M).hom ≫
      K ◁ a.counit.app L =
    (λ_ (T ⊗ M)).inv ≫ η_ K K' ▷ (T ⊗ M) ≫ (α_ K K' (T ⊗ M)).hom ≫
      K ◁ ((α_ K' T M).inv ≫ g ▷ M ≫ a.counit.app L)
  simp only [comp_whiskerRight, Category.assoc, whiskerLeft_comp]
  rw [associator_naturality_middle_assoc]
  monoidal

/-- **The strength is invertible when the tensor factor is dualizable.** If `K` has a right dual
`K'`, the strength `K ⊗ H(L) ⟶ H(K ⊗ L)` of an adjunction `- ⊗ M ⊣ H` is an isomorphism. This is
the form of [Stacks, Tag 0ATN] in which the factor tensored inside the internal Hom is perfect. -/
theorem isIso_internalHomStrength_of_dual {M : C} {H : C ⥤ C} (a : tensorRight M ⊣ H)
    (K K' : C) [ExactPairing K K'] (L : C) : IsIso (internalHomStrength a K L) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  have h : (fun x : T ⟶ K ⊗ H.obj L => x ≫ internalHomStrength a K L) =
      (a.homEquiv _ _) ∘ (tensorLeftHomEquiv (T ⊗ M) K K' L) ∘
        (fun y => (α_ K' T M).inv ≫ y) ∘ (a.homEquiv _ _).symm ∘
          (tensorLeftHomEquiv T K K' (H.obj L)).symm := by
    funext x
    obtain ⟨g, rfl⟩ := (tensorLeftHomEquiv T K K' (H.obj L)).surjective x
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact tensorLeftHomEquiv_comp_internalHomStrength a K K' T L g
  rw [h]
  refine (a.homEquiv _ _).bijective.comp ((tensorLeftHomEquiv _ K K' L).bijective.comp
    (Function.Bijective.comp ?_ ((a.homEquiv _ _).symm.bijective.comp
      (tensorLeftHomEquiv _ K K' _).symm.bijective)))
  exact ⟨fun y y' hyy => (cancel_epi _).1 hyy,
    fun z => ⟨(α_ K' T M).hom ≫ z, Iso.inv_hom_id_assoc _ _⟩⟩

end CategoryTheory.MonoidalCategory

end
