module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic

/-!
# Morphisms of schemes landing in an affine open

Let `Y` be a scheme and let `U` be an affine open of `Y`. A morphism of schemes `c : Z ⟶ Y`
whose image is contained in `U` is the same thing as a ring map `Γ(Y, U) ⟶ Γ(Z, ⊤)`, namely
`c.appLE U ⊤`. This file records the two halves of that bijection, which are the local
ingredient for the anti-equivalence of Stacks Tag 01SA.

## Main definitions

* `ιTopIso` is the canonical isomorphism `Γ(Y, U) ⟶ Γ(U.toScheme, ⊤)` between the sections of
  `Y` over an open and the global sections of the corresponding open subscheme, in the form
  `U.ι.appLE U ⊤`.
* `liftToOpen` is the factorization of a morphism landing in `U` through `U.toScheme`, and
  `homOfAppLE` is the morphism `Z ⟶ Y` landing in `U` attached to a ring map
  `Γ(Y, U) ⟶ Γ(Z, ⊤)`.

## Main results

* `homOfAppLE_appLE` and `eq_of_appLE_eq`: the map `c ↦ c.appLE U ⊤` from the morphisms
  `Z ⟶ Y` landing in an affine open `U` to the ring maps `Γ(Y, U) ⟶ Γ(Z, ⊤)` is surjective and
  injective.

## Implementation notes

Everything is deduced from `Stacks.RelativeSpec.affineHomEquiv`, which identifies the morphisms
into an affine scheme with the ring maps on global sections, by factoring a morphism landing in
`U` through the open subscheme `U.toScheme` (`AlgebraicGeometry.IsOpenImmersion.lift`) and
transporting along `ιTopIso`, which is an isomorphism by the Mathlib instance for
`U.ι.appLE U ⊤`.

The proof argument of `AlgebraicGeometry.Scheme.Hom.appLE` makes rewriting the morphism inside
an `appLE` produce an ill-typed motive; `appLE_congr_hom` substitutes such an equality
instead, the two proof arguments then being equal by proof irrelevance.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {Y Z : Scheme.{u}}

/-! ### Generalities on `appLE` -/

/-- The sections over `⊤` of a morphism, in the form `appLE ⊤ ⊤`. -/
public theorem appLE_top_top (t : Z ⟶ Y) (e : (⊤ : Z.Opens) ≤ t ⁻¹ᵁ ⊤) :
    t.appLE ⊤ ⊤ e = t.appTop :=
  have h : Z.presheaf.map (homOfLE e).op = 𝟙 Γ(Z, ⊤) :=
    Eq.trans (congrArg Z.presheaf.map
      (Subsingleton.elim (homOfLE e).op (𝟙 (op (⊤ : Z.Opens))))) (Z.presheaf.map_id _)
  Eq.trans (congrArg (fun k ↦ t.appTop ≫ k) h) (Category.comp_id t.appTop)

/-- The sections over an open of two equal morphisms agree. -/
public theorem appLE_congr_hom {c₁ c₂ : Z ⟶ Y} (hc : c₁ = c₂) {U : Y.Opens} {W : Z.Opens}
    (h₁ : W ≤ c₁ ⁻¹ᵁ U) (h₂ : W ≤ c₂ ⁻¹ᵁ U) : c₁.appLE U W h₁ = c₂.appLE U W h₂ := by
  subst hc; rfl

/-- The canonical isomorphism from the sections of `Y` over an open `U` to the global sections
of the open subscheme `U.toScheme`. -/
public noncomputable abbrev ιTopIso (U : Y.Opens) : Γ(Y, U) ⟶ Γ(U.toScheme, ⊤) :=
  U.ι.appLE U ⊤ U.ι_preimage_self.ge

/-- A morphism that factors through the open subscheme `U.toScheme` lands in `U`. -/
public theorem le_preimage_of_comp_ι {U : Y.Opens} (t : Z ⟶ U.toScheme) :
    (⊤ : Z.Opens) ≤ (t ≫ U.ι) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage, U.ι_preimage_self]
  exact le_top

/-- The sections over `U` of a morphism that factors through the open subscheme `U.toScheme`
are the global sections of the factorization, transported along `ιTopIso`. -/
public theorem appLE_comp_ι {U : Y.Opens} (t : Z ⟶ U.toScheme) :
    (t ≫ U.ι).appLE U ⊤ (le_preimage_of_comp_ι t) = ιTopIso U ≫ t.appTop := by
  rw [← appLE_top_top t (by simp)]
  exact (Scheme.Hom.appLE_comp_appLE t U.ι U ⊤ ⊤ U.ι_preimage_self.ge _).symm

/-! ### Morphisms landing in an open -/

/-- The image of a morphism landing in an open `U` is contained in the image of `U.ι`. -/
public theorem range_le_range_ι {U : Y.Opens} {c : Z ⟶ Y} (h : (⊤ : Z.Opens) ≤ c ⁻¹ᵁ U) :
    Set.range c.base ⊆ Set.range U.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  exact h (show z ∈ (⊤ : Z.Opens) from trivial)

/-- The factorization of a morphism landing in an open `U` through the open subscheme
`U.toScheme`. -/
public noncomputable def liftToOpen {U : Y.Opens} (c : Z ⟶ Y)
    (h : (⊤ : Z.Opens) ≤ c ⁻¹ᵁ U) : Z ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι c (range_le_range_ι h)

/-- The factorization `liftToOpen c h` composed with the inclusion `U.ι` recovers `c`. -/
@[simp]
public theorem liftToOpen_comp_ι {U : Y.Opens} (c : Z ⟶ Y) (h : (⊤ : Z.Opens) ≤ c ⁻¹ᵁ U) :
    liftToOpen c h ≫ U.ι = c :=
  IsOpenImmersion.lift_fac _ _ _

/-- The sections over `U` of a morphism landing in `U` are the global sections of its
factorization through `U.toScheme`, transported along `ιTopIso`. -/
public theorem appLE_eq_ιTopIso_comp {U : Y.Opens} (c : Z ⟶ Y) (h : (⊤ : Z.Opens) ≤ c ⁻¹ᵁ U) :
    c.appLE U ⊤ h = ιTopIso U ≫ (liftToOpen c h).appTop :=
  (appLE_congr_hom (liftToOpen_comp_ι c h).symm h (le_preimage_of_comp_ι _)).trans
    (appLE_comp_ι _)

/-! ### Morphisms landing in an affine open -/

/-- A morphism of schemes landing in an affine open `U` of the target is determined by the ring
map it induces on the sections over `U`. -/
public theorem eq_of_appLE_eq {U : Y.Opens} (hU : IsAffineOpen U) {c₁ c₂ : Z ⟶ Y}
    (h₁ : (⊤ : Z.Opens) ≤ c₁ ⁻¹ᵁ U) (h₂ : (⊤ : Z.Opens) ≤ c₂ ⁻¹ᵁ U)
    (h : c₁.appLE U ⊤ h₁ = c₂.appLE U ⊤ h₂) : c₁ = c₂ := by
  have : IsAffine U.toScheme := hU
  rw [appLE_eq_ιTopIso_comp c₁ h₁, appLE_eq_ιTopIso_comp c₂ h₂, cancel_epi] at h
  rw [← liftToOpen_comp_ι c₁ h₁, ← liftToOpen_comp_ι c₂ h₂, ext_of_isAffine h]

/-- The morphism `Z ⟶ Y` landing in an affine open `U` of `Y` attached to a ring map
`Γ(Y, U) ⟶ Γ(Z, ⊤)`. -/
public noncomputable def homOfAppLE {U : Y.Opens} (hU : IsAffineOpen U) (Z : Scheme.{u})
    (χ : Γ(Y, U) ⟶ Γ(Z, ⊤)) : Z ⟶ Y :=
  have : IsAffine U.toScheme := hU
  (Stacks.RelativeSpec.affineHomEquiv U.toScheme Z).symm (inv (ιTopIso U) ≫ χ) ≫ U.ι

/-- The morphism attached to a ring map on the sections over `U` lands in `U`. -/
public theorem homOfAppLE_le_preimage {U : Y.Opens} (hU : IsAffineOpen U) (Z : Scheme.{u})
    (χ : Γ(Y, U) ⟶ Γ(Z, ⊤)) : (⊤ : Z.Opens) ≤ (homOfAppLE hU Z χ) ⁻¹ᵁ U :=
  le_preimage_of_comp_ι _

/-- The ring map on the sections over `U` induced by `homOfAppLE hU Z χ` is `χ`. -/
@[simp]
public theorem homOfAppLE_appLE {U : Y.Opens} (hU : IsAffineOpen U) (Z : Scheme.{u})
    (χ : Γ(Y, U) ⟶ Γ(Z, ⊤)) :
    (homOfAppLE hU Z χ).appLE U ⊤ (homOfAppLE_le_preimage hU Z χ) = χ := by
  have : IsAffine U.toScheme := hU
  calc (homOfAppLE hU Z χ).appLE U ⊤ (homOfAppLE_le_preimage hU Z χ)
      = ιTopIso U ≫ ((Stacks.RelativeSpec.affineHomEquiv U.toScheme Z).symm
          (inv (ιTopIso U) ≫ χ)).appTop := appLE_comp_ι _
    _ = χ := by
        rw [Stacks.RelativeSpec.affineHomEquiv_symm_appTop, IsIso.hom_inv_id_assoc]

end Stacks.AffineAlgebraEquivalence

end
