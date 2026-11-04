module

public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inverse image of a composite of morphisms of topoi

Let `φ : E → F` and `ψ : F → G` be morphisms of topoi. Their composite `ψ ∘ φ : E → G` is
`MorphismOfTopoi.comp ψ φ`, whose inverse image is the composite `ψ⁻¹ ⋙ φ⁻¹` of the inverse images
— contravariantly, the inverse image of the *second* morphism coming first.

This file records the comparison `ψ⁻¹ ⋙ φ⁻¹ ≅ (ψ ∘ φ)⁻¹`, the transposition across the adjunction
of a composite, the product comparison of the inverse image of a composite, and the transposition
of a pairing across the adjunction of a composite.

Everything here is stated for arbitrary categories, as `MorphismOfTopoi` itself is, so it applies
both to sheaf categories and to `Type w` in the guise of `Sh(pt)`.

## Main definitions

* `MorphismOfTopoi.inverseImageCompIso`: the comparison `ψ⁻¹ ⋙ φ⁻¹ ≅ (ψ ∘ φ)⁻¹`, which is the
  identity.
* `MorphismOfTopoi.inverseImageCompIsoOfEq`: the same comparison for a morphism of topoi `χ`
  presented as a factorisation `χ = ψ ∘ φ` rather than as the composite on the nose.

## Main results

* `MorphismOfTopoi.comp_homEquiv_apply`: transposing across the adjunction of a composite is
  transposing across the adjunction of `φ` and then across that of `ψ`.
* `MorphismOfTopoi.prodComparison_inverseImage_comp`: the product comparison of the inverse image
  of a composite is the inverse image along `φ` of the product comparison of `ψ⁻¹`, followed by the
  product comparison of `φ⁻¹`.
* `MorphismOfTopoi.comp_homEquiv_prodComparison`: transposing a pairing of the inverse images of
  `A` and `B` across the adjunction of the composite is transposing it across the adjunction of `φ`
  and then across that of `ψ`, the two product comparisons entering one at each stage.

## References

* [Stacks Project, Tag 00XA](https://stacks.math.columbia.edu/tag/00XA)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory Limits

namespace MorphismOfTopoi

universe v u v' u' v'' u''

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
  {G : Type u''} [Category.{v''} G] (φ : MorphismOfTopoi E F) (ψ : MorphismOfTopoi F G)

/-- For `φ : E → F` and `ψ : F → G`, the comparison `ψ⁻¹ ⋙ φ⁻¹ ≅ (ψ ∘ φ)⁻¹` from the composite of
the inverse images to the inverse image of the composite; it is the identity. -/
def inverseImageCompIso : ψ.inverseImage ⋙ φ.inverseImage ≅ (ψ.comp φ).inverseImage :=
  Iso.refl _

/-- The forward map of `MorphismOfTopoi.inverseImageCompIso` is the identity. -/
@[simp]
lemma inverseImageCompIso_hom :
    (inverseImageCompIso φ ψ).hom = 𝟙 (ψ.inverseImage ⋙ φ.inverseImage) :=
  rfl

/-- The inverse map of `MorphismOfTopoi.inverseImageCompIso` is the identity. -/
@[simp]
lemma inverseImageCompIso_inv :
    (inverseImageCompIso φ ψ).inv = 𝟙 (ψ.inverseImage ⋙ φ.inverseImage) :=
  rfl

/-- The comparison of `MorphismOfTopoi.inverseImageCompIso` for a morphism of topoi `χ` given as a
factorisation `χ = ψ ∘ φ`: the isomorphism `ψ⁻¹ ⋙ φ⁻¹ ≅ χ⁻¹`. -/
def inverseImageCompIsoOfEq {χ : MorphismOfTopoi E G} (hχ : χ = ψ.comp φ) :
    ψ.inverseImage ⋙ φ.inverseImage ≅ χ.inverseImage :=
  inverseImageCompIso φ ψ ≪≫ (eqToIso (congrArg MorphismOfTopoi.inverseImage hχ)).symm

/-- A map `(ψ ∘ φ)⁻¹A ⟶ T` is transposed to `A ⟶ ψ_*φ_*T` across `(ψ ∘ φ)⁻¹ ⊣ (ψ ∘ φ)_*` by
transposing first across `φ⁻¹ ⊣ φ_*` and then across `ψ⁻¹ ⊣ ψ_*`. -/
@[sga "4 IV 3.3.1" "partial"]
theorem comp_homEquiv_apply {A : G} {T : E} (g : (ψ.comp φ).inverseImage.obj A ⟶ T) :
    (ψ.comp φ).adj.homEquiv A T g =
      ψ.adj.homEquiv A (φ.pushforward.obj T)
        (φ.adj.homEquiv (ψ.inverseImage.obj A) T g) :=
  Adjunction.comp_homEquiv_apply ψ.adj φ.adj g

section Prod

variable [HasBinaryProducts E] [HasBinaryProducts F] [HasBinaryProducts G] (A B : G)

/-- The product comparison of the inverse image of a composite `ψ ∘ φ` is the inverse image along
`φ` of the product comparison of `ψ⁻¹`, followed by the product comparison of `φ⁻¹`. -/
theorem prodComparison_inverseImage_comp :
    prodComparison (ψ.comp φ).inverseImage A B =
      φ.inverseImage.map (prodComparison ψ.inverseImage A B) ≫
        prodComparison φ.inverseImage (ψ.inverseImage.obj A) (ψ.inverseImage.obj B) :=
  prodComparison_comp ψ.inverseImage φ.inverseImage

/-- A pairing `q : φ⁻¹ψ⁻¹A ⨯ φ⁻¹ψ⁻¹B ⟶ T` of the iterated inverse images, composed with the product
comparison of `(ψ ∘ φ)⁻¹` and transposed across the adjunction of the composite, is obtained in two
stages: compose with the product comparison of `φ⁻¹` and transpose across `φ⁻¹ ⊣ φ_*`, then compose
with the product comparison of `ψ⁻¹` and transpose across `ψ⁻¹ ⊣ ψ_*`. -/
theorem comp_homEquiv_prodComparison {T : E}
    (q : φ.inverseImage.obj (ψ.inverseImage.obj A) ⨯
      φ.inverseImage.obj (ψ.inverseImage.obj B) ⟶ T) :
    (ψ.comp φ).adj.homEquiv (A ⨯ B) T
        (prodComparison (ψ.comp φ).inverseImage A B ≫ q) =
      ψ.adj.homEquiv (A ⨯ B) (φ.pushforward.obj T)
        (prodComparison ψ.inverseImage A B ≫
          φ.adj.homEquiv (ψ.inverseImage.obj A ⨯ ψ.inverseImage.obj B) T
            (prodComparison φ.inverseImage (ψ.inverseImage.obj A)
              (ψ.inverseImage.obj B) ≫ q)) := by
  refine (comp_homEquiv_apply φ ψ
    (prodComparison (ψ.comp φ).inverseImage A B ≫ q)).trans
    (congrArg (fun m ↦ ψ.adj.homEquiv (A ⨯ B) (φ.pushforward.obj T) m) ?_)
  refine Eq.trans (congrArg (fun m ↦ φ.adj.homEquiv (ψ.inverseImage.obj (A ⨯ B)) T m)
    ((congrArg (fun m ↦ m ≫ q) (prodComparison_inverseImage_comp φ ψ A B)).trans
      (Category.assoc _ _ _))) ?_
  exact φ.adj.homEquiv_naturality_left _ _

end Prod

end MorphismOfTopoi

end
