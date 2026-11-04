module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateSquarePasting
import all StacksFrontier.CategoryTheory.Adjunction.ConjugateSquarePasting

/-!
# Conjugate squares of adjunctions and vertical pasting

Conjugation of isomorphisms between left adjoints along adjunctions, its compatibility with
composition, associativity and whiskering, and the conjugate of a square of right adjoints. The
conjugate squares satisfy the composition and unit laws whenever the original squares do. We also
treat vertical pasting of squares of functors and its composition law.

## Main definitions

* `CategoryTheory.Adjunction.conjugateSquare`: The isomorphism of left adjoints conjugate to an
  isomorphism of composites of right adjoints.
* `CategoryTheory.Functor.pasteSquare`: The vertical pasting of two squares of functors.

## Main results

* `CategoryTheory.Adjunction.conjugateIsoEquiv_trans`: Conjugation reverses composition of
  isomorphisms.
* `CategoryTheory.Adjunction.conjugateSquare_comp`: The composition law for conjugate squares.
* `CategoryTheory.Adjunction.conjugateSquare_id`: The unit law for conjugate squares.
* `CategoryTheory.Functor.pseudonatural_of_iso`: The composition law of a family of squares is
  preserved by replacing its functors by isomorphic ones.
* `CategoryTheory.Functor.pasteSquare_comp`: Vertical pasting preserves the composition law.
* `CategoryTheory.Functor.unitLaw_of_compLaw`: A square satisfying the composition law satisfies
  the unit law.

## Implementation notes

This file supplements `StacksFrontier.CategoryTheory.Adjunction.ConjugateSquarePasting`: it holds
the declarations and imports of an alternative version of that module which other modules of
this library use beside the version kept there.
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory.Adjunction

universe v₀ v₁ v₂ v₃ v₄ v₅ u₀ u₁ u₂ u₃ u₄ u₅

section Iso

variable {C : Type u₀} {D : Type u₁} [Category.{v₀} C] [Category.{v₁} D]
  {L₁ L₂ L₃ : C ⥤ D} {R₁ R₂ R₃ : D ⥤ C}

/-- **Conjugation reverses composition of isomorphisms.** -/
theorem conjugateIsoEquiv_trans (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (α : L₃ ≅ L₂) (β : L₂ ≅ L₁) :
    conjugateIsoEquiv adj₁ adj₃ (α ≪≫ β) =
      conjugateIsoEquiv adj₁ adj₂ β ≪≫ conjugateIsoEquiv adj₂ adj₃ α :=
  Iso.ext (conjugateEquiv_comp adj₁ adj₂ adj₃ β.hom α.hom).symm

/-- Conjugating the identity between two adjunctions of a composite of three functors, the two
bracketings of the composite adjunction, gives the identity. -/
theorem conjugateIsoEquiv_assoc_refl {A : Type u₂} {B : Type u₃} [Category.{v₂} A]
    [Category.{v₃} B] {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateIsoEquiv (adj₀₁.comp (adj₁₂.comp adj₂₃)) ((adj₀₁.comp adj₁₂).comp adj₂₃)
      (Iso.refl _) = Iso.refl _ := by
  apply Iso.ext
  show conjugateEquiv _ _ (𝟙 _) = 𝟙 _
  have e : (𝟙 (L₀₁ ⋙ L₁₂ ⋙ L₂₃)) = (Functor.associator L₀₁ L₁₂ L₂₃).hom := by
    ext
    simp
  rw [e, conjugateEquiv_associator_hom]
  ext
  simp

/-- Conjugating the identity between the two bracketings of the composite adjunction of three
functors, from the left-nested to the right-nested one, gives the identity. -/
theorem conjugateIsoEquiv_assoc_refl' {A : Type u₂} {B : Type u₃} [Category.{v₂} A]
    [Category.{v₃} B] {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateIsoEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      (Iso.refl _) = Iso.refl _ := by
  have e := conjugateIsoEquiv_trans ((adj₀₁.comp adj₁₂).comp adj₂₃)
    (adj₀₁.comp (adj₁₂.comp adj₂₃)) ((adj₀₁.comp adj₁₂).comp adj₂₃) (Iso.refl _) (Iso.refl _)
  rw [conjugateIsoEquiv_assoc_refl] at e
  simp only [Iso.trans_refl] at e
  rw [← e]
  exact Iso.ext (conjugateEquiv_id _)

/-- Changing the first adjunction of a conjugation to one whose conjugate of the identity with it
is the identity does not change the conjugate. -/
theorem conjugateIsoEquiv_congr_left (a a' : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (h : conjugateIsoEquiv a a' (Iso.refl L₁) = Iso.refl R₁) (α : L₂ ≅ L₁) :
    conjugateIsoEquiv a b α = conjugateIsoEquiv a' b α := by
  have e := conjugateIsoEquiv_trans a a' b α (Iso.refl L₁)
  rwa [Iso.trans_refl, h, Iso.refl_trans] at e

/-- Changing the second adjunction of a conjugation to one whose conjugate of the identity with
it is the identity does not change the conjugate. -/
theorem conjugateIsoEquiv_congr_right (a : L₁ ⊣ R₁) (b b' : L₂ ⊣ R₂)
    (h : conjugateIsoEquiv b b' (Iso.refl L₂) = Iso.refl R₂) (α : L₂ ≅ L₁) :
    conjugateIsoEquiv a b α = conjugateIsoEquiv a b' α := by
  have e := conjugateIsoEquiv_trans a b b' (Iso.refl L₂) α
  rw [Iso.refl_trans, h, Iso.trans_refl] at e
  exact e.symm

/-- Conjugation along an isomorphism of left adjoints whiskered on the left. -/
theorem conjugateIsoEquiv_isoWhiskerLeft {A : Type u₂} [Category.{v₂} A] {L : A ⥤ C}
    {R : C ⥤ A} (adj : L ⊣ R) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (τ : L₂ ≅ L₁) :
    conjugateIsoEquiv (adj.comp adj₁) (adj.comp adj₂) (isoWhiskerLeft L τ) =
      isoWhiskerRight (conjugateIsoEquiv adj₁ adj₂ τ) R :=
  Iso.ext (conjugateEquiv_whiskerLeft adj₁ adj₂ adj τ.hom)

/-- Conjugation along an isomorphism of left adjoints whiskered on the right. -/
theorem conjugateIsoEquiv_isoWhiskerRight {B : Type u₂} [Category.{v₂} B] {L : D ⥤ B}
    {R : B ⥤ D} (adj : L ⊣ R) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (τ : L₂ ≅ L₁) :
    conjugateIsoEquiv (adj₁.comp adj) (adj₂.comp adj) (isoWhiskerRight τ L) =
      isoWhiskerLeft R (conjugateIsoEquiv adj₁ adj₂ τ) :=
  Iso.ext (conjugateEquiv_whiskerRight adj₁ adj₂ adj τ.hom)

end Iso

section Square

variable {M₀ : Type u₀} {M₁ : Type u₁} {N₀ : Type u₂} {N₁ : Type u₃}
  [Category.{v₀} M₀] [Category.{v₁} M₁] [Category.{v₂} N₀] [Category.{v₃} N₁]
  {Φ₀ : M₀ ⥤ N₀} {Ψ₀ : N₀ ⥤ M₀} {Φ₁ : M₁ ⥤ N₁} {Ψ₁ : N₁ ⥤ M₁}
  {Lb : M₁ ⥤ M₀} {Pb : M₀ ⥤ M₁} {Qb : N₁ ⥤ N₀} {Rb : N₀ ⥤ N₁}

/-- **The conjugate of a square of right adjoints**: an isomorphism `Ψ₀ ⋙ Pb ≅ Rb ⋙ Ψ₁` of
right adjoints gives the isomorphism `Φ₁ ⋙ Qb ≅ Lb ⋙ Φ₀` of their left adjoints. -/
def conjugateSquare (aΦ₀ : Φ₀ ⊣ Ψ₀) (aΦ₁ : Φ₁ ⊣ Ψ₁) (ap : Lb ⊣ Pb) (aq : Qb ⊣ Rb)
    (ρ : Ψ₀ ⋙ Pb ≅ Rb ⋙ Ψ₁) : Φ₁ ⋙ Qb ≅ Lb ⋙ Φ₀ :=
  (conjugateIsoEquiv (ap.comp aΦ₀) (aΦ₁.comp aq)).symm ρ

/-- Conjugating `conjugateSquare aΦ₀ aΦ₁ ap aq ρ` back along the composite adjunctions recovers
`ρ`. -/
theorem conjugateIsoEquiv_conjugateSquare (aΦ₀ : Φ₀ ⊣ Ψ₀) (aΦ₁ : Φ₁ ⊣ Ψ₁) (ap : Lb ⊣ Pb)
    (aq : Qb ⊣ Rb) (ρ : Ψ₀ ⋙ Pb ≅ Rb ⋙ Ψ₁) :
    conjugateIsoEquiv (ap.comp aΦ₀) (aΦ₁.comp aq) (conjugateSquare aΦ₀ aΦ₁ ap aq ρ) = ρ :=
  Equiv.apply_symm_apply _ _

/-- Conjugating `conjugateSquare aΦ₀ aΦ₁ ap aq ρ` followed by a whiskered isomorphism `τ` of left
adjoints recovers `ρ` precomposed with the conjugate of `τ`. -/
private theorem conjugateIsoEquiv_conjugateSquare_trans_whiskerRight {L' : M₁ ⥤ M₀}
    {R' : M₀ ⥤ M₁} (X : L' ⊣ R') (aΦ₀ : Φ₀ ⊣ Ψ₀) (aΦ₁ : Φ₁ ⊣ Ψ₁) (ap : Lb ⊣ Pb)
    (aq : Qb ⊣ Rb) (ρ : Ψ₀ ⋙ Pb ≅ Rb ⋙ Ψ₁) (τ : Lb ≅ L') :
    conjugateIsoEquiv (X.comp aΦ₀) (aΦ₁.comp aq)
      (conjugateSquare aΦ₀ aΦ₁ ap aq ρ ≪≫ isoWhiskerRight τ Φ₀) =
      isoWhiskerLeft Ψ₀ (conjugateIsoEquiv X ap τ) ≪≫ ρ := by
  rw [conjugateIsoEquiv_trans _ (ap.comp aΦ₀), conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_conjugateSquare]

end Square

section Comp

variable {M₀ : Type u₀} {M₁ : Type u₁} {M₂ : Type u₂} {N₀ : Type u₃} {N₁ : Type u₄}
  {N₂ : Type u₅} [Category.{v₀} M₀] [Category.{v₁} M₁] [Category.{v₂} M₂] [Category.{v₃} N₀]
  [Category.{v₄} N₁] [Category.{v₅} N₂]
  {Φ₀ : M₀ ⥤ N₀} {Ψ₀ : N₀ ⥤ M₀} {Φ₁ : M₁ ⥤ N₁} {Ψ₁ : N₁ ⥤ M₁} {Φ₂ : M₂ ⥤ N₂} {Ψ₂ : N₂ ⥤ M₂}
  (aΦ₀ : Φ₀ ⊣ Ψ₀) (aΦ₁ : Φ₁ ⊣ Ψ₁) (aΦ₂ : Φ₂ ⊣ Ψ₂)
  {Lb : M₁ ⥤ M₀} {Pb : M₀ ⥤ M₁} {Lb' : M₂ ⥤ M₁} {Pb' : M₁ ⥤ M₂} {Lc : M₂ ⥤ M₀}
  {Pc : M₀ ⥤ M₂} (apb : Lb ⊣ Pb) (apb' : Lb' ⊣ Pb') (apc : Lc ⊣ Pc)
  {Qb : N₁ ⥤ N₀} {Rb : N₀ ⥤ N₁} {Qb' : N₂ ⥤ N₁} {Rb' : N₁ ⥤ N₂} {Qc : N₂ ⥤ N₀}
  {Rc : N₀ ⥤ N₂} (aqb : Qb ⊣ Rb) (aqb' : Qb' ⊣ Rb') (aqc : Qc ⊣ Rc)

/-- **The composition law for conjugate squares.** If the squares of right adjoints paste, against
the conjugates `Pb ⋙ Pb' ≅ Pc` and `Rb ⋙ Rb' ≅ Rc` of comparisons `τ` and `υ` of the left adjoints
along a composite, then so do their conjugate squares, against `τ` and `υ` themselves. -/
theorem conjugateSquare_comp (ρb : Ψ₀ ⋙ Pb ≅ Rb ⋙ Ψ₁) (ρb' : Ψ₁ ⋙ Pb' ≅ Rb' ⋙ Ψ₂)
    (ρc : Ψ₀ ⋙ Pc ≅ Rc ⋙ Ψ₂) (τ : Lc ≅ Lb' ⋙ Lb) (υ : Qc ≅ Qb' ⋙ Qb)
    (h : isoWhiskerLeft Ψ₀ (conjugateIsoEquiv (apb'.comp apb) apc τ) ≪≫ ρc =
      isoWhiskerRight ρb Pb' ≪≫ isoWhiskerLeft Rb ρb' ≪≫
        isoWhiskerRight (conjugateIsoEquiv (aqb'.comp aqb) aqc υ) Ψ₂) :
    conjugateSquare aΦ₀ aΦ₂ apc aqc ρc ≪≫ isoWhiskerRight τ Φ₀ =
      isoWhiskerLeft Φ₂ υ ≪≫ isoWhiskerRight (conjugateSquare aΦ₁ aΦ₂ apb' aqb' ρb') Qb ≪≫
        isoWhiskerLeft Lb' (conjugateSquare aΦ₀ aΦ₁ apb aqb ρb) := by
  apply (conjugateIsoEquiv ((apb'.comp apb).comp aΦ₀) (aΦ₂.comp aqc)).injective
  have hY : conjugateIsoEquiv ((apb'.comp apb).comp aΦ₀) ((apb'.comp aΦ₁).comp aqb)
      (isoWhiskerLeft Lb' (conjugateSquare aΦ₀ aΦ₁ apb aqb ρb)) = isoWhiskerRight ρb Pb' := by
    rw [conjugateIsoEquiv_congr_left _ (apb'.comp (apb.comp aΦ₀)) _
      (conjugateIsoEquiv_assoc_refl' _ _ _),
      conjugateIsoEquiv_congr_right _ _ (apb'.comp (aΦ₁.comp aqb))
        (conjugateIsoEquiv_assoc_refl' _ _ _),
      conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_conjugateSquare]
  have hX : conjugateIsoEquiv ((apb'.comp aΦ₁).comp aqb) (aΦ₂.comp (aqb'.comp aqb))
      (isoWhiskerRight (conjugateSquare aΦ₁ aΦ₂ apb' aqb' ρb') Qb) = isoWhiskerLeft Rb ρb' := by
    rw [conjugateIsoEquiv_congr_right _ _ ((aΦ₂.comp aqb').comp aqb)
      (conjugateIsoEquiv_assoc_refl _ _ _),
      conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_conjugateSquare]
  rw [conjugateIsoEquiv_conjugateSquare_trans_whiskerRight, h,
    conjugateIsoEquiv_trans _ (aΦ₂.comp (aqb'.comp aqb)),
    conjugateIsoEquiv_isoWhiskerLeft aΦ₂ (aqb'.comp aqb) aqc υ,
    conjugateIsoEquiv_trans _ ((apb'.comp aΦ₁).comp aqb), hX, hY, Iso.trans_assoc]

end Comp

section Id

variable {M : Type u₀} {N : Type u₁} [Category.{v₀} M] [Category.{v₁} N]
  {Φ : M ⥤ N} {Ψ : N ⥤ M} (aΦ : Φ ⊣ Ψ) {L : M ⥤ M} {P : M ⥤ M} {Q : N ⥤ N} {R : N ⥤ N}
  (ap : L ⊣ P) (aq : Q ⊣ R)

/-- **The unit law for conjugate squares.** If a square of right adjoints over identifications
of the left adjoints `L ≅ 𝟭` and `Q ≅ 𝟭` with the identity is the unit law of the right adjoints,
then so is its conjugate. -/
theorem conjugateSquare_id (ρ : Ψ ⋙ P ≅ R ⋙ Ψ) (γ' : L ≅ 𝟭 M) (γ : Q ≅ 𝟭 N)
    (h : (rightUnitor Ψ).symm ≪≫ isoWhiskerLeft Ψ (conjugateIsoEquiv Adjunction.id ap γ') ≪≫ ρ =
      (leftUnitor Ψ).symm ≪≫ isoWhiskerRight (conjugateIsoEquiv Adjunction.id aq γ) Ψ) :
    conjugateSquare aΦ aΦ ap aq ρ ≪≫ isoWhiskerRight γ' Φ ≪≫ leftUnitor Φ =
      isoWhiskerLeft Φ γ ≪≫ rightUnitor Φ := by
  apply (conjugateIsoEquiv aΦ (aΦ.comp aq)).injective
  have e₁ : conjugateIsoEquiv aΦ (Adjunction.id.comp aΦ) (leftUnitor Φ) = (rightUnitor Ψ).symm :=
    Iso.ext (conjugateEquiv_leftUnitor_hom aΦ)
  have e₂ : conjugateIsoEquiv aΦ (aΦ.comp Adjunction.id) (rightUnitor Φ) = (leftUnitor Ψ).symm :=
    Iso.ext (conjugateEquiv_rightUnitor_hom aΦ)
  have hL : conjugateIsoEquiv aΦ (aΦ.comp aq)
      (conjugateSquare aΦ aΦ ap aq ρ ≪≫ isoWhiskerRight γ' Φ ≪≫ leftUnitor Φ) =
      (rightUnitor Ψ).symm ≪≫ isoWhiskerLeft Ψ (conjugateIsoEquiv Adjunction.id ap γ') ≪≫ ρ := by
    rw [← Iso.trans_assoc, conjugateIsoEquiv_trans _ (Adjunction.id.comp aΦ),
      conjugateIsoEquiv_conjugateSquare_trans_whiskerRight, e₁]
  have hR : conjugateIsoEquiv aΦ (aΦ.comp aq) (isoWhiskerLeft Φ γ ≪≫ rightUnitor Φ) =
      (leftUnitor Ψ).symm ≪≫ isoWhiskerRight (conjugateIsoEquiv Adjunction.id aq γ) Ψ := by
    rw [conjugateIsoEquiv_trans _ (aΦ.comp Adjunction.id), conjugateIsoEquiv_isoWhiskerLeft, e₂]
  rw [hL, hR, h]

end Id

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

universe v₀ v₁ v₂ v₃ v₄ v₅ u₀ u₁ u₂ u₃ u₄ u₅

variable {A : Type u₀} {B : Type u₁} {C : Type u₂} {A' : Type u₃} {B' : Type u₄} {C' : Type u₅}
  [Category.{v₀} A] [Category.{v₁} B] [Category.{v₂} C] [Category.{v₃} A'] [Category.{v₄} B']
  [Category.{v₅} C'] {eA : A ⥤ A'} {eB : B ⥤ B'} {eC : C ⥤ C'}
  {P₁ Pc₁ : A' ⥤ B'} {P₂ Pc₂ : B' ⥤ C'} {P₃ Pc₃ : A' ⥤ C'}
  {Q₁ Qc₁ : A ⥤ B} {Q₂ Qc₂ : B ⥤ C} {Q₃ Qc₃ : A ⥤ C}

/-- **Replacing the functors of a pseudonatural family of squares along isomorphisms.** Let
`r₁ : Qc₁ ⋙ eB ≅ eA ⋙ Pc₁`, `r₂`, `r₃` be squares satisfying the composition law against
comparisons `πc : Pc₁ ⋙ Pc₂ ≅ Pc₃` and `πc' : Qc₁ ⋙ Qc₂ ≅ Qc₃`, and let `χ`, `χ'` identify
functors `P`, `Q` with the `Pc`, `Qc`, compatibly with comparisons `π : P₁ ⋙ P₂ ≅ P₃` and
`π' : Q₁ ⋙ Q₂ ≅ Q₃`. Then the transported squares `eA ⋙ Pᵢ ≅ Qᵢ ⋙ eB` satisfy the composition
law against `π` and `π'`. -/
theorem pseudonatural_of_iso
    (χ₁ : P₁ ≅ Pc₁) (χ₂ : P₂ ≅ Pc₂) (χ₃ : P₃ ≅ Pc₃) (χ₁' : Q₁ ≅ Qc₁) (χ₂' : Q₂ ≅ Qc₂)
    (χ₃' : Q₃ ≅ Qc₃) (π : P₁ ⋙ P₂ ≅ P₃) (πc : Pc₁ ⋙ Pc₂ ≅ Pc₃) (π' : Q₁ ⋙ Q₂ ≅ Q₃)
    (πc' : Qc₁ ⋙ Qc₂ ≅ Qc₃)
    (hχ : isoWhiskerRight χ₁ P₂ ≪≫ isoWhiskerLeft Pc₁ χ₂ ≪≫ πc = π ≪≫ χ₃)
    (hχ' : isoWhiskerRight χ₁' Q₂ ≪≫ isoWhiskerLeft Qc₁ χ₂' ≪≫ πc' = π' ≪≫ χ₃')
    (r₁ : Qc₁ ⋙ eB ≅ eA ⋙ Pc₁) (r₂ : Qc₂ ⋙ eC ≅ eB ⋙ Pc₂) (r₃ : Qc₃ ⋙ eC ≅ eA ⋙ Pc₃)
    (hr : isoWhiskerRight πc'.symm eC ≪≫ isoWhiskerLeft Qc₁ r₂ ≪≫ isoWhiskerRight r₁ Pc₂ ≪≫
      isoWhiskerLeft eA πc = r₃) :
    isoWhiskerLeft eA π ≪≫ (isoWhiskerLeft eA χ₃ ≪≫ r₃.symm ≪≫ isoWhiskerRight χ₃'.symm eC) =
      isoWhiskerRight (isoWhiskerLeft eA χ₁ ≪≫ r₁.symm ≪≫ isoWhiskerRight χ₁'.symm eB) P₂ ≪≫
        isoWhiskerLeft Q₁ (isoWhiskerLeft eB χ₂ ≪≫ r₂.symm ≪≫ isoWhiskerRight χ₂'.symm eC) ≪≫
        isoWhiskerRight π' eC := by
  subst hr
  ext X
  have e₁ := NatTrans.congr_app (congrArg Iso.hom hχ) (eA.obj X)
  have e₂ := NatTrans.congr_app (congrArg Iso.inv hχ') X
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_inv, isoWhiskerRight_inv, whiskerLeft_app,
    whiskerRight_app, Iso.symm_hom, Iso.symm_inv, Functor.comp_obj, Category.assoc] at e₁ e₂ ⊢
  rw [← reassoc_of% e₁]
  have e₂' : χ₃'.inv.app X = πc'.inv.app X ≫ χ₂'.inv.app (Qc₁.obj X) ≫
      Q₂.map (χ₁'.inv.app X) ≫ π'.hom.app X := by
    simpa using (congrArg (· ≫ π'.hom.app X) e₂).symm
  have e₃ : eC.map (πc'.hom.app X) ≫ eC.map (χ₃'.inv.app X) =
      eC.map (χ₂'.inv.app (Qc₁.obj X)) ≫ eC.map (Q₂.map (χ₁'.inv.app X)) ≫
        eC.map (π'.hom.app X) := by
    rw [← eC.map_comp, ← eC.map_comp, ← eC.map_comp, e₂', Iso.hom_inv_id_app_assoc]
  rw [e₃]
  simp only [Functor.map_comp, Category.assoc, NatTrans.naturality_assoc,
    Iso.hom_inv_id_app_assoc]
  congr 2
  have n₁ := r₂.inv.naturality (χ₁'.inv.app X)
  simp only [Functor.comp_map] at n₁
  rw [reassoc_of% n₁]
  congr 2
  simp only [← eC.map_comp]
  rw [reassoc_of% (χ₂'.inv.naturality (χ₁'.inv.app X))]

section Paste

variable {A₀ : Type u₀} {A₁ : Type u₁} {A₂ : Type u₂} {B₀ : Type u₃} {B₁ : Type u₄}
  {B₂ : Type u₅} [Category.{v₀} A₀] [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} B₀]
  [Category.{v₄} B₁] [Category.{v₅} B₂]

/-- **Vertical pasting of two squares**: a square `E₁ ⋙ R ≅ P ⋙ E₀` on top of a square
`I₁ ⋙ Q ≅ R ⋙ I₀` gives a square for the composite vertical functors. -/
def pasteSquare {C₀ : Type*} {C₁ : Type*} [Category* C₀] [Category* C₁] {E₀ : A₀ ⥤ B₀}
    {E₁ : A₁ ⥤ B₁} {I₀ : B₀ ⥤ C₀} {I₁ : B₁ ⥤ C₁} {P : A₁ ⥤ A₀} {R : B₁ ⥤ B₀} {Q : C₁ ⥤ C₀}
    (ρ : E₁ ⋙ R ≅ P ⋙ E₀) (s : I₁ ⋙ Q ≅ R ⋙ I₀) : (E₁ ⋙ I₁) ⋙ Q ≅ P ⋙ E₀ ⋙ I₀ :=
  associator E₁ I₁ Q ≪≫ isoWhiskerLeft E₁ s ≪≫ (associator E₁ R I₀).symm ≪≫
    isoWhiskerRight ρ I₀ ≪≫ associator P E₀ I₀

/-- The component of `pasteSquare ρ s` at `M` is
`s.hom.app (E₁.obj M) ≫ I₀.map (ρ.hom.app M)`. -/
@[simp]
theorem pasteSquare_hom_app {C₀ : Type*} {C₁ : Type*} [Category* C₀] [Category* C₁]
    {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {I₀ : B₀ ⥤ C₀} {I₁ : B₁ ⥤ C₁} {P : A₁ ⥤ A₀} {R : B₁ ⥤ B₀}
    {Q : C₁ ⥤ C₀} (ρ : E₁ ⋙ R ≅ P ⋙ E₀) (s : I₁ ⋙ Q ≅ R ⋙ I₀) (M : A₁) :
    (pasteSquare ρ s).hom.app M = s.hom.app (E₁.obj M) ≫ I₀.map (ρ.hom.app M) := by
  simp [pasteSquare]

/-- **Vertical pasting keeps the composition law**: if the top squares paste against the
comparisons `τ` and `μ` of the horizontal composites, and the bottom squares against `μ` and `υ`,
then the pasted squares paste against `τ` and `υ`. -/
theorem pasteSquare_comp {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂} {I₀ : B₀ ⥤ C₀} {I₁ : B₁ ⥤ C₁}
    {I₂ : B₂ ⥤ C₂} {P₁ : A₁ ⥤ A₀} {P₂ : A₂ ⥤ A₁} {Pc : A₂ ⥤ A₀} {R₁ : B₁ ⥤ B₀} {R₂ : B₂ ⥤ B₁}
    {Rc : B₂ ⥤ B₀} {Q₁ : C₁ ⥤ C₀} {Q₂ : C₂ ⥤ C₁} {Qc : C₂ ⥤ C₀}
    (τ : Pc ≅ P₂ ⋙ P₁) (μ : Rc ≅ R₂ ⋙ R₁) (υ : Qc ≅ Q₂ ⋙ Q₁)
    (ρ₁ : E₁ ⋙ R₁ ≅ P₁ ⋙ E₀) (ρ₂ : E₂ ⋙ R₂ ≅ P₂ ⋙ E₁) (ρc : E₂ ⋙ Rc ≅ Pc ⋙ E₀)
    (s₁ : I₁ ⋙ Q₁ ≅ R₁ ⋙ I₀) (s₂ : I₂ ⋙ Q₂ ≅ R₂ ⋙ I₁) (sc : I₂ ⋙ Qc ≅ Rc ⋙ I₀)
    (hρ : ρc ≪≫ isoWhiskerRight τ E₀ =
      isoWhiskerLeft E₂ μ ≪≫ isoWhiskerRight ρ₂ R₁ ≪≫ isoWhiskerLeft P₂ ρ₁)
    (hs : sc ≪≫ isoWhiskerRight μ I₀ =
      isoWhiskerLeft I₂ υ ≪≫ isoWhiskerRight s₂ Q₁ ≪≫ isoWhiskerLeft R₂ s₁) :
    pasteSquare ρc sc ≪≫ isoWhiskerRight τ (E₀ ⋙ I₀) =
      isoWhiskerLeft (E₂ ⋙ I₂) υ ≪≫ isoWhiskerRight (pasteSquare ρ₂ s₂) Q₁ ≪≫
        isoWhiskerLeft P₂ (pasteSquare ρ₁ s₁) := by
  ext M
  have e₁ := NatTrans.congr_app (congrArg Iso.hom hρ) M
  have e₂ := NatTrans.congr_app (congrArg Iso.hom hs) (E₂.obj M)
  have n := s₁.hom.naturality (ρ₂.hom.app M)
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app, comp_obj, comp_map] at e₁ e₂ n
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app, pasteSquare_hom_app, comp_obj, comp_map,
    Category.assoc]
  rw [← I₀.map_comp, e₁, I₀.map_comp, I₀.map_comp, reassoc_of% e₂, ← reassoc_of% n,
    Q₁.map_comp, Category.assoc]

/-- **The unit law of a square from its composition law.** Let `ρ : E ⋙ Q ≅ P ⋙ E` be a square
over endofunctors `P`, `Q` identified with the identity by `γP`, `γQ`, and let `ρc` be a square
over endofunctors `Pc`, `Qc`, identified with `P`, `Q` by `dP`, `dQ` and with the composites
`P ⋙ P`, `Q ⋙ Q` by `cP`, `cQ`. If `ρc` is `ρ` read through `dP`, `dQ`, and `ρ` pasted with
itself is `ρc` read through `cP`, `cQ`, and the identifications satisfy the unit laws, then `ρ`
satisfies the unit law
`ρ ≪≫ isoWhiskerRight γP E ≪≫ leftUnitor E = isoWhiskerLeft E γQ ≪≫ rightUnitor E`. This is the
familiar fact that an idempotent isomorphism is an identity. -/
theorem unitLaw_of_compLaw {A : Type u₀} {B : Type u₁} [Category.{v₀} A] [Category.{v₁} B]
    {E : A ⥤ B} {P Pc : A ⥤ A} {Q Qc : B ⥤ B} (ρ : E ⋙ Q ≅ P ⋙ E) (ρc : E ⋙ Qc ≅ Pc ⋙ E)
    (cP : Pc ≅ P ⋙ P) (cQ : Qc ≅ Q ⋙ Q) (dP : Pc ≅ P) (dQ : Qc ≅ Q) (γP : P ≅ 𝟭 A)
    (γQ : Q ≅ 𝟭 B)
    (hcomp : ρc ≪≫ isoWhiskerRight cP E =
      isoWhiskerLeft E cQ ≪≫ isoWhiskerRight ρ Q ≪≫ isoWhiskerLeft P ρ)
    (hd : ρc ≪≫ isoWhiskerRight dP E = isoWhiskerLeft E dQ ≪≫ ρ)
    (hP : cP ≪≫ isoWhiskerLeft P γP ≪≫ rightUnitor P = dP)
    (hQ : cQ ≪≫ isoWhiskerRight γQ Q ≪≫ leftUnitor Q = dQ) :
    ρ ≪≫ isoWhiskerRight γP E ≪≫ leftUnitor E = isoWhiskerLeft E γQ ≪≫ rightUnitor E := by
  ext M
  have e₁ := NatTrans.congr_app (congrArg Iso.hom hcomp) M
  have e₂ := NatTrans.congr_app (congrArg Iso.hom hd) M
  have e₃ := NatTrans.congr_app (congrArg Iso.hom hP) M
  have e₄ := NatTrans.congr_app (congrArg Iso.hom hQ) (E.obj M)
  have nρ := ρ.hom.naturality (γP.hom.app M)
  have nγ := γP.hom.naturality (γP.hom.app M)
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app, comp_obj, comp_map, id_obj, id_map,
    rightUnitor_hom_app, leftUnitor_hom_app, Category.comp_id] at e₁ e₂ e₃ e₄ nρ nγ
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app, comp_obj, id_obj, rightUnitor_hom_app,
    leftUnitor_hom_app, Category.comp_id]
  have hPγ : P.map (γP.hom.app M) = γP.hom.app (P.obj M) := (cancel_mono _).1 nγ
  have h₁ : dQ.hom.app (E.obj M) =
      cQ.hom.app (E.obj M) ≫ Q.map (ρ.hom.app M ≫ E.map (γP.hom.app M)) := by
    rw [← cancel_mono (ρ.hom.app M), ← e₂, ← e₃, E.map_comp, reassoc_of% e₁, ← hPγ, ← nρ,
      Q.map_comp, Category.assoc, Category.assoc]
  have h₂ : Q.map (ρ.hom.app M ≫ E.map (γP.hom.app M)) = Q.map (γQ.hom.app (E.obj M)) := by
    rw [← cancel_epi (cQ.hom.app (E.obj M)), ← h₁, e₄]
  have n₁ := γQ.hom.naturality (ρ.hom.app M ≫ E.map (γP.hom.app M))
  have n₂ := γQ.hom.naturality (γQ.hom.app (E.obj M))
  simp only [id_obj, id_map] at n₁ n₂
  rw [← cancel_epi (γQ.hom.app (Q.obj (E.obj M)))]
  exact n₁.symm.trans ((congrArg (· ≫ γQ.hom.app (E.obj M)) h₂).trans n₂)

end Paste

end CategoryTheory.Functor

end
