module

public import StacksFrontier.Deformation.CofiberedPresentation.SmoothPresentation
public import StacksFrontier.Deformation.ResidueField.PresentationRestriction

/-!
# The invariant `2 dim A - dim B` read off a smooth chart over a larger residue field

Let `ℱ` be a predeformation category over `𝒞_{Λ,k}` with a versal formal object `ξ` over `A`
and a ring `B` prorepresenting the functor of isomorphisms of `ξ`. Let `l/k` be a finite separable
extension, and suppose that a category `ℱ_l` equivalent over `𝒞_{Λ,l}` to the change of residue
field `ℱ_{l/k}` receives a smooth morphism `g : ℱ_V ⟶ ℱ_l` from a category `ℱ_V` equivalent over
`𝒞_{Λ,l}` to `A'|_{𝒞_{Λ,l}}`, whose self `2`-fibre product `ℱ_V ×_{g, ℱ_l, g} ℱ_V` is equivalent
over `𝒞_{Λ,l}` to `B'|_{𝒞_{Λ,l}}`. Then `2 dim A - dim B = 2 dim A' - dim B'`.

## Main results

* `Deformation.twoMul_ringKrullDim_sub_eq_of_smoothChart`: the invariant `2 dim A - dim B` of a
  versal object is computed by a smooth chart over a finite separable extension of the residue
  field.
-/

@[expose] public section

open CategoryTheory

universe u uF vF uL vL uV vV

namespace Deformation

/-- **The invariant `2 dim A - dim B` of a versal object is computed by a smooth chart over a
finite separable extension of the residue field.** Let `ξ` be a versal formal object over `A` of
a predeformation category `ℱ` over `𝒞_{Λ,k}` and `B` a ring prorepresenting the functor of
isomorphisms of `ξ`. Let `l/k` be finite separable, let `ℱ_l` be a predeformation category over
`𝒞_{Λ,l}` equivalent over `𝒞_{Λ,l}` to `ℱ_{l/k}`, and let `g : ℱ_V ⟶ ℱ_l` be smooth, with `ℱ_V`
equivalent to `A'|_{𝒞_{Λ,l}}` and `ℱ_V ×_{g, ℱ_l, g} ℱ_V` equivalent to `B'|_{𝒞_{Λ,l}}` over
`𝒞_{Λ,l}`. Then `2 dim A - dim B = 2 dim A' - dim B'`, all four dimensions being finite. -/
public theorem twoMul_ringKrullDim_sub_eq_of_smoothChart (T : ChangeOfFieldsSituation.{u, u, u})
    [Algebra.IsSeparable T.k T.l] {F : Type uF} [Category.{u} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, u, u} T.Λ T.k) (hp : IsPredeformationCategory.{u, u, u} p)
    (ξ : FormalObject p) (hξ : IsVersal hp.cofibered ξ) (B : CompleteLocalAlgCat.{u, u, u} T.Λ T.k)
    (e : restrictedCoyoneda B ≅ (versalGroupoid p hp ξ).arrows)
    {FL : Type uL} [Category.{u} FL] (pL : FL ⥤ ArtinianLocalAlgCat.{u, u, u} T.Λ T.l)
    (hpL : IsPredeformationCategory.{u, u, u} pL)
    (E : StacksRepresentableCFG.EquivalenceOver (changeOfFieldsProjection T p) pL)
    (A' B' : CompleteLocalAlgCat.{u, u, u} T.Λ T.l)
    {FV : Type uV} [Category.{vV} FV] {pV : FV ⥤ ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (eV : StacksRepresentableCFG.EquivalenceOver (CategoryOfElements.π (restrictedCoyoneda A')) pV)
    (g : FV ⥤ FL) (hg : g ⋙ pL = pV)
    (hsm : IsSmooth (⟨g, hg⟩ : BasedFunctor (BasedCategory.ofFunctor pV)
      (BasedCategory.ofFunctor pL)))
    (eB : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.structureFunctor pV pV pL g g)
      (CategoryOfElements.π (restrictedCoyoneda B'))) :
    ∃ a b a' b' : ℕ, ringKrullDim ξ.base = a ∧ ringKrullDim B = b ∧ ringKrullDim A' = a' ∧
      ringKrullDim B' = b' ∧ 2 * a + b' = 2 * a' + b := by
  obtain ⟨H, hH, ⟨PH⟩, ⟨eA'⟩, ⟨eB'⟩⟩ :=
    exists_presentation_of_smoothChart pL hpL A' B' eV g hg hsm eB
  exact GroupoidInFunctors.twoMul_ringKrullDim_sub_eq_of_changeOfFields T
    (versalGroupoid p hp ξ) (isSmooth_versalGroupoid p hp ξ hξ) H hH
    (versalGroupoidObjectsIso p hp ξ) e.symm eA' eB' (presentationOfIsVersal p hp ξ hξ) PH E

end Deformation

end
