module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.KoszulExactness
public import StacksFrontier.AlgebraicGeometry.Modules.StalkBasisSections
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Hyperplane

/-!
# The section `T` trivializes `𝒪_E(1)` on `C = {T ≠ 0}`

Let `E = Proj_X(Sym^*(𝒞)[T])` and `C ⊆ E` the open where the section `T` of `𝒪_E(1)` does not
vanish. Over an affine open `V` of `X`, `C ∩ π⁻¹V` is the image `W` of the standard open `D₊(T)`
of the chart over `V`, where `T` generates `𝒪_E(1)`. So multiplication by `T` is a bijection
`Γ(E, U) ⟶ Γ(𝒪_E(1), U)` for every open `U ⊆ C`.

## Main results

* `Stacks.Chow.ProjectiveCompletion.openW_eq`: `W = C ∩ π⁻¹V`.
* `Stacks.Chow.ProjectiveCompletion.isStalkBasis_coordT`: the germ of `T` is a stalk basis at
  every point of `C`.
* `Stacks.Chow.ProjectiveCompletion.bijective_smul_coordT`: multiplication by `T` over an open of
  `C`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]

/-- Restricting along `A ≤ C` is restricting along `B ≤ C`, then along `A ≤ B`. -/
private theorem map_homOfLE_op_eq_comp {Y : Type*} [Category Y] [TopologicalSpace Y]
    {D : Type*} [Category D] (P : (Opens Y)ᵒᵖ ⥤ D) {A B C : Opens Y} (hAB : A ≤ B) (hBC : B ≤ C)
    (hAC : A ≤ C) : P.map (homOfLE hAC).op = P.map (homOfLE hBC).op ≫ P.map (homOfLE hAB).op := by
  rw [← Functor.map_comp]
  rfl

/-- **Over an affine open `V`, the open `C` is the chart `W = D₊(T)`.** -/
theorem openW_eq {V : X.Opens} (hV : IsAffineOpen V) :
    openW 𝒞 hV = openT 𝒞 ⊓ proj 𝒞 ⁻¹ᵁ V := by
  have hpre := chart_preimage_openT 𝒞 V hV
  apply le_antisymm
  · intro x hx
    refine ⟨?_, openW_le 𝒞 hV hx⟩
    obtain ⟨ζ, hζ, rfl⟩ := hx
    have : ζ ∈ chart 𝒞 V hV ⁻¹ᵁ openT 𝒞 := by rw [hpre]; exact hζ
    exact this
  · rintro x ⟨hxT, hxV⟩
    have hx : x ∈ Set.range (chart 𝒞 V hV) := by
      rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.image_top_eq_opensRange, chart_image_top_eq]
      exact hxV
    obtain ⟨ζ, rfl⟩ := hx
    have hζ : ζ ∈ chart 𝒞 V hV ⁻¹ᵁ openT 𝒞 := hxT
    rw [hpre] at hζ
    exact (Scheme.Hom.apply_mem_image_iff _).2 hζ

/-- The restriction of `T` to `W` is the degree-one section of `T` over `V`, restricted. -/
theorem coordT_restrict_openW {V : X.Opens} (hV : IsAffineOpen V) :
    (twist 𝒞).presheaf.map (homOfLE (le_top : openW 𝒞 hV ≤ ⊤)).op (coordT 𝒞) =
      (twist 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op
        (((twistData 𝒞).ψ 1).val.app (op V)
          ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op V)
            ((module 𝒞).presheaf.map (homOfLE le_top).op (sectionT 𝒞)))) := by
  have h := SectionZeroScheme.bundleSectionOf_restrict (module 𝒞) (bundlePieces (module 𝒞))
    (sectionT 𝒞) V
  rw [map_homOfLE_op_eq_comp _ (openW_le 𝒞 hV) le_top, ConcreteCategory.comp_apply]
  exact congrArg ((twist 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op) h

/-- **The germ of `T` is a stalk basis at every point of `C`.** -/
theorem isStalkBasis_coordT (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] (ξ : space 𝒞)
    (hξ : ξ ∈ openT 𝒞) :
    Stacks.Divisors.IsStalkBasis (twist 𝒞) ξ ((twist 𝒞).presheaf.germ ⊤ ξ trivial (coordT 𝒞)) := by
  have : 𝒞.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _
  refine (exists_isAffineOpen_basis_sections 𝒞 r ((proj 𝒞).base ξ)).elim fun V hV => ?_
  obtain ⟨hV, hξV, ⟨b⟩⟩ := hV
  have hW : ξ ∈ openW 𝒞 hV := by rw [openW_eq]; exact ⟨hξ, hξV⟩
  have hg : (twist 𝒞).presheaf.germ ⊤ ξ trivial (coordT 𝒞) = germT 𝒞 hV ξ hW := by
    rw [← (twist 𝒞).presheaf.germ_res_apply (homOfLE (le_top : openW 𝒞 hV ≤ ⊤)) ξ hW,
      coordT_restrict_openW]
    rfl
  rw [hg]
  exact bijective_smul_germT 𝒞 hV b ξ hW

/-- **Multiplication by `T` is bijective over every open of `C`.** -/
theorem bijective_smul_coordT (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
    {U : (space 𝒞).Opens} (hU : U ≤ openT 𝒞) :
    Function.Bijective fun c : Γ(space 𝒞, U) =>
      c • (twist 𝒞).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (coordT 𝒞) := by
  have h := Stacks.Divisors.bijective_smul_of_isStalkBasis (twist 𝒞)
    ((twist 𝒞).presheaf.map (homOfLE (le_top : openT 𝒞 ≤ ⊤)).op (coordT 𝒞))
    (fun y hy => by
      rw [(twist 𝒞).presheaf.germ_res_apply]
      exact isStalkBasis_coordT 𝒞 r y hy) hU
  rw [map_homOfLE_op_eq_comp _ hU le_top]
  exact h

end Stacks.Chow.ProjectiveCompletion
