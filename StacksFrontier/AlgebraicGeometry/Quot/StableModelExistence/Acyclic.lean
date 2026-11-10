module

public import
  StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso.FibreCohomology
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessComplete

/-!
# Structurally acyclic morphisms

A morphism of schemes `φ : A ⟶ B` is *structurally acyclic* if `𝒪_B = φ_*𝒪_A` and
`Rⁱφ_*𝒪_A = 0` for every `i > 0`, that is, if `Rφ_*𝒪_A = 𝒪_B`. This is the property `(*)` of the
proof of [Stacks, Tag 0E97] (there with the fibre dimension bound, and only for `i = 1`; for a
proper morphism whose fibres have dimension at most one the two agree by [Stacks, Tag 0E7D]
part (1)).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsStructurallyAcyclic φ`: `𝒪_B = φ_*𝒪_A` and `Rⁱφ_*𝒪_A = 0`
  for `i > 0`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsStructurallyAcyclic.comp`: stability under composition.
* `AlgebraicGeometry.Scheme.Hom.isStructurallyAcyclic_of_isIso`: isomorphisms are structurally
  acyclic.
* `AlgebraicGeometry.Scheme.Hom.isStructurallyAcyclic_of_isZero_rightDerived_one`: for a proper
  morphism whose fibres have dimension at most one it suffices that `𝒪_B = φ_*𝒪_A` and
  `R¹φ_*𝒪_A = 0` ([Stacks, Tag 0E7D] part (1)).
* `AlgebraicGeometry.ContractionUniquenessComplete.specialMap_comp`: the special fibre of a
  composite is the composite of the special fibres.
* `AlgebraicGeometry.ContractionUniquenessComplete.isProper_specialMap`: the special fibre of a
  proper morphism is proper.
* `AlgebraicGeometry.ContractionUniquenessComplete.isStructurallyAcyclic_specialMap_comp`: hence
  structural acyclicity of special fibres is stable under composition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism `φ : A ⟶ B` is *structurally acyclic* if `𝒪_B ⟶ φ_*𝒪_A` is an isomorphism and the
higher direct images `Rⁱφ_*𝒪_A`, `i > 0`, vanish. -/
abbrev IsStructurallyAcyclic {A B : Scheme.{u}} (φ : A ⟶ B) : Prop :=
  IsIso (SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom) ∧
    ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward φ).rightDerived i).obj
      (SheafOfModules.unit A.ringCatSheaf))

variable {X Y Z : Scheme.{u}}

/-- **Structural acyclicity is stable under composition**: `𝒪_Z = (ψ ∘ φ)_*𝒪_X` by composing the
two isomorphisms, and `Rⁿ(ψ ∘ φ)_*𝒪_X ≅ Rⁿψ_*𝒪_Y` by Leray, since `Rφ_*𝒪_X = 𝒪_Y`. -/
theorem IsStructurallyAcyclic.comp {φ : X ⟶ Y} {ψ : Y ⟶ Z} [QuasiCompact φ] [QuasiSeparated φ]
    [CompactSpace Y] (hφ : φ.IsStructurallyAcyclic) (hψ : ψ.IsStructurallyAcyclic) :
    (φ ≫ ψ).IsStructurallyAcyclic :=
  ⟨Stacks.Curves.StableModel.isIso_unitToPushforwardObjUnit_comp φ ψ hφ.1 hψ.1, fun i hi =>
    (hψ.2 i hi).of_iso (Stacks.Curves.StableModel.rightDerivedCompUnitIso φ ψ hφ.1 hφ.2 i)⟩

/-- **An isomorphism is structurally acyclic.** -/
theorem isStructurallyAcyclic_of_isIso (φ : X ⟶ Y) [IsIso φ] : φ.IsStructurallyAcyclic :=
  ⟨Stacks.Models.SpecialFibreIso.isIso_unitToPushforwardUnit_of_isIso φ, fun i hi =>
    Stacks.Models.SpecialFibreIso.isZero_rightDerived_unit_of_isAffineHom φ i hi⟩

/-- **Structural acyclicity from degree one** ([Stacks, Tag 0E7D] part (1)): for a proper
morphism all of whose fibres have dimension at most one, the higher direct images of `𝒪_X` in
degrees at least two vanish, so it suffices that `𝒪_Y = φ_*𝒪_X` and `R¹φ_*𝒪_X = 0`. -/
theorem isStructurallyAcyclic_of_isZero_rightDerived_one (φ : X ⟶ Y) [IsProper φ]
    (hdim : ∀ y : Y, topologicalKrullDim (φ.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h₀ : IsIso (SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom))
    (h₁ : IsZero (((Scheme.Modules.pushforward φ).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    φ.IsStructurallyAcyclic := by
  refine ⟨h₀, fun i hi => ?_⟩
  rcases (show i = 1 ∨ 1 < i by omega) with rfl | h
  · exact h₁
  · exact Stacks.Models.SpecialFibreIso.isZero_rightDerived_unit_of_fiber_dim_le_one φ hdim i h

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.ContractionUniquenessComplete

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]
  {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of Λ)) (fY : Y ⟶ Spec (.of Λ)) (fZ : Z ⟶ Spec (.of Λ))

/-- **The special fibre of a composite is the composite of the special fibres.** -/
theorem specialMap_comp (c : X ⟶ Y) (d : Y ⟶ Z) (hc : c ≫ fY = fX) (hd : d ≫ fZ = fY) :
    specialMap fX fZ (c ≫ d) (by rw [Category.assoc, hd, hc]) =
      specialMap fX fY c hc ≫ specialMap fY fZ d hd := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    refine (pullback.lift_fst _ _ _).trans ?_
    rw [pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc]
  · rw [Category.assoc, specialMap_snd, specialMap_snd, specialMap_snd]

/-- **The special fibre of a proper morphism is proper.** -/
theorem isProper_specialMap [IsProper fX] [IsProper fY] (c : X ⟶ Y) (hc : c ≫ fY = fX) :
    IsProper (specialMap fX fY c hc) := by
  have : IsProper (specialMap fX fY c hc ≫ pullback.snd fY (closedPoint Λ)) := by
    rw [specialMap_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd fY (closedPoint Λ))

/-- **Structural acyclicity of special fibres is stable under composition.** -/
theorem isStructurallyAcyclic_specialMap_comp (c : X ⟶ Y) (d : Y ⟶ Z) (hc : c ≫ fY = fX)
    (hd : d ≫ fZ = fY) [QuasiCompact (specialMap fX fY c hc)]
    [QuasiSeparated (specialMap fX fY c hc)] [CompactSpace ↥(pullback fY (closedPoint Λ))]
    (h₁ : (specialMap fX fY c hc).IsStructurallyAcyclic)
    (h₂ : (specialMap fY fZ d hd).IsStructurallyAcyclic) :
    (specialMap fX fZ (c ≫ d) (by rw [Category.assoc, hd, hc])).IsStructurallyAcyclic := by
  rw [specialMap_comp fX fY fZ c d hc hd]
  exact h₁.comp h₂

end AlgebraicGeometry.ContractionUniquenessComplete

end
