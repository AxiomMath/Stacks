module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderAmbientSplitting
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderProjectionFormulaIso

/-!
# The kernel of `F_{T'} ⟶ i_* F_T` and `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site and let `(U, T, δ)` be an object of `CRIS(X/S)`
with first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2] and projection
`p₀ : T' ⟶ T`.

[Stacks, Tag 07J6] reads the connection `∇(s) = p₁^* s - p₀^* s` inside `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`,
as the kernel of `p₁^* F_T ⟶ F_T`.  The sheaf `F_T ⊗_{𝒪_T} p₀_* 𝒪_{T'}` splits as
`(F_T ⊗_{𝒪_T} Ω_{T/S,δ}) ⊞ F_T` (`Crystalline.firstOrderThickeningStructureTensorSplitting`), and
`p₀_* F_{T'}` splits as `ker(i^* : p₀_* F_{T'} ⟶ F_T) ⊞ F_T`
(`Crystalline.GlobalCrystallineSituation.firstOrderAmbientSplitting`).  This module builds the
morphism comparing the two first summands out of a comparison of the two middle terms, and shows
that it is an isomorphism when the comparison map of [Stacks, Tag 07IQ] at `p₀` is one and the
comparison of the middle terms carries one section to the other.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.ambientSchemeCrystalComparison`: the comparison map
  `p₀^* F_T ⟶ F_{T'}` of [Stacks, Tag 07IQ] between sheaves of modules on the ambient schemes.
* `Crystalline.GlobalCrystallineSituation.firstOrderTensorToAmbient`: the comparison
  `F_T ⊗_{𝒪_T} p₀_* 𝒪_{T'} ⟶ p₀_* F_{T'}` of the two middle terms.
* `Crystalline.GlobalCrystallineSituation.firstOrderKernelComparison`: the morphism
  `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker(i^*)` it induces.
* `Crystalline.GlobalCrystallineSituation.firstOrderKernelIso`: that morphism as an isomorphism.

## Main results

* `Stacks.ShortComplex.isIso_of_splitting_of_section_eq`: for two split short complexes, an
  isomorphism of the middle terms carrying the section of one splitting to the section of the
  other induces an isomorphism of the first terms.
* `Crystalline.GlobalCrystallineSituation.isIso_firstOrderTensorToAmbient`: the comparison of the
  middle terms is an isomorphism as soon as
  `Crystalline.GlobalCrystallineSituation.ambientSchemeCrystalComparison` is one.
* `Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison`: the comparison
  `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker(i^*)` is an isomorphism under those two hypotheses.
* `Crystalline.GlobalCrystallineSituation.firstOrderTensorToAmbient_whiskerLeft_inlSheaf`: the
  second hypothesis follows from a statement about the projection-formula map alone.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
  MonoidalCategory

universe v u

noncomputable section

namespace Stacks.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Round trip through the first terms of two split short complexes, when the sections match. -/
private theorem round_trip_eq_id {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.Splitting) (h₂ : S₂.Splitting) (e : S₁.X₂ ⟶ S₂.X₂) (e' : S₂.X₂ ⟶ S₁.X₂)
    (he : e ≫ e' = 𝟙 _) (k : S₂.X₃ ⟶ S₁.X₃) (hs : h₂.s ≫ e' = k ≫ h₁.s) :
    (S₁.f ≫ e ≫ h₂.r) ≫ S₂.f ≫ e' ≫ h₁.r = 𝟙 S₁.X₁ := by
  have key : (S₁.f ≫ e ≫ h₂.r) ≫ S₂.f ≫ e' ≫ h₁.r =
      S₁.f ≫ e ≫ (h₂.r ≫ S₂.f) ≫ e' ≫ h₁.r := by
    simp only [Category.assoc]
  rw [key, h₂.r_f]
  simp only [Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub, Category.assoc]
  rw [← Category.assoc h₂.s e' h₁.r, hs]
  simp [reassoc_of% he, h₁.s_r]

/-- **An isomorphism of the middle terms of two split short complexes which carries one section
to the other induces an isomorphism of the first terms.** -/
theorem isIso_of_splitting_of_section_eq {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.Splitting) (h₂ : S₂.Splitting) (e : S₁.X₂ ≅ S₂.X₂) (w : S₁.X₃ ≅ S₂.X₃)
    (hse : h₁.s ≫ e.hom = w.hom ≫ h₂.s) :
    IsIso (S₁.f ≫ e.hom ≫ h₂.r) := by
  have hsei : h₂.s ≫ e.inv = w.inv ≫ h₁.s := by
    rw [Iso.comp_inv_eq, Category.assoc, hse, Iso.inv_hom_id_assoc]
  exact ⟨S₂.f ≫ e.inv ≫ h₁.r, round_trip_eq_id h₁ h₂ _ _ e.hom_inv_id _ hsei,
    round_trip_eq_id h₂ h₁ _ _ e.inv_hom_id _ hse⟩

end Stacks.ShortComplex

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)

/-! ### The comparison map of [Stacks, Tag 07IQ] on the ambient schemes -/

/-- **The comparison map `p₀^* F_T ⟶ F_{T'}` of [Stacks, Tag 07IQ], between sheaves of modules
on the ambient schemes.**  It is the adjoint transpose of the `f`-map
`Crystalline.GlobalCrystallineSituation.firstOrderAmbientInclMap` along the adjunction between
`AlgebraicGeometry.Scheme.Modules.pullback` and `AlgebraicGeometry.Scheme.Modules.pushforward`
at the morphism of schemes `p₀ : T' ⟶ T`. -/
def ambientSchemeCrystalComparison :
    (Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
        (Thickening.ambientSchemeModule M A) ⟶
      Thickening.ambientSchemeModule M (firstOrderThickeningObject S A) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction
    (firstOrderThickeningSiteP₀ S A).targetHom.hom).homEquiv _ _).symm
      (firstOrderAmbientInclMap M A)

/-- **The comparison map recovers the `f`-map** when composed with the unit of the
adjunction. -/
theorem unit_comp_map_ambientSchemeCrystalComparison :
    (Scheme.Modules.pullbackPushforwardAdjunction
          (firstOrderThickeningSiteP₀ S A).targetHom.hom).unit.app
        (Thickening.ambientSchemeModule M A) ≫
      (Scheme.Modules.pushforward (firstOrderThickeningSiteP₀ S A).targetHom.hom).map
        (ambientSchemeCrystalComparison M A) =
    firstOrderAmbientInclMap M A := by
  have h : (Scheme.Modules.pullbackPushforwardAdjunction
      (firstOrderThickeningSiteP₀ S A).targetHom.hom).homEquiv _ _
        (ambientSchemeCrystalComparison M A) = firstOrderAmbientInclMap M A :=
    Equiv.apply_symm_apply _ _
  rwa [Adjunction.homEquiv_unit] at h

/-! ### The comparison of the two middle terms -/

/-- **The comparison `F_T ⊗_{𝒪_T} p₀_* 𝒪_{T'} ⟶ p₀_* F_{T'}` of the middle terms of the two
splittings.**  It is the projection-formula map
`Crystalline.firstOrderThickeningProjectionFormulaMap` followed by the direct image along `p₀`
of the comparison map
`Crystalline.GlobalCrystallineSituation.ambientSchemeCrystalComparison`. -/
def firstOrderTensorToAmbient :
    firstOrderThickeningTensorUnitRestriction A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A) ⟶
      (Scheme.Modules.pushforward (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
        (Thickening.ambientSchemeModule M (firstOrderThickeningObject S A)) :=
  firstOrderThickeningProjectionFormulaMap A.thickening.target S.S.scheme A.toBase.hom
      (Thickening.ambientSchemeModule M A) ≫
    (Scheme.Modules.pushforward (firstOrderThickeningSiteP₀ S A).targetHom.hom).map
      (ambientSchemeCrystalComparison M A)

/-- **The comparison of the middle terms is an isomorphism** as soon as the comparison map of
[Stacks, Tag 07IQ] at `p₀` is one. -/
theorem isIso_firstOrderTensorToAmbient
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)
    (hc : IsIso (ambientSchemeCrystalComparison M A)) :
    IsIso (firstOrderTensorToAmbient M A) :=
  IsIso.comp_isIso' (isIso_firstOrderThickeningProjectionFormulaMap _ _ _ _)
    (((Scheme.Modules.pushforward (firstOrderThickeningSiteP₀ S A).targetHom.hom).mapIso
      (@asIso _ _ _ _ _ hc)).isIso_hom)

/-! ### The comparison of the kernel with `F_T ⊗ Ω` -/

/-- **The canonical morphism `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker(i^* : p₀_* F_{T'} ⟶ F_T)`**: the
inclusion `Crystalline.firstOrderThickeningTensorInr` of `F_T ⊗_{𝒪_T} Ω_{T/S,δ}` into
`F_T ⊗_{𝒪_T} p₀_* 𝒪_{T'}`, followed by the comparison
`Crystalline.GlobalCrystallineSituation.firstOrderTensorToAmbient` of the middle terms and by
the retraction `Crystalline.GlobalCrystallineSituation.firstOrderAmbientRetraction` of the
kernel inclusion. -/
def firstOrderKernelComparison :
    firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A) ⟶
      firstOrderAmbientKernel M A :=
  firstOrderThickeningTensorInr A.thickening.target S.S.scheme A.toBase.hom
      (Thickening.ambientSchemeModule M A) ≫
    firstOrderTensorToAmbient M A ≫ firstOrderAmbientRetraction M A

/-- **The comparison of the middle terms carries one section to the other as soon as the
projection-formula map does**: if the comorphism `g ↦ (g, 0)` of `p₀` tensored with `F_T`, read
through the right unitor, composes with `Crystalline.firstOrderThickeningProjectionFormulaMap` to
the unit of the adjunction between `p₀^*` and `p₀_*`, then it composes with
`Crystalline.GlobalCrystallineSituation.firstOrderTensorToAmbient` to
`Crystalline.GlobalCrystallineSituation.firstOrderAmbientInclMap`. -/
theorem firstOrderTensorToAmbient_whiskerLeft_inlSheaf
    (h : (Thickening.ambientSchemeModule M A ◁
        firstOrderThickeningInlSheaf A.thickening.target S.S.scheme A.toBase.hom) ≫
          firstOrderThickeningProjectionFormulaMap A.thickening.target S.S.scheme A.toBase.hom
            (Thickening.ambientSchemeModule M A) =
        (ρ_ (Thickening.ambientSchemeModule M A)).hom ≫
          (Scheme.Modules.pullbackPushforwardAdjunction
              (firstOrderThickeningSiteP₀ S A).targetHom.hom).unit.app
            (Thickening.ambientSchemeModule M A)) :
    (Thickening.ambientSchemeModule M A ◁
        firstOrderThickeningInlSheaf A.thickening.target S.S.scheme A.toBase.hom) ≫
          firstOrderTensorToAmbient M A =
      (ρ_ (Thickening.ambientSchemeModule M A)).hom ≫ firstOrderAmbientInclMap M A := by
  have e1 : (Thickening.ambientSchemeModule M A ◁
        firstOrderThickeningInlSheaf A.thickening.target S.S.scheme A.toBase.hom) ≫
          firstOrderTensorToAmbient M A =
      ((Thickening.ambientSchemeModule M A ◁
        firstOrderThickeningInlSheaf A.thickening.target S.S.scheme A.toBase.hom) ≫
          firstOrderThickeningProjectionFormulaMap A.thickening.target S.S.scheme A.toBase.hom
            (Thickening.ambientSchemeModule M A)) ≫
        (Scheme.Modules.pushforward (firstOrderThickeningSiteP₀ S A).targetHom.hom).map
          (ambientSchemeCrystalComparison M A) :=
    (Category.assoc _ _ _).symm
  rw [e1, h]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k ↦ (ρ_ (Thickening.ambientSchemeModule M A)).hom ≫ k)
      (unit_comp_map_ambientSchemeCrystalComparison M A))

/-- **The canonical morphism `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker(i^*)` is an isomorphism**, the
identification of [Stacks, Tag 07J6] at the level of sheaves of `𝒪_T`-modules, provided the
comparison map `Crystalline.GlobalCrystallineSituation.ambientSchemeCrystalComparison` is an
isomorphism (`hc`) and `Crystalline.GlobalCrystallineSituation.firstOrderTensorToAmbient` carries
the section `p₀^♯ ⊗ F_T` of one splitting to the section `p₀^*` of the other (`hnorm`). -/
theorem isIso_firstOrderKernelComparison
    (hc : IsIso (ambientSchemeCrystalComparison M A))
    (hnorm : (Thickening.ambientSchemeModule M A ◁
        firstOrderThickeningInlSheaf A.thickening.target S.S.scheme A.toBase.hom) ≫
          firstOrderTensorToAmbient M A =
        (ρ_ (Thickening.ambientSchemeModule M A)).hom ≫ firstOrderAmbientInclMap M A) :
    IsIso (firstOrderKernelComparison M A) :=
  Stacks.ShortComplex.isIso_of_splitting_of_section_eq
    (firstOrderThickeningStructureTensorSplitting A.thickening.target S.S.scheme A.toBase.hom
      (Thickening.ambientSchemeModule M A))
    (firstOrderAmbientSplitting M A)
    (@asIso _ _ _ _ _ (isIso_firstOrderTensorToAmbient M A hc))
    (ρ_ (Thickening.ambientSchemeModule M A)) hnorm

/-- **The identification of [Stacks, Tag 07J6] as an isomorphism**, under the hypotheses of
`Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison`:

`F_T ⊗_{𝒪_T} Ω_{T/S,δ} ≅ ker(i^* : p₀_* F_{T'} ⟶ F_T)`,

whose underlying morphism is the canonical one
`Crystalline.GlobalCrystallineSituation.firstOrderKernelComparison`. -/
def firstOrderKernelIso
    (hc : IsIso (ambientSchemeCrystalComparison M A))
    (hnorm : (Thickening.ambientSchemeModule M A ◁
        firstOrderThickeningInlSheaf A.thickening.target S.S.scheme A.toBase.hom) ≫
          firstOrderTensorToAmbient M A =
        (ρ_ (Thickening.ambientSchemeModule M A)).hom ≫ firstOrderAmbientInclMap M A) :
    firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A) ≅
      firstOrderAmbientKernel M A :=
  @asIso _ _ _ _ _ (isIso_firstOrderKernelComparison M A hc hnorm)

/-- The isomorphism of
`Crystalline.GlobalCrystallineSituation.firstOrderKernelIso` is the canonical morphism. -/
theorem firstOrderKernelIso_hom
    (hc : IsIso (ambientSchemeCrystalComparison M A))
    (hnorm : (Thickening.ambientSchemeModule M A ◁
        firstOrderThickeningInlSheaf A.thickening.target S.S.scheme A.toBase.hom) ≫
          firstOrderTensorToAmbient M A =
        (ρ_ (Thickening.ambientSchemeModule M A)).hom ≫ firstOrderAmbientInclMap M A) :
    (firstOrderKernelIso M A hc hnorm).hom = firstOrderKernelComparison M A := rfl

end GlobalCrystallineSituation

end Crystalline

end

end
