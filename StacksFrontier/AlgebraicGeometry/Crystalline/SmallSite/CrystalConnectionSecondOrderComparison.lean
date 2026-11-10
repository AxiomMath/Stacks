module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderIdealTensorMono
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionKernel

/-!
# The degree-two canonical map `F_T ⊗ Ω² ⟶ q₀_* F_{T''}` of [Stacks, Tag 07J6] on `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` and let `(U, T, δ)` be an object
of `Cris(X/S)` with second-order universal thickening `(U, T'', δ'')` of [Stacks, Tag 07J3].

The integrability half of the proof of [Stacks, Tag 07J6] reads the outcome of its computation
"as a section of the subsheaf `F_T ⊗ Ω²_{T/S,δ}` of `q₂^* F`".  The subsheaf is the image of the
degree-two canonical morphism

`F_T ⊗_{𝒪_T} Ω²_{T/S,δ} ⟶ q₀_* F_{T''}`,

`F_T` tensored with the inclusion `η ↦ (0, 0, 0, η)` of the top summand of
`𝒪_{T''} = 𝒪_T ⊕ Ω ⊕ Ω ⊕ Ω²`, followed by the projection-formula morphism at `q₀` and the
direct image of the comparison map `c : q₀^* F_T ⟶ F_{T''}`.  For a crystal this is a split
monomorphism: the top summand is a direct summand, the projection formula holds at `q₀` for every
module (`q₀` is the identity on underlying spaces), and `c` is invertible.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `secondOrderAmbientInclMap` — `q₀^* : F_T ⟶ q₀_* F_{T''}`.
* `ambientSchemeCrystalComparisonQ₀` — the comparison map `q₀^* F_T ⟶ F_{T''}`.
* `secondOrderTensorComparison` — the degree-two canonical morphism.

## Main results

* `isSplitMono_secondOrderTensorComparison` — for a crystal the degree-two canonical morphism is
  a split monomorphism.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

namespace GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (M : SheafOfModules.{u} (structureSheaf S))
  (A : CrystallineThickening S)

/-- **`q₀^* : F_T ⟶ q₀_* F_{T''}`**, the restriction along the first projection `q₀ : T'' ⟶ T`
of [Stacks, Tag 07J3], as a morphism of sheaves of `𝒪_T`-modules. -/
abbrev secondOrderAmbientInclMap :
    crysAmbientSchemeModules M A ⟶
      (Scheme.Modules.pushforward (secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)) :=
  crysAmbientFMap M (secondOrderThickeningCrysQ₀ S A)

/-- **The comparison map `q₀^* F_T ⟶ F_{T''}` of [Stacks, Tag 07IQ]**, between sheaves of modules
on the ambient schemes: the adjoint transpose of `q₀^*`. -/
def ambientSchemeCrystalComparisonQ₀ :
    (Scheme.Modules.pullback (secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M A) ⟶
      crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction
    (secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom).homEquiv _ _).symm
      (secondOrderAmbientInclMap M A)

/-- **The comparison map recovers `q₀^*`** when composed with the unit of the adjunction. -/
theorem unit_comp_map_ambientSchemeCrystalComparisonQ₀ :
    (Scheme.Modules.pullbackPushforwardAdjunction
          (secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom).unit.app
        (crysAmbientSchemeModules M A) ≫
      (Scheme.Modules.pushforward (secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom).map
        (ambientSchemeCrystalComparisonQ₀ M A) =
    secondOrderAmbientInclMap M A :=
  (Adjunction.homEquiv_unit ..).symm.trans (Equiv.apply_symm_apply _ _)

/-- **For a crystal the comparison map at `q₀` is an isomorphism.** -/
theorem isIso_ambientSchemeCrystalComparisonQ₀ (hM : IsSheafCrystal M) :
    IsIso (ambientSchemeCrystalComparisonQ₀ M A) :=
  isIso_homEquiv_symm_crysAmbientFMap M hM (secondOrderThickeningCrysQ₀ S A)

/-- **The comparison `F_T ⊗_{𝒪_T} q₀_* 𝒪_{T''} ⟶ q₀_* F_{T''}`**: the projection-formula
morphism at `q₀` followed by the direct image of the comparison map. -/
def secondOrderTensorToAmbient :
    secondOrderThickeningTensorUnitRestriction A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A) ⟶
      (Scheme.Modules.pushforward (secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)) :=
  secondOrderThickeningProjectionFormulaMap A.obj.thickening.target S.S.scheme A.obj.toBase.hom
      (crysAmbientSchemeModules M A) ≫
    (Scheme.Modules.pushforward (secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom).map
      (ambientSchemeCrystalComparisonQ₀ M A)

/-- **The comparison of the middle terms is an isomorphism** once the comparison map at `q₀` is
one. -/
theorem isIso_secondOrderTensorToAmbient
    (M : SheafOfModules.{u} (structureSheaf S)) (A : CrystallineThickening S)
    (hc : IsIso (ambientSchemeCrystalComparisonQ₀ M A)) :
    IsIso (secondOrderTensorToAmbient M A) :=
  IsIso.comp_isIso' (isIso_secondOrderThickeningProjectionFormulaMap _ _ _ _)
    (((Scheme.Modules.pushforward (secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom).mapIso
      (@asIso _ _ _ _ _ hc)).isIso_hom)

/-- **The degree-two canonical map `F_T ⊗_{𝒪_T} Ω²_{T/S,δ} ⟶ q₀_* F_{T''}`**: `F_T` tensored with
the inclusion `η ↦ (0, 0, 0, η)` of the top summand of `𝒪_{T''}`, followed by the comparison of
the middle terms. -/
def secondOrderTensorComparison :
    secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A) ⟶
      (Scheme.Modules.pushforward (secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)) :=
  secondOrderThickeningTensorTopInr A.obj.thickening.target S.S.scheme A.obj.toBase.hom
      (crysAmbientSchemeModules M A) ≫
    secondOrderTensorToAmbient M A

/-- **For a crystal the degree-two canonical map is a split monomorphism.** -/
theorem isSplitMono_secondOrderTensorComparison
    (M : SheafOfModules.{u} (structureSheaf S)) (A : CrystallineThickening S)
    (hM : IsSheafCrystal M) :
    IsSplitMono (secondOrderTensorComparison M A) := by
  have := isIso_secondOrderTensorToAmbient M A (isIso_ambientSchemeCrystalComparisonQ₀ M A hM)
  have := isSplitMono_secondOrderThickeningTensorTopInr A.obj.thickening.target S.S.scheme
    A.obj.toBase.hom (crysAmbientSchemeModules M A)
  change IsSplitMono (secondOrderThickeningTensorTopInr A.obj.thickening.target S.S.scheme
    A.obj.toBase.hom (crysAmbientSchemeModules M A) ≫ secondOrderTensorToAmbient M A)
  infer_instance

/-- **The retraction of the degree-two canonical map**, for a crystal. -/
def secondOrderTensorRetraction (hM : IsSheafCrystal M) :
    (Scheme.Modules.pushforward (secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)) ⟶
      secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A) :=
  haveI := isSplitMono_secondOrderTensorComparison M A hM
  retraction (secondOrderTensorComparison M A)

/-- **The degree-two canonical map followed by its retraction is the identity.** -/
@[reassoc (attr := simp)]
theorem secondOrderTensorComparison_comp_retraction (hM : IsSheafCrystal M) :
    secondOrderTensorComparison M A ≫ secondOrderTensorRetraction M A hM = 𝟙 _ :=
  have := isSplitMono_secondOrderTensorComparison M A hM
  IsSplitMono.id (secondOrderTensorComparison M A)

/-- **On sections, the retraction undoes the degree-two canonical map.** -/
theorem secondOrderTensorRetraction_comparison_apply (hM : IsSheafCrystal M)
    (W : (A.obj.thickening.target.scheme.Opens)ᵒᵖ)
    (w : (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj W) :
    (secondOrderTensorRetraction M A hM).val.app W
        ((secondOrderTensorComparison M A).val.app W w) = w :=
  congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app W w)
    (secondOrderTensorComparison_comp_retraction M A hM)

end GlobalCrystallineSituation.SmallSite

end Crystalline

end

end
