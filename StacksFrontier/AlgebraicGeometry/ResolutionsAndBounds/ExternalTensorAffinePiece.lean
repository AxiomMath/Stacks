module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.GlobalSections
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealPowPullback

/-!
# One affine piece of the resolution of a module on a product

Let `X` and `Y` be schemes over `S`, both locally Noetherian and with the resolution property,
with `X ×_S Y` Noetherian, and let `F` be a quasi-coherent `𝒪_{X ×_S Y}`-module. For opens
`U ⊆ X` and `V ⊆ Y` let `𝓙 = pr₁^*𝓘 · pr₂^*𝓘'` be the product of the vanishing ideal sheaves of
the complements of `U` and of `V`, so that `V(𝓙) = X ×_S Y ∖ U ×_S V`.

Given a section `s` of `F` over `U ×_S V` this file produces an integer `n`, finite locally free
modules `𝓔` on `X` and `𝓖` on `Y`, an epimorphism `𝓔 ⊠ 𝓖 ⟶ 𝓙ⁿ` and a morphism `𝓙ⁿ ⟶ F`
carrying the unit section of `𝓙ⁿ` over `U ×_S V` to `s`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.support_compl_externalProduct_complementIdeal`: the
  open complement of `V(𝓙)` is `U ×_S V`, for `𝓙` the product of the vanishing ideal sheaves of
  the complements of `U` and of `V`.
* `AlgebraicGeometry.exists_epi_externalTensorProduct_hom_app_oneSection`: a section of `F` over
  the complement of `V(𝓙)` is the image of the unit section under a morphism `𝓙ⁿ ⟶ F`, and `𝓙ⁿ`
  is a quotient of an external tensor product of finite locally free modules.
* `AlgebraicGeometry.exists_epi_externalTensorProduct_hom_app_eq_of_opens`: the same with the
  complement of `V(𝓙)` written as `U ×_S V`.

## References

* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 0F86](https://stacks.math.columbia.edu/tag/0F86)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerColimit
open Stacks.AlgebraicGeometry.IdealPullback

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The open complement of the vanishing locus of the vanishing ideal sheaf of the complement of
an open `U` is `U` itself. -/
theorem support_compl_complementIdeal {X : Scheme.{u}} (U : X.Opens) :
    ((complementIdeal U).support.compl : X.Opens) = U :=
  Opens.ext (by
    rw [show ((complementIdeal U).support.compl : Set X)
      = ((complementIdeal U).support : Set X)ᶜ from rfl, coe_support_complementIdeal, compl_compl])

/-- **The open complement of `V(𝓙)` is `U ×_S V`**, for `𝓙 = pr₁^*𝓘 · pr₂^*𝓘'` the product of
the vanishing ideal sheaves of the complements of `U ⊆ X` and of `V ⊆ Y`. -/
theorem support_compl_externalProduct_complementIdeal {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (U : X.Opens) (V : Y.Opens) :
    ((externalProduct f g (complementIdeal U) (complementIdeal V)).support.compl :
        (pullback f g).Opens) =
      pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V :=
  support_externalProduct_compl f g (coe_support_complementIdeal U)
    (coe_support_complementIdeal V)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- Let `X` and `Y` be locally Noetherian schemes over `S` with the resolution property, let
`X ×_S Y` be Noetherian, let `F` be a quasi-coherent `𝒪_{X ×_S Y}`-module and let `𝓘`, `𝓘'` be
quasi-coherent sheaves of ideals on `X` and on `Y`. Every section `s` of `F` over the open
complement of `V(𝓙)`, `𝓙 = pr₁^*𝓘 · pr₂^*𝓘'`, is the image of the unit section of `𝓙ⁿ` under a
morphism `𝓙ⁿ ⟶ F`, for an `n` for which `𝓙ⁿ` is a quotient of `𝓔 ⊠ 𝓖` with `𝓔` finite locally
free on `X` and `𝓖` finite locally free on `Y`. -/
theorem exists_epi_externalTensorProduct_hom_app_oneSection (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian X] [HasResolutionProperty X]
    [IsLocallyNoetherian Y] [HasResolutionProperty Y] [IsNoetherian (pullback f g)]
    (I : X.IdealSheafData) (I' : Y.IdealSheafData) (F : (pullback f g).Modules)
    [F.IsQuasicoherent]
    (s : Γ(F, ((Scheme.IdealSheafData.externalProduct f g I I').support.compl :
      (pullback f g).Opens))) :
    ∃ (n : ℕ) (E : X.Modules) (G : Y.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G)
      (ε : externalTensorProduct f g E G ⟶
        idealPow (Scheme.IdealSheafData.externalProduct f g I I') n) (_ : Epi ε)
      (ψ : idealPow (Scheme.IdealSheafData.externalProduct f g I I') n ⟶ F),
      ψ.app _ (oneSection (Scheme.IdealSheafData.externalProduct f g I I') n) = s := by
  obtain ⟨n, ψ, hψ⟩ := exists_hom_idealPow_app_oneSection_eq_of_isQuasicoherent
    (Scheme.IdealSheafData.externalProduct f g I I') F s
  obtain ⟨E, hE, e, he⟩ := exists_isFiniteLocallyFree_epi_idealPow I n
  obtain ⟨G, hG, e', he'⟩ := exists_isFiniteLocallyFree_epi_idealPow I' n
  have := he
  have := he'
  have hmap : Epi (externalTensorProductMap f g e e') := externalTensorProductMap_epi f g e e'
  refine ⟨n, E, G, hE, hG,
    externalTensorProductMap f g e e' ≫ externalTensorIdealPowMul f g I I' n, ?_, ψ, hψ⟩
  exact @epi_comp _ _ _ _ _ _ hmap _ (epi_externalTensorIdealPowMul f g I I' n)

/-- `exists_epi_externalTensorProduct_hom_app_oneSection` with the section given over any open
`W` identified with the complement of `V(𝓙)` and with the unit section replaced by the existence
of a preimage. -/
theorem exists_epi_externalTensorProduct_hom_app_eq (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian X] [HasResolutionProperty X]
    [IsLocallyNoetherian Y] [HasResolutionProperty Y] [IsNoetherian (pullback f g)]
    (I : X.IdealSheafData) (I' : Y.IdealSheafData) (F : (pullback f g).Modules)
    [F.IsQuasicoherent] {W : (pullback f g).Opens}
    (hW : ((Scheme.IdealSheafData.externalProduct f g I I').support.compl :
      (pullback f g).Opens) = W) (s : Γ(F, W)) :
    ∃ (n : ℕ) (E : X.Modules) (G : Y.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G)
      (ε : externalTensorProduct f g E G ⟶
        idealPow (Scheme.IdealSheafData.externalProduct f g I I') n) (_ : Epi ε)
      (ψ : idealPow (Scheme.IdealSheafData.externalProduct f g I I') n ⟶ F)
      (w : Γ(idealPow (Scheme.IdealSheafData.externalProduct f g I I') n, W)),
      ψ.app W w = s := by
  subst hW
  obtain ⟨n, E, G, hE, hG, ε, hε, ψ, hψ⟩ :=
    exists_epi_externalTensorProduct_hom_app_oneSection f g I I' F s
  exact ⟨n, E, G, hE, hG, ε, hε, ψ, oneSection _ n, hψ⟩

/-- For opens `U ⊆ X` and `V ⊆ Y` and `𝓙` the product of the vanishing ideal sheaves of their
complements, every section of `F` over `U ×_S V = pr₁⁻¹ U ⊓ pr₂⁻¹ V` is the image of a section
of `𝓙ⁿ` under a morphism `𝓙ⁿ ⟶ F`, for an `n` for which `𝓙ⁿ` is a quotient of an external
tensor product of finite locally free modules. -/
theorem exists_epi_externalTensorProduct_hom_app_eq_of_opens (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian X] [HasResolutionProperty X]
    [IsLocallyNoetherian Y] [HasResolutionProperty Y] [IsNoetherian (pullback f g)]
    (U : X.Opens) (V : Y.Opens) (F : (pullback f g).Modules) [F.IsQuasicoherent]
    (s : Γ(F, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) :
    ∃ (n : ℕ) (E : X.Modules) (G : Y.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G)
      (ε : externalTensorProduct f g E G ⟶
        idealPow (Scheme.IdealSheafData.externalProduct f g
          (Scheme.IdealSheafData.complementIdeal U)
          (Scheme.IdealSheafData.complementIdeal V)) n) (_ : Epi ε)
      (ψ : idealPow (Scheme.IdealSheafData.externalProduct f g
        (Scheme.IdealSheafData.complementIdeal U)
        (Scheme.IdealSheafData.complementIdeal V)) n ⟶ F)
      (w : Γ(idealPow (Scheme.IdealSheafData.externalProduct f g
        (Scheme.IdealSheafData.complementIdeal U)
        (Scheme.IdealSheafData.complementIdeal V)) n,
        pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)),
      ψ.app (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) w = s :=
  exists_epi_externalTensorProduct_hom_app_eq f g _ _ F
    (Scheme.IdealSheafData.support_compl_externalProduct_complementIdeal f g U V) s

end AlgebraicGeometry

end

end
