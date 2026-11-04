module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.IntegralTransform
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ThickeningInvariance

/-!
# A kernel supported on a closed subscheme, trivial there

Let `q₁ : Q ⟶ X` and `q₃ : Q ⟶ T` be morphisms of schemes, `𝓜` a sheaf of `Λ`-modules on `Q` with
`- ⊗ 𝓜` exact, and `Q = Q_U ⊔ Q_Δ` a decomposition into an open and the complementary closed
subscheme. If `R(q₃|_{Q_U})_!` kills `(q₁⁻¹ K ⊗ 𝓜)|_{Q_U}` and `𝓜|_{Q_Δ}` is the unit `Λ`, then

`R q₃! (q₁⁻¹ K ⊗ 𝓜) ≅ R (q₃|_{Q_Δ})_! ((q₁|_{Q_Δ})⁻¹ K)`.

This is the step of Fourier inversion where the kernel `L_ψ(t(x + u))` of `Φ ∘ Φ` on
`Q = 𝔸¹_x × 𝔸¹_t × 𝔸¹_u` contributes nothing off the antidiagonal `x + u = 0` (there its
cohomology along `t` vanishes) and is trivial on it. The isomorphism is the second map of the
open-closed triangle of [Stacks, Tag 0GKP], whose first vertex vanishes.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedTensorRightUnitIso`: `- ⊗ N ≅ id` on `D⁺` when
  `N ≅ Λ`.

## Main results

* `Stacks.EtaleCohomology.IsExactTensorRight.of_iso`,
  `Stacks.EtaleCohomology.isExactTensorRight_unit`.
* `Stacks.EtaleCohomology.nonempty_derivedLowerShriek_tensor_iso_closed_of_isZero_open`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  isMonoidal_W_etaleModules etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ]

/-- Additivity and preservation of finite limits and colimits transfer along a natural
isomorphism of functors. -/
private theorem additive_and_preservesFinite_of_iso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasFiniteLimits C] [HasFiniteColimits C] {F G : C ⥤ D}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : F ≅ G) :
    G.Additive ∧ PreservesFiniteLimits G ∧ PreservesFiniteColimits G :=
  ⟨Functor.additive_of_iso e, preservesFiniteLimits_of_natIso e,
    preservesFiniteColimits_of_natIso e⟩

variable {Λ} in
/-- Exactness of `- ⊗ N` is invariant under isomorphism of `N`. -/
theorem IsExactTensorRight.of_iso {X : Scheme.{u}} {A B : EtaleModules.{u, 0} Λ X} (e : A ≅ B)
    (hA : IsExactTensorRight Λ A) : IsExactTensorRight Λ B := by
  have := hA.1; have := hA.2.1; have := hA.2.2
  exact additive_and_preservesFinite_of_iso ((tensoringRight _).mapIso e)

/-- `- ⊗ Λ` is exact: it is the identity. -/
theorem isExactTensorRight_unit (X : Scheme.{u}) :
    IsExactTensorRight Λ (𝟙_ (EtaleModules.{u, 0} Λ X)) :=
  additive_and_preservesFinite_of_iso (rightUnitorNatIso _).symm

/-- **`- ⊗ N ≅ id` on `D⁺` when `N ≅ Λ`**, from the right unitor. -/
def etaleModuleDerivedTensorRightUnitIso {X : Scheme.{u}} {N : EtaleModules.{u, 0} Λ X}
    (e : N ≅ 𝟙_ _) (hN : IsExactTensorRight Λ N) :
    etaleModuleDerivedTensorRight Λ N hN ≅ 𝟭 _ :=
  haveI := hN.1; haveI := hN.2.1; haveI := hN.2.2
  Stacks.DerivedFunctor.mapDerivedCategoryPlusNatIso
      ((tensoringRight _).mapIso e ≪≫ rightUnitorNatIso _) ≪≫
    Functor.mapDerivedCategoryPlusIdIso

section Support

variable {Q T X : Scheme.{u}} (q₁ : Q ⟶ X) {q₃ : Q ⟶ T} [QuasiCompact q₃]
  (jQ : CompactificationOf (Over.mk q₃)) {QU QΔ : Scheme.{u}} (jU : QU ⟶ Q) [IsOpenImmersion jU]
  (iΔ : QΔ ⟶ Q) [IsClosedImmersion iΔ] (hij : Set.range jU.base = (Set.range iΔ.base)ᶜ)
  (𝓜 : EtaleModules.{u, 0} Λ Q) (h𝓜 : IsExactTensorRight Λ 𝓜)
  (eΔ : (etaleModuleInverseImage.{u, 0} Λ iΔ).obj 𝓜 ≅ 𝟙_ _)

include hij eΔ in
/-- **A kernel without cohomology off a closed subscheme, and trivial on it.** If
`R(q₃|_{Q_U})_!` kills `(q₁⁻¹ K ⊗ 𝓜)|_{Q_U}` and `𝓜|_{Q_Δ} ≅ Λ`, then
`R q₃! (q₁⁻¹ K ⊗ 𝓜) ≅ R(q₃|_{Q_Δ})_! ((q₁|_{Q_Δ})⁻¹ K)`: the second map of the open-closed
triangle of [Stacks, Tag 0GKP] is invertible, its first vertex being zero. -/
theorem nonempty_derivedLowerShriek_tensor_iso_closed_of_isZero_open
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hU : IsZero ((derivedLowerShriek.{u, 0} (jU ≫ q₃) (jQ.restrictOpen jU) Λ).obj
      ((etaleModuleRestriction.{u, 0} Λ jU).mapDerivedCategoryPlus.obj
        ((etaleModuleDerivedTensorRight Λ 𝓜 h𝓜).obj
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ q₁).obj K))))) :
    Nonempty ((derivedLowerShriek.{u, 0} q₃ jQ Λ).obj ((etaleModuleDerivedTensorRight Λ 𝓜 h𝓜).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ q₁).obj K)) ≅
      (derivedLowerShriek.{u, 0} (iΔ ≫ q₃) (jQ.restrictClosed iΔ) Λ).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (iΔ ≫ q₁)).obj K)) := by
  obtain ⟨a, b, c, h⟩ := exists_distTriang_derivedLowerShriek_openClosed_plus Λ jQ jU iΔ hij
    ((etaleModuleDerivedTensorRight Λ 𝓜 h𝓜).obj
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ q₁).obj K))
  have : IsIso b := (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ h).1 hU
  have h𝓜Δ : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ iΔ).obj 𝓜) :=
    (isExactTensorRight_unit Λ QΔ).of_iso eΔ.symm
  exact ⟨asIso b ≪≫ (derivedLowerShriek.{u, 0} (iΔ ≫ q₃) (jQ.restrictClosed iΔ) Λ).mapIso
    ((etaleModuleDerivedInverseImageTensorRightIso Λ iΔ 𝓜 h𝓜 h𝓜Δ).app _ ≪≫
      (etaleModuleDerivedTensorRightUnitIso Λ eΔ h𝓜Δ).app _ ≪≫
      ((etaleModuleDerivedInverseImagePlusCompIsoAny Λ iΔ q₁).app K).symm)⟩

end Support

end Stacks.EtaleCohomology

end
