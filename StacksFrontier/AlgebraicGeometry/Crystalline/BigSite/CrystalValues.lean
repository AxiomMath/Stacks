module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineBaseChangeAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.FiniteLocallyFreeCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealSheaf

/-!
# The values of a quasi-coherent crystal on `CRIS(X/S)` along a morphism of affine objects

Let `F` be a quasi-coherent sheaf of `𝒪_{X/S}`-modules on the big crystalline site and let
`g : (U', T', δ') ⟶ (U, T, δ)` be a morphism of `CRIS(X/S)` whose two ambient schemes are affine.
The base change of sections along `g`,

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} F(U, T, δ) ⟶ F(U', T', δ')`,  `t ⊗ s ↦ t · g^* s`,

is bijective.  This is the crystal property of `F` read on the values of `F` rather than on its
restrictions `F_T`.

## Main results

In the namespace `Crystalline.GlobalCrystallineSituation`:

* `bijective_extensionSectionsMapAlong_of_isQuasicoherentOnSite`: the base change of sections of a
  quasi-coherent module along a morphism of affine objects is bijective.
* `IsFiniteLocallyFreeQuasicoherentCrystal.bijective_extensionSectionsMapAlong`: the same for a
  crystal in finite locally free modules.
* `extensionSectionsLinearEquivAlong`: the base change of sections as a linear equivalence over
  `Γ(T', 𝒪_{T'})`.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) {A A' : Thickening S} (g : A' ⟶ A)

/-- **The base change of the sections of a quasi-coherent sheaf of `𝒪_{X/S}`-modules along a
morphism of `CRIS(X/S)` with affine ambient schemes is bijective**:

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} F(U, T, δ) ≅ F(U', T', δ')`,  `t ⊗ s ↦ t · g^* s`. -/
theorem bijective_extensionSectionsMapAlong_of_isQuasicoherentOnSite
    [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
    (hM : M.IsQuasicoherentOnSite) :
    Function.Bijective (extensionSectionsMapAlong M g) := by
  have : (ambientSchemeModules M A).IsQuasicoherent :=
    isQuasicoherent_ambientModuleRestriction
      (isLocallyQuasiCoherent_of_isQuasicoherentOnSite M hM) A
  exact bijective_extensionSectionsMapAlong M g (isSheafCrystal_of_isQuasicoherentOnSite M hM)

/-- **The base change of the sections of a crystal in finite locally free modules along a morphism
of `CRIS(X/S)` with affine ambient schemes is bijective.** -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.bijective_extensionSectionsMapAlong
    [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (hM : IsFiniteLocallyFreeQuasicoherentCrystal M) :
    Function.Bijective (extensionSectionsMapAlong M g) :=
  bijective_extensionSectionsMapAlong_of_isQuasicoherentOnSite M g hM.isQuasicoherentOnSite

/-- The sections of `F` over the source of `g`, as a module over the synonym
`Crystalline.GlobalCrystallineSituation.ringAlong` of the sections of `𝒪_{X/S}` there, acting
through the identity. -/
instance moduleRingAlongValues : Module (ringAlong g) (M.val.obj (op A')) :=
  inferInstanceAs (Module (crysSheafRing S A') (M.val.obj (op A')))

/-- The action of `Crystalline.GlobalCrystallineSituation.moduleRingAlongValues` is the action
of the sections of `𝒪_{X/S}` over the source of `g`. -/
theorem ringAlong_smul_sections (t : ringAlong g) (x : M.val.obj (op A')) :
    t • x = siteRingAlong g t • x := rfl

/-- **The base change of sections along `g` is linear over `Γ(T', 𝒪_{T'})`**, acting on the left
factor of the tensor product. -/
theorem extensionSectionsMapAlong_smul (t : ringAlong g)
    (z : ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A)) :
    extensionSectionsMapAlong M g (t • z) = t • extensionSectionsMapAlong M g z := by
  induction z using TensorProduct.inductionOn with
  | tmul t' s =>
      rw [TensorProduct.smul_tmul', extensionSectionsMapAlong_tmul,
        extensionSectionsMapAlong_tmul, ringAlong_smul_sections, smul_smul]
      rfl
  | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]

/-- **The base change of sections along `g`, as a map of `Γ(T', 𝒪_{T'})`-modules.** -/
def extensionSectionsLinearMapAlong :
    ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A) →ₗ[ringAlong g] M.val.obj (op A') where
  toFun := extensionSectionsMapAlong M g
  map_add' := map_add _
  map_smul' := extensionSectionsMapAlong_smul M g

/-- `Crystalline.GlobalCrystallineSituation.extensionSectionsLinearMapAlong` on a pure tensor. -/
@[simp]
theorem extensionSectionsLinearMapAlong_tmul (t : ringAlong g) (s : M.val.obj (op A)) :
    extensionSectionsLinearMapAlong M g (t ⊗ₜ[crysSheafRing S A] s) =
      siteRingAlong g t • moduleSiteRestrict M g s :=
  extensionSectionsMapAlong_tmul M g t s

/-- **The base change of the sections of a quasi-coherent sheaf of `𝒪_{X/S}`-modules along a
morphism of `CRIS(X/S)` with affine ambient schemes, as a linear equivalence over
`Γ(T', 𝒪_{T'})`**:

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} F(U, T, δ) ≃ F(U', T', δ')`,  `t ⊗ s ↦ t · g^* s`. -/
def extensionSectionsLinearEquivAlong
    [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
    (hM : M.IsQuasicoherentOnSite) :
    ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A) ≃ₗ[ringAlong g] M.val.obj (op A') :=
  LinearEquiv.ofBijective (extensionSectionsLinearMapAlong M g)
    (bijective_extensionSectionsMapAlong_of_isQuasicoherentOnSite M g hM)

/-- `Crystalline.GlobalCrystallineSituation.extensionSectionsLinearEquivAlong` on a pure
tensor. -/
@[simp]
theorem extensionSectionsLinearEquivAlong_tmul
    [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
    (hM : M.IsQuasicoherentOnSite) (t : ringAlong g) (s : M.val.obj (op A)) :
    extensionSectionsLinearEquivAlong M g hM (t ⊗ₜ[crysSheafRing S A] s) =
      siteRingAlong g t • moduleSiteRestrict M g s :=
  extensionSectionsMapAlong_tmul M g t s

end Crystalline.GlobalCrystallineSituation

end

end
