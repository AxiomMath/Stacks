module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.VectorBundleIso
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The zero section of the projective completion

Let `E = Proj_X(Sym^*(𝒞)[T])` with projection `π`, and let `j : 𝐕(𝒞) ⟶ E` be the inclusion of the
vector bundle `𝐕(𝒞) = Spec_X(Sym^*(𝒞))` as the open `C = {T ≠ 0}`. The **zero section**
`i : X ⟶ E` is the zero section of `𝐕(𝒞)` followed by `j`. It is a section of `π`, hence a closed
immersion.

Over an affine open `V` of `X`, `i` maps `V` into the chart `W = D₊(T)`, and on functions it sends
the coordinate `y_m = m / T` to `0` and the pullback of a function `r` on `V` to `r`.

## Main definitions

* `Stacks.Chow.ProjectiveCompletion.vectorBundleIncl`: `j : 𝐕(𝒞) ⟶ E`.
* `Stacks.Chow.ProjectiveCompletion.zeroSec`: `i : X ⟶ E`.

## Main results

* `Stacks.Chow.ProjectiveCompletion.vectorBundleIncl_proj`: `j ≫ π = p`.
* `Stacks.Chow.ProjectiveCompletion.zeroSec_proj`: `i ≫ π = 𝟙`.
* `Stacks.Chow.ProjectiveCompletion.isClosedImmersion_zeroSec`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

/-- **The inclusion `j : 𝐕(𝒞) ⟶ E`** of the vector bundle as the open `C = {T ≠ 0}`. -/
@[sga "5 VII 9.1"]
def vectorBundleIncl : Scheme.Modules.vectorBundle X 𝒞 ⟶ space 𝒞 :=
  inv (toVectorBundle 𝒞 r).left ≫ (openT 𝒞).ι

/-- The inclusion `j : 𝐕(𝒞) ⟶ E` is an open immersion. -/
@[sga "5 VII 9.1" "(ii)"]
instance isOpenImmersion_vectorBundleIncl : IsOpenImmersion (vectorBundleIncl 𝒞 r) := by
  unfold vectorBundleIncl
  infer_instance

/-- **`j` is a morphism over `X`**: `j ≫ π = p`. -/
@[sga "5 VII 9.1" "(ii)"]
theorem vectorBundleIncl_proj :
    vectorBundleIncl 𝒞 r ≫ proj 𝒞 = Scheme.Modules.vectorBundleToBase X 𝒞 := by
  rw [vectorBundleIncl, Category.assoc, IsIso.inv_comp_eq]
  exact (Over.w (toVectorBundle 𝒞 r)).symm

/-- **The zero section `i : X ⟶ E`** of the projective completion. -/
def zeroSec : X ⟶ space 𝒞 :=
  (Scheme.Modules.vectorBundleOverZeroSection 𝒞).left ≫ vectorBundleIncl 𝒞 r

/-- The zero section is a section of `π`: `i ≫ π = 𝟙 X`. -/
theorem zeroSec_proj : zeroSec 𝒞 r ≫ proj 𝒞 = 𝟙 X := by
  rw [zeroSec, Category.assoc, vectorBundleIncl_proj]
  exact Scheme.Modules.vectorBundleOverZeroSection_left_comp 𝒞

/-- The zero section `i : X ⟶ E` is a closed immersion. -/
instance isClosedImmersion_zeroSec : IsClosedImmersion (zeroSec 𝒞 r) := by
  have : IsClosedImmersion (zeroSec 𝒞 r ≫ proj 𝒞) := by
    rw [zeroSec_proj]
    infer_instance
  exact IsClosedImmersion.of_comp (zeroSec 𝒞 r) (proj 𝒞)

/-- The zero section takes values in the open `C = {T ≠ 0}`. -/
theorem range_zeroSec_le_openT (x : X) : zeroSec 𝒞 r x ∈ openT 𝒞 := by
  change ((Scheme.Modules.vectorBundleOverZeroSection 𝒞).left ≫ inv (toVectorBundle 𝒞 r).left ≫
    (openT 𝒞).ι) x ∈ openT 𝒞
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact ((openT 𝒞).ι_image_le ⊤) ⟨_, trivial, rfl⟩

/-! ### The zero section on the functions of a chart -/

section Affine

variable {V : X.Opens} (hV : IsAffineOpen V)

/-- The identity morphism induces the identity on sections over an open. -/
private theorem appLE_id_apply {Y : Scheme.{u}} {U : Y.Opens} (e : U ≤ (𝟙 Y : Y ⟶ Y) ⁻¹ᵁ U)
    (z : Γ(Y, U)) : ((𝟙 Y : Y ⟶ Y).appLE U U e).hom z = z := by
  change (Y.presheaf.map (homOfLE e).op).hom ((Scheme.Hom.app (𝟙 Y) U).hom z) = z
  rw [Scheme.Hom.id_app]
  exact congrArg (fun φ : Γ(Y, U) ⟶ Γ(Y, U) => φ.hom z) (Y.presheaf.map_id (op U))

/-- The zero section maps `V` into the chart `W = D₊(T)` over `V`. -/
theorem le_preimage_zeroSec_openW : V ≤ zeroSec 𝒞 r ⁻¹ᵁ openW 𝒞 hV := by
  intro x hx
  change zeroSec 𝒞 r x ∈ openW 𝒞 hV
  rw [openW_eq]
  refine ⟨range_zeroSec_le_openT 𝒞 r x, ?_⟩
  change (zeroSec 𝒞 r ≫ proj 𝒞) x ∈ V
  rw [zeroSec_proj]
  exact hx

/-- **The zero section on the functions of the chart `W`**, `Γ(E, W) ⟶ Γ(X, V)`. -/
abbrev zeta : Γ(space 𝒞, openW 𝒞 hV) ⟶ Γ(X, V) :=
  (zeroSec 𝒞 r).appLE (openW 𝒞 hV) V (le_preimage_zeroSec_openW 𝒞 r hV)

/-- The zero section is a section of `π`, read on the functions of `W`. -/
theorem zeta_proj_app (c : Γ(X, V)) :
    zeta 𝒞 r hV ((space 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op ((proj 𝒞).app V c)) =
      c := by
  have h1 : (space 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op ≫ zeta 𝒞 r hV =
      (zeroSec 𝒞 r).appLE (proj 𝒞 ⁻¹ᵁ V) V
        ((le_preimage_zeroSec_openW 𝒞 r hV).trans (Scheme.Hom.preimage_mono _ (openW_le 𝒞 hV))) :=
    Scheme.Hom.map_appLE _ _ _
  have h2 := Scheme.Hom.comp_appLE (zeroSec 𝒞 r) (proj 𝒞) V V
    (by rw [zeroSec_proj]; exact le_rfl)
  rw [Stacks.Chow.ProjectiveCompletion.appLE_congr_of_eq (zeroSec_proj 𝒞 r)] at h2
  have h4 := congrArg (fun φ : Γ(X, V) ⟶ Γ(X, V) => φ.hom c) h2
  refine Eq.trans ?_ (h4.symm.trans (appLE_id_apply _ c))
  exact congrArg (fun φ : Γ(space 𝒞, proj 𝒞 ⁻¹ᵁ V) ⟶ Γ(X, V) => φ.hom ((proj 𝒞).app V c)) h1

/-- The inverse of the isomorphism `C ≅ 𝐕(𝒞)` is a morphism over `X`. -/
theorem inv_toVectorBundle_openToBase :
    inv (toVectorBundle 𝒞 r).left ≫ openToBase 𝒞 = Scheme.Modules.vectorBundleToBase X 𝒞 := by
  rw [IsIso.inv_comp_eq]
  exact (Over.w (toVectorBundle 𝒞 r)).symm

/-- The ring isomorphism `kappa` is the map on functions of the open immersion `C ⟶ E`, from `W` to
`C ∩ π⁻¹V`. -/
theorem kappa_eq_appLE (x : Γ(space 𝒞, openW 𝒞 hV)) :
    kappa 𝒞 hV x = (openT 𝒞).ι.appLE (openW 𝒞 hV) (openToBase 𝒞 ⁻¹ᵁ V)
      (by rw [← image_preimage_openToBase_eq 𝒞 hV, Scheme.Hom.preimage_image_eq]) x := by
  have h := Scheme.Hom.map_appLE (openT 𝒞).ι
    (Scheme.Hom.preimage_image_eq (openT 𝒞).ι (openToBase 𝒞 ⁻¹ᵁ V)).ge
    (eqToHom (image_preimage_openToBase_eq 𝒞 hV)).op
  change ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ V)).hom
    ((space 𝒞).presheaf.map (eqToHom (image_preimage_openToBase_eq 𝒞 hV)).op x) = _
  rw [Scheme.Hom.appIso_hom']
  exact congrArg (fun φ : Γ(space 𝒞, openW 𝒞 hV) ⟶ Γ((openT 𝒞).toScheme, openToBase 𝒞 ⁻¹ᵁ V) =>
    φ.hom x) h

/-- The identification `Sym_R(M) ≅ Γ(𝐕(𝒞), p⁻¹V)`. -/
def symVB (a : SymmetricAlgebra Γ(X, V) Γ(𝒞, V)) :
    Γ(Scheme.Modules.vectorBundle X 𝒞, Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) :=
  haveI := Scheme.Modules.isAffineHom_vectorBundleOver X (F := 𝒞)
  ((Scheme.Modules.vectorBundlePushforwardIso X (F := 𝒞)).inv.right.hom.app (op V)).hom
    (Stacks.SymAlgSections.symSectionsRingEquiv 𝒞 hV a)

/-- The ring map `theta` is the map on functions of `C ⟶ 𝐕(𝒞)` from `p⁻¹V` to `C ∩ π⁻¹V`,
precomposed with `symVB`. -/
theorem theta_eq_appLE (a : SymmetricAlgebra Γ(X, V) Γ(𝒞, V)) :
    theta 𝒞 r hV a = (toVectorBundle 𝒞 r).left.appLE
      (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) (openToBase 𝒞 ⁻¹ᵁ V)
      (preimage_toVectorBundle 𝒞 r V).ge (symVB 𝒞 hV a) := by
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := 𝒞)
  change toVectorBundleRing 𝒞 r V _ = _
  rw [toVectorBundleRing_apply]
  exact congrArg (fun φ : Γ(Scheme.Modules.vectorBundle X 𝒞,
      Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) ⟶ Γ((openT 𝒞).toScheme, openToBase 𝒞 ⁻¹ᵁ V) =>
      φ.hom (symVB 𝒞 hV a))
    (pushforwardAlgebraMap_app (toVectorBundle 𝒞 r) V (preimage_toVectorBundle 𝒞 r V).ge)

/-- The inverse of `C ≅ 𝐕(𝒞)` maps `p⁻¹V` into `C ∩ π⁻¹V`. -/
theorem le_preimage_inv_toVectorBundle :
    Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V ≤
      inv (toVectorBundle 𝒞 r).left ⁻¹ᵁ (openToBase 𝒞 ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, inv_toVectorBundle_openToBase]

/-- On functions over `p⁻¹V`, the maps induced by `C ⟶ 𝐕(𝒞)` and its inverse compose to the
identity. -/
theorem inv_appLE_appLE
    (z : Γ(Scheme.Modules.vectorBundle X 𝒞, Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V)) :
    (inv (toVectorBundle 𝒞 r).left).appLE (openToBase 𝒞 ⁻¹ᵁ V)
        (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) (le_preimage_inv_toVectorBundle 𝒞 r)
      ((toVectorBundle 𝒞 r).left.appLE (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V)
        (openToBase 𝒞 ⁻¹ᵁ V) (preimage_toVectorBundle 𝒞 r V).ge z) = z := by
  have h := Scheme.Hom.appLE_comp_appLE (inv (toVectorBundle 𝒞 r).left)
    (toVectorBundle 𝒞 r).left (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V)
    (openToBase 𝒞 ⁻¹ᵁ V) (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V)
    (preimage_toVectorBundle 𝒞 r V).ge (le_preimage_inv_toVectorBundle 𝒞 r)
  rw [Stacks.Chow.ProjectiveCompletion.appLE_congr_of_eq (IsIso.inv_hom_id _)] at h
  refine (congrArg (fun φ : Γ(Scheme.Modules.vectorBundle X 𝒞,
      Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) ⟶ Γ(Scheme.Modules.vectorBundle X 𝒞,
        Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) => φ.hom z) h).trans ?_
  exact appLE_id_apply _ z

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] in
/-- The zero section of `𝐕(𝒞)` maps `V` into `p⁻¹V`. -/
theorem le_preimage_zeroSection :
    V ≤ (Scheme.Modules.vectorBundleOverZeroSection 𝒞).left ⁻¹ᵁ
      (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, Scheme.Modules.vectorBundleOverZeroSection_left_comp]
  exact le_rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] in
/-- **The zero section kills the generators**: the section `m` of `𝒞`, read as a function on
`𝐕(𝒞)` over `V`, vanishes on the zero section. -/
theorem zeroSection_appLE_symVB_ι (m : Γ(𝒞, V)) :
    (Scheme.Modules.vectorBundleOverZeroSection 𝒞).left.appLE
        (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) V (le_preimage_zeroSection 𝒞 (V := V))
      (symVB 𝒞 hV (SymmetricAlgebra.ι Γ(X, V) Γ(𝒞, V) m)) = 0 := by
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := 𝒞)
  have h2 := Scheme.Modules.vectorBundleHomEquiv_apply 𝒞 (Over.mk (𝟙 X))
    (Scheme.Modules.vectorBundleOverZeroSection 𝒞)
  have h3 := congrArg (fun φ => (SheafOfModules.Hom.val φ).app (op V) m)
    (h2.symm.trans (Scheme.Modules.vectorBundleHomEquiv_vectorBundleOverZeroSection 𝒞))
  refine Eq.trans ?_ h3
  change _ = ((((Scheme.Modules.symmetricAlgebraSheafComparison 𝒞).hom ≫
    (Scheme.Modules.vectorBundlePushforwardIso X (F := 𝒞)).inv ≫
      pushforwardAlgebraMap (Scheme.Modules.vectorBundleOverZeroSection 𝒞)).right.hom.app
        (op V)).hom
    (Stacks.RelativeSpec.ungradedAlgebraSheafIncl X _ _ 1 V
      (((Scheme.Modules.symmetricAlgebraGen X 𝒞).val.app (op V)) m)))
  change _ = ((pushforwardAlgebraMap (Scheme.Modules.vectorBundleOverZeroSection 𝒞)).right.hom.app
    (op V)).hom (((Scheme.Modules.vectorBundlePushforwardIso X (F := 𝒞)).inv.right.hom.app
      (op V)).hom (((Scheme.Modules.symmetricAlgebraSheafComparison 𝒞).hom.right.hom.app
        (op V)).hom (Stacks.RelativeSpec.ungradedAlgebraSheafIncl X _ _ 1 V
          (((Scheme.Modules.symmetricAlgebraGen X 𝒞).val.app (op V)) m))))
  rw [symmetricAlgebraSheafComparison_hom_ungradedAlgebraSheafIncl,
    ← Stacks.SymAlgSections.symSectionsRingEquiv_ι_eq_ungradedIncl 𝒞 hV]
  exact (congrArg (fun φ : Γ(Scheme.Modules.vectorBundle X 𝒞,
      Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) ⟶ Γ(X, V) => φ.hom
        (symVB 𝒞 hV (SymmetricAlgebra.ι Γ(X, V) Γ(𝒞, V) m)))
    (pushforwardAlgebraMap_app (Scheme.Modules.vectorBundleOverZeroSection 𝒞) V
      (le_preimage_zeroSection 𝒞 (V := V)))).symm

/-- **The zero section kills the coordinates**: `i^*(y_m) = 0` on `V`. -/
theorem zeta_coordY (m : Γ(𝒞, V)) : zeta 𝒞 r hV (coordY 𝒞 hV m) = 0 := by
  have e1 : openToBase 𝒞 ⁻¹ᵁ V ≤ (openT 𝒞).ι ⁻¹ᵁ openW 𝒞 hV := by
    rw [← image_preimage_openToBase_eq 𝒞 hV, Scheme.Hom.preimage_image_eq]
  have hAB := Scheme.Hom.appLE_comp_appLE (inv (toVectorBundle 𝒞 r).left) (openT 𝒞).ι
    (openW 𝒞 hV) (openToBase 𝒞 ⁻¹ᵁ V) (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) e1
    (le_preimage_inv_toVectorBundle 𝒞 r)
  have hABC := Scheme.Hom.appLE_comp_appLE (Scheme.Modules.vectorBundleOverZeroSection 𝒞).left
    (inv (toVectorBundle 𝒞 r).left ≫ (openT 𝒞).ι) (openW 𝒞 hV)
    (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) V
    ((le_preimage_inv_toVectorBundle 𝒞 r).trans
      ((Opens.map (inv (toVectorBundle 𝒞 r).left).base).map (homOfLE e1)).le)
    (le_preimage_zeroSection 𝒞 (V := V))
  have hz : zeta 𝒞 r hV (coordY 𝒞 hV m) =
      (Scheme.Modules.vectorBundleOverZeroSection 𝒞).left.appLE
        (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) V (le_preimage_zeroSection 𝒞 (V := V))
        ((inv (toVectorBundle 𝒞 r).left).appLE (openToBase 𝒞 ⁻¹ᵁ V)
          (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) (le_preimage_inv_toVectorBundle 𝒞 r)
          ((openT 𝒞).ι.appLE (openW 𝒞 hV) (openToBase 𝒞 ⁻¹ᵁ V) e1 (coordY 𝒞 hV m))) := by
    rw [← hAB] at hABC
    exact (congrArg (fun φ : Γ(space 𝒞, openW 𝒞 hV) ⟶ Γ(X, V) => φ.hom (coordY 𝒞 hV m))
      hABC).symm
  rw [hz, ← kappa_eq_appLE, ← theta_ι 𝒞 r hV, theta_eq_appLE, inv_appLE_appLE]
  exact zeroSection_appLE_symVB_ι 𝒞 hV m

end Affine

end Stacks.Chow.ProjectiveCompletion
