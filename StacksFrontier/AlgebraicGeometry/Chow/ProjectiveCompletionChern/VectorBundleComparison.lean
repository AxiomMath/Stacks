module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.OpenTTrivial
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ChartBase
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundlePoints

/-!
# The open `C = {T ≠ 0}` of the projective completion is the vector bundle `𝐕(𝒞)`

Let `E = Proj_X(Sym^*(𝒞)[T])` and `C ⊆ E` the open where `T` does not vanish, a scheme over `X`
through `π`. Dividing by `T`, which trivializes `𝒪_E(1)` on `C`, every section `m` of `𝒞` gives a
function `m / T` on `C`; this is a morphism of `𝒪_X`-modules `𝒞 ⟶ (C ⟶ X)_* 𝒪_C`, hence a morphism
`C ⟶ 𝐕(𝒞) = Spec_X(Sym^*(𝒞))` over `X`.

## Main definitions

* `Stacks.Chow.ProjectiveCompletion.divT`: the function `m / T` on `C ∩ π⁻¹U`.
* `Stacks.Chow.ProjectiveCompletion.nu`: the morphism `𝒞 ⟶ (C ⟶ X)_* 𝒪_C`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]

/-- The open `C = {T ≠ 0}` as a scheme over `X`. -/
abbrev openToBase : (openT 𝒞).toScheme ⟶ X := (openT 𝒞).ι ≫ proj 𝒞

/-- The image in `E` of the preimage in `C` of an open `U ⊆ X` is contained in `C`. -/
theorem image_preimage_le_openT (U : X.Opens) :
    (openT 𝒞).ι ''ᵁ (openToBase 𝒞 ⁻¹ᵁ U) ≤ openT 𝒞 :=
  Scheme.Opens.ι_image_le _ _

/-- The image in `E` of the preimage in `C` of an open `U ⊆ X` is contained in `π⁻¹U`. -/
theorem image_preimage_le_proj (U : X.Opens) :
    (openT 𝒞).ι ''ᵁ (openToBase 𝒞 ⁻¹ᵁ U) ≤ proj 𝒞 ⁻¹ᵁ U :=
  Scheme.Hom.image_preimage_le (openT 𝒞).ι (proj 𝒞 ⁻¹ᵁ U)

/-- The degree-one section `ψ₁(m)` of `𝒪_E(1)` over `π⁻¹U` of a section `m` of `𝒞`. -/
def psiInl (U : X.Opens) (m : Γ(𝒞, U)) : Γ(twist 𝒞, proj 𝒞 ⁻¹ᵁ U) :=
  ((twistData 𝒞).ψ 1).val.app (op U)
    ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op U)
      (Scheme.Modules.Hom.app (inl 𝒞) U m))

/-- The section `ψ₁(m)` is additive in `m`. -/
theorem psiInl_add (U : X.Opens) (m m' : Γ(𝒞, U)) :
    psiInl 𝒞 U (m + m') = psiInl 𝒞 U m + psiInl 𝒞 U m' := by
  unfold psiInl
  rw [app_add]
  exact (congrArg (fun z => ((twistData 𝒞).ψ 1).val.app (op U) z)
    (((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op U)).hom.map_add _ _)).trans
    ((((twistData 𝒞).ψ 1).val.app (op U)).hom.map_add _ _)

/-- The section `ψ₁(m)` is `𝒪_X(U)`-linear in `m`, acting through `π`. -/
theorem psiInl_smul (U : X.Opens) (c : Γ(X, U)) (m : Γ(𝒞, U)) :
    psiInl 𝒞 U (c • m) = (proj 𝒞).app U c • psiInl 𝒞 U m := by
  unfold psiInl
  rw [Scheme.Modules.Hom.app_smul]
  exact (congrArg (fun z => ((twistData 𝒞).ψ 1).val.app (op U) z)
    (((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op U)).hom.map_smul _ _)).trans
    ((((twistData 𝒞).ψ 1).val.app (op U)).hom.map_smul _ _)

/-- The section `ψ₁(m)` commutes with restriction to a smaller open `U' ⊆ U`. -/
theorem psiInl_res {U U' : X.Opens} (i : U' ≤ U) (m : Γ(𝒞, U)) :
    psiInl 𝒞 U' (𝒞.presheaf.map (homOfLE i).op m) =
      (twist 𝒞).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ i)).op (psiInl 𝒞 U m) := by
  unfold psiInl
  have h1 : Scheme.Modules.Hom.app (inl 𝒞) U' (𝒞.presheaf.map (homOfLE i).op m) =
      (module 𝒞).presheaf.map (homOfLE i).op (Scheme.Modules.Hom.app (inl 𝒞) U m) :=
    PresheafOfModules.naturality_apply (inl 𝒞).val (homOfLE i).op m
  rw [h1]
  refine (congrArg (fun z => ((twistData 𝒞).ψ 1).val.app (op U') z)
    (PresheafOfModules.naturality_apply (Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val
      (homOfLE i).op _)).trans ?_
  exact PresheafOfModules.naturality_apply ((twistData 𝒞).ψ 1).val (homOfLE i).op _

variable (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

/-- **The function `m / T`** on `C ∩ π⁻¹U`, for a section `m` of `𝒞` over `U`. -/
def divT (U : X.Opens) (m : Γ(𝒞, U)) : Γ(space 𝒞, (openT 𝒞).ι ''ᵁ (openToBase 𝒞 ⁻¹ᵁ U)) :=
  (Equiv.ofBijective _ (bijective_smul_coordT 𝒞 r (image_preimage_le_openT 𝒞 U))).symm
    ((twist 𝒞).presheaf.map (homOfLE (image_preimage_le_proj 𝒞 U)).op (psiInl 𝒞 U m))

/-- The function `m / T` times the section `T` is the restriction of `ψ₁(m)` to `C ∩ π⁻¹U`. -/
theorem divT_smul_coordT (U : X.Opens) (m : Γ(𝒞, U)) :
    divT 𝒞 r U m • (twist 𝒞).presheaf.map (homOfLE le_top).op (coordT 𝒞) =
      (twist 𝒞).presheaf.map (homOfLE (image_preimage_le_proj 𝒞 U)).op (psiInl 𝒞 U m) :=
  Equiv.ofBijective_apply_symm_apply
    (fun c : Γ(space 𝒞, (openT 𝒞).ι ''ᵁ (openToBase 𝒞 ⁻¹ᵁ U)) =>
      c • (twist 𝒞).presheaf.map (homOfLE le_top).op (coordT 𝒞))
    (bijective_smul_coordT 𝒞 r (image_preimage_le_openT 𝒞 U)) _

/-- A function `a` on `C ∩ π⁻¹U` with `a • T = ψ₁(m)` there equals `m / T`. -/
theorem eq_divT {U : X.Opens} {m : Γ(𝒞, U)} {a : Γ(space 𝒞, (openT 𝒞).ι ''ᵁ (openToBase 𝒞 ⁻¹ᵁ U))}
    (ha : a • (twist 𝒞).presheaf.map (homOfLE le_top).op (coordT 𝒞) =
      (twist 𝒞).presheaf.map (homOfLE (image_preimage_le_proj 𝒞 U)).op (psiInl 𝒞 U m)) :
    a = divT 𝒞 r U m :=
  (bijective_smul_coordT 𝒞 r (image_preimage_le_openT 𝒞 U)).1
    (ha.trans (divT_smul_coordT 𝒞 r U m).symm)

/-- The function `m / T` is additive in `m`. -/
theorem divT_add (U : X.Opens) (m m' : Γ(𝒞, U)) :
    divT 𝒞 r U (m + m') = divT 𝒞 r U m + divT 𝒞 r U m' := by
  refine (eq_divT 𝒞 r ?_).symm
  rw [add_smul, divT_smul_coordT, divT_smul_coordT, psiInl_add, map_add]

/-- The restriction of a function on `π⁻¹U` to `C ∩ π⁻¹U`. -/
abbrev resC (U : X.Opens) (c : Γ(space 𝒞, proj 𝒞 ⁻¹ᵁ U)) :
    Γ(space 𝒞, (openT 𝒞).ι ''ᵁ (openToBase 𝒞 ⁻¹ᵁ U)) :=
  (space 𝒞).presheaf.map (homOfLE (image_preimage_le_proj 𝒞 U)).op c

/-- For a function `c` on `U`, `(c • m) / T` is the pullback of `c` times `m / T`. -/
theorem divT_smul (U : X.Opens) (c : Γ(X, U)) (m : Γ(𝒞, U)) :
    divT 𝒞 r U (c • m) = resC 𝒞 U ((proj 𝒞).app U c) * divT 𝒞 r U m := by
  refine (eq_divT 𝒞 r ?_).symm
  rw [mul_smul, divT_smul_coordT, psiInl_smul, Scheme.Modules.map_smul]

/-- The function `m / T` commutes with restriction to a smaller open `U' ⊆ U`. -/
theorem divT_res {U U' : X.Opens} (i : U' ≤ U) (m : Γ(𝒞, U)) :
    divT 𝒞 r U' (𝒞.presheaf.map (homOfLE i).op m) =
      (space 𝒞).presheaf.map (homOfLE (Scheme.Hom.image_mono _
        (Scheme.Hom.preimage_mono _ i))).op (divT 𝒞 r U m) := by
  refine (eq_divT 𝒞 r ?_).symm
  have h := congrArg ((twist 𝒞).presheaf.map (homOfLE (Scheme.Hom.image_mono _
    (Scheme.Hom.preimage_mono _ i))).op) (divT_smul_coordT 𝒞 r U m)
  rw [psiInl_res]
  simp only [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at h ⊢
  exact h

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] in
/-- Pulling back a function on `π⁻¹U` to `C` is restricting it and reading it on `C`. -/
theorem appIso_hom_resC (U : X.Opens) (c : Γ(space 𝒞, proj 𝒞 ⁻¹ᵁ U)) :
    ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ U)).hom (resC 𝒞 U c) =
      (openT 𝒞).ι.app (proj 𝒞 ⁻¹ᵁ U) c := by
  have key : (space 𝒞).presheaf.map (homOfLE (image_preimage_le_proj 𝒞 U)).op ≫
      ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ U)).hom = (openT 𝒞).ι.app (proj 𝒞 ⁻¹ᵁ U) := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    exact Scheme.Hom.appLE_eq_app _
  exact congrArg (fun φ => φ c) key

/-- **The morphism `𝒞 ⟶ (C ⟶ X)_* 𝒪_C`**, `m ↦ m / T`. -/
def nu : 𝒞 ⟶ Scheme.Modules.structurePushforward (openToBase 𝒞) :=
  Stacks.AlgebraicGeometry.ModuleLimits.homOfSections
    (fun U m => (show Γ(Scheme.Modules.structurePushforward (openToBase 𝒞), U) from
      ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ U)).hom (divT 𝒞 r U m)))
    (fun U m m' => by
      change ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ U)).hom (divT 𝒞 r U (m + m')) = _
      rw [divT_add, map_add]
      rfl)
    (fun U c m => by
      change ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ U)).hom (divT 𝒞 r U (c • m)) = _
      rw [divT_smul, map_mul, appIso_hom_resC]
      rfl)
    (fun U U' i m => by
      change ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ U)).hom
        (divT 𝒞 r U (𝒞.presheaf.map (homOfLE i).op m)) = _
      rw [divT_res]
      exact congrArg (fun φ => φ (divT 𝒞 r U' m))
        (Scheme.Hom.appIso_hom_naturality (openT 𝒞).ι
          (homOfLE (Scheme.Hom.preimage_mono (openToBase 𝒞) i)).op))

/-- On sections over `U`, the morphism `nu` sends `m` to the function `m / T` on `C`. -/
theorem nu_app (U : X.Opens) (m : Γ(𝒞, U)) :
    Scheme.Modules.Hom.app (nu 𝒞 r) U m =
      ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ U)).hom (divT 𝒞 r U m) := rfl

end Stacks.Chow.ProjectiveCompletion
