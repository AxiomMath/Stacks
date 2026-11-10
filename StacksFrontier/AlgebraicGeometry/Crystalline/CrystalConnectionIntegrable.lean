module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningSections

/-!
# Integrability of the canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6]

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site, let `(U, T, δ)` be an object of `CRIS(X/S)`,
and write `D = Γ(T, 𝒪_T)`, `Ω = Γ(T, Ω_{T/S,δ})`, `Ω² = Γ(T, Ω²_{T/S,δ})` and `M = F(U, T, δ)`.

`Crystalline.GlobalCrystallineSituation.crystalConnection` is the canonical connection
`∇(s) = p₁^* s - p₀^* s`, a section of `F` over the first-order universal thickening
`(U, T', δ')` of [Stacks, Tag 07J2] killed by restriction along the diagonal, and
`Crystalline.GlobalCrystallineSituation.crystalConnectionTensor` is that connection read inside
`Ω ⊗_D M`.  This module proves that the composite `∇ ∘ ∇ : M ⟶ Ω² ⊗_D M` of that connection
with its own degree-one extension of §07J5 vanishes, computing on the second-order universal
thickening `(U, T'', δ'')` of [Stacks, Tag 07J3], with
`𝒪_{T''} = 𝒪_T ⊕ Ω_{T/S,δ} ⊕ Ω_{T/S,δ} ⊕ Ω²_{T/S,δ}` and the three morphisms
`q₀₁, q₁₂, q₀₂ : T'' ⟶ T'`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.diffAction₂` — the degree-two canonical map
  `Ω² ⊗_D M ⟶ F(U, T'', δ'')`, `η ⊗ s ↦ η · q₀^* s`.
* `Crystalline.GlobalCrystallineSituation.crysWedgeRight` — exterior multiplication on the right
  by a one-form, `Ω ⊗_D M ⟶ Ω² ⊗_D M`.
* `Crystalline.GlobalCrystallineSituation.extendedConnectionTensor` — the degree-one extension
  `∇(ω ⊗ s) = ∇(s) ∧ ω + (d ω) ⊗ s` of the connection.
* `Crystalline.GlobalCrystallineSituation.diffActionLeft` and
  `Crystalline.GlobalCrystallineSituation.diffActionRight` — the canonical maps into the two
  middle summands of `𝒪_{T''}`.
* `Crystalline.GlobalCrystallineSituation.secondOrderSectionsMap` — the degree-two base-change
  map `M × (Ω ⊗ M) × (Ω ⊗ M) × (Ω² ⊗ M) ⟶ F(U, T'', δ'')`.
* `Crystalline.GlobalCrystallineSituation.secondOrderIdealProjUnit` — the retraction of the
  degree-two canonical map at `F = 𝒪_{X/S}`.

## Main results

* `Crystalline.GlobalCrystallineSituation.crystalConnection_cocycle` — the curvature identity
  `q₀₁^* ∇(s) + q₁₂^* ∇(s) = q₀₂^* ∇(s)`, for every sheaf of `𝒪_{X/S}`-modules.
* `Crystalline.GlobalCrystallineSituation.diffAction₂_extendedConnectionTensor` — for every `z` in
  `Ω ⊗_D M`, the image of `∇(z)` under the degree-two canonical map is
  `q₀₁^* (z ·) + q₁₂^* (z ·) - q₀₂^* (z ·)`.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_comp_self_eq_zero` —
  `∇ ∘ ∇ = 0`, given the degree-one identification and injectivity of the degree-two canonical
  map.
* `Crystalline.GlobalCrystallineSituation.injective_diffAction₂_of_injective` — the degree-two
  canonical map is injective as soon as the degree-two base-change map is.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_comp_self_eq_zero_of_bijective`
  — `∇ ∘ ∇ = 0` for any sheaf of `𝒪_{X/S}`-modules whose sections over the two universal
  thickenings are the base change of its sections over the object.
* `Crystalline.GlobalCrystallineSituation.injective_diffAction₂_unit` — the degree-two canonical
  map is injective at `F = 𝒪_{X/S}`.
* `Crystalline.GlobalCrystallineSituation.structureSheafCrystalConnection_isIntegrable` — the
  canonical connection is integrable at `F = 𝒪_{X/S}`.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S))

/-! ### Restricting the connection along a morphism into the first-order thickening -/

/-- **Restricting `∇(s)` along a morphism into the first-order universal thickening gives the
difference of the two composites.** -/
theorem moduleSiteRestrict_crystalConnection {A B : Thickening S}
    (g : B ⟶ firstOrderThickeningObject S A) (g₀ g₁ : B ⟶ A)
    (h₀ : g ≫ firstOrderThickeningSiteP₀ S A = g₀)
    (h₁ : g ≫ firstOrderThickeningSiteP₁ S A = g₁) (s : M.val.obj (op A)) :
    moduleSiteRestrict M g (crystalConnection M A s) =
      moduleSiteRestrict M g₁ s - moduleSiteRestrict M g₀ s := by
  rw [crystalConnection_apply, map_sub, moduleSiteRestrict_comp, moduleSiteRestrict_comp, h₀, h₁]

/-! ### The curvature identity on the second-order thickening -/

/-- **The curvature identity of the canonical connection, on the second-order universal
thickening of [Stacks, Tag 07J3].**  For every sheaf of `𝒪_{X/S}`-modules, every object
`(U, T, δ)` and every section `s` of `F` over it,

`q₀₁^* ∇(s) + q₁₂^* ∇(s) = q₀₂^* ∇(s)`

in `F(U, T'', δ'')`. -/
theorem crystalConnection_cocycle (A : Thickening S) (s : M.val.obj (op A)) :
    moduleSiteRestrict M (secondOrderThickeningSiteQ₀₁ S A) (crystalConnection M A s) +
        moduleSiteRestrict M (secondOrderThickeningSiteQ₁₂ S A) (crystalConnection M A s) =
      moduleSiteRestrict M (secondOrderThickeningSiteQ₀₂ S A) (crystalConnection M A s) := by
  rw [moduleSiteRestrict_crystalConnection M (secondOrderThickeningSiteQ₀₁ S A) _ _
      (secondOrderThickeningSiteQ₀₁_comp_P₀ S A) (secondOrderThickeningSiteQ₀₁_comp_P₁ S A),
    moduleSiteRestrict_crystalConnection M (secondOrderThickeningSiteQ₁₂ S A) _ _
      (secondOrderThickeningSiteQ₁₂_comp_P₀ S A) (secondOrderThickeningSiteQ₁₂_comp_P₁ S A),
    moduleSiteRestrict_crystalConnection M (secondOrderThickeningSiteQ₀₂ S A) _ _
      (secondOrderThickeningSiteQ₀₂_comp_P₀ S A) (secondOrderThickeningSiteQ₀₂_comp_P₁ S A)]
  abel

/-! ### Restriction along the three morphisms `T'' ⟶ T'`, composed with `p₀` -/

/-- Restricting along `p₀` and then `q₀₁` is restricting along `q₀`. -/
theorem moduleSiteRestrict_q₀₁_p₀ (A : Thickening S) (s : M.val.obj (op A)) :
    moduleSiteRestrict M (secondOrderThickeningSiteQ₀₁ S A)
        (moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s) =
      moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s := by
  rw [moduleSiteRestrict_comp, secondOrderThickeningSiteQ₀₁_comp_P₀]

/-- Restricting along `p₀` and then `q₁₂` is restricting along `q₁`. -/
theorem moduleSiteRestrict_q₁₂_p₀ (A : Thickening S) (s : M.val.obj (op A)) :
    moduleSiteRestrict M (secondOrderThickeningSiteQ₁₂ S A)
        (moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s) =
      moduleSiteRestrict M (secondOrderThickeningSiteQ₁ S A) s := by
  rw [moduleSiteRestrict_comp, secondOrderThickeningSiteQ₁₂_comp_P₀]

/-- Restricting along `p₀` and then `q₀₂` is restricting along `q₀`. -/
theorem moduleSiteRestrict_q₀₂_p₀ (A : Thickening S) (s : M.val.obj (op A)) :
    moduleSiteRestrict M (secondOrderThickeningSiteQ₀₂ S A)
        (moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s) =
      moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s := by
  rw [moduleSiteRestrict_comp, secondOrderThickeningSiteQ₀₂_comp_P₀]

/-! ### The degree-two canonical map -/

/-- The bilinear datum of `Crystalline.GlobalCrystallineSituation.diffAction₂`: a two-form `η` and
a section `s` of `F` over the object go to the section `η · q₀^* s` of `F` over the second-order
thickening. -/
def diffAction₂Aux (A : Thickening S) :
    crysSecondFormSections A →+
      (M.val.obj (op A) →+ M.val.obj (op (secondOrderThickeningObject S A))) :=
  AddMonoidHom.mk'
    (fun η ↦ AddMonoidHom.mk'
      (fun s ↦ secondOrderTopSection A η •
        moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s)
      (fun s t ↦ by rw [map_add, smul_add]))
    (fun η η' ↦ by
      ext s
      change secondOrderTopSection A (η + η') •
          moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s =
        secondOrderTopSection A η •
            moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s +
          secondOrderTopSection A η' •
            moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s
      rw [secondOrderTopSection_add, add_smul])

/-- **The degree-two canonical map `F_T ⊗_{𝒪_T} Ω²_{T/S,δ} ⟶ F(U, T'', δ'')` of
[Stacks, Tag 07J6]**, on sections over an object: a two-form `η` and a section `s` go to
`η · q₀^* s`, the two-form being read in `𝒪_{T''}` through the top summand `Ω²_{T/S,δ}` of
[Stacks, Tag 07J3]. -/
def diffAction₂ (A : Thickening S) :
    crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A) →+
      M.val.obj (op (secondOrderThickeningObject S A)) :=
  TensorProduct.liftAddHom (diffAction₂Aux M A)
    (fun b η s ↦ by
      change secondOrderTopSection A (b • η) •
          moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s =
        secondOrderTopSection A η •
          moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) (b • s)
      rw [map_smulₛₗ, smul_smul, secondOrderTopSection_mul_crysSheafRingMap_q₀])

/-- The degree-two canonical map sends `η ⊗ s` to `η · q₀^* s`. -/
@[simp]
theorem diffAction₂_tmul (A : Thickening S) (η : crysSecondFormSections A)
    (s : M.val.obj (op A)) :
    diffAction₂ M A (η ⊗ₜ[crysSheafRing S A] s) =
      secondOrderTopSection A η • moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s :=
  TensorProduct.liftAddHom_tmul _ _ η s

/-! ### Exterior multiplication on the right by a one-form -/

/-- The bilinear datum of `Crystalline.GlobalCrystallineSituation.crysWedgeRight`. -/
def crysWedgeRightAux (A : Thickening S) (ω : crysDiffSections A) :
    crysDiffSections A →+
      (M.val.obj (op A) →+
        crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :=
  AddMonoidHom.mk'
    (fun ω' ↦ AddMonoidHom.mk'
      (fun s ↦ crysWedgeSections A ω' ω ⊗ₜ[crysSheafRing S A] s)
      (fun s t ↦ TensorProduct.tmul_add _ _ _))
    (fun ω' ω'' ↦ by
      ext s
      change crysWedgeSections A (ω' + ω'') ω ⊗ₜ[crysSheafRing S A] s =
        crysWedgeSections A ω' ω ⊗ₜ[crysSheafRing S A] s +
          crysWedgeSections A ω'' ω ⊗ₜ[crysSheafRing S A] s
      rw [crysWedgeSections_add_left, TensorProduct.add_tmul])

/-- **Exterior multiplication on the right by a one-form**, `Ω ⊗_D M ⟶ Ω² ⊗_D M`,
`ω' ⊗ s ↦ (ω' ∧ ω) ⊗ s`. -/
def crysWedgeRight (A : Thickening S) (ω : crysDiffSections A) :
    crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A) →+
      crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A) :=
  TensorProduct.liftAddHom (crysWedgeRightAux M A ω)
    (fun b ω' s ↦ by
      change crysWedgeSections A (b • ω') ω ⊗ₜ[crysSheafRing S A] s =
        crysWedgeSections A ω' ω ⊗ₜ[crysSheafRing S A] (b • s)
      rw [crysWedgeSections_smul_left, TensorProduct.smul_tmul])

/-- Exterior multiplication on the right by `ω` sends `ω' ⊗ s` to `(ω' ∧ ω) ⊗ s`. -/
@[simp]
theorem crysWedgeRight_tmul (A : Thickening S) (ω ω' : crysDiffSections A)
    (s : M.val.obj (op A)) :
    crysWedgeRight M A ω (ω' ⊗ₜ[crysSheafRing S A] s) =
      crysWedgeSections A ω' ω ⊗ₜ[crysSheafRing S A] s :=
  TensorProduct.liftAddHom_tmul _ _ ω' s

/-- Exterior multiplication on the right by a one-form is `𝒪_T`-linear. -/
theorem crysWedgeRight_smul (A : Thickening S) (ω : crysDiffSections A) (b : crysSheafRing S A)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    crysWedgeRight M A ω (b • z) = b • crysWedgeRight M A ω z := by
  induction z using TensorProduct.inductionOn with
  | tmul ω' s =>
      rw [TensorProduct.smul_tmul', crysWedgeRight_tmul, crysWedgeRight_tmul,
        crysWedgeSections_smul_left, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- Exterior multiplication on the right by `b • ω` is `b` times exterior multiplication on the
right by `ω`. -/
theorem crysWedgeRight_smul_form (A : Thickening S) (ω : crysDiffSections A)
    (b : crysSheafRing S A)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    crysWedgeRight M A (b • ω) z = b • crysWedgeRight M A ω z := by
  induction z using TensorProduct.inductionOn with
  | tmul ω' s =>
      rw [crysWedgeRight_tmul, crysWedgeRight_tmul, crysWedgeSections_smul_right,
        TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

/-- Exterior multiplication on the right is additive in the one-form. -/
theorem crysWedgeRight_add_form (A : Thickening S) (ω ω' : crysDiffSections A)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    crysWedgeRight M A (ω + ω') z = crysWedgeRight M A ω z + crysWedgeRight M A ω' z := by
  induction z using TensorProduct.inductionOn with
  | tmul ω'' s =>
      rw [crysWedgeRight_tmul, crysWedgeRight_tmul, crysWedgeRight_tmul,
        crysWedgeSections_add_right, TensorProduct.add_tmul]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
      abel

/-! ### The degree-one extension of the connection -/

/-- The bilinear datum of
`Crystalline.GlobalCrystallineSituation.extendedConnectionTensor`. -/
def extendedConnectionTensorAux (A : Thickening S) (h : FirstOrderIdealBaseChange M A) :
    crysDiffSections A →+
      (M.val.obj (op A) →+
        crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :=
  AddMonoidHom.mk'
    (fun ω ↦ AddMonoidHom.mk'
      (fun s ↦ crysWedgeRight M A ω (crystalConnectionTensor M A h s) +
        crysDeRham A ω ⊗ₜ[crysSheafRing S A] s)
      (fun s t ↦ by
        rw [map_add, map_add, TensorProduct.tmul_add]
        abel))
    (fun ω ω' ↦ by
      ext s
      change crysWedgeRight M A (ω + ω') (crystalConnectionTensor M A h s) +
          crysDeRham A (ω + ω') ⊗ₜ[crysSheafRing S A] s =
        crysWedgeRight M A ω (crystalConnectionTensor M A h s) +
            crysDeRham A ω ⊗ₜ[crysSheafRing S A] s +
          (crysWedgeRight M A ω' (crystalConnectionTensor M A h s) +
            crysDeRham A ω' ⊗ₜ[crysSheafRing S A] s)
      rw [crysWedgeRight_add_form, crysDeRham_add, TensorProduct.add_tmul]
      abel)

/-- **The degree-one extension of the connection, of [Stacks, Section 60.15, Tag 07J5], in the
crystalline spelling**: the map

`∇ : Ω ⊗_D M ⟶ Ω² ⊗_D M`,  `ω ⊗ s ↦ ∇(s) ∧ ω + (d ω) ⊗ s`,

with `d = d_{T/S,δ}` the degree-one divided power de Rham differential. -/
def extendedConnectionTensor (A : Thickening S) (h : FirstOrderIdealBaseChange M A) :
    crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A) →+
      crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A) :=
  TensorProduct.liftAddHom (extendedConnectionTensorAux M A h)
    (fun b ω s ↦ by
      have hD : crysDeRham A (b • ω) ⊗ₜ[crysSheafRing S A] s =
          b • (crysDeRham A ω ⊗ₜ[crysSheafRing S A] s) +
            crysWedgeSections A (sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b) ω
              ⊗ₜ[crysSheafRing S A] s := by
        rw [crysDeRham_smul, TensorProduct.add_tmul, TensorProduct.smul_tmul']
      have hRW : crysWedgeRight M A ω (crystalConnectionTensor M A h (b • s)) =
          b • crysWedgeRight M A ω (crystalConnectionTensor M A h s) +
            crysWedgeSections A (sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b) ω
              ⊗ₜ[crysSheafRing S A] s := by
        rw [crystalConnectionTensor_smul, map_add, crysWedgeRight_smul, crysWedgeRight_tmul]
      have hT : crysDeRham A ω ⊗ₜ[crysSheafRing S A] (b • s) =
          b • (crysDeRham A ω ⊗ₜ[crysSheafRing S A] s) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      change crysWedgeRight M A (b • ω) (crystalConnectionTensor M A h s) +
          crysDeRham A (b • ω) ⊗ₜ[crysSheafRing S A] s =
        crysWedgeRight M A ω (crystalConnectionTensor M A h (b • s)) +
          crysDeRham A ω ⊗ₜ[crysSheafRing S A] (b • s)
      rw [crysWedgeRight_smul_form, hD, hRW, hT]
      abel)

/-- The degree-one extension sends `ω ⊗ s` to `∇(s) ∧ ω + (d ω) ⊗ s`. -/
@[simp]
theorem extendedConnectionTensor_tmul (A : Thickening S) (h : FirstOrderIdealBaseChange M A)
    (ω : crysDiffSections A) (s : M.val.obj (op A)) :
    extendedConnectionTensor M A h (ω ⊗ₜ[crysSheafRing S A] s) =
      crysWedgeRight M A ω (crystalConnectionTensor M A h s) +
        crysDeRham A ω ⊗ₜ[crysSheafRing S A] s :=
  TensorProduct.liftAddHom_tmul _ _ ω s

/-! ### The source's computation -/

/-- **Exterior multiplication on the right, read through the two canonical maps.**  For every `z`
in `Ω ⊗_D M`,

`(z ∧ ω) · (degree-two map) = q₁₂^* ω · q₀₁^* (z ·)`. -/
theorem diffAction₂_crysWedgeRight (A : Thickening S) (ω : crysDiffSections A)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    diffAction₂ M A (crysWedgeRight M A ω z) =
      crysSheafRingMap (secondOrderThickeningSiteQ₁₂ S A)
          (firstOrderThickeningDiffSection A ω) •
        moduleSiteRestrict M (secondOrderThickeningSiteQ₀₁ S A) (diffAction M A z) := by
  induction z using TensorProduct.inductionOn with
  | tmul ω' s =>
      rw [crysWedgeRight_tmul, diffAction₂_tmul, diffAction_tmul, map_smulₛₗ, smul_smul,
        crysSheafRingMap_q₁₂_mul_q₀₁_diffSection, moduleSiteRestrict_q₀₁_p₀]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]

/-- **The integrability computation of [Stacks, Lemma 60.15.1, Tag 07J6].**  For every `z` in
`Ω ⊗_D M`, the image of its extension `∇(z)` under the degree-two canonical map is the alternating
sum of the three restrictions of the image of `z` under the degree-one canonical map:

`∇(z) · (degree-two map) = q₀₁^* (z ·) + q₁₂^* (z ·) - q₀₂^* (z ·)`. -/
theorem diffAction₂_extendedConnectionTensor (A : Thickening S)
    (h : FirstOrderIdealBaseChange M A)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    diffAction₂ M A (extendedConnectionTensor M A h z) =
      moduleSiteRestrict M (secondOrderThickeningSiteQ₀₁ S A) (diffAction M A z) +
        moduleSiteRestrict M (secondOrderThickeningSiteQ₁₂ S A) (diffAction M A z) -
        moduleSiteRestrict M (secondOrderThickeningSiteQ₀₂ S A) (diffAction M A z) := by
  induction z using TensorProduct.inductionOn with
  | tmul ω t =>
      rw [extendedConnectionTensor_tmul, map_add, diffAction₂_crysWedgeRight,
        diffAction_crystalConnectionTensor,
        moduleSiteRestrict_crystalConnection M (secondOrderThickeningSiteQ₀₁ S A) _ _
          (secondOrderThickeningSiteQ₀₁_comp_P₀ S A) (secondOrderThickeningSiteQ₀₁_comp_P₁ S A),
        diffAction₂_tmul, diffAction_tmul, map_smulₛₗ, map_smulₛₗ, map_smulₛₗ,
        moduleSiteRestrict_q₀₁_p₀, moduleSiteRestrict_q₁₂_p₀, moduleSiteRestrict_q₀₂_p₀, smul_sub]
      linear_combination (norm := module) -(crysSheafRingMap_q₀₁_add_q₁₂_diffSection A ω •
        moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) t)
  | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, map_add, map_add, hx, hy]
      abel

/-- **The curvature of the canonical connection is carried to zero by the degree-two canonical
map.** -/
theorem diffAction₂_extendedConnectionTensor_crystalConnectionTensor (A : Thickening S)
    (h : FirstOrderIdealBaseChange M A) (s : M.val.obj (op A)) :
    diffAction₂ M A
        (extendedConnectionTensor M A h (crystalConnectionTensor M A h s)) = 0 := by
  rw [diffAction₂_extendedConnectionTensor, diffAction_crystalConnectionTensor,
    crystalConnection_cocycle, sub_self]

/-- **Integrability of the canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6]**: given the
degree-one identification `h` and injectivity of the degree-two canonical map, the composite
`∇ ∘ ∇ : M ⟶ Ω² ⊗_D M` of the connection with its own degree-one extension of §07J5 vanishes. -/
theorem crystalConnectionTensor_comp_self_eq_zero (A : Thickening S)
    (h : FirstOrderIdealBaseChange M A) (hinj : Function.Injective (diffAction₂ M A))
    (s : M.val.obj (op A)) :
    extendedConnectionTensor M A h (crystalConnectionTensor M A h s) = 0 :=
  hinj
    ((diffAction₂_extendedConnectionTensor_crystalConnectionTensor M A h s).trans
      (map_zero (diffAction₂ M A)).symm)

/-! ### The base-change map on global sections, in degree two -/

/-- The bilinear datum of `Crystalline.GlobalCrystallineSituation.diffActionLeft`. -/
def diffActionLeftAux (A : Thickening S) :
    crysDiffSections A →+
      (M.val.obj (op A) →+ M.val.obj (op (secondOrderThickeningObject S A))) :=
  AddMonoidHom.mk'
    (fun ω ↦ AddMonoidHom.mk'
      (fun s ↦ secondOrderLeftSection A ω •
        moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s)
      (fun s t ↦ by rw [map_add, smul_add]))
    (fun ω ω' ↦ by
      ext s
      change secondOrderLeftSection A (ω + ω') •
          moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s =
        secondOrderLeftSection A ω •
            moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s +
          secondOrderLeftSection A ω' •
            moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s
      rw [secondOrderLeftSection_add, add_smul])

/-- **The canonical map into the first middle summand**, `Ω ⊗_D M ⟶ F(U, T'', δ'')`,
`ω ⊗ s ↦ (0, ω, 0, 0) · q₀^* s`. -/
def diffActionLeft (A : Thickening S) :
    crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A) →+
      M.val.obj (op (secondOrderThickeningObject S A)) :=
  TensorProduct.liftAddHom (diffActionLeftAux M A)
    (fun b ω s ↦ by
      change secondOrderLeftSection A (b • ω) •
          moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s =
        secondOrderLeftSection A ω •
          moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) (b • s)
      rw [map_smulₛₗ, smul_smul, secondOrderLeftSection_mul_crysSheafRingMap_q₀])

/-- The bilinear datum of `Crystalline.GlobalCrystallineSituation.diffActionRight`. -/
def diffActionRightAux (A : Thickening S) :
    crysDiffSections A →+
      (M.val.obj (op A) →+ M.val.obj (op (secondOrderThickeningObject S A))) :=
  AddMonoidHom.mk'
    (fun ω ↦ AddMonoidHom.mk'
      (fun s ↦ secondOrderRightSection A ω •
        moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s)
      (fun s t ↦ by rw [map_add, smul_add]))
    (fun ω ω' ↦ by
      ext s
      change secondOrderRightSection A (ω + ω') •
          moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s =
        secondOrderRightSection A ω •
            moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s +
          secondOrderRightSection A ω' •
            moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s
      rw [secondOrderRightSection_add, add_smul])

/-- **The canonical map into the second middle summand**, `Ω ⊗_D M ⟶ F(U, T'', δ'')`,
`ω ⊗ s ↦ (0, 0, ω, 0) · q₀^* s`. -/
def diffActionRight (A : Thickening S) :
    crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A) →+
      M.val.obj (op (secondOrderThickeningObject S A)) :=
  TensorProduct.liftAddHom (diffActionRightAux M A)
    (fun b ω s ↦ by
      change secondOrderRightSection A (b • ω) •
          moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s =
        secondOrderRightSection A ω •
          moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) (b • s)
      rw [map_smulₛₗ, smul_smul, secondOrderRightSection_mul_crysSheafRingMap_q₀])

/-- **The base change of the sections of `F` along `q₀`**, read through the direct sum
decomposition `Γ(T'', 𝒪_{T''}) = Γ(T, 𝒪_T) ⊕ Ω ⊕ Ω ⊕ Ω²` of [Stacks, Tag 07J3]: the map

`M × (Ω ⊗ M) × (Ω ⊗ M) × (Ω² ⊗ M) ⟶ Γ(T'', F_{T''})`,
`(s, z₁, z₂, w) ↦ q₀^* s + z₁ + z₂ + w`,

each summand read in `𝒪_{T''}` through the corresponding summand. -/
def secondOrderSectionsMap (A : Thickening S) :
    M.val.obj (op A) ×
        ((crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ×
          ((crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ×
            (crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A)))) →+
      M.val.obj (op (secondOrderThickeningObject S A)) :=
  AddMonoidHom.mk'
    (fun x ↦ moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) x.1 +
      diffActionLeft M A x.2.1 + diffActionRight M A x.2.2.1 + diffAction₂ M A x.2.2.2)
    (fun x y ↦ by
      change moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) (x.1 + y.1) +
          diffActionLeft M A (x.2.1 + y.2.1) + diffActionRight M A (x.2.2.1 + y.2.2.1) +
          diffAction₂ M A (x.2.2.2 + y.2.2.2) = _
      rw [map_add, map_add, map_add, map_add]
      abel)

/-- The degree-two base-change map sends `(s, z₁, z₂, w)` to `q₀^* s + z₁ + z₂ + w`. -/
@[simp]
theorem secondOrderSectionsMap_apply (A : Thickening S) (s : M.val.obj (op A))
    (z₁ z₂ : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A))
    (w : crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    secondOrderSectionsMap M A (s, z₁, z₂, w) =
      moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s +
        diffActionLeft M A z₁ + diffActionRight M A z₂ + diffAction₂ M A w := rfl

/-- **On the top summand the base-change map is the degree-two canonical map.** -/
theorem secondOrderSectionsMap_top (A : Thickening S)
    (w : crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    secondOrderSectionsMap M A (0, 0, 0, w) = diffAction₂ M A w := by
  rw [secondOrderSectionsMap_apply, map_zero, map_zero, map_zero, add_zero, add_zero, zero_add]

/-- **The degree-two canonical map is injective** as soon as the base-change map of
[Stacks, Tag 07J3] is, being its restriction to the top summand. -/
theorem injective_diffAction₂_of_injective (A : Thickening S)
    (h : Function.Injective (secondOrderSectionsMap M A)) :
    Function.Injective (diffAction₂ M A) := fun w w' hw ↦
  congrArg (·.2.2.2) (@h (0, 0, 0, w) (0, 0, 0, w')
    (by rwa [secondOrderSectionsMap_top, secondOrderSectionsMap_top]))

/-- **Integrability of the canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6], for any
sheaf of `𝒪_{X/S}`-modules whose sections over the two universal thickenings are the base change
of its sections over the object.**  That is: if the degree-one base-change map
`Crystalline.GlobalCrystallineSituation.firstOrderSectionsMap` of [Stacks, Tag 07J2] is bijective
and the degree-two one `Crystalline.GlobalCrystallineSituation.secondOrderSectionsMap` of
[Stacks, Tag 07J3] is injective, then `∇ ∘ ∇ = 0`. -/
theorem crystalConnectionTensor_comp_self_eq_zero_of_bijective (A : Thickening S)
    (h₁ : Function.Bijective (firstOrderSectionsMap M A))
    (h₂ : Function.Injective (secondOrderSectionsMap M A)) (s : M.val.obj (op A)) :
    extendedConnectionTensor M A (firstOrderIdealBaseChangeOfBijective M A h₁)
        (crystalConnectionTensor M A (firstOrderIdealBaseChangeOfBijective M A h₁) s) = 0 :=
  crystalConnectionTensor_comp_self_eq_zero M A (firstOrderIdealBaseChangeOfBijective M A h₁)
    (injective_diffAction₂_of_injective M A h₂) s

/-! ### The case `F = 𝒪_{X/S}`: the degree-two map is injective -/

/-- **The retraction of the degree-two canonical map at `F = 𝒪_{X/S}`**: the projection of a
section of `𝒪_{T''}` onto the top summand `Ω²_{T/S,δ}`, tensored with the unit section. -/
def secondOrderIdealProjUnit (A : Thickening S) :
    (SheafOfModules.unit (crystallineStructureSheaf S)).val.obj
        (op (secondOrderThickeningObject S A)) →+
      crysSecondFormSections A ⊗[crysSheafRing S A]
        (SheafOfModules.unit (crystallineStructureSheaf S)).val.obj (op A) :=
  AddMonoidHom.mk'
    (fun t ↦ secondOrderExtTop t ⊗ₜ[crysSheafRing S A] (1 : crysSheafRing S A))
    (fun _ _ ↦ TensorProduct.add_tmul _ _ _)

/-- At `F = 𝒪_{X/S}` the degree-two canonical map sends a pure tensor `η ⊗ x` to the two-form
`x η` read in the top summand. -/
theorem diffAction₂_unit_tmul (A : Thickening S) (η : crysSecondFormSections A)
    (x : crysSheafRing S A) :
    diffAction₂ (SheafOfModules.unit (crystallineStructureSheaf S)) A
        (η ⊗ₜ[crysSheafRing S A] x) = secondOrderTopSection A (x • η) :=
  (diffAction₂_tmul (SheafOfModules.unit (crystallineStructureSheaf S)) A η x).trans
    (secondOrderTopSection_mul_crysSheafRingMap_q₀ A η x)

/-- The retraction recovers a pure tensor: the top coordinate of `η · q₀^* x`, tensored with the
unit section, is `η ⊗ x`. -/
theorem secondOrderIdealProjUnit_diffAction₂_tmul (A : Thickening S)
    (η : crysSecondFormSections A) (x : crysSheafRing S A) :
    secondOrderIdealProjUnit A
        (diffAction₂ (SheafOfModules.unit (crystallineStructureSheaf S)) A
          (η ⊗ₜ[crysSheafRing S A] x)) =
      η ⊗ₜ[crysSheafRing S A] x := by
  have h1 : secondOrderIdealProjUnit A
      (diffAction₂ (SheafOfModules.unit (crystallineStructureSheaf S)) A
        (η ⊗ₜ[crysSheafRing S A] x)) =
      (x • η) ⊗ₜ[crysSheafRing S A] (1 : crysSheafRing S A) :=
    congrArg (secondOrderIdealProjUnit A) (diffAction₂_unit_tmul A η x)
  rw [h1, TensorProduct.smul_tmul, smul_eq_mul, mul_one]

/-- The projection onto the top summand is a left inverse of the degree-two canonical map at
`F = 𝒪_{X/S}`. -/
theorem secondOrderIdealProjUnit_diffAction₂ (A : Thickening S)
    (z : crysSecondFormSections A ⊗[crysSheafRing S A]
      (SheafOfModules.unit (crystallineStructureSheaf S)).val.obj (op A)) :
    secondOrderIdealProjUnit A
        (diffAction₂ (SheafOfModules.unit (crystallineStructureSheaf S)) A z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul η x => exact secondOrderIdealProjUnit_diffAction₂_tmul A η x
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- **The degree-two canonical map is injective at `F = 𝒪_{X/S}`.** -/
theorem injective_diffAction₂_unit (A : Thickening S) :
    Function.Injective (diffAction₂ (SheafOfModules.unit (crystallineStructureSheaf S)) A) :=
  Function.LeftInverse.injective (secondOrderIdealProjUnit_diffAction₂ A)

/-- **Stacks Project, Tag 07J6 at `F = 𝒪_{X/S}`, for the tag's own canonical connection.**  The
connection `∇(s) = p₁^* s - p₀^* s` of the first-order universal thickening of
[Stacks, Tag 07J2], read inside `Ω ⊗_D 𝒪_T(T)`, is integrable: its composite with its own
degree-one extension `∇(ω ⊗ s) = ∇(s) ∧ ω + (d ω) ⊗ s` of §07J5 vanishes. -/
theorem structureSheafCrystalConnection_isIntegrable (A : Thickening S)
    (b : (SheafOfModules.unit (crystallineStructureSheaf S)).val.obj (op A)) :
    extendedConnectionTensor (SheafOfModules.unit (crystallineStructureSheaf S)) A
        (firstOrderIdealBaseChangeUnit A)
        (crystalConnectionTensor (SheafOfModules.unit (crystallineStructureSheaf S)) A
          (firstOrderIdealBaseChangeUnit A) b) = 0 :=
  crystalConnectionTensor_comp_self_eq_zero _ A (firstOrderIdealBaseChangeUnit A)
    (injective_diffAction₂_unit A) b

end Crystalline.GlobalCrystallineSituation

end

end
