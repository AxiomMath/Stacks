module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectCrystalConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondExteriorPowerAffineSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineConnection

/-!
# The canonical connection of a crystal on `Cris(X/S)` as an integrable ring-level connection

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], a sheaf of
`𝒪_{X/S}`-modules `ℱ` on the small crystalline site `Cris(X/S)`, and an object `B = (U, T, δ)` of
`Cris(X/S)` whose ambient scheme `T` is affine and lies over an affine open `V` of the divided
power base.  Write `D = Γ(T, 𝒪_T)` and `Mod = ℱ(U, T, δ)`.

`SmallSite/CrysAffineConnection.lean` builds the canonical connection
`∇ : Mod ⟶ Γ(T, Ω_{T/S,δ}) ⊗_D Mod` of [Stacks, Lemma 60.15.1, Tag 07J6], `∇(s) = p₁^* s - p₀^* s`,
and proves it integrable in the spelling of the second-order universal thickening.  This module
reads it as a term of the ring-level structure `Crystalline.Connection` of [Stacks, Tag 07I0],
relative to the presentation `Crystalline.GlobalCrystallineSituation.crysPi` of the sections
`Ω_{X/S}(B)` of the crystalline differentials, and proves it **integrable in the sense of
[Stacks, Tag 07I0]**: the ring-level extension `Crystalline.extendedConnection` composes with it
to zero.  By `Crystalline.extendedConnection_comp_self_eq_zero` all the extensions
`Mod ⊗_D ⋀^p Ω_{X/S}(B) ⟶ Mod ⊗_D ⋀^{p+1} Ω_{X/S}(B)` then compose to zero, which is what makes
the de Rham complex of [Stacks, Tag 07LM] a complex.

Two identifications are used: `Crystalline.GlobalCrystallineSituation.affineCrysOmegaEquiv`, the
sections of the sheaf `Ω_{T/S,δ}` over the affine `T` are `Ω_{X/S}(B)`; and
`Crystalline.bijective_dpSecondExteriorToSheaf_app`, the sections of `Ω²_{T/S,δ}` over the affine
`T` are `⋀²` of those of `Ω_{T/S,δ}`.  The second is what lets the outcome of the integrability
computation, read in `Γ(T, Ω²_{T/S,δ}) ⊗_D Mod`, be read in `Mod ⊗_D ⋀² Ω_{X/S}(B)`.

## Main definitions

Everything lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.AffineConnection`.

* `tensorFlip` — `Γ(T, Ω_{T/S,δ}) ⊗_D Mod ≅ Mod ⊗_D Ω_{X/S}(B)`.
* `ringConnection` — **the canonical connection as a term of `Crystalline.Connection`.**
* `secondFormsEquiv` — `⋀²_D Ω_{X/S}(B) ≅ Γ(T, Ω²_{T/S,δ})`, `η ∧ ω ↦ η ∧ ω`.

## Main results

* `ringConnection_apply` — the value: the connection of `SmallSite/CrysAffineConnection.lean`
  read through `tensorFlip`.
* `ringConnection_isIntegrable` — **integrability in the sense of [Stacks, Tag 07I0]**.

## References

* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct
open Stacks.DeRham.DifferentialDescent

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.AffineConnection

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))
  (B : CrystallineThickening S)

/-- The sections of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` over an object, as a module over
the section ring in the `crysFormRing` spelling of the ring-level connection machinery. -/
instance moduleFormRingSmallSections :
    Module (GlobalCrystallineSituation.crysFormRing S B.obj) (F.val.obj (op B)) :=
  inferInstanceAs (Module (crysSheafRing S B.obj) (F.val.obj (op B)))

variable [IsAffine B.obj.thickening.target.scheme] {V : S.S.scheme.Opens}
  (hVB : (⊤ : B.obj.thickening.target.scheme.Opens) ≤ B.obj.toBase.hom ⁻¹ᵁ V)
  (hV : IsAffineOpen V)

/-! ### The connection -/

/-- **The two readings of the target of the canonical connection agree** over an
affine-over-affine object: `Γ(T, Ω_{T/S,δ}) ⊗_D Mod ≅ Mod ⊗_D Ω_{X/S}(B)`, by `TensorProduct.comm`
and `affineCrysOmegaEquiv`. -/
def tensorFlip :
    crysDiffSections B.obj ⊗[GlobalCrystallineSituation.crysFormRing S B.obj] F.val.obj (op B)
      ≃ₗ[GlobalCrystallineSituation.crysFormRing S B.obj]
      F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) :=
  (TensorProduct.comm (GlobalCrystallineSituation.crysFormRing S B.obj) (crysDiffSections B.obj)
      (F.val.obj (op B))).trans
    (TensorProduct.congr
      (LinearEquiv.refl (GlobalCrystallineSituation.crysFormRing S B.obj) (F.val.obj (op B)))
      (affineCrysOmegaEquiv B.obj hVB hV))

/-- `tensorFlip` on a pure tensor. -/
@[simp]
theorem tensorFlip_tmul (ω : crysDiffSections B.obj) (s : F.val.obj (op B)) :
    tensorFlip F B hVB hV (ω ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj] s) =
      s ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        affineCrysOmegaEquiv B.obj hVB hV ω := rfl

/-- The inverse of `tensorFlip` on a pure tensor. -/
@[simp]
theorem tensorFlip_symm_tmul (s : F.val.obj (op B))
    (η : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    (tensorFlip F B hVB hV).symm (s ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj] η) =
      (affineCrysOmegaEquiv B.obj hVB hV).symm η ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        s := by
  rw [LinearEquiv.symm_apply_eq, tensorFlip_tmul, LinearEquiv.apply_symm_apply]

/-- `tensorFlip`, as an additive equivalence whose source is spelled over `crysSheafRing`, the ring
of `SmallSite/CrysAffineConnection.lean`. -/
def tensorFlipAdd :
    crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) ≃+
      F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) :=
  (tensorFlip F B hVB hV).toAddEquiv

/-- `tensorFlipAdd` on a pure tensor. -/
theorem tensorFlipAdd_tmul (ω : crysDiffSections B.obj) (s : F.val.obj (op B)) :
    tensorFlipAdd F B hVB hV (ω ⊗ₜ[crysSheafRing S B.obj] s) =
      s ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        affineCrysOmegaEquiv B.obj hVB hV ω := rfl

/-- The inverse of `tensorFlipAdd` on a pure tensor. -/
theorem tensorFlipAdd_symm_tmul (s : F.val.obj (op B))
    (η : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    (tensorFlipAdd F B hVB hV).symm (s ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj] η) =
      (affineCrysOmegaEquiv B.obj hVB hV).symm η ⊗ₜ[crysSheafRing S B.obj] s :=
  tensorFlip_symm_tmul F B hVB hV s η

variable {F B} (he : Function.Bijective (crysExtensionSectionsMap F B))

/-- **Stacks Project, Lemma 60.15.1, Tag 07J6, in the ring-level spelling of [Stacks, Tag 07I0],
for a sheaf of modules on `Cris(X/S)`.**  The canonical connection

`∇ : ℱ(B) ⟶ ℱ(B) ⊗_D Ω_{X/S}(B)`

over an affine-over-affine object, relative to the presentation `crysPi` of `Ω_{X/S}(B)`: the
connection `p₁^* s - p₀^* s` of `SmallSite/CrysAffineConnection.lean` read through `tensorFlip`.
Its Leibniz rule is the Leibniz rule of that connection. -/
def ringConnection :
    Connection ↥Γ(S.S.scheme, ⊤) (GlobalCrystallineSituation.crysFormRing S B.obj) (crysPi S B.obj)
      (F.val.obj (op B)) where
  toAddMonoidHom :=
    (tensorFlipAdd F B hVB hV).toAddMonoidHom.comp (connection he)
  leibniz' b s := by
    refine (congrArg (tensorFlip F B hVB hV) (connection_smul he b s)).trans ?_
    refine ((tensorFlip F B hVB hV).map_add _ _).trans ?_
    exact congrArg₂ (· + ·) ((tensorFlip F B hVB hV).map_smul b _)
      (congrArg (fun x ↦ s ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj] x)
        (affineCrysOmegaEquiv_crysPi_D B.obj hVB hV b))

/-- The value of the ring-level connection: the connection of `SmallSite/CrysAffineConnection.lean`
read through `tensorFlipAdd`. -/
theorem ringConnection_apply (s : F.val.obj (op B)) :
    ringConnection hVB hV he s = tensorFlipAdd F B hVB hV (connection he s) := rfl

/-! ### Two-forms -/

variable (B)

/-- The two-forms over an object, as a module over the section ring in the `crysFormRing`
spelling. -/
instance moduleFormRingSecondFormSections :
    Module (GlobalCrystallineSituation.crysFormRing S B.obj) (crysSecondFormSections B.obj) :=
  inferInstanceAs (Module Γ(B.obj.thickening.target.scheme, ⊤) (crysSecondFormSections B.obj))

/-- The exterior product of two one-forms of `Ω_{X/S}(B)`, read in `Γ(T, Ω²_{T/S,δ})` through the
identification of `Ω_{X/S}(B)` with `Γ(T, Ω_{T/S,δ})`. -/
def wedgePair (x y : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    crysSecondFormSections B.obj :=
  crysWedgeSections B.obj ((affineCrysOmegaEquiv B.obj hVB hV).symm x)
    ((affineCrysOmegaEquiv B.obj hVB hV).symm y)

/-- `wedgePair` is additive in the first one-form. -/
theorem wedgePair_add_left (x x' y : ↥((GlobalCrystallineSituation.crysDifferentials S).obj
    (op B.obj))) :
    wedgePair B hVB hV (x + x') y = wedgePair B hVB hV x y + wedgePair B hVB hV x' y := by
  unfold wedgePair
  rw [map_add, crysWedgeSections_add_left]

/-- `wedgePair` is additive in the second one-form. -/
theorem wedgePair_add_right (x y y' : ↥((GlobalCrystallineSituation.crysDifferentials S).obj
    (op B.obj))) :
    wedgePair B hVB hV x (y + y') = wedgePair B hVB hV x y + wedgePair B hVB hV x y' := by
  unfold wedgePair
  rw [map_add, crysWedgeSections_add_right]

/-- `wedgePair` is linear in the first one-form. -/
theorem wedgePair_smul_left (c : GlobalCrystallineSituation.crysFormRing S B.obj)
    (x y : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    wedgePair B hVB hV (c • x) y = c • wedgePair B hVB hV x y := by
  unfold wedgePair
  rw [LinearEquiv.map_smul]
  exact crysWedgeSections_smul_left B.obj c _ _

/-- `wedgePair` is linear in the second one-form. -/
theorem wedgePair_smul_right (c : GlobalCrystallineSituation.crysFormRing S B.obj)
    (x y : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    wedgePair B hVB hV x (c • y) = c • wedgePair B hVB hV x y := by
  unfold wedgePair
  rw [LinearEquiv.map_smul]
  exact crysWedgeSections_smul_right B.obj c _ _

/-- `wedgePair` is alternating. -/
theorem wedgePair_self (x : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    wedgePair B hVB hV x x = 0 :=
  dpWedge_self _ _ _ _ _

/-- **The exterior product of two one-forms of `Ω_{X/S}(B)`, read in `Γ(T, Ω²_{T/S,δ})`**, as an
alternating map. -/
def wedgeAlternating :
    ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))
      [⋀^Fin 2]→ₗ[GlobalCrystallineSituation.crysFormRing S B.obj]
        crysSecondFormSections B.obj where
  toFun v := wedgePair B hVB hV (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Function.update_self,
        Function.update_of_ne (Fin.zero_ne_one (n := 0)).symm]
      exact wedgePair_add_left B hVB hV x y (v 1)
    · simp only [Fin.mk_one, Fin.isValue, Function.update_self,
        Function.update_of_ne (Fin.zero_ne_one (n := 0))]
      exact wedgePair_add_right B hVB hV (v 0) x y
  map_update_smul' v i c x := by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Function.update_self,
        Function.update_of_ne (Fin.zero_ne_one (n := 0)).symm]
      exact wedgePair_smul_left B hVB hV c x (v 1)
    · simp only [Fin.mk_one, Fin.isValue, Function.update_self,
        Function.update_of_ne (Fin.zero_ne_one (n := 0))]
      exact wedgePair_smul_right B hVB hV c (v 0) x
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change wedgePair B hVB hV (v 0) (v 1) = 0
      rw [show v 1 = v 0 from hv.symm]
      exact wedgePair_self B hVB hV (v 0)
    · change wedgePair B hVB hV (v 0) (v 1) = 0
      rw [show v 1 = v 0 from hv]
      exact wedgePair_self B hVB hV (v 0)
    · exact absurd rfl hij

/-- **The comparison `⋀²_D Ω_{X/S}(B) ⟶ Γ(T, Ω²_{T/S,δ})`**, `η ∧ ω ↦ η ∧ ω`. -/
def secondFormsMap :
    ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^2
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) →ₗ[
      GlobalCrystallineSituation.crysFormRing S B.obj] crysSecondFormSections B.obj :=
  exteriorPower.alternatingMapLinearEquiv (wedgeAlternating B hVB hV)

/-- The comparison on a wedge. -/
theorem secondFormsMap_ιMulti
    (v : Fin 2 → ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    secondFormsMap B hVB hV
        (exteriorPower.ιMulti (GlobalCrystallineSituation.crysFormRing S B.obj) 2 v) =
      wedgePair B hVB hV (v 0) (v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

/-! ### The inverse comparison -/

/-- The ring `Γ(T, 𝒪_T)` in the spelling over which the sections of `Ω_{T/S,δ}` form a module. -/
abbrev ambientRing : Type u :=
  ((B.obj.thickening.target.scheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op ⊤) : Type u)

/-- The two spellings of `Γ(T, 𝒪_T)` are the same ring. -/
def ambientRingCast : ambientRing B →+* GlobalCrystallineSituation.crysFormRing S B.obj :=
  RingHom.id _

/-- The second exterior power of `Ω_{X/S}(B)`, as a module over `Γ(T, 𝒪_T)` in the spelling of
the sections of `Ω_{T/S,δ}`. -/
@[instance_reducible]
def moduleAmbientRingSecondForms :
    Module (ambientRing B) (⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^2
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :=
  Module.compHom _ (ambientRingCast B)

attribute [local instance] moduleAmbientRingSecondForms

/-- The sections of `Ω_{T/S,δ}` over `T`, in the spelling of the presheaf of modules
`dpDifferentialsModules`. -/
abbrev ambientForms : Type u :=
  ↥((dpDifferentialsModules B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj (op ⊤))

/-- `(x, y) ↦ ψ x ∧ ψ y`, alternating over `Γ(T, 𝒪_T)`. -/
def wedgeInvAlternating :
    ambientForms B [⋀^Fin 2]→ₗ[ambientRing B]
      ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^2
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) where
  toFun v := exteriorPower.ιMulti (GlobalCrystallineSituation.crysFormRing S B.obj) 2
    (fun i ↦ affineCrysOmegaEquiv B.obj hVB hV (v i))
  map_update_add' v i x y := by
    have h : (fun j ↦ affineCrysOmegaEquiv B.obj hVB hV (Function.update v i (x + y) j)) =
        Function.update (fun j ↦ affineCrysOmegaEquiv B.obj hVB hV (v j)) i
          (affineCrysOmegaEquiv B.obj hVB hV x + affineCrysOmegaEquiv B.obj hVB hV y) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; exact map_add _ x y
      · simp only [Function.update_of_ne hj]
    have hx : (fun j ↦ affineCrysOmegaEquiv B.obj hVB hV (Function.update v i x j)) =
        Function.update (fun j ↦ affineCrysOmegaEquiv B.obj hVB hV (v j)) i
          (affineCrysOmegaEquiv B.obj hVB hV x) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]
      · simp only [Function.update_of_ne hj]
    have hy : (fun j ↦ affineCrysOmegaEquiv B.obj hVB hV (Function.update v i y j)) =
        Function.update (fun j ↦ affineCrysOmegaEquiv B.obj hVB hV (v j)) i
          (affineCrysOmegaEquiv B.obj hVB hV y) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]
      · simp only [Function.update_of_ne hj]
    rw [h, hx, hy]
    exact (exteriorPower.ιMulti _ 2).map_update_add _ i _ _
  map_update_smul' v i c x := by
    have h : (fun j ↦ affineCrysOmegaEquiv B.obj hVB hV (Function.update v i (c • x) j)) =
        Function.update (fun j ↦ affineCrysOmegaEquiv B.obj hVB hV (v j)) i
          (ambientRingCast B c • affineCrysOmegaEquiv B.obj hVB hV x) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]
        exact (affineCrysOmegaEquiv B.obj hVB hV).map_smul (ambientRingCast B c) x
      · simp only [Function.update_of_ne hj]
    have hx : (fun j ↦ affineCrysOmegaEquiv B.obj hVB hV (Function.update v i x j)) =
        Function.update (fun j ↦ affineCrysOmegaEquiv B.obj hVB hV (v j)) i
          (affineCrysOmegaEquiv B.obj hVB hV x) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]
      · simp only [Function.update_of_ne hj]
    rw [h, hx]
    exact (exteriorPower.ιMulti _ 2).map_update_smul _ i _ _
  map_eq_zero_of_eq' v i j hv hij :=
    (exteriorPower.ιMulti _ 2).map_eq_zero_of_eq _ (congrArg _ hv) hij

/-- The sections over `T` of the sectionwise second exterior power of `Ω_{T/S,δ}`, mapped to
`⋀²_D Ω_{X/S}(B)`. -/
def secondFormsInvPresheaf :
    ↥((dpSecondExteriorPresheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj
        (op ⊤)) →ₗ[ambientRing B]
      ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^2
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) :=
  (exteriorPower.alternatingMapLinearEquiv (wedgeInvAlternating B hVB hV)).comp
    (PresheafOfModules.extPowSections 2
      (dpDifferentialsModules B.obj.thickening.target S.S.scheme B.obj.toBase.hom)
      (op ⊤)).toLinearMap

/-- The wedge of two sections of `Ω_{T/S,δ}` over `T`, as a section over `T` of the sectionwise
second exterior power.  Spelled at the sections of `extPow` so that the comparison with the
exterior power happens once, here. -/
def wedgeTwoAmbient (x y : crysDiffSections B.obj) :
    ↥((dpSecondExteriorPresheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj
      (op ⊤)) :=
  exteriorPower.ιMulti _ 2 ![x, y]

omit [IsAffine B.obj.thickening.target.scheme] in
/-- The sectionwise wedge of two sections of `Ω_{T/S,δ}` is `wedgeTwoAmbient`. -/
theorem dpWedgePresheaf_eq_wedgeTwoAmbient (x y : crysDiffSections B.obj) :
    dpWedgePresheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom (op ⊤) x y =
      wedgeTwoAmbient B x y := by
  refine Subtype.ext ?_
  unfold wedgeTwoAmbient
  rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  simp [List.ofFn_succ]
  rfl

/-- The inverse comparison on a wedge: `x ∧ y ↦ ψ x ∧ ψ y`. -/
theorem secondFormsInvPresheaf_wedgeTwoAmbient (x y : crysDiffSections B.obj) :
    secondFormsInvPresheaf B hVB hV (wedgeTwoAmbient B x y) =
      exteriorPower.ιMulti (GlobalCrystallineSituation.crysFormRing S B.obj) 2
        ![affineCrysOmegaEquiv B.obj hVB hV x, affineCrysOmegaEquiv B.obj hVB hV y] := by
  refine (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (wedgeInvAlternating B hVB hV) ![x, y]).trans ?_
  change exteriorPower.ιMulti _ 2 _ = _
  congr 1
  funext i
  fin_cases i <;> rfl

/-! ### The comparison of two-forms is bijective -/

/-- The sheafification unit `⋀² Γ(T, Ω_{T/S,δ}) ⟶ Γ(T, Ω²_{T/S,δ})` over `T`, as a function. -/
abbrev secondFormsUnit
    (w : ↥((dpSecondExteriorPresheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj
      (op ⊤))) : crysSecondFormSections B.obj :=
  (dpSecondExteriorToSheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app (op ⊤) w

omit [IsAffine B.obj.thickening.target.scheme] in
/-- The sheafification unit carries the sectionwise wedge to the exterior product of sections. -/
theorem secondFormsUnit_wedgeTwoAmbient (x y : crysDiffSections B.obj) :
    secondFormsUnit B (wedgeTwoAmbient B x y) = crysWedgeSections B.obj x y := by
  rw [← dpWedgePresheaf_eq_wedgeTwoAmbient]
  rfl

/-- The sheafification unit over the affine `T` is bijective. -/
theorem bijective_secondFormsUnit : Function.Bijective (secondFormsUnit B) :=
  bijective_dpSecondExteriorToSheaf_app B.obj.thickening.target S.S.scheme B.obj.toBase.hom
    (isAffineOpen_top _)

/-- The sections over `T` of the sectionwise second exterior power, as the second exterior power
of the sections of `Ω_{T/S,δ}`. -/
abbrev secondFormsSections :=
  PresheafOfModules.extPowSections 2
    (dpDifferentialsModules B.obj.thickening.target S.S.scheme B.obj.toBase.hom) (op ⊤)

/-- The comparison after the inverse comparison, read on the second exterior power of the sections
of `Ω_{T/S,δ}`. -/
def secondFormsRoundTrip :
    ↥(⋀[ambientRing B]^2 (ambientForms B)) →+ crysSecondFormSections B.obj :=
  ((secondFormsMap B hVB hV).toAddMonoidHom.comp
    (secondFormsInvPresheaf B hVB hV).toAddMonoidHom).comp
      (secondFormsSections B).symm.toAddEquiv.toAddMonoidHom

/-- The sheafification unit, read on the second exterior power of the sections of
`Ω_{T/S,δ}`. -/
def secondFormsUnitHom :
    ↥(⋀[ambientRing B]^2 (ambientForms B)) →+ crysSecondFormSections B.obj :=
  ((dpSecondExteriorToSheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app
    (op ⊤)).hom.toAddMonoidHom.comp (secondFormsSections B).symm.toAddEquiv.toAddMonoidHom

/-- The round trip and the unit agree on a wedge. -/
theorem secondFormsRoundTrip_wedgeTwoAmbient (v : Fin 2 → ambientForms B) :
    secondFormsRoundTrip B hVB hV (exteriorPower.ιMulti (ambientRing B) 2 v) =
      secondFormsUnitHom B (exteriorPower.ιMulti (ambientRing B) 2 v) := by
  have hv : (secondFormsSections B).symm (exteriorPower.ιMulti (ambientRing B) 2 v) =
      wedgeTwoAmbient B (v 0) (v 1) := by
    refine (secondFormsSections B).injective ?_
    rw [LinearEquiv.apply_symm_apply]
    change exteriorPower.ιMulti (ambientRing B) 2 v = exteriorPower.ιMulti _ 2 ![v 0, v 1]
    congr 1
    funext i
    fin_cases i <;> rfl
  change secondFormsMap B hVB hV (secondFormsInvPresheaf B hVB hV
      ((secondFormsSections B).symm (exteriorPower.ιMulti (ambientRing B) 2 v))) =
    secondFormsUnit B ((secondFormsSections B).symm (exteriorPower.ιMulti (ambientRing B) 2 v))
  rw [hv]
  refine (congrArg (secondFormsMap B hVB hV)
    (secondFormsInvPresheaf_wedgeTwoAmbient B hVB hV (v 0) (v 1))).trans ?_
  refine (secondFormsMap_ιMulti B hVB hV _).trans ?_
  refine Eq.trans ?_ (secondFormsUnit_wedgeTwoAmbient B (v 0) (v 1)).symm
  exact congrArg₂ (crysWedgeSections B.obj)
    ((affineCrysOmegaEquiv B.obj hVB hV).symm_apply_apply (v 0))
    ((affineCrysOmegaEquiv B.obj hVB hV).symm_apply_apply (v 1))

/-- The round trip is semilinear. -/
theorem secondFormsRoundTrip_smul (c : ambientRing B) (z : ↥(⋀[ambientRing B]^2 (ambientForms B))) :
    secondFormsRoundTrip B hVB hV (c • z) =
      ambientRingCast B c • secondFormsRoundTrip B hVB hV z := by
  change secondFormsMap B hVB hV (secondFormsInvPresheaf B hVB hV
      ((secondFormsSections B).symm (c • z))) = _
  rw [LinearEquiv.map_smul, (secondFormsInvPresheaf B hVB hV).map_smul]
  exact (secondFormsMap B hVB hV).map_smul _ _

omit [IsAffine B.obj.thickening.target.scheme] in
/-- The unit, read on the exterior power, is semilinear. -/
theorem secondFormsUnitHom_smul (c : ambientRing B) (z : ↥(⋀[ambientRing B]^2 (ambientForms B))) :
    secondFormsUnitHom B (c • z) = ambientRingCast B c • secondFormsUnitHom B z := by
  change ((dpSecondExteriorToSheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app
    (op ⊤)).hom ((secondFormsSections B).symm (c • z)) = _
  rw [LinearEquiv.map_smul]
  exact ((dpSecondExteriorToSheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app
    (op ⊤)).hom.map_smul c _

/-- Induction on an exterior power from the generating wedges. -/
private theorem exteriorPower_induction {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} {P : ⋀[R]^n M → Prop} (x : ⋀[R]^n M) (mem : ∀ v, P (exteriorPower.ιMulti R n v))
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y)) (smul : ∀ (c : R) x, P x → P (c • x)) :
    P x := by
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      exact mem v
  | zero => exact zero
  | add z z' _ _ hz hz' => exact add z z' hz hz'
  | smul c z _ hz => exact smul c z hz

/-- The round trip is the sheafification unit: the two agree on wedges, which span. -/
theorem secondFormsRoundTrip_eq_secondFormsUnitHom :
    secondFormsRoundTrip B hVB hV = secondFormsUnitHom B := by
  refine AddMonoidHom.ext fun y ↦ ?_
  refine exteriorPower_induction
    (P := fun y ↦ secondFormsRoundTrip B hVB hV y = secondFormsUnitHom B y) y (fun v ↦ ?_) ?_
    (fun z z' hz hz' ↦ ?_) fun c z hz ↦ ?_
  · exact secondFormsRoundTrip_wedgeTwoAmbient B hVB hV v
  · exact (map_zero _).trans (map_zero _).symm
  · exact (map_add _ z z').trans ((congrArg₂ (· + ·) hz hz').trans (map_add _ z z').symm)
  · exact (secondFormsRoundTrip_smul B hVB hV c z).trans
      ((congrArg (ambientRingCast B c • ·) hz).trans (secondFormsUnitHom_smul B c z).symm)

/-- **The two comparisons of two-forms are compatible**: the unit is the comparison
`⋀²_D Ω_{X/S}(B) ⟶ Γ(T, Ω²_{T/S,δ})` after the inverse comparison. -/
theorem secondFormsMap_secondFormsInvPresheaf
    (w : ↥((dpSecondExteriorPresheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj
      (op ⊤))) :
    secondFormsMap B hVB hV (secondFormsInvPresheaf B hVB hV w) = secondFormsUnit B w := by
  have h := congrArg (fun φ : ↥(⋀[ambientRing B]^2 (ambientForms B)) →+
      crysSecondFormSections B.obj ↦ φ ((secondFormsSections B) w))
    (secondFormsRoundTrip_eq_secondFormsUnitHom B hVB hV)
  simp only [secondFormsRoundTrip, secondFormsUnitHom, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass] at h
  exact h

/-- **The inverse comparison is surjective**: every wedge of two forms of `Ω_{X/S}(B)` is the image
of a wedge of two sections of `Ω_{T/S,δ}`. -/
theorem surjective_secondFormsInvPresheaf :
    Function.Surjective (secondFormsInvPresheaf B hVB hV) := by
  intro x
  refine exteriorPower_induction (P := (· ∈ LinearMap.range (secondFormsInvPresheaf B hVB hV))) x
    (fun v ↦ ?_) (Submodule.zero_mem _) (fun z z' hz hz' ↦ Submodule.add_mem _ hz hz')
    fun c z hz ↦ Submodule.smul_mem _ (show ambientRing B from c) hz
  refine ⟨wedgeTwoAmbient B ((affineCrysOmegaEquiv B.obj hVB hV).symm (v 0))
    ((affineCrysOmegaEquiv B.obj hVB hV).symm (v 1)), ?_⟩
  refine (secondFormsInvPresheaf_wedgeTwoAmbient B hVB hV _ _).trans ?_
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **The comparison `⋀²_D Ω_{X/S}(B) ⟶ Γ(T, Ω²_{T/S,δ})` is bijective.** -/
theorem bijective_secondFormsMap : Function.Bijective (secondFormsMap B hVB hV) := by
  refine ⟨fun x x' hxx' ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨w, rfl⟩ := surjective_secondFormsInvPresheaf B hVB hV x
    obtain ⟨w', rfl⟩ := surjective_secondFormsInvPresheaf B hVB hV x'
    rw [secondFormsMap_secondFormsInvPresheaf, secondFormsMap_secondFormsInvPresheaf] at hxx'
    rw [(bijective_secondFormsUnit B).1 hxx']
  · obtain ⟨w, rfl⟩ := (bijective_secondFormsUnit B).2 z
    exact ⟨_, secondFormsMap_secondFormsInvPresheaf B hVB hV w⟩

/-- **The comparison of two-forms as a linear equivalence**,
`⋀²_D Ω_{X/S}(B) ≅ Γ(T, Ω²_{T/S,δ})`. -/
def secondFormsEquiv :
    ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^2
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) ≃ₗ[
      GlobalCrystallineSituation.crysFormRing S B.obj] crysSecondFormSections B.obj :=
  LinearEquiv.ofBijective (secondFormsMap B hVB hV) (bijective_secondFormsMap B hVB hV)

/-! ### Integrability in the sense of [Stacks, Tag 07I0] -/

variable {B}

/-- The extension to differential forms of the canonical connection of a sheaf of modules on
`Cris(X/S)` over an affine-over-affine object, by [Stacks, Tag 07I0]. -/
abbrev ringExtension :
    ExtendedConnection (canonicalSourceDeRham ↥Γ(S.S.scheme, ⊤)
      (GlobalCrystallineSituation.crysFormRing S B.obj)) (crysPi S B.obj)
      (ringConnection hVB hV he) :=
  Crystalline.extendedConnection (canonicalSourceDeRham ↥Γ(S.S.scheme, ⊤)
      (GlobalCrystallineSituation.crysFormRing S B.obj))
    (crysPi S B.obj) (surjective_crysPi S B.obj) (generationHypothesis_crysPi S B.obj)
    (ringConnection hVB hV he)

/-- **The descended de Rham differential in degree one, read in `Γ(T, Ω²_{T/S,δ})`, is the de Rham
differential of `Ω_{T/S,δ}`.** -/
theorem secondFormsMap_descendedDifferential
    (ω : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    secondFormsMap B hVB hV (descendedDifferential (ringExtension hVB hV he).deRhamDifferential 1
        ((exteriorPower.oneEquiv _ _).symm ω)) =
      crysDeRham B.obj ((affineCrysOmegaEquiv B.obj hVB hV).symm ω) := by
  have hrule := extendedConnection_satisfiesRule (pi := crysPi S B.obj)
    (canonicalSourceDeRham ↥Γ(S.S.scheme, ⊤) (GlobalCrystallineSituation.crysFormRing S B.obj))
    (surjective_crysPi S B.obj) (generationHypothesis_crysPi S B.obj) (ringConnection hVB hV he)
  have hgen : ∀ (c b : GlobalCrystallineSituation.crysFormRing S B.obj),
      secondFormsMap B hVB hV (descendedDifferential (ringExtension hVB hV he).deRhamDifferential
          1 ((exteriorPower.oneEquiv _ _).symm (c • GlobalCrystallineSituation.crysD S B.obj b))) =
        crysDeRham B.obj ((affineCrysOmegaEquiv B.obj hVB hV).symm
          (c • GlobalCrystallineSituation.crysD S B.obj b)) := by
    intro c b
    have h1 : (exteriorPower.oneEquiv (GlobalCrystallineSituation.crysFormRing S B.obj)
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))).symm
          (c • GlobalCrystallineSituation.crysD S B.obj b) =
            SourceDeRham.tgtGen (crysPi S B.obj) 1 ![c, b] := by
      rw [LinearEquiv.map_smul, exteriorPower.oneEquiv_symm_apply]
      rfl
    rw [h1, descendedDifferential_apply, hrule 1 ![c, b]]
    change secondFormsMap B hVB hV (exteriorPower.ιMulti _ 2 _) = _
    rw [secondFormsMap_ιMulti, LinearEquiv.map_smul]
    change wedgePair B hVB hV (GlobalCrystallineSituation.crysD S B.obj c)
      (GlobalCrystallineSituation.crysD S B.obj b) = _
    refine Eq.trans ?_ (crysDeRham_smul B.obj c _).symm
    unfold wedgePair
    rw [affineCrysOmegaEquiv_symm_crysD, affineCrysOmegaEquiv_symm_crysD]
    have h0 : crysDeRham B.obj (crysDerivation B.obj b) = 0 :=
      dpDeRham_d B.obj.thickening.target S.S.scheme B.obj.toBase.hom (op ⊤) b
    rw [h0]
    exact (zero_add _).symm.trans (congrArg (· + _) (smul_zero c).symm)
  have key : ∀ x ∈ Submodule.span (GlobalCrystallineSituation.crysFormRing S B.obj)
      (Set.range (GlobalCrystallineSituation.crysD S B.obj)),
      ∀ c : GlobalCrystallineSituation.crysFormRing S B.obj,
        secondFormsMap B hVB hV (descendedDifferential
            (ringExtension hVB hV he).deRhamDifferential 1
            ((exteriorPower.oneEquiv _ _).symm (c • x))) =
          crysDeRham B.obj ((affineCrysOmegaEquiv B.obj hVB hV).symm (c • x)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨b, rfl⟩ := hz
        exact fun c ↦ hgen c b
    | zero =>
        intro c
        rw [smul_zero, map_zero, map_zero, map_zero, map_zero]
        exact (dpDeRham_zero B.obj.thickening.target S.S.scheme B.obj.toBase.hom (op ⊤)).symm
    | add z z' _ _ hz hz' =>
        intro c
        rw [smul_add, map_add, map_add, map_add, hz c, hz' c, map_add, crysDeRham_add]
    | smul a z _ hz =>
        intro c
        rw [smul_smul]
        exact hz (c * a)
  have h := key ω (by rw [crysD_span]; exact Submodule.mem_top) 1
  rwa [one_smul] at h

omit he in
variable (F) in
/-- `ℱ(B) ⊗_D ⋀²_D Ω_{X/S}(B) ≅ Γ(T, Ω²_{T/S,δ}) ⊗_D ℱ(B)`, the comparison of two-forms tensored
with the module and the factors swapped. -/
def secondTensorEquiv :
    F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
        ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^2
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) ≃+
      crysSecondFormSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) :=
  ((TensorProduct.congr (LinearEquiv.refl _ _) (secondFormsEquiv B hVB hV)).trans
    (TensorProduct.comm _ _ _)).toAddEquiv

omit he in
/-- `secondTensorEquiv` on a pure tensor. -/
theorem secondTensorEquiv_tmul (s : F.val.obj (op B))
    (x : ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^2
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    secondTensorEquiv F hVB hV (s ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj] x) =
      secondFormsMap B hVB hV x ⊗ₜ[crysSheafRing S B.obj] s := rfl

omit he in
/-- The first term of the extended connection, read through the comparison of two-forms, is the
exterior multiplication on the right of `SmallSite/CrysAffineConnection.lean`. -/
theorem secondTensorEquiv_leftWedge
    (ω : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)))
    (z : F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    secondTensorEquiv F hVB hV (TensorProduct.map LinearMap.id
        ((leftWedge 1).flip ((exteriorPower.oneEquiv _ _).symm ω)) z) =
      wedgeRight F B ((affineCrysOmegaEquiv B.obj hVB hV).symm ω)
        ((tensorFlipAdd F B hVB hV).symm z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s η =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.flip_apply, secondTensorEquiv_tmul,
        exteriorPower.oneEquiv_symm_apply, leftWedge_ιMulti, secondFormsMap_ιMulti,
        tensorFlipAdd_symm_tmul, wedgeRight_tmul]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The degree-one extension of [Stacks, Tag 07I0] on `ℱ(B) ⊗_D Ω_{X/S}(B)`, read in
`Γ(T, Ω²_{T/S,δ}) ⊗_D ℱ(B)`. -/
def ringExtensionOne :
    F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) →+
      crysSecondFormSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) :=
  (secondTensorEquiv F hVB hV).toAddMonoidHom.comp
    ((RestrictScalars.addEquiv _ _ _).toAddMonoidHom.comp
      (((ringExtension hVB hV he).toLinearMap 1).toAddMonoidHom.comp
        ((RestrictScalars.addEquiv ↥Γ(S.S.scheme, ⊤)
            (GlobalCrystallineSituation.crysFormRing S B.obj) _).symm.toAddMonoidHom.comp
          (TensorProduct.map LinearMap.id
            (exteriorPower.oneEquiv _ _).symm.toLinearMap).toAddMonoidHom)))

/-- `ringExtensionOne` on a pure tensor. -/
theorem ringExtensionOne_tmul (s : F.val.obj (op B))
    (ω : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    ringExtensionOne hVB hV he (s ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj] ω) =
      extendedConnection he ((tensorFlipAdd F B hVB hV).symm
        (s ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj] ω)) := by
  change secondTensorEquiv F hVB hV (RestrictScalars.addEquiv _ _ _
      ((ringExtension hVB hV he).toLinearMap 1
        (s ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
          (exteriorPower.oneEquiv _ _).symm ω))) = _
  rw [(ringExtension hVB hV he).map_tmul 1 s, map_add, secondTensorEquiv_leftWedge,
    tensorFlipAdd_symm_tmul, extendedConnection_tmul, ringConnection_apply,
    AddEquiv.symm_apply_apply, secondTensorEquiv_tmul]
  congr 1
  rw [← descendedDifferential_apply, secondFormsMap_descendedDifferential]

/-- **The degree-one extension of [Stacks, Tag 07I0], read through the comparison of two-forms, is
the degree-one extension of `SmallSite/CrysAffineConnection.lean`.** -/
theorem ringExtensionOne_eq :
    ringExtensionOne hVB hV he =
      (extendedConnection he).comp (tensorFlipAdd F B hVB hV).symm.toAddMonoidHom := by
  refine AddMonoidHom.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul s ω => exact ringExtensionOne_tmul hVB hV he s ω
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ x y).symm)

/-- **Integrability of the canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6] in the sense
of [Stacks, Tag 07I0]**, for a sheaf of modules on `Cris(X/S)` over an affine-over-affine object:
the connection composes with its own degree-one extension to zero.  Read through the comparison
of two-forms, that composite is the composite `∇ ∘ ∇` of `SmallSite/CrysAffineConnection.lean`,
which vanishes as soon as the base change along `q₀` is injective. -/
theorem ringConnection_isIntegrable
    (he₂ : Function.Injective (crysSecondExtensionSectionsMap F B)) :
    Connection.IsIntegrable (canonicalSourceDeRham ↥Γ(S.S.scheme, ⊤)
        (GlobalCrystallineSituation.crysFormRing S B.obj))
      (crysPi S B.obj) (surjective_crysPi S B.obj) (generationHypothesis_crysPi S B.obj)
      (ringConnection hVB hV he) := by
  refine Connection.isIntegrable_of_comp_eq_zero fun s ↦ ?_
  refine (RestrictScalars.addEquiv _ _ _).injective ((secondTensorEquiv F hVB hV).injective ?_)
  have h := congrArg (fun φ : _ →+ _ ↦ φ (ringConnection hVB hV he s))
    (ringExtensionOne_eq hVB hV he)
  refine h.trans ?_
  change extendedConnection he ((tensorFlipAdd F B hVB hV).symm
    (tensorFlipAdd F B hVB hV (connection he s))) = _
  rw [AddEquiv.symm_apply_apply, extendedConnection_connection he he₂ s]
  exact ((secondTensorEquiv F hVB hV).map_zero.symm.trans
    (congrArg (secondTensorEquiv F hVB hV) (map_zero (RestrictScalars.addEquiv
      ↥Γ(S.S.scheme, ⊤) (GlobalCrystallineSituation.crysFormRing S B.obj)
      (F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
        ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^(1 + 1)
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))))).symm))

end Crystalline.GlobalCrystallineSituation.SmallSite.AffineConnection

end

end
