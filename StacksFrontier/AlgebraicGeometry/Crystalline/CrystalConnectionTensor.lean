module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionGeneral

/-!
# The canonical connection of a crystal, valued in `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site and let `(U, T, δ)` be an object of `CRIS(X/S)`
with first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2]. Write
`D = Γ(T, 𝒪_T)`, `Ω = Γ(T, Ω_{T/S,δ})` and `M = F(U, T, δ)`.

The canonical map `Ω ⊗_D M ⟶ Γ(T', F_{T'})`, `ω ⊗ s ↦ ω · p₀^* s`, lands in the kernel of
restriction along the diagonal `i : T ⟶ T'`. Given a two-sided inverse of it on that kernel, the
difference `p₁^* s - p₀^* s` defines a connection `∇ : M ⟶ Ω ⊗_D M` satisfying the Leibniz rule
`∇(b s) = b ∇(s) + d b ⊗ s` of [Stacks, Tag 07J6]. For `F = 𝒪_{X/S}` such an inverse exists, and
the connection is `b ↦ d b ⊗ 1`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.diffAction`: the canonical map
  `Ω ⊗_D M ⟶ Γ(T', F_{T'})`, `ω ⊗ s ↦ ω · p₀^* s`.
* `Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`: an additive retraction of
  `diffAction` which is a two-sided inverse of it on the kernel of restriction along the diagonal.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionTensor`: the connection
  `∇ : M ⟶ Ω ⊗_D M` defined by such a retraction.
* `Crystalline.GlobalCrystallineSituation.firstOrderIdealBaseChangeUnit`: the retraction for
  `F = 𝒪_{X/S}`.

## Main results

* `Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_siteι_diffAction`: the canonical
  map lands in the kernel of restriction along the diagonal.
* `Crystalline.GlobalCrystallineSituation.diffAction_smul`: it is semilinear over `p₀`.
* `Crystalline.GlobalCrystallineSituation.diffSection_smul_diffAction`: the square-zero summand
  of differentials annihilates its image.
* `Crystalline.GlobalCrystallineSituation.diffAction_crystalConnectionTensor`: the canonical map
  carries `∇(s)` to `p₁^* s - p₀^* s`.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_smul`: the Leibniz rule
  `∇(b s) = b ∇(s) + d b ⊗ s`.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_unit`: at `F = 𝒪_{X/S}` the
  connection is `b ↦ d_{T/S,δ} b ⊗ 1`.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The base ring and the module of differentials, on sections over an object -/

/-- The commutative ring structure on the sections of `𝒪_{X/S}` over an object, that of the
global sections of its ambient scheme. -/
instance crysSheafRingCommRing (A : Thickening S) : CommRing (crysSheafRing S A) :=
  inferInstanceAs (CommRing Γ(A.thickening.target.scheme, ⊤))

/-- The sections `Ω = Γ(T, Ω_{T/S,δ})` of the module of divided power differentials over the
whole ambient scheme of an object. -/
abbrev crysDiffSections (A : Thickening S) : Type u :=
  Γ(dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom, ⊤)

/-! ### Arithmetic of the square-zero summand on sections -/

variable (M : SheafOfModules.{u} (crystallineStructureSheaf S))

/-- Reading a differential as a section of `𝒪_{T'}` is additive. -/
theorem firstOrderThickeningDiffSection_add (A : Thickening S) (ω ω' : crysDiffSections A) :
    firstOrderThickeningDiffSection A (ω + ω') =
      firstOrderThickeningDiffSection A ω + firstOrderThickeningDiffSection A ω' :=
  map_add (firstOrderThickeningInr A.thickening.target S.S.scheme A.toBase.hom (op ⊤)) ω ω'

/-- Reading the zero differential as a section of `𝒪_{T'}` gives zero. -/
@[simp]
theorem firstOrderThickeningDiffSection_zero (A : Thickening S) :
    firstOrderThickeningDiffSection A (0 : crysDiffSections A) = 0 :=
  map_zero (firstOrderThickeningInr A.thickening.target S.S.scheme A.toBase.hom (op ⊤))

/-- Restriction along the diagonal `i : T ⟶ T'` kills the summand of differentials of
`𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`. -/
@[simp]
theorem crysSheafRingMap_siteι_diffSection (A : Thickening S) (ω : crysDiffSections A) :
    crysSheafRingMap (firstOrderThickeningSiteι S A) (firstOrderThickeningDiffSection A ω) = 0 :=
  rfl

/-- The summand of differentials of `𝒪_{T'}` is an ideal of square zero: the product of two
sections coming from differentials vanishes. -/
theorem firstOrderThickeningDiffSection_mul (A : Thickening S) (ω ω' : crysDiffSections A) :
    firstOrderThickeningDiffSection A ω * firstOrderThickeningDiffSection A ω' = 0 := by
  have hz : crysSheafRingMap (firstOrderThickeningSiteι S A)
      (firstOrderThickeningDiffSection A ω) • ω' = (0 : crysDiffSections A) := by
    rw [crysSheafRingMap_siteι_diffSection, zero_smul]
  exact (mul_firstOrderThickeningInr A.thickening.target S.S.scheme A.toBase.hom (op ⊤)
      (firstOrderThickeningDiffSection A ω) ω').trans
    ((congrArg
        (fun x ↦ firstOrderThickeningInr A.thickening.target S.S.scheme A.toBase.hom (op ⊤) x)
        hz).trans
      (map_zero (firstOrderThickeningInr A.thickening.target S.S.scheme A.toBase.hom (op ⊤))))

/-- The component in the summand of differentials of a section of `𝒪_{T'}` over the whole
ambient scheme: the second coordinate of the additive identification `𝒪_{T'}(T') = 𝒪_T(T) ⊕ Ω`
of [Stacks, Tag 07J2]. -/
def crysDiffPart (A : Thickening S)
    (t : crysSheafRing S (firstOrderThickeningObject S A)) : crysDiffSections A :=
  (firstOrderThickeningEquiv A.thickening.target S.S.scheme A.toBase.hom (op ⊤) t).2

/-- Taking the component in the summand of differentials is additive. -/
theorem crysDiffPart_add (A : Thickening S)
    (t t' : crysSheafRing S (firstOrderThickeningObject S A)) :
    crysDiffPart A (t + t') = crysDiffPart A t + crysDiffPart A t' := rfl

/-- The component in the summand of differentials of a differential read as a section is the
differential itself. -/
@[simp]
theorem crysDiffPart_diffSection (A : Thickening S) (ω : crysDiffSections A) :
    crysDiffPart A (firstOrderThickeningDiffSection A ω) = ω := rfl

/-! ### The canonical map `F_T ⊗ Ω ⟶ ker` -/

/-- The biadditive map sending a differential `ω` and a section `s` of `F` over an object to the
section `ω · p₀^* s` of `F` over the first-order thickening. -/
def diffActionAux (A : Thickening S) :
    crysDiffSections A →+
      (M.val.obj (op A) →+ M.val.obj (op (firstOrderThickeningObject S A))) :=
  AddMonoidHom.mk'
    (fun ω ↦ AddMonoidHom.mk'
      (fun s ↦ firstOrderThickeningDiffSection A ω •
        moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s)
      (fun s t ↦ by rw [map_add, smul_add]))
    (fun ω ω' ↦ by
      ext s
      change firstOrderThickeningDiffSection A (ω + ω') •
          moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s =
        firstOrderThickeningDiffSection A ω •
            moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s +
          firstOrderThickeningDiffSection A ω' •
            moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s
      rw [firstOrderThickeningDiffSection_add, add_smul])

/-- The canonical map `Ω ⊗_D M ⟶ Γ(T', F_{T'})` on sections over an object, sending `ω ⊗ s` to
`ω · p₀^* s`. -/
def diffAction (A : Thickening S) :
    crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A) →+
      M.val.obj (op (firstOrderThickeningObject S A)) :=
  TensorProduct.liftAddHom (diffActionAux M A)
    (fun b ω s ↦ (firstOrderThickeningDiffSection_smul_balanced M A b ω s).symm)

/-- The canonical map sends `ω ⊗ s` to `ω · p₀^* s`. -/
@[simp]
theorem diffAction_tmul (A : Thickening S) (ω : crysDiffSections A) (s : M.val.obj (op A)) :
    diffAction M A (ω ⊗ₜ[crysSheafRing S A] s) =
      firstOrderThickeningDiffSection A ω •
        moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s :=
  TensorProduct.liftAddHom_tmul _ _ ω s

/-- The canonical map lands in the kernel of restriction along the diagonal. -/
theorem moduleSiteRestrict_siteι_diffAction (A : Thickening S)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    moduleSiteRestrict M (firstOrderThickeningSiteι S A) (diffAction M A z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul ω s =>
      rw [diffAction_tmul, map_smulₛₗ, crysSheafRingMap_siteι_diffSection, zero_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- The canonical map is semilinear over `p₀`: `diffAction (b • z) = p₀(b) • diffAction z`. -/
theorem diffAction_smul (A : Thickening S) (b : crysSheafRing S A)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    diffAction M A (b • z) =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b • diffAction M A z := by
  induction z using TensorProduct.inductionOn with
  | tmul ω s =>
      rw [TensorProduct.smul_tmul', diffAction_tmul, diffAction_tmul, smul_smul,
        crysSheafRingMap_siteP₀_mul_diffSection]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The summand of differentials of `𝒪_{T'}` annihilates the image of the canonical map. -/
theorem diffSection_smul_diffAction (A : Thickening S) (ω : crysDiffSections A)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    firstOrderThickeningDiffSection A ω • diffAction M A z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul ω' s =>
      rw [diffAction_tmul, smul_smul, firstOrderThickeningDiffSection_mul, zero_smul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

/-! ### The datum inverting the canonical map -/

/-- An additive retraction of `Crystalline.GlobalCrystallineSituation.diffAction` which is a
two-sided inverse of it on the kernel of restriction along the diagonal; equivalently, an
identification of that kernel with `Ω ⊗_D M`. -/
structure FirstOrderIdealBaseChange (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (A : Thickening S) where
  /-- The inverse map, from the sections over the first-order thickening to `Ω ⊗_D M`. -/
  proj : M.val.obj (op (firstOrderThickeningObject S A)) →+
    crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)
  /-- It is a left inverse of the canonical map. -/
  proj_diffAction : ∀ z, proj (diffAction M A z) = z
  /-- It is a right inverse of the canonical map on the ideal of the diagonal. -/
  diffAction_proj : ∀ t, moduleSiteRestrict M (firstOrderThickeningSiteι S A) t = 0 →
    diffAction M A (proj t) = t

namespace FirstOrderIdealBaseChange

variable {M}

/-- Given a `FirstOrderIdealBaseChange`, the canonical map is injective. -/
theorem injective_diffAction {A : Thickening S} (h : FirstOrderIdealBaseChange M A) :
    Function.Injective (diffAction M A) :=
  Function.LeftInverse.injective h.proj_diffAction

end FirstOrderIdealBaseChange

/-! ### The connection with the target of the tag -/

/-- The connection `∇ : Γ(T, F_T) ⟶ Γ(T, Ω_{T/S,δ}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T)` of a sheaf of
`𝒪_{X/S}`-modules, the retraction `h` applied to the difference `p₁^* s - p₀^* s` of the
restrictions along the two projections of the first-order universal thickening. -/
def crystalConnectionTensor (A : Thickening S) (h : FirstOrderIdealBaseChange M A) :
    M.val.obj (op A) →+ crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A) :=
  h.proj.comp (crystalConnection M A)

/-- `∇(s)` is the retraction applied to `p₁^* s - p₀^* s`. -/
theorem crystalConnectionTensor_apply (A : Thickening S) (h : FirstOrderIdealBaseChange M A)
    (s : M.val.obj (op A)) :
    crystalConnectionTensor M A h s = h.proj (crystalConnection M A s) := rfl

/-- The canonical map carries `∇(s)` to the difference `p₁^* s - p₀^* s`. -/
theorem diffAction_crystalConnectionTensor (A : Thickening S)
    (h : FirstOrderIdealBaseChange M A) (s : M.val.obj (op A)) :
    diffAction M A (crystalConnectionTensor M A h s) = crystalConnection M A s :=
  h.diffAction_proj _ (crystalConnection_map_ι M A s)

/-- The Leibniz rule `∇(b s) = b ∇(s) + d b ⊗ s` of [Stacks, Tag 07J6], with
`d = d_{T/S,δ}` the universal divided power derivation. -/
theorem crystalConnectionTensor_smul (A : Thickening S) (h : FirstOrderIdealBaseChange M A)
    (b : crysSheafRing S A) (s : M.val.obj (op A)) :
    crystalConnectionTensor M A h (b • s) =
      b • crystalConnectionTensor M A h s +
        sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b ⊗ₜ[crysSheafRing S A] s := by
  refine h.injective_diffAction ?_
  rw [diffAction_crystalConnectionTensor, map_add, diffAction_smul,
    diffAction_crystalConnectionTensor, diffAction_tmul, crystalConnection_smul]
  refine congrArg (fun x ↦ x + firstOrderThickeningDiffSection A
    (sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b) •
      moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s) ?_
  have hsub : crysSheafRingMap (firstOrderThickeningSiteP₁ S A) b =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b +
        firstOrderThickeningDiffSection A
          (sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b) := by
    rw [← crysSheafRingMap_siteP₁_sub_siteP₀]
    abel
  rw [hsub, add_smul, ← diffAction_crystalConnectionTensor M A h s,
    diffSection_smul_diffAction, add_zero]

/-! ### The case `F = 𝒪_{X/S}`: the datum exists -/

/-- A section of `𝒪_{T'}` killed by restriction along the diagonal is the differential given by
its own component in the summand of differentials. -/
theorem firstOrderThickeningDiffSection_crysDiffPart (A : Thickening S)
    (t : crysSheafRing S (firstOrderThickeningObject S A))
    (ht : crysSheafRingMap (firstOrderThickeningSiteι S A) t = 0) :
    firstOrderThickeningDiffSection A (crysDiffPart A t) = t :=
  congrArg Subtype.val
    ((firstOrderThickeningKernelEquiv A.thickening.target S.S.scheme A.toBase.hom
      (op ⊤)).apply_symm_apply ⟨t, RingHom.mem_ker.mpr ht⟩)

/-- For `F = 𝒪_{X/S}`, the canonical map sends `ω ⊗ x` to the differential `x • ω`, read as a
section of `𝒪_{T'}`. -/
private theorem diffAction_unit_tmul (A : Thickening S) (ω : crysDiffSections A)
    (x : crysSheafRing S A) :
    diffAction (SheafOfModules.unit (crystallineStructureSheaf S)) A (ω ⊗ₜ[crysSheafRing S A] x) =
      firstOrderThickeningDiffSection A (x • ω) :=
  (diffAction_tmul (SheafOfModules.unit (crystallineStructureSheaf S)) A ω x).trans
    (diffSection_mul_crysSheafRingMap_siteP₀ A x ω)

/-- For `F = 𝒪_{X/S}`, the component in the summand of differentials of the image of `ω ⊗ x`
under the canonical map is `x • ω`. -/
theorem crysDiffPart_diffAction_unit_tmul (A : Thickening S) (ω : crysDiffSections A)
    (x : crysSheafRing S A) :
    crysDiffPart A (diffAction (SheafOfModules.unit (crystallineStructureSheaf S)) A
        (ω ⊗ₜ[crysSheafRing S A] x)) = x • ω := by
  rw [diffAction_unit_tmul, crysDiffPart_diffSection]

/-- For `F = 𝒪_{X/S}`, the component in the summand of differentials of `ω · p₀^* x`, tensored
with `1`, is `ω ⊗ x`. -/
theorem tmul_crysDiffPart_diffAction_unit (A : Thickening S) (ω : crysDiffSections A)
    (x : crysSheafRing S A) :
    crysDiffPart A (diffAction (SheafOfModules.unit (crystallineStructureSheaf S)) A
          (ω ⊗ₜ[crysSheafRing S A] x)) ⊗ₜ[crysSheafRing S A] (1 : crysSheafRing S A) =
      ω ⊗ₜ[crysSheafRing S A] x := by
  rw [crysDiffPart_diffAction_unit_tmul, TensorProduct.smul_tmul, smul_eq_mul, mul_one]

/-- The `FirstOrderIdealBaseChange` of the structure sheaf `𝒪_{X/S}`: the projection onto the
summand of differentials of `𝒪_{T'}(T') = 𝒪_T(T) ⊕ Ω`, tensored with the unit section. -/
def firstOrderIdealBaseChangeUnit (A : Thickening S) :
    FirstOrderIdealBaseChange (SheafOfModules.unit (crystallineStructureSheaf S)) A where
  proj := AddMonoidHom.mk'
    (fun t ↦ crysDiffPart A t ⊗ₜ[crysSheafRing S A] (1 : crysSheafRing S A))
    (fun t t' ↦
      (congrArg (fun x ↦ x ⊗ₜ[crysSheafRing S A] (1 : crysSheafRing S A))
        (crysDiffPart_add A t t')).trans (TensorProduct.add_tmul _ _ _))
  proj_diffAction z := by
    induction z using TensorProduct.inductionOn with
    | tmul ω x => exact tmul_crysDiffPart_diffAction_unit A ω x
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  diffAction_proj t ht := by
    have h1 := diffAction_tmul (SheafOfModules.unit (crystallineStructureSheaf S)) A
      (crysDiffPart A t) (1 : crysSheafRing S A)
    have h2 : firstOrderThickeningDiffSection A (crysDiffPart A t) •
        moduleSiteRestrict (SheafOfModules.unit (crystallineStructureSheaf S))
          (firstOrderThickeningSiteP₀ S A) (1 : crysSheafRing S A) =
        firstOrderThickeningDiffSection A ((1 : crysSheafRing S A) • crysDiffPart A t) :=
      diffSection_mul_crysSheafRingMap_siteP₀ A 1 (crysDiffPart A t)
    refine h1.trans (h2.trans ?_)
    rw [one_smul]
    exact firstOrderThickeningDiffSection_crysDiffPart A t ht

/-- At `F = 𝒪_{X/S}`, the connection defined by
`Crystalline.GlobalCrystallineSituation.firstOrderIdealBaseChangeUnit` is `b ↦ d_{T/S,δ} b ⊗ 1`. -/
theorem crystalConnectionTensor_unit (A : Thickening S)
    (b : (SheafOfModules.unit (crystallineStructureSheaf S)).val.obj (op A)) :
    crystalConnectionTensor (SheafOfModules.unit (crystallineStructureSheaf S)) A
        (firstOrderIdealBaseChangeUnit A) b =
      sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b ⊗ₜ[crysSheafRing S A]
        (1 : crysSheafRing S A) := by
  rw [crystalConnectionTensor_apply, crystalConnection_unit]
  exact congrArg (fun x ↦ x ⊗ₜ[crysSheafRing S A] (1 : crysSheafRing S A))
    (crysDiffPart_diffSection A (sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b))

end Crystalline.GlobalCrystallineSituation

end

end
