module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderIdealAffineIntegrable
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysSecondOrderAffineBaseChange

/-!
# The canonical connection of a crystal on `Cris(X/S)`, on global sections over an object

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], a sheaf of
`𝒪_{X/S}`-modules `ℱ` on the **small** crystalline site `Cris(X/S)` and an object `B = (U, T, δ)`
of `Cris(X/S)`.  Write `D = Γ(T, 𝒪_T)`, `Ω = Γ(T, Ω_{T/S,δ})`, `Ω² = Γ(T, Ω²_{T/S,δ})` and
`Mod = ℱ(U, T, δ)`, and let `(U, T', δ')` and `(U, T'', δ'')` be the first- and second-order
universal thickenings of [Stacks, Tag 07J2] and [Stacks, Remark 60.14.5, Tag 07J3].

This module builds the canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6] on global
sections,

`∇ : Mod ⟶ Ω ⊗_D Mod`,   `∇(s) = p₁^* s - p₀^* s`,

read inside `Ω ⊗_D Mod` through the identification of `Ω ⊗_D Mod` with the sections of `ℱ` over
`(U, T', δ')` killed by restriction along the diagonal, proves its Leibniz rule
`∇(b s) = b ∇(s) + d b ⊗ s`, and proves that it is **integrable**: it composes to zero with its
degree-one extension `∇(ω ⊗ s) = ∇(s) ∧ ω + d ω ⊗ s` of [Stacks, Section 60.15, Tag 07J5].  The
recipe is the source's: the connection is the difference of the two restrictions along the two
projections `p₀, p₁ : T' ⟶ T`, and integrability is the source's computation on `T''` with the
three maps `q₀₁, q₁₂, q₀₂ : T'' ⟶ T'`.

## The two inputs

The identification of `Ω ⊗_D Mod` with the ideal of the diagonal, and the injectivity of the
degree-two canonical map `Ω² ⊗_D Mod ⟶ ℱ(U, T'', δ'')`, `η ⊗ s ↦ η · q₀^* s`, through which the
outcome of the integrability computation is read, are both consequences of the bijectivity of the
base change of sections

`D' ⊗_D Mod ⟶ ℱ(U, T', δ')` and `D'' ⊗_D Mod ⟶ ℱ(U, T'', δ'')`

along `p₀` and `q₀`: the splittings `D' = D ⊕ Ω` and `D'' = D ⊕ Ω ⊕ Ω ⊕ Ω²` of
[Stacks, Tag 07J2] and [Stacks, Tag 07J3] identify the relevant summands.  Those two bijectivity
statements are taken as arguments `he` and `he₂` by the constructions below, and they are
**theorems** for a crystal in quasi-coherent modules on an object with affine ambient scheme:
`...SmallSite.bijective_crysExtensionSectionsMap_of_isQuasicoherentOnSite` of
`SmallSite/CrysFirstOrderAffineBaseChange.lean` and
`...SmallSite.bijective_crysSecondExtensionSectionsMap_of_isQuasicoherentOnSite` of
`SmallSite/CrysSecondOrderAffineBaseChange.lean`.  On a non-affine object the global-sections
identification is false (see
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean`), which is why this
spelling of the connection is the affine one; the sheaf-level connection on `ℱ_T` over an arbitrary
object is a separate construction.

## Main definitions

Everything lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.AffineConnection`.

* `connectionDifference` — `s ↦ p₁^* s - p₀^* s`, a section of `ℱ` over `(U, T', δ')`.
* `diffAction` — the canonical map `Ω ⊗_D Mod ⟶ ℱ(U, T', δ')`, `ω ⊗ s ↦ ω · p₀^* s`.
* `proj` — its inverse on the ideal of the diagonal.
* `connection` — **the canonical connection** `∇ : Mod ⟶ Ω ⊗_D Mod`.
* `diffAction₂` — the degree-two canonical map `Ω² ⊗_D Mod ⟶ ℱ(U, T'', δ'')`.
* `extendedConnection` — the degree-one extension `Ω ⊗_D Mod ⟶ Ω² ⊗_D Mod` of §07J5.

## Main results

* `diffAction_connection` — `∇(s)` is read back to `p₁^* s - p₀^* s` by the canonical map.
* `connection_smul` — the Leibniz rule `∇(b s) = b ∇(s) + d b ⊗ s`.
* `connectionDifference_cocycle` — the curvature identity `q₀₁^* ∇ + q₁₂^* ∇ = q₀₂^* ∇` on `T''`.
* `diffAction₂_extendedConnection` — the source's integrability computation.
* `extendedConnection_connection` — **integrability**, `∇ ∘ ∇ = 0`.

## References

* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Section 60.15, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.AffineConnection

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))
  (B : CrystallineThickening S)

/-! ### Restriction along the maps of the two universal thickenings -/

/-- Restriction along `p₀ : T' ⟶ T` is semilinear over the map of section rings. -/
theorem restrict_p₀_smul (b : crysSheafRing S B.obj) (s : F.val.obj (op B)) :
    crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) (b • s) =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S B.obj) b •
        crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s :=
  F.val.map_smul (firstOrderThickeningCrysP₀ S B).op b s

/-- Restriction along `p₁ : T' ⟶ T` is semilinear over the map of section rings. -/
theorem restrict_p₁_smul (b : crysSheafRing S B.obj) (s : F.val.obj (op B)) :
    crysSiteRestrict F (firstOrderThickeningCrysP₁ S B) (b • s) =
      crysSheafRingMap (firstOrderThickeningSiteP₁ S B.obj) b •
        crysSiteRestrict F (firstOrderThickeningCrysP₁ S B) s :=
  F.val.map_smul (firstOrderThickeningCrysP₁ S B).op b s

/-- Restriction along the diagonal `i : T ⟶ T'` is semilinear over the map of section rings. -/
theorem restrict_ι_smul (t : crysSheafRing S (firstOrderThickeningObject S B.obj))
    (x : F.val.obj (op (firstOrderThickeningCrysObject S B))) :
    crysSiteRestrict F (firstOrderThickeningCrysι S B) (t • x) =
      crysSheafRingMap (firstOrderThickeningSiteι S B.obj) t •
        crysSiteRestrict F (firstOrderThickeningCrysι S B) x :=
  F.val.map_smul (firstOrderThickeningCrysι S B).op t x

/-- Restriction along `q₀ : T'' ⟶ T` is semilinear over the map of section rings. -/
theorem restrict_q₀_smul (b : crysSheafRing S B.obj) (s : F.val.obj (op B)) :
    crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) (b • s) =
      crysSheafRingMap (secondOrderThickeningSiteQ₀ S B.obj) b •
        crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) s :=
  F.val.map_smul (secondOrderThickeningCrysQ₀ S B).op b s

/-- Restriction along `q₀₁ : T'' ⟶ T'` is semilinear over the map of section rings. -/
theorem restrict_q₀₁_smul (t : crysSheafRing S (firstOrderThickeningObject S B.obj))
    (x : F.val.obj (op (firstOrderThickeningCrysObject S B))) :
    crysSiteRestrict F (secondOrderThickeningCrysQ₀₁ S B) (t • x) =
      crysSheafRingMap (secondOrderThickeningSiteQ₀₁ S B.obj) t •
        crysSiteRestrict F (secondOrderThickeningCrysQ₀₁ S B) x :=
  F.val.map_smul (secondOrderThickeningCrysQ₀₁ S B).op t x

/-- Restriction along `q₁₂ : T'' ⟶ T'` is semilinear over the map of section rings. -/
theorem restrict_q₁₂_smul (t : crysSheafRing S (firstOrderThickeningObject S B.obj))
    (x : F.val.obj (op (firstOrderThickeningCrysObject S B))) :
    crysSiteRestrict F (secondOrderThickeningCrysQ₁₂ S B) (t • x) =
      crysSheafRingMap (secondOrderThickeningSiteQ₁₂ S B.obj) t •
        crysSiteRestrict F (secondOrderThickeningCrysQ₁₂ S B) x :=
  F.val.map_smul (secondOrderThickeningCrysQ₁₂ S B).op t x

/-- Restriction along `q₀₂ : T'' ⟶ T'` is semilinear over the map of section rings. -/
theorem restrict_q₀₂_smul (t : crysSheafRing S (firstOrderThickeningObject S B.obj))
    (x : F.val.obj (op (firstOrderThickeningCrysObject S B))) :
    crysSiteRestrict F (secondOrderThickeningCrysQ₀₂ S B) (t • x) =
      crysSheafRingMap (secondOrderThickeningSiteQ₀₂ S B.obj) t •
        crysSiteRestrict F (secondOrderThickeningCrysQ₀₂ S B) x :=
  F.val.map_smul (secondOrderThickeningCrysQ₀₂ S B).op t x

/-- Restriction along a morphism of `Cris(X/S)` carries zero to zero. -/
theorem restrict_zero {C D : CrystallineThickening S} (g : C ⟶ D) :
    crysSiteRestrict F g 0 = 0 :=
  map_zero _

/-- Restriction along a morphism of `Cris(X/S)` is compatible with subtraction. -/
theorem restrict_sub {C D : CrystallineThickening S} (g : C ⟶ D) (s t : F.val.obj (op D)) :
    crysSiteRestrict F g (s - t) = crysSiteRestrict F g s - crysSiteRestrict F g t :=
  map_sub _ s t

/-! ### The difference of the two restrictions -/

/-- **The difference `p₁^* s - p₀^* s` of the restrictions of a section along the two projections
of the first-order universal thickening** of [Stacks, Tag 07J2]: the recipe of the canonical
connection of [Stacks, Tag 07J6], before its value is read inside `Ω ⊗_D Mod`. -/
def connectionDifference :
    F.val.obj (op B) →+ F.val.obj (op (firstOrderThickeningCrysObject S B)) :=
  AddMonoidHom.mk'
    (fun s ↦ crysSiteRestrict F (firstOrderThickeningCrysP₁ S B) s -
      crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s)
    (fun s t ↦ by
      rw [crysSiteRestrict_add, crysSiteRestrict_add]
      abel)

/-- The value of `connectionDifference`. -/
theorem connectionDifference_apply (s : F.val.obj (op B)) :
    connectionDifference F B s =
      crysSiteRestrict F (firstOrderThickeningCrysP₁ S B) s -
        crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s := rfl

/-- **Restricting the difference along a morphism into the first-order thickening** reads its two
terms along the two composites. -/
theorem restrict_connectionDifference {C : CrystallineThickening S}
    (g : C ⟶ firstOrderThickeningCrysObject S B) (g₀ g₁ : C ⟶ B)
    (h₀ : g ≫ firstOrderThickeningCrysP₀ S B = g₀)
    (h₁ : g ≫ firstOrderThickeningCrysP₁ S B = g₁) (s : F.val.obj (op B)) :
    crysSiteRestrict F g (connectionDifference F B s) =
      crysSiteRestrict F g₁ s - crysSiteRestrict F g₀ s := by
  rw [connectionDifference_apply, restrict_sub, crysSiteRestrict_comp, crysSiteRestrict_comp, h₀,
    h₁]

/-- **The difference lies in the ideal of the diagonal**: both projections retract the diagonal
`i : T ⟶ T'`. -/
theorem restrict_ι_connectionDifference (s : F.val.obj (op B)) :
    crysSiteRestrict F (firstOrderThickeningCrysι S B) (connectionDifference F B s) = 0 := by
  rw [restrict_connectionDifference F B _ (𝟙 B) (𝟙 B)
    (firstOrderThickeningCrysι_comp_P₀ S B) (firstOrderThickeningCrysι_comp_P₁ S B), sub_self]

/-- **The Leibniz rule for the difference**: `∇(b s) = p₁(b) ∇(s) + d b · p₀^* s`, with the
differential read as a section of `𝒪_{T'}` through the square-zero summand. -/
theorem connectionDifference_smul (b : crysSheafRing S B.obj) (s : F.val.obj (op B)) :
    connectionDifference F B (b • s) =
      crysSheafRingMap (firstOrderThickeningSiteP₁ S B.obj) b • connectionDifference F B s +
        firstOrderThickeningDiffSection B.obj (crysDerivation B.obj b) •
          crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s := by
  rw [connectionDifference_apply, connectionDifference_apply, restrict_p₁_smul, restrict_p₀_smul,
    smul_sub, crysDerivation, ← crysSheafRingMap_siteP₁_sub_siteP₀, sub_smul]
  abel

/-! ### The canonical map `Ω ⊗_D Mod ⟶ ℱ(U, T', δ')` -/

/-- The bilinear datum of `diffAction`. -/
def diffActionAux :
    crysDiffSections B.obj →+
      (F.val.obj (op B) →+ F.val.obj (op (firstOrderThickeningCrysObject S B))) :=
  AddMonoidHom.mk'
    (fun ω ↦ AddMonoidHom.mk'
      (fun s ↦ firstOrderThickeningDiffSection B.obj ω •
        crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s)
      (fun s t ↦ by rw [crysSiteRestrict_add, smul_add]))
    (fun ω ω' ↦ by
      ext s
      change firstOrderThickeningDiffSection B.obj (ω + ω') •
          crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s =
        firstOrderThickeningDiffSection B.obj ω •
            crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s +
          firstOrderThickeningDiffSection B.obj ω' •
            crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s
      rw [firstOrderThickeningDiffSection_add, add_smul])

/-- **The canonical map `Ω ⊗_D Mod ⟶ ℱ(U, T', δ')` of [Stacks, Tag 07J6]**, `ω ⊗ s ↦ ω · p₀^* s`,
the differential being read as a section of `𝒪_{T'}` through the square-zero summand of
[Stacks, Tag 07J2]. -/
def diffAction :
    crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) →+
      F.val.obj (op (firstOrderThickeningCrysObject S B)) :=
  TensorProduct.liftAddHom (diffActionAux F B) (fun b ω s ↦ by
    change firstOrderThickeningDiffSection B.obj (b • ω) •
        crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s =
      firstOrderThickeningDiffSection B.obj ω •
        crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) (b • s)
    rw [restrict_p₀_smul, smul_smul, diffSection_mul_crysSheafRingMap_siteP₀])

/-- The canonical map on a pure tensor: `ω ⊗ s ↦ ω · p₀^* s`. -/
@[simp]
theorem diffAction_tmul (ω : crysDiffSections B.obj) (s : F.val.obj (op B)) :
    diffAction F B (ω ⊗ₜ[crysSheafRing S B.obj] s) =
      firstOrderThickeningDiffSection B.obj ω •
        crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s :=
  TensorProduct.liftAddHom_tmul _ _ ω s

/-- The canonical map lands in the ideal of the diagonal. -/
theorem restrict_ι_diffAction
    (z : crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    crysSiteRestrict F (firstOrderThickeningCrysι S B) (diffAction F B z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul ω s => rw [diffAction_tmul, restrict_ι_smul, crysSheafRingMap_siteι_diffSection, zero_smul]
  | add x y hx hy => rw [map_add, crysSiteRestrict_add, hx, hy, add_zero]

/-- The canonical map is semilinear over `p₀`. -/
theorem diffAction_smul (b : crysSheafRing S B.obj)
    (z : crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    diffAction F B (b • z) =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S B.obj) b • diffAction F B z := by
  induction z using TensorProduct.inductionOn with
  | tmul ω s =>
      rw [TensorProduct.smul_tmul', diffAction_tmul, diffAction_tmul, smul_smul,
        crysSheafRingMap_siteP₀_mul_diffSection]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- A differential annihilates the image of the canonical map, the summand of differentials being
of square zero. -/
theorem diffSection_smul_diffAction (ω : crysDiffSections B.obj)
    (z : crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    firstOrderThickeningDiffSection B.obj ω • diffAction F B z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul ω' s =>
      rw [diffAction_tmul, smul_smul, firstOrderThickeningDiffSection_mul, zero_smul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

/-! ### The splitting of the base change along `p₀` -/

/-- The reading of the summand `Ω` of `D' = D ⊕ Ω` inside the base change `D' ⊗_D Mod`. -/
def diffTensorMap :
    crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) →ₗ[crysSheafRing S B.obj]
      crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) :=
  TensorProduct.map (firstOrderDiffSectionLinear B.obj) LinearMap.id

/-- `diffTensorMap` on a pure tensor. -/
@[simp]
theorem diffTensorMap_tmul (ω : crysDiffSections B.obj) (s : F.val.obj (op B)) :
    diffTensorMap F B (ω ⊗ₜ[crysSheafRing S B.obj] s) =
      firstOrderThickeningDiffSection B.obj ω ⊗ₜ[crysSheafRing S B.obj] s :=
  TensorProduct.map_tmul _ _ ω s

/-- **The two components of the splitting `D' ⊗_D Mod ≅ Mod × (Ω ⊗_D Mod)`** induced by
`D' = D ⊕ Ω`: `t ⊗ s ↦ (i^*(t) · s, dpart(t) ⊗ s)`. -/
def splitInv :
    crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) →ₗ[crysSheafRing S B.obj]
      F.val.obj (op B) × (crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :=
  LinearMap.prod
    ((TensorProduct.lid (crysSheafRing S B.obj) (F.val.obj (op B))).toLinearMap ∘ₗ
      TensorProduct.map (crysSheafRingMapSiteιLinear B.obj) LinearMap.id)
    (TensorProduct.map (crysDiffPartLinear B.obj) LinearMap.id)

/-- The two components of a pure tensor `t ⊗ s` of `D' ⊗_D Mod`. -/
@[simp]
theorem splitInv_tmul (t : crysSheafRing S (firstOrderThickeningObject S B.obj))
    (s : F.val.obj (op B)) :
    splitInv F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      (crysSheafRingMap (firstOrderThickeningSiteι S B.obj) t • s,
        crysDiffPart B.obj t ⊗ₜ[crysSheafRing S B.obj] s) := by
  refine Prod.ext ?_ ?_ <;>
    simp [splitInv, crysSheafRingMapSiteιLinear, crysDiffPartLinear]

/-- The splitting undoes the summand of differentials. -/
theorem splitInv_diffTensorMap
    (z : crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    splitInv F B (diffTensorMap F B z) = (0, z) := by
  induction z using TensorProduct.inductionOn with
  | tmul ω s =>
      rw [diffTensorMap_tmul, splitInv_tmul, crysSheafRingMap_siteι_diffSection,
        crysDiffPart_diffSection, zero_smul]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', Prod.mk_add_mk, add_zero]

/-- **The splitting recombines**: every element of `D' ⊗_D Mod` is `1 ⊗ s + z` for its two
components. -/
theorem one_tmul_splitInv_add_diffTensorMap
    (x : crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
      F.val.obj (op B)) :
    (1 : crysSheafRing S (firstOrderThickeningObject S B.obj)) ⊗ₜ[crysSheafRing S B.obj]
        (splitInv F B x).1 + diffTensorMap F B (splitInv F B x).2 = x := by
  induction x using TensorProduct.inductionOn with
  | tmul t s =>
      rw [splitInv_tmul, diffTensorMap_tmul, ← TensorProduct.smul_tmul, crysSheafRing_smul_def,
        mul_one, ← TensorProduct.add_tmul, siteP₀_siteι_add_diffSection]
  | add x y hx hy =>
      rw [map_add, Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add, map_add]
      nth_rewrite 3 [← hx]
      nth_rewrite 3 [← hy]
      abel

/-- On the summand of differentials the base change along `p₀` is the canonical map. -/
theorem crysExtensionSectionsMap_diffTensorMap
    (z : crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    crysExtensionSectionsMap F B (diffTensorMap F B z) = diffAction F B z := by
  induction z using TensorProduct.inductionOn with
  | tmul ω s =>
      rw [diffTensorMap_tmul, crysExtensionSectionsMap_tmul, diffAction_tmul]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

/-- On the unit summand the base change along `p₀` is the restriction along `p₀`. -/
theorem crysExtensionSectionsMap_one_tmul (s : F.val.obj (op B)) :
    crysExtensionSectionsMap F B
        ((1 : crysSheafRing S (firstOrderThickeningObject S B.obj)) ⊗ₜ[crysSheafRing S B.obj] s) =
      crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s := by
  rw [crysExtensionSectionsMap_tmul, one_smul]

/-- Restriction along the diagonal of the base change recovers the first component. -/
theorem restrict_ι_crysExtensionSectionsMap
    (x : crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
      F.val.obj (op B)) :
    crysSiteRestrict F (firstOrderThickeningCrysι S B) (crysExtensionSectionsMap F B x) =
      (splitInv F B x).1 := by
  induction x using TensorProduct.inductionOn with
  | tmul t s =>
      rw [crysExtensionSectionsMap_tmul, splitInv_tmul, restrict_ι_smul, crysSiteRestrict_comp,
        firstOrderThickeningCrysι_comp_P₀, crysSiteRestrict_id]
  | add x y hx hy => rw [map_add, crysSiteRestrict_add, hx, hy, map_add, Prod.fst_add]

/-! ### The canonical connection -/

section Connection

variable {F B} (he : Function.Bijective (crysExtensionSectionsMap F B))

/-- The base change along `p₀`, as an additive equivalence. -/
def extensionEquiv :
    crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) ≃+ F.val.obj (op (firstOrderThickeningCrysObject S B)) :=
  AddEquiv.ofBijective (crysExtensionSectionsMap F B) he

/-- **The inverse of the canonical map on the ideal of the diagonal**: the second component of
the preimage under the base change along `p₀`. -/
def proj :
    F.val.obj (op (firstOrderThickeningCrysObject S B)) →+
      crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) :=
  (AddMonoidHom.snd _ _).comp
    ((splitInv F B).toAddMonoidHom.comp (extensionEquiv he).symm.toAddMonoidHom)

/-- The value of `proj`. -/
theorem proj_apply (t : F.val.obj (op (firstOrderThickeningCrysObject S B))) :
    proj he t = (splitInv F B ((extensionEquiv he).symm t)).2 := rfl

/-- The projection is a left inverse of the canonical map. -/
theorem proj_diffAction
    (z : crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    proj he (diffAction F B z) = z := by
  have h : (extensionEquiv he) (diffTensorMap F B z) = diffAction F B z :=
    crysExtensionSectionsMap_diffTensorMap F B z
  rw [proj_apply, ← h, AddEquiv.symm_apply_apply, splitInv_diffTensorMap]

/-- The projection is a right inverse of the canonical map on the ideal of the diagonal. -/
theorem diffAction_proj (t : F.val.obj (op (firstOrderThickeningCrysObject S B)))
    (ht : crysSiteRestrict F (firstOrderThickeningCrysι S B) t = 0) :
    diffAction F B (proj he t) = t := by
  set x := (extensionEquiv he).symm t with hx
  have hxt : crysExtensionSectionsMap F B x = t := (extensionEquiv he).apply_symm_apply t
  have h1 : (splitInv F B x).1 = 0 := by
    rw [← restrict_ι_crysExtensionSectionsMap, hxt, ht]
  have hsplit := one_tmul_splitInv_add_diffTensorMap F B x
  rw [h1, TensorProduct.tmul_zero, zero_add] at hsplit
  rw [proj_apply, ← hx, ← crysExtensionSectionsMap_diffTensorMap, hsplit, hxt]

include he in
/-- The canonical map is injective. -/
theorem injective_diffAction : Function.Injective (diffAction F B) :=
  Function.LeftInverse.injective (proj_diffAction he)

/-- **Stacks Project, Lemma 60.15.1, Tag 07J6, on global sections over an object.**  The canonical
connection

`∇ : ℱ(U, T, δ) ⟶ Γ(T, Ω_{T/S,δ}) ⊗_{Γ(T, 𝒪_T)} ℱ(U, T, δ)`,

the difference `p₁^* s - p₀^* s` of the restrictions along the two projections of the first-order
universal thickening, read inside `Ω ⊗_D Mod` through the inverse of the canonical map on the ideal
of the diagonal.  The bijectivity `he` of the base change along `p₀` is a theorem for a crystal
in quasi-coherent modules over an object with affine ambient scheme. -/
def connection :
    F.val.obj (op B) →+ crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) :=
  (proj he).comp (connectionDifference F B)

/-- The value of the connection: the projection of `p₁^* s - p₀^* s`. -/
theorem connection_apply (s : F.val.obj (op B)) :
    connection he s = proj he (connectionDifference F B s) := rfl

/-- **The connection is the recipe of [Stacks, Tag 07J6]**: the canonical map carries `∇(s)` back
to `p₁^* s - p₀^* s`. -/
theorem diffAction_connection (s : F.val.obj (op B)) :
    diffAction F B (connection he s) = connectionDifference F B s :=
  diffAction_proj he _ (restrict_ι_connectionDifference F B s)

/-- **The Leibniz rule of [Stacks, Tag 07J6]**, `∇(b s) = b ∇(s) + d b ⊗ s`. -/
theorem connection_smul (b : crysSheafRing S B.obj) (s : F.val.obj (op B)) :
    connection he (b • s) =
      b • connection he s + crysDerivation B.obj b ⊗ₜ[crysSheafRing S B.obj] s := by
  refine injective_diffAction he ?_
  rw [diffAction_connection, map_add, diffAction_smul, diffAction_connection, diffAction_tmul,
    connectionDifference_smul]
  refine congrArg (fun x ↦ x + firstOrderThickeningDiffSection B.obj (crysDerivation B.obj b) •
      crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s) ?_
  rw [crysSheafRingMap_siteP₁_eq, add_smul, ← diffAction_connection he s,
    diffSection_smul_diffAction, add_zero]

end Connection

/-! ### The degree-two canonical map -/

/-- The bilinear datum of `diffAction₂`. -/
def diffAction₂Aux :
    crysSecondFormSections B.obj →+
      (F.val.obj (op B) →+ F.val.obj (op (secondOrderThickeningCrysObject S B))) :=
  AddMonoidHom.mk'
    (fun η ↦ AddMonoidHom.mk'
      (fun s ↦ secondOrderTopSection B.obj η •
        crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) s)
      (fun s t ↦ by rw [crysSiteRestrict_add, smul_add]))
    (fun η η' ↦ by
      ext s
      change secondOrderTopSection B.obj (η + η') •
          crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) s =
        secondOrderTopSection B.obj η •
            crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) s +
          secondOrderTopSection B.obj η' •
            crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) s
      rw [secondOrderTopSection_add, add_smul])

/-- **The degree-two canonical map `Ω² ⊗_D Mod ⟶ ℱ(U, T'', δ'')` of [Stacks, Tag 07J6]**,
`η ⊗ s ↦ η · q₀^* s`, the two-form being read in `𝒪_{T''}` through the top summand of
[Stacks, Tag 07J3].  It is the map through which the source reads the outcome of its
integrability computation inside `Ω² ⊗ ℱ`. -/
def diffAction₂ :
    crysSecondFormSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) →+
      F.val.obj (op (secondOrderThickeningCrysObject S B)) :=
  TensorProduct.liftAddHom (diffAction₂Aux F B) (fun b η s ↦ by
    change secondOrderTopSection B.obj (b • η) •
        crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) s =
      secondOrderTopSection B.obj η •
        crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) (b • s)
    rw [restrict_q₀_smul, smul_smul, secondOrderTopSection_mul_crysSheafRingMap_q₀])

/-- The degree-two canonical map on a pure tensor: `η ⊗ s ↦ η · q₀^* s`. -/
@[simp]
theorem diffAction₂_tmul (η : crysSecondFormSections B.obj) (s : F.val.obj (op B)) :
    diffAction₂ F B (η ⊗ₜ[crysSheafRing S B.obj] s) =
      secondOrderTopSection B.obj η • crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) s :=
  TensorProduct.liftAddHom_tmul _ _ η s

/-- The reading of the top summand `Ω²` of `D''` inside the base change `D'' ⊗_D Mod`. -/
def topTensorMap :
    crysSecondFormSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) →ₗ[
        crysSheafRing S B.obj]
      crysSheafRing S (secondOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) :=
  TensorProduct.map (SecondOrderAffine.topSectionLinear B.obj) LinearMap.id

/-- The top coordinate of the base change `D'' ⊗_D Mod`. -/
def topProj :
    crysSheafRing S (secondOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) →ₗ[crysSheafRing S B.obj]
      crysSecondFormSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) :=
  TensorProduct.map (SecondOrderAffine.topPartLinear B.obj) LinearMap.id

/-- The top coordinate undoes the inclusion of the top summand. -/
theorem topProj_topTensorMap
    (w : crysSecondFormSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    topProj F B (topTensorMap F B w) = w := by
  induction w using TensorProduct.inductionOn with
  | tmul η s => rfl
  | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-- On the top summand the base change along `q₀` is the degree-two canonical map. -/
theorem crysSecondExtensionSectionsMap_topTensorMap
    (w : crysSecondFormSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    crysSecondExtensionSectionsMap F B (topTensorMap F B w) = diffAction₂ F B w := by
  induction w using TensorProduct.inductionOn with
  | tmul η s => rfl
  | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw']

/-- **The degree-two canonical map is injective** as soon as the base change along `q₀` is: it is
that base change restricted to the top summand of the splitting of [Stacks, Tag 07J3]. -/
theorem injective_diffAction₂ (he₂ : Function.Injective (crysSecondExtensionSectionsMap F B)) :
    Function.Injective (diffAction₂ F B) := by
  intro w w' h
  rw [← crysSecondExtensionSectionsMap_topTensorMap, ← crysSecondExtensionSectionsMap_topTensorMap]
    at h
  rw [← topProj_topTensorMap F B w, ← topProj_topTensorMap F B w', he₂ h]

/-! ### Exterior multiplication on the right by a one-form -/

/-- The bilinear datum of `wedgeRight`. -/
def wedgeRightAux (ω : crysDiffSections B.obj) :
    crysDiffSections B.obj →+
      (F.val.obj (op B) →+
        crysSecondFormSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :=
  AddMonoidHom.mk'
    (fun ω' ↦ AddMonoidHom.mk'
      (fun s ↦ crysWedgeSections B.obj ω' ω ⊗ₜ[crysSheafRing S B.obj] s)
      (fun s t ↦ TensorProduct.tmul_add _ _ _))
    (fun ω' ω'' ↦ by
      ext s
      change crysWedgeSections B.obj (ω' + ω'') ω ⊗ₜ[crysSheafRing S B.obj] s =
        crysWedgeSections B.obj ω' ω ⊗ₜ[crysSheafRing S B.obj] s +
          crysWedgeSections B.obj ω'' ω ⊗ₜ[crysSheafRing S B.obj] s
      rw [crysWedgeSections_add_left, TensorProduct.add_tmul])

/-- **Exterior multiplication on the right by a one-form**, `ω' ⊗ s ↦ (ω' ∧ ω) ⊗ s`, the term
`∇(s) ∧ ω` of the extension of a connection of §07J5. -/
def wedgeRight (ω : crysDiffSections B.obj) :
    crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) →+
      crysSecondFormSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) :=
  TensorProduct.liftAddHom (wedgeRightAux F B ω)
    (fun b ω' s ↦ by
      change crysWedgeSections B.obj (b • ω') ω ⊗ₜ[crysSheafRing S B.obj] s =
        crysWedgeSections B.obj ω' ω ⊗ₜ[crysSheafRing S B.obj] (b • s)
      rw [crysWedgeSections_smul_left, TensorProduct.smul_tmul])

/-- Exterior multiplication on the right, on a pure tensor. -/
@[simp]
theorem wedgeRight_tmul (ω ω' : crysDiffSections B.obj) (s : F.val.obj (op B)) :
    wedgeRight F B ω (ω' ⊗ₜ[crysSheafRing S B.obj] s) =
      crysWedgeSections B.obj ω' ω ⊗ₜ[crysSheafRing S B.obj] s :=
  TensorProduct.liftAddHom_tmul _ _ ω' s

/-- Exterior multiplication on the right is linear in the tensor. -/
theorem wedgeRight_smul (ω : crysDiffSections B.obj) (b : crysSheafRing S B.obj)
    (z : crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    wedgeRight F B ω (b • z) = b • wedgeRight F B ω z := by
  induction z using TensorProduct.inductionOn with
  | tmul ω' s =>
      rw [TensorProduct.smul_tmul', wedgeRight_tmul, wedgeRight_tmul,
        crysWedgeSections_smul_left, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- Exterior multiplication on the right is linear in the one-form. -/
theorem wedgeRight_smul_form (ω : crysDiffSections B.obj) (b : crysSheafRing S B.obj)
    (z : crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    wedgeRight F B (b • ω) z = b • wedgeRight F B ω z := by
  induction z using TensorProduct.inductionOn with
  | tmul ω' s =>
      rw [wedgeRight_tmul, wedgeRight_tmul, crysWedgeSections_smul_right,
        TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

/-- Exterior multiplication on the right is additive in the one-form. -/
theorem wedgeRight_add_form (ω ω' : crysDiffSections B.obj)
    (z : crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    wedgeRight F B (ω + ω') z = wedgeRight F B ω z + wedgeRight F B ω' z := by
  induction z using TensorProduct.inductionOn with
  | tmul ω'' s =>
      rw [wedgeRight_tmul, wedgeRight_tmul, wedgeRight_tmul, crysWedgeSections_add_right,
        TensorProduct.add_tmul]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
      abel

/-! ### The curvature identity -/

/-- **The curvature identity on the second-order thickening**:
`q₀₁^* ∇(s) + q₁₂^* ∇(s) = q₀₂^* ∇(s)` for the difference of the two restrictions, by the six
relations of [Stacks, Tag 07J3]. -/
theorem connectionDifference_cocycle (s : F.val.obj (op B)) :
    crysSiteRestrict F (secondOrderThickeningCrysQ₀₁ S B) (connectionDifference F B s) +
        crysSiteRestrict F (secondOrderThickeningCrysQ₁₂ S B) (connectionDifference F B s) =
      crysSiteRestrict F (secondOrderThickeningCrysQ₀₂ S B) (connectionDifference F B s) := by
  rw [restrict_connectionDifference F B (secondOrderThickeningCrysQ₀₁ S B) _ _
      (secondOrderThickeningCrysQ₀₁_comp_P₀ S B) (secondOrderThickeningCrysQ₀₁_comp_P₁ S B),
    restrict_connectionDifference F B (secondOrderThickeningCrysQ₁₂ S B) _ _
      (secondOrderThickeningCrysQ₁₂_comp_P₀ S B) (secondOrderThickeningCrysQ₁₂_comp_P₁ S B),
    restrict_connectionDifference F B (secondOrderThickeningCrysQ₀₂ S B) _ _
      (secondOrderThickeningCrysQ₀₂_comp_P₀ S B) (secondOrderThickeningCrysQ₀₂_comp_P₁ S B)]
  abel

/-- Restricting along `p₀` and then `q₀₁` is restricting along `q₀`. -/
theorem restrict_q₀₁_p₀ (s : F.val.obj (op B)) :
    crysSiteRestrict F (secondOrderThickeningCrysQ₀₁ S B)
        (crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s) =
      crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) s := by
  rw [crysSiteRestrict_comp, secondOrderThickeningCrysQ₀₁_comp_P₀]

/-- Restricting along `p₀` and then `q₁₂` is restricting along `q₁`. -/
theorem restrict_q₁₂_p₀ (s : F.val.obj (op B)) :
    crysSiteRestrict F (secondOrderThickeningCrysQ₁₂ S B)
        (crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s) =
      crysSiteRestrict F (secondOrderThickeningCrysQ₁ S B) s := by
  rw [crysSiteRestrict_comp, secondOrderThickeningCrysQ₁₂_comp_P₀]

/-- Restricting along `p₀` and then `q₀₂` is restricting along `q₀`. -/
theorem restrict_q₀₂_p₀ (s : F.val.obj (op B)) :
    crysSiteRestrict F (secondOrderThickeningCrysQ₀₂ S B)
        (crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) s) =
      crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) s := by
  rw [crysSiteRestrict_comp, secondOrderThickeningCrysQ₀₂_comp_P₀]

/-- Exterior multiplication on the right, read through the two canonical maps. -/
theorem diffAction₂_wedgeRight (ω : crysDiffSections B.obj)
    (z : crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    diffAction₂ F B (wedgeRight F B ω z) =
      crysSheafRingMap (secondOrderThickeningSiteQ₁₂ S B.obj)
          (firstOrderThickeningDiffSection B.obj ω) •
        crysSiteRestrict F (secondOrderThickeningCrysQ₀₁ S B) (diffAction F B z) := by
  induction z using TensorProduct.inductionOn with
  | tmul ω' s =>
      rw [wedgeRight_tmul, diffAction₂_tmul, diffAction_tmul, restrict_q₀₁_smul, smul_smul,
        crysSheafRingMap_q₁₂_mul_q₀₁_diffSection, restrict_q₀₁_p₀]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, crysSiteRestrict_add, smul_add]

/-! ### The degree-one extension of the connection, and integrability -/

section Integrable

variable {F B} (he : Function.Bijective (crysExtensionSectionsMap F B))

/-- The bilinear datum of `extendedConnection`. -/
def extendedConnectionAux :
    crysDiffSections B.obj →+
      (F.val.obj (op B) →+
        crysSecondFormSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :=
  AddMonoidHom.mk'
    (fun ω ↦ AddMonoidHom.mk'
      (fun s ↦ wedgeRight F B ω (connection he s) +
        crysDeRham B.obj ω ⊗ₜ[crysSheafRing S B.obj] s)
      (fun s t ↦ by
        rw [map_add, map_add, TensorProduct.tmul_add]
        abel))
    (fun ω ω' ↦ by
      ext s
      change wedgeRight F B (ω + ω') (connection he s) +
          crysDeRham B.obj (ω + ω') ⊗ₜ[crysSheafRing S B.obj] s =
        wedgeRight F B ω (connection he s) +
            crysDeRham B.obj ω ⊗ₜ[crysSheafRing S B.obj] s +
          (wedgeRight F B ω' (connection he s) +
            crysDeRham B.obj ω' ⊗ₜ[crysSheafRing S B.obj] s)
      rw [wedgeRight_add_form, crysDeRham_add, TensorProduct.add_tmul]
      abel)

/-- **The degree-one extension of the canonical connection, of [Stacks, Section 60.15,
Tag 07J5]**: `Ω ⊗_D Mod ⟶ Ω² ⊗_D Mod`, `ω ⊗ s ↦ ∇(s) ∧ ω + d ω ⊗ s`.  It is well defined on
the tensor product because the Leibniz rules of `∇` and of `d` cancel when a scalar is moved
across the tensor sign. -/
def extendedConnection :
    crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) →+
      crysSecondFormSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B) :=
  TensorProduct.liftAddHom (extendedConnectionAux he)
    (fun b ω s ↦ by
      have hL : wedgeRight F B (b • ω) (connection he s) =
          b • wedgeRight F B ω (connection he s) :=
        wedgeRight_smul_form F B ω b _
      have hD : crysDeRham B.obj (b • ω) ⊗ₜ[crysSheafRing S B.obj] s =
          b • (crysDeRham B.obj ω ⊗ₜ[crysSheafRing S B.obj] s) +
            crysWedgeSections B.obj (crysDerivation B.obj b) ω
              ⊗ₜ[crysSheafRing S B.obj] s := by
        rw [crysDeRham_smul, TensorProduct.add_tmul, TensorProduct.smul_tmul']
        rfl
      have hRW : wedgeRight F B ω (connection he (b • s)) =
          b • wedgeRight F B ω (connection he s) +
            crysWedgeSections B.obj (crysDerivation B.obj b) ω
              ⊗ₜ[crysSheafRing S B.obj] s := by
        rw [connection_smul, map_add, wedgeRight_smul, wedgeRight_tmul]
      have hT : crysDeRham B.obj ω ⊗ₜ[crysSheafRing S B.obj] (b • s) =
          b • (crysDeRham B.obj ω ⊗ₜ[crysSheafRing S B.obj] s) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      change wedgeRight F B (b • ω) (connection he s) +
          crysDeRham B.obj (b • ω) ⊗ₜ[crysSheafRing S B.obj] s =
        wedgeRight F B ω (connection he (b • s)) +
          crysDeRham B.obj ω ⊗ₜ[crysSheafRing S B.obj] (b • s)
      rw [hL, hD, hRW, hT]
      abel)

/-- The degree-one extension on a pure tensor: `ω ⊗ s ↦ ∇(s) ∧ ω + d ω ⊗ s`. -/
@[simp]
theorem extendedConnection_tmul (ω : crysDiffSections B.obj) (s : F.val.obj (op B)) :
    extendedConnection he (ω ⊗ₜ[crysSheafRing S B.obj] s) =
      wedgeRight F B ω (connection he s) + crysDeRham B.obj ω ⊗ₜ[crysSheafRing S B.obj] s :=
  TensorProduct.liftAddHom_tmul _ _ ω s

/-- **The integrability computation of [Stacks, Lemma 60.15.1, Tag 07J6]**: the degree-two
canonical map carries the extension `∇(z)` to the alternating sum of the three restrictions of
the image of `z` under the degree-one canonical map. -/
theorem diffAction₂_extendedConnection
    (z : crysDiffSections B.obj ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    diffAction₂ F B (extendedConnection he z) =
      crysSiteRestrict F (secondOrderThickeningCrysQ₀₁ S B) (diffAction F B z) +
        crysSiteRestrict F (secondOrderThickeningCrysQ₁₂ S B) (diffAction F B z) -
        crysSiteRestrict F (secondOrderThickeningCrysQ₀₂ S B) (diffAction F B z) := by
  induction z using TensorProduct.inductionOn with
  | tmul ω t =>
      rw [extendedConnection_tmul, map_add, diffAction₂_wedgeRight, diffAction_connection,
        restrict_connectionDifference F B (secondOrderThickeningCrysQ₀₁ S B) _ _
          (secondOrderThickeningCrysQ₀₁_comp_P₀ S B) (secondOrderThickeningCrysQ₀₁_comp_P₁ S B) t,
        diffAction₂_tmul, diffAction_tmul, restrict_q₀₁_smul, restrict_q₁₂_smul,
        restrict_q₀₂_smul, restrict_q₀₁_p₀, restrict_q₁₂_p₀, restrict_q₀₂_p₀]
      have key : crysSheafRingMap (secondOrderThickeningSiteQ₀₁ S B.obj)
              (firstOrderThickeningDiffSection B.obj ω) •
            crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) t +
          crysSheafRingMap (secondOrderThickeningSiteQ₁₂ S B.obj)
              (firstOrderThickeningDiffSection B.obj ω) •
            crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) t =
          crysSheafRingMap (secondOrderThickeningSiteQ₀₂ S B.obj)
              (firstOrderThickeningDiffSection B.obj ω) •
            crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) t +
          secondOrderTopSection B.obj (crysDeRham B.obj ω) •
            crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) t := by
        rw [← add_smul, ← add_smul, crysSheafRingMap_q₀₁_add_q₁₂_diffSection]
      set P := crysSiteRestrict F (secondOrderThickeningCrysQ₀ S B) t
      set Q := crysSiteRestrict F (secondOrderThickeningCrysQ₁ S B) t
      set a := crysSheafRingMap (secondOrderThickeningSiteQ₀₁ S B.obj)
        (firstOrderThickeningDiffSection B.obj ω)
      set b := crysSheafRingMap (secondOrderThickeningSiteQ₁₂ S B.obj)
        (firstOrderThickeningDiffSection B.obj ω)
      set c := crysSheafRingMap (secondOrderThickeningSiteQ₀₂ S B.obj)
        (firstOrderThickeningDiffSection B.obj ω)
      set e := secondOrderTopSection B.obj (crysDeRham B.obj ω) • P
      have key' : a • P - c • P = e - b • P :=
        sub_eq_sub_iff_add_eq_add.mpr (key.trans (add_comm _ _))
      rw [smul_sub, show a • P + b • Q - c • P = (a • P - c • P) + b • Q by abel, key']
      abel
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy, crysSiteRestrict_add, crysSiteRestrict_add,
        crysSiteRestrict_add]
      abel

/-- **Integrability of the canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6]**, on global
sections over an object: the connection composes with its own degree-one extension of §07J5 to
zero.  The degree-two canonical map carries the composite to the alternating sum of the three
restrictions of `p₁^* s - p₀^* s` to `(U, T'', δ'')`, which vanishes by the curvature identity, and
that map is injective as soon as the base change along `q₀` is. -/
theorem extendedConnection_connection
    (he₂ : Function.Injective (crysSecondExtensionSectionsMap F B)) (s : F.val.obj (op B)) :
    extendedConnection he (connection he s) = 0 := by
  refine injective_diffAction₂ F B he₂ ?_
  rw [diffAction₂_extendedConnection, diffAction_connection, map_zero, sub_eq_zero]
  exact connectionDifference_cocycle F B s

end Integrable

end Crystalline.GlobalCrystallineSituation.SmallSite.AffineConnection

end

end
