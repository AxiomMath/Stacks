module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineConnectionRing

/-!
# Naturality of the canonical connection of a crystal on `Cris(X/S)`, and of its extensions

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] and a sheaf of
`𝒪_{X/S}`-modules `ℱ` on the small crystalline site `Cris(X/S)`.  Over every affine-over-affine
object `B` of `Cris(X/S)` the canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6] is a
ring-level connection

`∇_B : ℱ(B) ⟶ ℱ(B) ⊗ Ω_{X/S}(B)`

(`...SmallSite.AffineConnection.ringConnection`), and [Stacks, Tag 07I0] extends it to every
degree, `ℱ(B) ⊗ ⋀^i Ω_{X/S}(B) ⟶ ℱ(B) ⊗ ⋀^{i+1} Ω_{X/S}(B)`.  [Stacks, Tag 07J6] says that the
connection "is functorial in `T` because the construction of `T'` is functorial in `T`"; this
module proves exactly that, for the connection and for all its extensions: along a morphism
`k : B ⟶ B'` of `Cris(X/S)` between two such objects, both commute with the transition maps
`m ⊗ ω ↦ k^* m ⊗ k^* ω`.

## The argument

The connection is read back to `p₁^* s - p₀^* s` by the canonical map
`D_B : ℱ(B) ⊗ Ω_{X/S}(B) ⟶ ℱ(U, T', δ')`, which is injective, and `p₁^* s - p₀^* s` is natural
because `T ↦ T'` is functorial (`firstOrderThickeningSiteMap`).  On `m ⊗ c · d b` the canonical
map is `(p₀(c) (p₁(b) - p₀(b))) · p₀^* m`, an expression in the restriction maps of `𝒪_{X/S}`
alone, so it too is natural, and naturality of the connection follows from injectivity of `D_B`.
For the extensions, the descended de Rham differential of [Stacks, Tag 07I0] is the de Rham
differential of `Ω^*_{X/S}` of [Stacks, Tag 07J4] (both are determined by the rule on the
standard generators, `Crystalline.dpConstDeRham_unique`), which is natural, and the rule
`d(m ⊗ ω) = ∇ m ∧ ω + m ⊗ d ω` reduces the claim to naturality of `∇` and of the wedge.

## Main definitions

Everything lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.AffineConnection`.

* `thickeningMap` — the morphism `T'_B ⟶ T'_{B'}` of `Cris(X/S)` induced by `k`.
* `restrictTensor`, `restrictForms` — the transition maps `m ⊗ ω ↦ k^* m ⊗ k^* ω` on
  `ℱ ⊗ Ω_{X/S}` and on `ℱ ⊗ Ω^i_{X/S}`.

## Main results

* `connectionDifference_naturality` — `p₁^* s - p₀^* s` is natural.
* `ringConnection_naturality` — **the canonical connection is natural.**
* `descendedDifferential_ringExtension` — the descended differential of [Stacks, Tag 07I0] is the
  de Rham differential of `Ω^*_{X/S}`.
* `extDiff_naturality` — **the extensions of the connection are natural.**

## References

* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct
open Stacks.DeRham.DifferentialDescent

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.AffineConnection

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))
  {B B' : CrystallineThickening S}

/-! ### The functoriality of the first-order thickening, in `Cris(X/S)` -/

/-- **The morphism `T'_B ⟶ T'_{B'}` of `Cris(X/S)` induced by a morphism `k : B ⟶ B'`**, the
functoriality of the first-order universal thickening of [Stacks, Tag 07J2]. -/
def thickeningMap (k : B ⟶ B') :
    firstOrderThickeningCrysObject S B ⟶ firstOrderThickeningCrysObject S B' :=
  ObjectProperty.homMk (firstOrderThickeningSiteMap k.hom)

/-- The functoriality of `T ↦ T'` commutes with the first projections. -/
theorem thickeningMap_comp_p₀ (k : B ⟶ B') :
    thickeningMap k ≫ firstOrderThickeningCrysP₀ S B' = firstOrderThickeningCrysP₀ S B ≫ k :=
  ObjectProperty.hom_ext _ (firstOrderThickeningSiteMap_comp_P₀ k.hom)

/-- The functoriality of `T ↦ T'` commutes with the second projections. -/
theorem thickeningMap_comp_p₁ (k : B ⟶ B') :
    thickeningMap k ≫ firstOrderThickeningCrysP₁ S B' = firstOrderThickeningCrysP₁ S B ≫ k :=
  ObjectProperty.hom_ext _ (firstOrderThickeningSiteMap_comp_P₁ k.hom)

/-- **The difference `p₁^* s - p₀^* s` is natural**: both of its terms are restrictions along
morphisms of `Cris(X/S)`, and the functoriality of `T ↦ T'` identifies the composites. -/
theorem connectionDifference_naturality (k : B ⟶ B') (s : F.val.obj (op B')) :
    crysSiteRestrict F (thickeningMap k) (connectionDifference F B' s) =
      connectionDifference F B (crysSiteRestrict F k s) := by
  rw [restrict_connectionDifference F B' (thickeningMap k) _ _ (thickeningMap_comp_p₀ k)
    (thickeningMap_comp_p₁ k), connectionDifference_apply, crysSiteRestrict_comp,
    crysSiteRestrict_comp]

/-- Restriction of `𝒪_{X/S}` along two equal composites of morphisms of `CRIS(X/S)`. -/
private theorem crysSheafRingMap_comm_of_comp_eq {A C D E : Thickening S}
    (f : A ⟶ C) (g : C ⟶ E) (f' : A ⟶ D) (g' : D ⟶ E) (h : f ≫ g = f' ≫ g')
    (x : crysSheafRing S E) :
    crysSheafRingMap f (crysSheafRingMap g x) = crysSheafRingMap f' (crysSheafRingMap g' x) := by
  rw [crysSheafRingMap_comp, h, ← crysSheafRingMap_comp]

/-- The ring maps of `T'_B ⟶ T'_{B'}` and of the first projections commute. -/
theorem crysSheafRingMap_thickeningMap_p₀ (k : B ⟶ B') (c : crysSheafRing S B'.obj) :
    crysSheafRingMap (thickeningMap k).hom
        (crysSheafRingMap (firstOrderThickeningSiteP₀ S B'.obj) c) =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S B.obj) (crysSheafRingMap k.hom c) :=
  crysSheafRingMap_comm_of_comp_eq _ _ _ _ (firstOrderThickeningSiteMap_comp_P₀ k.hom) c

/-- The ring maps of `T'_B ⟶ T'_{B'}` and of the second projections commute. -/
theorem crysSheafRingMap_thickeningMap_p₁ (k : B ⟶ B') (c : crysSheafRing S B'.obj) :
    crysSheafRingMap (thickeningMap k).hom
        (crysSheafRingMap (firstOrderThickeningSiteP₁ S B'.obj) c) =
      crysSheafRingMap (firstOrderThickeningSiteP₁ S B.obj) (crysSheafRingMap k.hom c) :=
  crysSheafRingMap_comm_of_comp_eq _ _ _ _ (firstOrderThickeningSiteMap_comp_P₁ k.hom) c

/-! ### The transition maps of `ℱ ⊗ Ω_{X/S}` and of `ℱ ⊗ Ω^i_{X/S}` -/

/-- The transition map of `Ω_{X/S}` along `k`, on sections. -/
abbrev restrictOmega (k : B ⟶ B')
    (η : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj))) :
    ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) :=
  (GlobalCrystallineSituation.crysDifferentials S).map k.hom.op η

/-- The transition map of `Ω_{X/S}` is semilinear. -/
theorem restrictOmega_smul (k : B ⟶ B') (c : GlobalCrystallineSituation.crysFormRing S B'.obj)
    (η : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj))) :
    restrictOmega k (c • η) = crysRingMap S k.hom c • restrictOmega k η :=
  PresheafOfModules.map_smul (GlobalCrystallineSituation.crysDifferentials S) (Quiver.Hom.op k.hom)
    c η

/-- The transition map of `Ω_{X/S}` is additive. -/
theorem restrictOmega_add (k : B ⟶ B')
    (η η' : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj))) :
    restrictOmega k (η + η') = restrictOmega k η + restrictOmega k η' :=
  map_add _ η η'

/-- The transition map of `Ω_{X/S}` carries `d b` to `d (k^* b)`. -/
theorem restrictOmega_crysD (k : B ⟶ B') (b : GlobalCrystallineSituation.crysFormRing S B'.obj) :
    restrictOmega k (GlobalCrystallineSituation.crysD S B'.obj b) =
      GlobalCrystallineSituation.crysD S B.obj (crysRingMap S k.hom b) :=
  crysD_map S k.hom b

/-- Restriction along `k` is semilinear, with the scalars in the `crysFormRing` spelling. -/
theorem crysSiteRestrict_smul' (k : B ⟶ B') (c : GlobalCrystallineSituation.crysFormRing S B'.obj)
    (m : F.val.obj (op B')) :
    crysSiteRestrict F k (c • m) = crysRingMap S k.hom c • crysSiteRestrict F k m :=
  crysSiteRestrict_smul F k c m

/-- The bilinear datum of `restrictTensor`. -/
def restrictTensorAux (k : B ⟶ B') :
    F.val.obj (op B') →+
      (↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj)) →+
        F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :=
  AddMonoidHom.mk'
    (fun m ↦ AddMonoidHom.mk'
      (fun η ↦ crysSiteRestrict F k m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        restrictOmega k η)
      (fun η η' ↦ by rw [restrictOmega_add, TensorProduct.tmul_add]))
    (fun m m' ↦ AddMonoidHom.ext fun η ↦ by
      change crysSiteRestrict F k (m + m') ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
          restrictOmega k η =
        crysSiteRestrict F k m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
            restrictOmega k η +
          crysSiteRestrict F k m' ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
            restrictOmega k η
      rw [crysSiteRestrict_add, TensorProduct.add_tmul])

/-- **The transition map of `ℱ ⊗ Ω_{X/S}` along `k`**, `m ⊗ η ↦ k^* m ⊗ k^* η`. -/
def restrictTensor (k : B ⟶ B') :
    F.val.obj (op B') ⊗[GlobalCrystallineSituation.crysFormRing S B'.obj]
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj)) →+
      F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) :=
  TensorProduct.liftAddHom (restrictTensorAux F k) (fun c m η ↦ by
    change crysSiteRestrict F k (c • m) ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        restrictOmega k η =
      crysSiteRestrict F k m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        restrictOmega k (c • η)
    rw [crysSiteRestrict_smul', restrictOmega_smul, TensorProduct.smul_tmul])

/-- The transition map of `ℱ ⊗ Ω_{X/S}` on a pure tensor. -/
@[simp]
theorem restrictTensor_tmul (k : B ⟶ B') (m : F.val.obj (op B'))
    (η : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj))) :
    restrictTensor F k (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B'.obj] η) =
      crysSiteRestrict F k m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        restrictOmega k η :=
  TensorProduct.liftAddHom_tmul _ _ m η

/-- Restriction along `T'_B ⟶ T'_{B'}` is semilinear. -/
theorem restrict_thickeningMap_smul (k : B ⟶ B')
    (t : crysSheafRing S (firstOrderThickeningObject S B'.obj))
    (x : F.val.obj (op (firstOrderThickeningCrysObject S B'))) :
    crysSiteRestrict F (thickeningMap k) (t • x) =
      crysSheafRingMap (thickeningMap k).hom t • crysSiteRestrict F (thickeningMap k) x :=
  F.val.map_smul (thickeningMap k).op t x

/-- The two spellings of the map of section rings along `k` agree. -/
theorem crysRingMap_eq_crysSheafRingMap (k : B ⟶ B')
    (c : GlobalCrystallineSituation.crysFormRing S B'.obj) :
    crysRingMap S k.hom c = crysSheafRingMap k.hom c := rfl

/-! ### Naturality of the connection -/

section Connection

variable {F}

section ReadBack

variable [IsAffine B.obj.thickening.target.scheme] {V : S.S.scheme.Opens}
  (hVB : (⊤ : B.obj.thickening.target.scheme.Opens) ≤ B.obj.toBase.hom ⁻¹ᵁ V)
  (hV : IsAffineOpen V)

variable (F) in
/-- **The canonical map of [Stacks, Tag 07J6], read on `ℱ(B) ⊗ Ω_{X/S}(B)`**: `m ⊗ η ↦ η · p₀^* m`,
the one-form being read in `𝒪_{T'}` through its square-zero summand. -/
def readBack :
    F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) →+
      F.val.obj (op (firstOrderThickeningCrysObject S B)) :=
  (diffAction F B).comp (tensorFlipAdd F B hVB hV).symm.toAddMonoidHom

/-- The canonical map read on `ℱ(B) ⊗ Ω_{X/S}(B)` is injective. -/
theorem injective_readBack (he : Function.Bijective (crysExtensionSectionsMap F B)) :
    Function.Injective (readBack F hVB hV) :=
  (injective_diffAction he).comp (tensorFlipAdd F B hVB hV).symm.injective

/-- The canonical map reads the connection back to `p₁^* s - p₀^* s`. -/
theorem readBack_ringConnection (he : Function.Bijective (crysExtensionSectionsMap F B))
    (s : F.val.obj (op B)) :
    readBack F hVB hV (ringConnection hVB hV he s) = connectionDifference F B s := by
  change diffAction F B ((tensorFlipAdd F B hVB hV).symm
    (tensorFlipAdd F B hVB hV (connection he s))) = _
  rw [AddEquiv.symm_apply_apply, diffAction_connection]

/-- **The canonical map on `m ⊗ c · d b`** is `(p₀(c) (p₁(b) - p₀(b))) · p₀^* m`, an expression in
the restriction maps of `𝒪_{X/S}` alone. -/
theorem readBack_tmul_smul_crysD (m : F.val.obj (op B))
    (c b : GlobalCrystallineSituation.crysFormRing S B.obj) :
    readBack F hVB hV (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        (c • GlobalCrystallineSituation.crysD S B.obj b)) =
      (crysSheafRingMap (firstOrderThickeningSiteP₀ S B.obj) c *
          (crysSheafRingMap (firstOrderThickeningSiteP₁ S B.obj) b -
            crysSheafRingMap (firstOrderThickeningSiteP₀ S B.obj) b)) •
        crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) m := by
  change diffAction F B ((tensorFlipAdd F B hVB hV).symm
    (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
      (c • GlobalCrystallineSituation.crysD S B.obj b))) = _
  rw [tensorFlipAdd_symm_tmul, LinearEquiv.map_smul, affineCrysOmegaEquiv_symm_crysD,
    diffAction_tmul]
  refine congrArg (· • crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) m) ?_
  exact (crysSheafRingMap_siteP₀_mul_diffSection B.obj c _).symm.trans
    (congrArg _ (crysSheafRingMap_siteP₁_sub_siteP₀ B.obj b).symm)

end ReadBack

variable [IsAffine B.obj.thickening.target.scheme] {V : S.S.scheme.Opens}
  (hVB : (⊤ : B.obj.thickening.target.scheme.Opens) ≤ B.obj.toBase.hom ⁻¹ᵁ V)
  (hV : IsAffineOpen V)
  [IsAffine B'.obj.thickening.target.scheme] {V' : S.S.scheme.Opens}
  (hVB' : (⊤ : B'.obj.thickening.target.scheme.Opens) ≤ B'.obj.toBase.hom ⁻¹ᵁ V')
  (hV' : IsAffineOpen V')

/-- **The canonical map is natural**: it commutes with the transition maps of `ℱ ⊗ Ω_{X/S}` and of
`ℱ` over the first-order thickenings. -/
theorem readBack_restrictTensor (k : B ⟶ B')
    (z : F.val.obj (op B') ⊗[GlobalCrystallineSituation.crysFormRing S B'.obj]
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj))) :
    readBack F hVB hV (restrictTensor F k z) =
      crysSiteRestrict F (thickeningMap k) (readBack F hVB' hV' z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, crysSiteRestrict_add]
  | tmul m η =>
      have key : ∀ η ∈ Submodule.span (GlobalCrystallineSituation.crysFormRing S B'.obj)
          (Set.range (GlobalCrystallineSituation.crysD S B'.obj)),
          ∀ c : GlobalCrystallineSituation.crysFormRing S B'.obj,
            readBack F hVB hV (restrictTensor F k
                (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B'.obj] (c • η))) =
              crysSiteRestrict F (thickeningMap k) (readBack F hVB' hV'
                (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B'.obj] (c • η))) := by
        intro η hη
        induction hη using Submodule.span_induction with
        | mem z hz =>
            obtain ⟨b, rfl⟩ := hz
            intro c
            have hc : crysSiteRestrict F (thickeningMap k)
                (crysSiteRestrict F (firstOrderThickeningCrysP₀ S B') m) =
                crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) (crysSiteRestrict F k m) := by
              rw [crysSiteRestrict_comp, crysSiteRestrict_comp, thickeningMap_comp_p₀]
            rw [restrictTensor_tmul, restrictOmega_smul, restrictOmega_crysD,
              readBack_tmul_smul_crysD, readBack_tmul_smul_crysD, restrict_thickeningMap_smul, hc]
            refine congrArg (· • crysSiteRestrict F (firstOrderThickeningCrysP₀ S B)
              (crysSiteRestrict F k m)) ?_
            exact ((map_mul _ _ _).trans (congrArg₂ (· * ·)
              (crysSheafRingMap_thickeningMap_p₀ k c)
              ((map_sub _ _ _).trans (congrArg₂ (· - ·) (crysSheafRingMap_thickeningMap_p₁ k b)
                (crysSheafRingMap_thickeningMap_p₀ k b))))).symm
        | zero =>
            intro c
            rw [smul_zero, TensorProduct.tmul_zero, map_zero, map_zero, map_zero, restrict_zero]
        | add x y _ _ hx hy =>
            intro c
            rw [smul_add, TensorProduct.tmul_add, map_add, map_add, hx c, hy c, map_add,
              crysSiteRestrict_add]
        | smul a x _ hx =>
            intro c
            rw [smul_smul]
            exact hx (c * a)
      have h := key η (by rw [crysD_span]; exact Submodule.mem_top) 1
      rwa [one_smul] at h

/-- **Naturality of the canonical connection of [Stacks, Tag 07J6]**: along a morphism `k` of
`Cris(X/S)` between two affine-over-affine objects, `∇(k^* s) = k^* ∇(s)`.  The canonical map reads
both sides back to `p₁^* (k^* s) - p₀^* (k^* s)`, and it is injective. -/
theorem ringConnection_naturality (he : Function.Bijective (crysExtensionSectionsMap F B))
    (he' : Function.Bijective (crysExtensionSectionsMap F B')) (k : B ⟶ B')
    (s : F.val.obj (op B')) :
    ringConnection hVB hV he (crysSiteRestrict F k s) =
      restrictTensor F k (ringConnection hVB' hV' he' s) := by
  refine injective_readBack hVB hV he ?_
  rw [readBack_ringConnection, readBack_restrictTensor hVB hV hVB' hV', readBack_ringConnection,
    connectionDifference_naturality]

end Connection

/-! ### The extensions of the connection -/

section Extension

variable {F} [IsAffine B.obj.thickening.target.scheme] {V : S.S.scheme.Opens}
  (hVB : (⊤ : B.obj.thickening.target.scheme.Opens) ≤ B.obj.toBase.hom ⁻¹ᵁ V)
  (hV : IsAffineOpen V) (he : Function.Bijective (crysExtensionSectionsMap F B))

/-- **The descended de Rham differential of [Stacks, Tag 07I0] is the de Rham differential of
`Ω^*_{X/S}` of [Stacks, Tag 07J4]**: both are linear over the base and obey the rule
`d(b₀ d b₁ ∧ ⋯ ∧ d bᵢ) = d b₀ ∧ ⋯ ∧ d bᵢ` on the standard generators, which determines them. -/
theorem descendedDifferential_ringExtension (i : ℕ) :
    descendedDifferential (ringExtension hVB hV he).deRhamDifferential i =
      (crysDeRhamComplex S).differential i B.obj := by
  have hrule := extendedConnection_satisfiesRule (pi := crysPi S B.obj)
    (canonicalSourceDeRham ↥Γ(S.S.scheme, ⊤) (GlobalCrystallineSituation.crysFormRing S B.obj))
    (surjective_crysPi S B.obj) (generationHypothesis_crysPi S B.obj) (ringConnection hVB hV he)
  refine dpConstDeRham_unique (crysBaseAppLE S B.obj) (crysDividedPowers S B.obj)
    (crysBaseSections S B.obj) i ?_ ((crysDeRhamComplex S).differential_base_smul i B.obj)
    (fun b ↦ hrule i b) ((crysDeRhamComplex S).differential_generator i B.obj)
  intro a ω
  exact ((ringExtension hVB hV he).deRhamDifferential i).map_smul a
    ((RestrictScalars.addEquiv _ _ _).symm ω)

/-- The extension of the connection in degree `i`, as an additive map of
`ℱ(B) ⊗ Ω^i_{X/S}(B)`. -/
def extDiff (i : ℕ) :
    F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
        ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^i
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) →+
      F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
        ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^(i + 1)
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) :=
  (RestrictScalars.addEquiv _ _ _).toAddMonoidHom.comp
    ((((ringExtension hVB hV he).toLinearMap i).toAddMonoidHom).comp
      (RestrictScalars.addEquiv ↥Γ(S.S.scheme, ⊤)
        (GlobalCrystallineSituation.crysFormRing S B.obj) _).symm.toAddMonoidHom)

/-- **The extension on a pure tensor**: `d(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω`, with `d` the de Rham
differential of `Ω^*_{X/S}`. -/
theorem extDiff_tmul (i : ℕ) (m : F.val.obj (op B))
    (ω : ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^i
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    extDiff hVB hV he i (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj] ω) =
      TensorProduct.map LinearMap.id ((leftWedge i).flip ω) (ringConnection hVB hV he m) +
        m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
          (crysDeRhamComplex S).differential i B.obj ω := by
  refine ((ringExtension hVB hV he).map_tmul i m ω).trans ?_
  rw [← descendedDifferential_apply, descendedDifferential_ringExtension]

/-- **Consecutive extensions compose to zero**, the connection being integrable
(`ringConnection_isIntegrable`) and [Stacks, Tag 07I0] (`extendedConnection_comp_self_eq_zero`). -/
theorem extDiff_comp_extDiff (he₂ : Function.Injective (crysSecondExtensionSectionsMap F B))
    (i : ℕ) (x : F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
        ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^i
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :
    extDiff hVB hV he (i + 1) (extDiff hVB hV he i x) = 0 := by
  have h := LinearMap.congr_fun (extendedConnection_comp_self_eq_zero
    (canonicalSourceDeRham ↥Γ(S.S.scheme, ⊤) (GlobalCrystallineSituation.crysFormRing S B.obj))
    (crysPi S B.obj) (surjective_crysPi S B.obj) (generationHypothesis_crysPi S B.obj)
    (ringConnection hVB hV he) (ringConnection_isIntegrable hVB hV he he₂) i)
    ((RestrictScalars.addEquiv _ _ _).symm x)
  exact congrArg (RestrictScalars.addEquiv _ _ _) h

end Extension

/-! ### The transition maps of `ℱ ⊗ Ω^i_{X/S}`, and naturality of the extensions -/

/-- The bilinear datum of `restrictForms`. -/
def restrictFormsAux (k : B ⟶ B') (i : ℕ) :
    F.val.obj (op B') →+
      (⋀[GlobalCrystallineSituation.crysFormRing S B'.obj]^i
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj)) →+
        F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
          ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^i
            ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) :=
  AddMonoidHom.mk'
    (fun m ↦ AddMonoidHom.mk'
      (fun ω ↦ crysSiteRestrict F k m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        GlobalCrystallineSituation.crysFormMap S k.hom ω)
      (fun ω ω' ↦ by rw [map_add, TensorProduct.tmul_add]))
    (fun m m' ↦ AddMonoidHom.ext fun ω ↦ by
      change crysSiteRestrict F k (m + m') ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
          GlobalCrystallineSituation.crysFormMap S k.hom ω =
        crysSiteRestrict F k m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
            GlobalCrystallineSituation.crysFormMap S k.hom ω +
          crysSiteRestrict F k m' ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
            GlobalCrystallineSituation.crysFormMap S k.hom ω
      rw [crysSiteRestrict_add, TensorProduct.add_tmul])

/-- **The transition map of `ℱ ⊗ Ω^i_{X/S}` along `k`**, `m ⊗ ω ↦ k^* m ⊗ k^* ω`. -/
def restrictForms (k : B ⟶ B') (i : ℕ) :
    F.val.obj (op B') ⊗[GlobalCrystallineSituation.crysFormRing S B'.obj]
        ⋀[GlobalCrystallineSituation.crysFormRing S B'.obj]^i
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj)) →+
      F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
        ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^i
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) :=
  TensorProduct.liftAddHom (restrictFormsAux F k i) (fun c m ω ↦ by
    change crysSiteRestrict F k (c • m) ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        GlobalCrystallineSituation.crysFormMap S k.hom ω =
      crysSiteRestrict F k m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        GlobalCrystallineSituation.crysFormMap S k.hom (c • ω)
    rw [crysSiteRestrict_smul', GlobalCrystallineSituation.crysFormMap_smul,
      TensorProduct.smul_tmul])

/-- The transition map of `ℱ ⊗ Ω^i_{X/S}` on a pure tensor. -/
@[simp]
theorem restrictForms_tmul (k : B ⟶ B') (i : ℕ) (m : F.val.obj (op B'))
    (ω : ⋀[GlobalCrystallineSituation.crysFormRing S B'.obj]^i
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj))) :
    restrictForms F k i (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B'.obj] ω) =
      crysSiteRestrict F k m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj]
        GlobalCrystallineSituation.crysFormMap S k.hom ω :=
  TensorProduct.liftAddHom_tmul _ _ m ω

/-- The transition maps of `Ω^*_{X/S}` respect the left exterior multiplication by a one-form. -/
theorem crysFormMap_leftWedge (k : B ⟶ B') (i : ℕ)
    (η : ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj)))
    (ω : ⋀[GlobalCrystallineSituation.crysFormRing S B'.obj]^i
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj))) :
    GlobalCrystallineSituation.crysFormMap S k.hom (leftWedge i η ω) =
      leftWedge i (restrictOmega k η) (GlobalCrystallineSituation.crysFormMap S k.hom ω) := by
  refine Subtype.ext ?_
  change ExteriorAlgebra.mapₛₗ _ _ (ExteriorAlgebra.ι _ η * ω.val) =
    ExteriorAlgebra.ι _ (restrictOmega k η) * ExteriorAlgebra.mapₛₗ _ _ ω.val
  rw [map_mul, ExteriorAlgebra.mapₛₗ_ι]
  rfl

/-- The transition maps commute with the first term `∇(m) ∧ ω` of the extension. -/
theorem restrictForms_leftWedge (k : B ⟶ B') (i : ℕ)
    (ω : ⋀[GlobalCrystallineSituation.crysFormRing S B'.obj]^i
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj)))
    (z : F.val.obj (op B') ⊗[GlobalCrystallineSituation.crysFormRing S B'.obj]
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj))) :
    restrictForms F k (i + 1) (TensorProduct.map LinearMap.id ((leftWedge i).flip ω) z) =
      TensorProduct.map LinearMap.id
          ((leftWedge i).flip (GlobalCrystallineSituation.crysFormMap S k.hom ω))
        (restrictTensor F k z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m η =>
      rw [TensorProduct.map_tmul, restrictForms_tmul, restrictTensor_tmul, TensorProduct.map_tmul]
      exact congrArg (crysSiteRestrict F k m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj] ·)
        (crysFormMap_leftWedge k i η ω)
  | add x y hx hy =>
      refine ((congrArg (restrictForms F k (i + 1))
        ((TensorProduct.map LinearMap.id ((leftWedge i).flip ω)).map_add x y)).trans
        ((restrictForms F k (i + 1)).map_add _ _)).trans ((congrArg₂ (· + ·) hx hy).trans ?_)
      exact ((TensorProduct.map LinearMap.id
          ((leftWedge i).flip (GlobalCrystallineSituation.crysFormMap S k.hom ω))).map_add
            _ _).symm.trans
        (congrArg _ ((restrictTensor F k).map_add x y).symm)

section ExtensionNaturality

variable {F} [IsAffine B.obj.thickening.target.scheme] {V : S.S.scheme.Opens}
  (hVB : (⊤ : B.obj.thickening.target.scheme.Opens) ≤ B.obj.toBase.hom ⁻¹ᵁ V)
  (hV : IsAffineOpen V)
  [IsAffine B'.obj.thickening.target.scheme] {V' : S.S.scheme.Opens}
  (hVB' : (⊤ : B'.obj.thickening.target.scheme.Opens) ≤ B'.obj.toBase.hom ⁻¹ᵁ V')
  (hV' : IsAffineOpen V')
  (he : Function.Bijective (crysExtensionSectionsMap F B))
  (he' : Function.Bijective (crysExtensionSectionsMap F B'))

/-- **Naturality of the extensions of the canonical connection**: in every degree, the extension
`ℱ ⊗ Ω^i_{X/S} ⟶ ℱ ⊗ Ω^{i+1}_{X/S}` commutes with the transition maps along a morphism of
`Cris(X/S)` between two affine-over-affine objects. -/
theorem extDiff_naturality (k : B ⟶ B') (i : ℕ)
    (x : F.val.obj (op B') ⊗[GlobalCrystallineSituation.crysFormRing S B'.obj]
      ⋀[GlobalCrystallineSituation.crysFormRing S B'.obj]^i
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B'.obj))) :
    extDiff hVB hV he i (restrictForms F k i x) =
      restrictForms F k (i + 1) (extDiff hVB' hV' he' i x) := by
  induction x using TensorProduct.inductionOn with
  | tmul m ω =>
      rw [restrictForms_tmul, extDiff_tmul, extDiff_tmul, map_add, restrictForms_tmul,
        restrictForms_leftWedge, ← ringConnection_naturality hVB hV hVB' hV' he he']
      exact congrArg
        (_ + crysSiteRestrict F k m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S B.obj] ·)
        ((crysDeRhamComplex S).differential_naturality i k.hom ω).symm
  | add x y hx hy =>
      refine ((congrArg (extDiff hVB hV he i) ((restrictForms F k i).map_add x y)).trans
        ((extDiff hVB hV he i).map_add _ _)).trans ((congrArg₂ (· + ·) hx hy).trans ?_)
      exact ((restrictForms F k (i + 1)).map_add _ _).symm.trans
        (congrArg _ ((extDiff hVB' hV' he' i).map_add x y).symm)

end ExtensionNaturality

end Crystalline.GlobalCrystallineSituation.SmallSite.AffineConnection

end

end
