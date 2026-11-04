module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineComparisonAlong

/-!
# The affine base change of sections along an arbitrary morphism of `CRIS(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site and let `g : (U', T', δ') ⟶ (U, T, δ)` be a
morphism of `CRIS(X/S)`.  This module carries out, for an **arbitrary** `g`, the tensor half of
the affine computation of the base change of sections:

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} F(U, T, δ) ⟶ F(U', T', δ')`,  `t ⊗ s ↦ t · g^* s`

is bijective whenever `F` is a crystal, the two ambient schemes are affine and `F_T` is
quasi-coherent.

`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` carries out the same
computation for the first projection `p₀ : T' ⟶ T` of the first-order universal thickening of
[Stacks, Tag 07J2], and
`StacksFrontier/AlgebraicGeometry/Crystalline/AffineComparisonAlong.lean` generalises the
*categorical* half of that computation — the comparison map `c_g : g^* F_T ⟶ F_{T'}` of
[Stacks, Tag 07IQ] and the tail of the chain — to an arbitrary `g`.  What is left, and is done
here, is the tensor half.

## Why the two scalar actions are carried on a synonym

The computation compares two tensor products: the algebraic one over the section *rings of the
site*, which is the source of the base-change map, and the one
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` produces, over the section rings of the
*ambient schemes*.  The two scalar actions are built from the two ring homomorphisms of
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap`, which agree only
pointwise, and **neither action is determined by the pair of objects**: both are built from `g`.
So neither

`Algebra (crysSheafRing S A) (crysSheafRing S A')`    nor
`Module Γ(T, 𝒪_T) Γ(T', 𝒪_{T'})`

can be found by instance search, and declaring them as instances at an arbitrary pair of objects
would be unsound.  At `p₀` this does not arise, the source object `T'` being
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningObject` of the target, so that the
morphism is recovered from the two objects.

The device used here is a type synonym `Crystalline.GlobalCrystallineSituation.ringAlong` for the
sections of `𝒪_{X/S}` over the source, carrying `g` in its type, on which both actions *are*
instances.  Carrying them instead as instance-implicit arguments with defining equations would
destroy the one load-bearing step of the computation,
`Crystalline.GlobalCrystallineSituation.affineCrossModuleAlong`, whose whole content is that the
plain tensor product over the ambient sections **is** the carrier of Mathlib's
`ModuleCat.extendScalars`, the two scalar actions being the same `Module.compHom` term.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.ringAlong` — the sections of `𝒪_{X/S}` over the source
  of `g`, carrying the two scalar actions built from `g`.
* `Crystalline.GlobalCrystallineSituation.extensionSectionsMapAlong` — the base change of
  sections along `g`.
* `Crystalline.GlobalCrystallineSituation.affineCrossEquivAlong` — the change of spelling between
  the two tensor products.
* `Crystalline.GlobalCrystallineSituation.affineExtensionHomAlong` — the affine chain.

## Main results

* `Crystalline.GlobalCrystallineSituation.bijective_affineExtensionHomAlong` — the chain is
  bijective for a crystal on affine objects.
* `Crystalline.GlobalCrystallineSituation.extensionSectionsMapAlong_eq_affineExtensionHomAlong` —
  the chain **is** the base change of sections.
* `Crystalline.GlobalCrystallineSituation.bijective_extensionSectionsMapAlong` — **the base
  change of sections along an arbitrary morphism is bijective** for a crystal on affine objects
  with quasi-coherent `F_T`.

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) {A A' : Thickening S} (g : A' ⟶ A)

/-! ### The sections over the source of `g`, with the two scalar actions `g` builds

Both scalar actions of the computation are built from `g` and so cannot be instances on the
sections of `𝒪_{X/S}` over the source object; they are instances on this synonym, which carries
`g` in its type.  Everything about it is the identity, and all of its lemmas are `rfl`. -/

/-- **The sections of `𝒪_{X/S}` over the source of a morphism `g` of `CRIS(X/S)`, carrying the
two scalar actions of the target that `g` builds**: the algebra structure over the sections of
`𝒪_{X/S}` over the target through the restriction map of the site, and the module structure over
the sections of the structure sheaf of the ambient scheme of the target through the map on global
sections of the morphism of ambient schemes.  The two are the two ring homomorphisms of
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap`, equal only pointwise, so
both actions are needed and neither can be an instance on the sections themselves. -/
def ringAlong (_g : A' ⟶ A) : Type u := crysSheafRing S A'

/-- The commutative ring structure of the sections of `𝒪_{X/S}` over the source of `g`. -/
instance : CommRing (ringAlong g) := inferInstanceAs (CommRing (crysSheafRing S A'))

/-- **The sections of `𝒪_{X/S}` over the source of `g` as an algebra over the sections over the
target**, through the restriction map of `𝒪_{X/S}` along `g`.  This is the scalar action the
base change of sections `Crystalline.GlobalCrystallineSituation.extensionSectionsMapAlong` is
taken over. -/
instance algebraRingAlong : Algebra (crysSheafRing S A) (ringAlong g) :=
  (crysSheafRingMap g).toAlgebra

/-- **The sections of `𝒪_{X/S}` over the source of `g` as a module over the sections of the
structure sheaf of the ambient scheme of the target**, through the map on global sections of the
morphism `g : T' ⟶ T` of ambient schemes.  This is the scalar action over which
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` extends scalars; it is *not* the action
of `Crystalline.GlobalCrystallineSituation.algebraRingAlong`, the two being built from the two
ring homomorphisms of
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap`. -/
instance moduleAmbientRingAlong :
    Module Γ(A.thickening.target.scheme, ⊤) (ringAlong g) :=
  Module.compHom Γ(A'.thickening.target.scheme, ⊤)
    (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom

/-- A section of `𝒪_{X/S}` over the source of `g`, read at the synonym carrying the two scalar
actions.  The identity. -/
def ringAlongSection (t : crysSheafRing S A') : ringAlong g := t

/-- The reading of `Crystalline.GlobalCrystallineSituation.ringAlongSection` in the other
direction.  The identity. -/
def siteRingAlong (t : ringAlong g) : crysSheafRing S A' := t

/-- Reading a section at the synonym and back is the identity. -/
@[simp]
theorem siteRingAlong_ringAlongSection (t : crysSheafRing S A') :
    siteRingAlong g (ringAlongSection g t) = t := rfl

/-- Reading an element of the synonym as a section and back is the identity. -/
@[simp]
theorem ringAlongSection_siteRingAlong (t : ringAlong g) :
    ringAlongSection g (siteRingAlong g t) = t := rfl

/-- Reading a section at the synonym is additive; it is the identity. -/
theorem siteRingAlong_add (t t' : ringAlong g) :
    siteRingAlong g (t + t') = siteRingAlong g t + siteRingAlong g t' := rfl

/-- **The scalars of the sections over the target act on the sections over the source by
multiplication after the restriction map of the site.** -/
theorem siteRingAlong_smul (b : crysSheafRing S A) (t : ringAlong g) :
    siteRingAlong g (b • t) = crysSheafRingMap g b * siteRingAlong g t := rfl

/-- **The two actions of the sections of `𝒪_T` on the sections of `𝒪_{T'}` agree** — the one
through the restriction map of the site along `g` and the one through the map on global sections
of the morphism `g : T' ⟶ T` of ambient schemes.  This is
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap` read on the synonym. -/
theorem ambientRingSection_smul_ringAlong (b : crysSheafRing S A) (t : ringAlong g) :
    ambientRingSection A b • t = ringAlongSection g (crysSheafRingMap g b * siteRingAlong g t) :=
  congrArg (fun y ↦ y * siteRingAlong g t)
    (appLE_top_eq_crysSheafRingMap g (top_le_preimage_ambient g) (ambientRingSection A b))

/-- `Crystalline.GlobalCrystallineSituation.ambientRingSection_smul_ringAlong`, read against the
algebra structure the base change of sections is taken over. -/
theorem ambientRingSection_smul_eq_smul (b : crysSheafRing S A) (t : ringAlong g) :
    ambientRingSection A b • t = b • t :=
  (ambientRingSection_smul_ringAlong g b t).trans (siteRingAlong_smul g b t).symm

/-! ### The base change of the sections of `F` along `g` -/

/-- The bilinear datum of
`Crystalline.GlobalCrystallineSituation.extensionSectionsMapAlong`. -/
def extensionSectionsAlongAux :
    ringAlong g →+ (M.val.obj (op A) →+ M.val.obj (op A')) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ siteRingAlong g t • moduleSiteRestrict M g s)
      (fun s s' ↦ by rw [map_add, smul_add]))
    (fun t t' ↦ by
      refine AddMonoidHom.ext fun s ↦ ?_
      change siteRingAlong g (t + t') • moduleSiteRestrict M g s =
        siteRingAlong g t • moduleSiteRestrict M g s +
          siteRingAlong g t' • moduleSiteRestrict M g s
      rw [siteRingAlong_add, add_smul])

/-- The bilinear datum sends `t` and `s` to `t · g^* s`. -/
@[simp]
theorem extensionSectionsAlongAux_apply (t : ringAlong g) (s : M.val.obj (op A)) :
    extensionSectionsAlongAux M g t s = siteRingAlong g t • moduleSiteRestrict M g s := rfl

/-- **The base change of the sections of `F` along an arbitrary morphism `g` of `CRIS(X/S)`**, on
the algebraic tensor product of sections over the objects: the map

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} F(U, T, δ) ⟶ F(U', T', δ')`

sending `t ⊗ s` to `t · g^* s`.  At `g = p₀` this is
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap`. -/
def extensionSectionsMapAlong :
    ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A) →+ M.val.obj (op A') :=
  TensorProduct.liftAddHom (extensionSectionsAlongAux M g) (fun b t s ↦ by
    rw [extensionSectionsAlongAux_apply, extensionSectionsAlongAux_apply, map_smulₛₗ,
      siteRingAlong_smul, smul_smul, mul_comm])

/-- **The base change of sections on a pure tensor**: `t ⊗ s ↦ t · g^* s`. -/
@[simp]
theorem extensionSectionsMapAlong_tmul (t : ringAlong g) (s : M.val.obj (op A)) :
    extensionSectionsMapAlong M g (t ⊗ₜ[crysSheafRing S A] s) =
      siteRingAlong g t • moduleSiteRestrict M g s :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-! ### The two tensor products of the affine computation agree

The source of the base change of sections is a tensor product over the section rings of the site;
the source of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` is one over the section
rings of the ambient schemes.  The two are different types — their scalar actions are the two
ring homomorphisms of
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap`, equal only pointwise —
and this is the change of spelling between them.  It is unconditional: no crystal hypothesis, no
quasi-coherence, no affineness. -/

/-- The bilinear datum of `Crystalline.GlobalCrystallineSituation.affineCrossAlong`. -/
def affineCrossAlongAux :
    ringAlong g →+ (M.val.obj (op A) →+
      ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ t ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s))
      (fun s s' ↦ (congrArg
          (fun y ↦ t ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)] ambientModuleSection M A y)
          (map_add (moduleSiteRestrict M (A.restrictOpenHom ⊤)) s s')).trans
        (TensorProduct.tmul_add _ _ _)))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _)

/-- The bilinear datum sends `t` and `s` to `t ⊗ g^* s`. -/
@[simp]
theorem affineCrossAlongAux_apply (t : ringAlong g) (s : M.val.obj (op A)) :
    affineCrossAlongAux M g t s =
      t ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s) := rfl

/-- **The base change of the sections of `F` along `g`, carried into the tensor product of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`**: the map

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} F(U, T, δ) ⟶ Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T)`

sending `t ⊗ s` to `t ⊗ g^* s`, the two tensor products being over the two actions of
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap`.  No hypothesis. -/
def affineCrossAlong :
    ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A) →+
      ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤) :=
  TensorProduct.liftAddHom (affineCrossAlongAux M g) (fun b t s ↦ by
    rw [affineCrossAlongAux_apply, affineCrossAlongAux_apply, ← ambientRingSection_smul_eq_smul,
      TensorProduct.smul_tmul, ambientModuleSection_smul, map_smulₛₗ])

/-- `Crystalline.GlobalCrystallineSituation.affineCrossAlong` sends `t ⊗ s` to `t ⊗ g^* s`. -/
@[simp]
theorem affineCrossAlong_tmul (t : ringAlong g) (s : M.val.obj (op A)) :
    affineCrossAlong M g (t ⊗ₜ[crysSheafRing S A] s) =
      t ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s) :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-- The scalars of the ambient sections act on the synonym through the restriction map of the
site, by `Crystalline.GlobalCrystallineSituation.ambientRingSection_smul_eq_smul` read with the
scalar in the spelling of the ambient scheme. -/
theorem ambientSmul_eq_siteSmul (r : Γ(A.thickening.target.scheme, ⊤)) (t : ringAlong g) :
    r • t = siteRingSection A r • t :=
  ambientRingSection_smul_eq_smul g (siteRingSection A r) t

/-- The bilinear datum of `Crystalline.GlobalCrystallineSituation.affineCrossInvAlong`. -/
def affineCrossInvAlongAux :
    ringAlong g →+ (Γ(ambientSchemeModules M A, ⊤) →+
      ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun x ↦ t ⊗ₜ[crysSheafRing S A]
        (restrictOpenTopEquiv M A).symm (siteModuleSection M A x))
      (fun x y ↦ (congrArg (fun z ↦ t ⊗ₜ[crysSheafRing S A] z)
          (map_add (restrictOpenTopEquiv M A).symm (siteModuleSection M A x)
            (siteModuleSection M A y))).trans
        (TensorProduct.tmul_add _ _ _)))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _)

/-- The bilinear datum sends `t` and `x` to `t ⊗ (g^*)^{-1} x`. -/
@[simp]
theorem affineCrossInvAlongAux_apply (t : ringAlong g) (x : Γ(ambientSchemeModules M A, ⊤)) :
    affineCrossInvAlongAux M g t x =
      t ⊗ₜ[crysSheafRing S A] (restrictOpenTopEquiv M A).symm (siteModuleSection M A x) := rfl

/-- **The inverse of `Crystalline.GlobalCrystallineSituation.affineCrossAlong`**, the map sending
`t ⊗ x` to `t ⊗ (g^*)^{-1} x`. -/
def affineCrossInvAlong :
    ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤) →+
      ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A) :=
  TensorProduct.liftAddHom (affineCrossInvAlongAux M g) (fun r t x ↦ by
    rw [affineCrossInvAlongAux_apply, affineCrossInvAlongAux_apply, ambientSmul_eq_siteSmul,
      TensorProduct.smul_tmul, restrictOpenTopEquiv_symm_smul])

/-- `Crystalline.GlobalCrystallineSituation.affineCrossInvAlong` sends `t ⊗ x` to
`t ⊗ (g^*)^{-1} x`. -/
@[simp]
theorem affineCrossInvAlong_tmul (t : ringAlong g) (x : Γ(ambientSchemeModules M A, ⊤)) :
    affineCrossInvAlong M g (t ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)] x) =
      t ⊗ₜ[crysSheafRing S A] (restrictOpenTopEquiv M A).symm (siteModuleSection M A x) :=
  TensorProduct.liftAddHom_tmul _ _ t x

/-- **The two tensor products of the affine computation of the base change along `g` agree**, as
an additive equivalence

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} F(U, T, δ) ≅ Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T)`

between the source of `Crystalline.GlobalCrystallineSituation.extensionSectionsMapAlong` and the
source of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at `⊤, ⊤`.  It is
unconditional: no crystal hypothesis, no quasi-coherence, no affineness. -/
def affineCrossEquivAlong :
    ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A) ≃+
      ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤) where
  toFun := affineCrossAlong M g
  invFun := affineCrossInvAlong M g
  map_add' := map_add (affineCrossAlong M g)
  left_inv z := by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul t s =>
        rw [affineCrossAlong_tmul, affineCrossInvAlong_tmul,
          siteModuleSection_ambientModuleSection, ← restrictOpenTopEquiv_apply,
          AddEquiv.symm_apply_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  right_inv w := by
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul t x =>
        rw [affineCrossInvAlong_tmul, affineCrossAlong_tmul,
          moduleSiteRestrict_restrictOpenTopEquiv_symm]
        rfl
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-! ### The chain on an affine pair of objects

On a pair of objects with affine ambient schemes and with `F_T` quasi-coherent the three factors
`Crystalline.GlobalCrystallineSituation.affineCrossEquivAlong`,
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at `⊤, ⊤` and
`Crystalline.GlobalCrystallineSituation.affineChainTailAlong` are each bijections, and
`Crystalline.GlobalCrystallineSituation.affineExtensionHomAlong` is their composite.  That that
composite **is** `Crystalline.GlobalCrystallineSituation.extensionSectionsMapAlong` is proved in
the section after this one, and with it bijectivity of the base change itself.
-/

section Affine

variable [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
  [(ambientSchemeModules M A).IsQuasicoherent]

/-- The affine base-change comparison of [Stacks, Tag 01I9] at the whole of the two ambient
schemes, which are affine. -/
abbrev affineBaseChangeTopIsoAlong :=
  affinePullbackSectionsBaseChangeIso g.targetHom.hom (ambientSchemeModules M A)
    (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g)

/-- `Crystalline.GlobalCrystallineSituation.affineCrossAlong`, with its target named at the
extension of scalars of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`.  The single
bridge between the two spellings of the tensor product: the plain tensor product over
`Crystalline.GlobalCrystallineSituation.moduleAmbientRingAlong` **is** the carrier of Mathlib's
`ModuleCat.extendScalars`, the two scalar actions being the same `Module.compHom` term. -/
def affineCrossModuleAlong :
    ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A) →+
      ((ModuleCat.extendScalars (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom).obj
        (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeModules M A, ⊤)) :
          Type u) :=
  affineCrossAlong M g

omit [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
  [(ambientSchemeModules M A).IsQuasicoherent] in
/-- The bridge is a bijection, being
`Crystalline.GlobalCrystallineSituation.affineCrossEquivAlong`. -/
theorem bijective_affineCrossModuleAlong :
    Function.Bijective (affineCrossModuleAlong M g) :=
  (affineCrossEquivAlong M g).bijective

omit [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
  [(ambientSchemeModules M A).IsQuasicoherent] in
/-- The bridge, on a pure tensor. -/
theorem affineCrossModuleAlong_tmul (t : ringAlong g) (s : M.val.obj (op A)) :
    affineCrossModuleAlong M g (t ⊗ₜ[crysSheafRing S A] s) =
      ambientRingSection A' (siteRingAlong g t) ⊗ₜ[
        Γ(A.thickening.target.scheme, ⊤),
        (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s) :=
  affineCrossAlong_tmul M g t s

/-- The base-change comparison at `⊤, ⊤`, as an additive map. -/
def affineBaseChangeTopHomAlong :
    ((ModuleCat.extendScalars (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom).obj
      (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeModules M A, ⊤)) :
        Type u) →+
      ((ModuleCat.of Γ(A'.thickening.target.scheme, ⊤)
        Γ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeModules M A), ⊤)) :
          Type u) :=
  (affineBaseChangeTopIsoAlong M g).hom.hom.toAddMonoidHom

/-- The base-change comparison, written out. -/
theorem affineBaseChangeTopHomAlong_apply
    (w : ((ModuleCat.extendScalars
        (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom).obj
      (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeModules M A, ⊤)) :
        Type u)) :
    affineBaseChangeTopHomAlong M g w = (affineBaseChangeTopIsoAlong M g).hom w := rfl

/-- **The base-change comparison is bijective** under quasi-coherence and affineness, being an
isomorphism of `ModuleCat`. -/
theorem bijective_affineBaseChangeTopHomAlong :
    Function.Bijective (affineBaseChangeTopHomAlong M g) := by
  have h : (affineBaseChangeTopHomAlong M g : _ → _) =
      fun w ↦ (affineBaseChangeTopIsoAlong M g).hom w :=
    funext fun w ↦ affineBaseChangeTopHomAlong_apply M g w
  rw [h]
  exact ConcreteCategory.bijective_of_isIso (affineBaseChangeTopIsoAlong M g).hom

/-- `Crystalline.GlobalCrystallineSituation.ambientPullbackSectionTopAlong`, with its type named
at the codomain of the base-change comparison.  The one bridge between the sections notation and
the `ModuleCat` object whose carrier it is. -/
def ambientPullbackSectionTopModuleAlong (x : Γ(ambientSchemeModules M A, ⊤)) :
    ((ModuleCat.of Γ(A'.thickening.target.scheme, ⊤)
      Γ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeModules M A), ⊤)) :
        Type u) :=
  ambientPullbackSectionTopAlong M g x

omit [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
  [(ambientSchemeModules M A).IsQuasicoherent] in
/-- The tail of the chain on a scalar multiple of a pullback of a section,
`Crystalline.GlobalCrystallineSituation.affineChainTailAlong_smul_ambientPullbackSectionTopAlong`,
read at the codomain of the base-change comparison. -/
theorem affineChainTailAlong_smul_ambientPullbackSectionTopModuleAlong
    (t : crysSheafRing S A') (x : Γ(ambientSchemeModules M A, ⊤)) :
    affineChainTailAlong M g
        (ambientRingSection A' t • ambientPullbackSectionTopModuleAlong M g x) =
      t • (restrictOpenTopEquiv M A').symm
        (moduleSiteRestrict M (restrictOpenMapTop g) (siteModuleSection M A x)) :=
  affineChainTailAlong_smul_ambientPullbackSectionTopAlong M g t x

/-- **The affine chain along `g`, as an additive map
`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} F(U, T, δ) ⟶ F(U', T', δ')`.** -/
def affineExtensionHomAlong :
    ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A) →+ M.val.obj (op A') :=
  ((affineChainTailAlong M g).comp (affineBaseChangeTopHomAlong M g)).comp
    (affineCrossModuleAlong M g)

/-- **The chain is bijective** for a crystal, on a pair of objects with affine ambient schemes
and with `F_T` quasi-coherent: each of its three factors is.  That the chain is
`Crystalline.GlobalCrystallineSituation.extensionSectionsMapAlong`, and hence that that map is
bijective, is `Crystalline.GlobalCrystallineSituation.bijective_extensionSectionsMapAlong`
below. -/
theorem bijective_affineExtensionHomAlong (hM : IsSheafCrystal M) :
    Function.Bijective (affineExtensionHomAlong M g) :=
  ((bijective_affineChainTailAlong M g hM).comp (bijective_affineBaseChangeTopHomAlong M g)).comp
    (bijective_affineCrossModuleAlong M g)

/-! ### The chain is the base change of sections

The one equation the chain still owes is that it **is**
`Crystalline.GlobalCrystallineSituation.extensionSectionsMapAlong`, and by additivity it is
enough to check that on a pure tensor.  The three devices of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` are used unchanged: the
comparison is applied through the abbreviation
`Crystalline.GlobalCrystallineSituation.affineBaseChangeTopIsoAlong` *as a term* and the
identification with `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` is taken as a
*rewrite*; the chain is applied as the function
`Crystalline.GlobalCrystallineSituation.affineExtensionFunAlong` rather than through the bundled
additive map; and each crossing of the boundary between the two spellings of the tensor product
sits in its own declaration, the heartbeat budget being counted per declaration.
-/

/-- The base-change comparison at `⊤, ⊤` carries `1 ⊗ a` to the pullback of `a`.  This is
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul`, with its value named at the
`ModuleCat` object whose carrier it is. -/
theorem affineBaseChangeTopAlong_one_tmul
    (a : Γ(ambientSchemeModules M A, (⊤ : A.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso g.targetHom.hom (ambientSchemeModules M A)
        (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g)).hom
        ((1 : Γ(A'.thickening.target.scheme,
          (⊤ : A'.thickening.target.scheme.Opens))) ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom] a) =
      ambientPullbackSectionTopModuleAlong M g a :=
  affinePullbackSectionsBaseChangeIso_one_tmul g.targetHom.hom (ambientSchemeModules M A)
    (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g) a

/-- The base-change comparison at `⊤, ⊤` carries `t ⊗ a` to `t` times the pullback of `a`.  This
is `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_tmul` followed by
`Crystalline.GlobalCrystallineSituation.affineBaseChangeTopAlong_one_tmul`; it is a declaration of
its own so that the two elaborations are paid for out of two budgets. -/
theorem affineBaseChangeTopAlong_tmul
    (r : Γ(A'.thickening.target.scheme, (⊤ : A'.thickening.target.scheme.Opens)))
    (a : Γ(ambientSchemeModules M A, (⊤ : A.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso g.targetHom.hom (ambientSchemeModules M A)
        (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g)).hom (r ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom] a) =
      r • ambientPullbackSectionTopModuleAlong M g a :=
  (affinePullbackSectionsBaseChangeIso_tmul g.targetHom.hom (ambientSchemeModules M A)
    (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g) r a).trans
      (congrArg (fun z ↦ r • z) (affineBaseChangeTopAlong_one_tmul M g a))

/-- **The abbreviation naming the affine base-change comparison is that comparison.**  Trivial,
and stated because it is the one step that has to be taken as a *rewrite*: with it the goal
becomes syntactically the statement of
`Crystalline.GlobalCrystallineSituation.affineBaseChangeTopAlong_tmul`, so that the unifier is
never asked to identify the abbreviation and the `ModuleCat.ExtendScalars` carrier of a pure
tensor in the same step. -/
theorem affineBaseChangeTopIsoAlong_eq :
    affineBaseChangeTopIsoAlong M g =
      affinePullbackSectionsBaseChangeIso g.targetHom.hom (ambientSchemeModules M A)
        (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g) := rfl

/-- `Crystalline.GlobalCrystallineSituation.affineBaseChangeTopAlong_tmul`, read through the
abbreviation the chain is written with. -/
theorem affineBaseChangeTopIsoAlong_hom_tmul
    (r : Γ(A'.thickening.target.scheme, (⊤ : A'.thickening.target.scheme.Opens)))
    (a : Γ(ambientSchemeModules M A, (⊤ : A.thickening.target.scheme.Opens))) :
    (affineBaseChangeTopIsoAlong M g).hom (r ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom] a) =
      r • ambientPullbackSectionTopModuleAlong M g a := by
  rw [affineBaseChangeTopIsoAlong_eq]
  exact affineBaseChangeTopAlong_tmul M g r a

/-- **The affine chain along `g` as a function**: the composite of the bridge, the base-change
comparison applied as a morphism of `ModuleCat`, and the tail.  This is
`Crystalline.GlobalCrystallineSituation.affineExtensionHomAlong` with the middle factor not
bundled as an additive map, which is what lets the normalisation below be stated against
`Crystalline.GlobalCrystallineSituation.affineBaseChangeTopIsoAlong_hom_tmul`. -/
def affineExtensionFunAlong (z : ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A)) :
    M.val.obj (op A') :=
  affineChainTailAlong M g ((affineBaseChangeTopIsoAlong M g).hom (affineCrossModuleAlong M g z))

/-- The function and the additive map are the same map; bundling the middle factor is all that
separates them. -/
theorem affineExtensionFunAlong_eq_affineExtensionHomAlong
    (z : ringAlong g ⊗[crysSheafRing S A] M.val.obj (op A)) :
    affineExtensionFunAlong M g z = affineExtensionHomAlong M g z := rfl

omit [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
  [(ambientSchemeModules M A).IsQuasicoherent] in
/-- **The base change of sections on a pure tensor, written in the form the tail of the chain
produces.**  The two restrictions of `s` to the whole of the ambient schemes agree with the
restriction along `g`, by
`Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_restrictOpenMapTop`. -/
theorem extensionSectionsMapAlong_tmul_restrictOpenMapTop (t : ringAlong g)
    (s : M.val.obj (op A)) :
    extensionSectionsMapAlong M g (t ⊗ₜ[crysSheafRing S A] s) =
      siteRingAlong g t • (restrictOpenTopEquiv M A').symm
        (moduleSiteRestrict M (restrictOpenMapTop g)
          (siteModuleSection M A
            (ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s)))) := by
  rw [extensionSectionsMapAlong_tmul, siteModuleSection_ambientModuleSection]
  refine congrArg (fun y ↦ siteRingAlong g t • y) (Eq.symm ?_)
  rw [AddEquiv.symm_apply_eq, restrictOpenTopEquiv_apply]
  exact moduleSiteRestrict_restrictOpenMapTop M g s

/-- **The chain and the base change of sections agree on a pure tensor.**  The bridge carries
`t ⊗ s` to `t ⊗ g^* s`, the base-change comparison carries that to `t · g^* s`, and the tail
carries that to `t · g^* s` read over the object, which is
`Crystalline.GlobalCrystallineSituation.extensionSectionsMapAlong` at `t ⊗ s`. -/
theorem affineExtensionFunAlong_tmul (t : ringAlong g) (s : M.val.obj (op A)) :
    affineExtensionFunAlong M g (t ⊗ₜ[crysSheafRing S A] s) =
      extensionSectionsMapAlong M g (t ⊗ₜ[crysSheafRing S A] s) := by
  have hcross : affineExtensionFunAlong M g (t ⊗ₜ[crysSheafRing S A] s) =
      affineChainTailAlong M g ((affineBaseChangeTopIsoAlong M g).hom
        (ambientRingSection A' (siteRingAlong g t) ⊗ₜ[
          Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
          (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom]
          ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s))) :=
    congrArg (fun w ↦ affineChainTailAlong M g ((affineBaseChangeTopIsoAlong M g).hom w))
      (affineCrossModuleAlong_tmul M g t s)
  have hcomp := (congrArg (affineChainTailAlong M g)
    (affineBaseChangeTopIsoAlong_hom_tmul M g (ambientRingSection A' (siteRingAlong g t))
      (ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s)))).trans
    (affineChainTailAlong_smul_ambientPullbackSectionTopModuleAlong M g (siteRingAlong g t)
      (ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s)))
  exact (hcross.trans hcomp).trans (extensionSectionsMapAlong_tmul_restrictOpenMapTop M g t s).symm

/-- `Crystalline.GlobalCrystallineSituation.affineExtensionFunAlong_tmul`, for the additive
map. -/
theorem affineExtensionHomAlong_tmul (t : ringAlong g) (s : M.val.obj (op A)) :
    affineExtensionHomAlong M g (t ⊗ₜ[crysSheafRing S A] s) =
      extensionSectionsMapAlong M g (t ⊗ₜ[crysSheafRing S A] s) :=
  (affineExtensionFunAlong_eq_affineExtensionHomAlong M g
      (t ⊗ₜ[crysSheafRing S A] s)).symm.trans (affineExtensionFunAlong_tmul M g t s)

/-- **The affine chain is the base change of sections**: two additive maps agreeing on every pure
tensor agree. -/
theorem extensionSectionsMapAlong_eq_affineExtensionHomAlong :
    (extensionSectionsMapAlong M g : _ → _) = (affineExtensionHomAlong M g : _ → _) := by
  funext w
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul t s => exact (affineExtensionHomAlong_tmul M g t s).symm
  | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-- **The base change of sections along an arbitrary morphism of `CRIS(X/S)` is bijective** for a
crystal on a pair of objects whose ambient schemes are affine and with `F_T` quasi-coherent.
This is the chain `Crystalline.GlobalCrystallineSituation.bijective_affineExtensionHomAlong`
together with the identification of the chain with
`Crystalline.GlobalCrystallineSituation.extensionSectionsMapAlong`.

At `g = p₀` this is
`Crystalline.GlobalCrystallineSituation.bijective_extensionSectionsMap`. -/
theorem bijective_extensionSectionsMapAlong (hM : IsSheafCrystal M) :
    Function.Bijective (extensionSectionsMapAlong M g) := by
  rw [extensionSectionsMapAlong_eq_affineExtensionHomAlong M g]
  exact bijective_affineExtensionHomAlong M g hM

end Affine

/-! ### The generalisation subsumes the case of the first projection

The development of `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` is the
case `g = p₀` of the one above: the two base-change maps are the same map, and so the bijectivity
proved there is the bijectivity proved here read at the first projection.  Nothing below is used
by anything; it records that the generalisation is one. -/

section SubsumesP₀

variable (B : Thickening S)

/-- **The base change of sections along `p₀` is the base change of sections along `p₀` read as an
arbitrary morphism.**  Both are the map `t ⊗ s ↦ t · p₀^* s` built by
`TensorProduct.liftAddHom`; the two scalar actions on the sections over the first-order universal
thickening are the same `RingHom.toAlgebra` term, one carried by
`Crystalline.GlobalCrystallineSituation.algebraCrysSheafRingSiteP₀` on the sections themselves and
one by `Crystalline.GlobalCrystallineSituation.algebraRingAlong` on the synonym. -/
theorem extensionSectionsMap_eq_extensionSectionsMapAlong :
    (extensionSectionsMap M B : _ → _) =
      (extensionSectionsMapAlong M (firstOrderThickeningSiteP₀ S B) : _ → _) := rfl

/-- **`Crystalline.GlobalCrystallineSituation.bijective_extensionSectionsMap` follows from
`Crystalline.GlobalCrystallineSituation.bijective_extensionSectionsMapAlong`**, the affineness of
the ambient scheme of the first-order universal thickening being
`Crystalline.GlobalCrystallineSituation.isAffine_target_firstOrderThickeningObject`. -/
theorem bijective_extensionSectionsMap_from_affineBaseChangeAlong
    [IsAffine B.thickening.target.scheme] [(ambientSchemeModules M B).IsQuasicoherent]
    (hM : IsSheafCrystal M) : Function.Bijective (extensionSectionsMap M B) := by
  rw [extensionSectionsMap_eq_extensionSectionsMapAlong M B]
  exact bijective_extensionSectionsMapAlong M (firstOrderThickeningSiteP₀ S B) hM

end SubsumesP₀

end Crystalline.GlobalCrystallineSituation

end

end
