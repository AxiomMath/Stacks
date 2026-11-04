module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.DualHomGlobalSections
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Situation
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The Künneth input on `X ×_k X` of Situation [Stacks, Tag 0G08], discharged

`AlgebraicGeometry.exists_kunnethComplex_of_tensorPairings` of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Situation` states the
conclusion of [Stacks, Tag 0G0A] at the hypotheses of Situation [Stacks, Tag 0G08] from two
Künneth inputs, one on each of the two products. **This file proves the one on `X ×_k X`**: the
pairing `(a, b) ↦ a ⊠ b` does exhibit `Hom(ℰ ⊠ 𝒢, ℰ' ⊠ 𝒢')` as `Hom(ℰ, ℰ') ⊗_k Hom(𝒢, 𝒢')`
when `X` and `Y` are proper over the field `k` and the four modules are finite locally free.
`AlgebraicGeometry.exists_kunnethComplex_of_imagePairing` below is therefore [Stacks, Tag 0G0A]
in Situation [Stacks, Tag 0G08] on one Künneth input rather than two. It still carries that
input, so the tag is not registered on it.

Through the duality of a finite locally free module the Hom group becomes a group of global
sections,

`Hom(ℰ ⊠ 𝒢, ℰ' ⊠ 𝒢') ≃ Γ(X ×_k Y, (ℰ' ⊗ ℰ^∨) ⊠ (𝒢' ⊗ 𝒢^∨))`,

the pure map `a ⊠ b` going to the external tensor section of the two one-factor duality
sections — that is
`AlgebraicGeometry.app_externalTensorDualTensorHomEquiv_tensorIso_externalTensorProductMap`,
with injectivity and additivity recorded separately below; and
`AlgebraicGeometry.bijective_globalBoxSectionMap_of_isProper` says that

`Γ(X, P) ⊗_k Γ(Y, Q) ⟶ Γ(X ×_k Y, P ⊠ Q)`, `s ⊗ t ↦ s ⊠ t`

is bijective for `P` and `Q` quasi-coherent and `X`, `Y` proper over `k`. Composing, the pairing
of Hom groups is a bijection out of `Hom(ℰ, ℰ') ⊗_k Hom(𝒢, 𝒢')` carrying pure tensors to pure
maps, which is exactly `AlgebraicGeometry.IsTensorPairing`.

## Where properness is spent

Only in `AlgebraicGeometry.bijective_globalBoxSectionMap_of_isProper`, and there twice:
quasi-compactness makes the two affine coverings finite and separatedness makes their pairwise
intersections affine. Neither use is removable. Without quasi-compactness the statement proved
here is **false**: for `X = Y = ∐_{n : ℕ} Spec k` with `ℰ = 𝒢 = 𝒪` the pairing is the inclusion
of `(∏_ℕ k) ⊗_k (∏_ℕ k)` into `∏_{ℕ × ℕ} k`, whose image is the finite-rank matrices, and the
implementation notes of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Kunneth` exhibit a
`AlgebraicGeometry.DiagonalResolution` on that `X` for which the box pairing is therefore not
surjective. Smoothness is *not* used.

## Main definitions

* `AlgebraicGeometry.unitHomLinearEquiv`: morphisms from the structure sheaf of a scheme over a
  field `k` are its global sections, as `k`-vector spaces.
* `AlgebraicGeometry.dualTensorHomLinearEquiv`: `Hom(P, ℱ) ≃ₗ[k] Γ(X, ℱ ⊗ P^∨)` for a finite
  locally free `P`.

## Main results

* `AlgebraicGeometry.app_externalTensorDualTensorHomEquiv_tensorIso_externalTensorProductMap`,
  `…_add` and `AlgebraicGeometry.eq_of_app_externalTensorDualTensorHomEquiv_tensorIso_eq`: the
  comparison `Hom(ℰ ⊠ 𝒢, ℰ' ⊠ 𝒢') ⟶ Γ(X ×_k Y, (ℰ' ⊗ ℰ^∨) ⊠ (𝒢' ⊗ 𝒢^∨))` at a pure map, its
  additivity, and its injectivity.
* `AlgebraicGeometry.isTensorPairing_externalTensorProductPairing`: **the pairing
  `(a, b) ↦ a ⊠ b` exhibits `Hom(ℰ ⊠ 𝒢, ℰ' ⊠ 𝒢')` as `Hom(ℰ, ℰ') ⊗_k Hom(𝒢, 𝒢')`** for four
  finite locally free modules on two schemes proper over a field.
* `AlgebraicGeometry.DiagonalResolution.isTensorPairing_boxPairing`: **the hypothesis `hbox` of
  `AlgebraicGeometry.exists_kunnethComplex_of_tensorPairings`**, at the hypotheses of Situation
  [Stacks, Tag 0G08].
* `AlgebraicGeometry.exists_kunnethComplex_of_imagePairing`: **[Stacks, Tag 0G0A] in Situation
  [Stacks, Tag 0G08]**, from the Künneth input on `X ×_k Y` alone.

## Implementation notes

*What is and is not achieved.* `AlgebraicGeometry.exists_kunnethComplex_of_imagePairing` still
carries one hypothesis, `himage`, the Künneth input at the *other* product `X ×_k Y`: that the
pairing `(a, c) ↦ a ⊠ c` exhibits the Hom group
`Hom_{D(𝒪_{X ×_k Y})}(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))` of the derived category as
`Hom(ℰᵢ, ℰⱼ) ⊗_k Hom(F(𝒢ᵢ), F(𝒢ⱼ))`. That input is not a consequence of the one proved here, for
two reasons. The duality bijection this file runs on does not apply to `F(𝒢ᵢ)`, which is an
arbitrary perfect complex rather than a finite locally free module in degree zero; and, as the
implementation notes of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Situation` record, the
Künneth formula for Ext of [Stacks, Tag 0FXZ] on `X ×_k Y` is not a consequence of the one on
`X ×_k X` — exactness of `F` collapses the source's sum over `p` to its `p = 0` summand, which is
`AlgebraicGeometry.DiagonalResolution.subsingleton_hom_map_secondFactor_shift`, but that is the
*second* equality of the source's display and not the first. So [Stacks, Tag 0G0A] is **not**
unconditional after this file; one of its two inputs is.

*How far the route through [Stacks, Tag 0FXZ] now reaches, and where it stops.* That tag asserts
the invertibility of the Künneth morphism for Ext of [Stacks, Tag 0FXY] as a morphism of objects
of `D(𝒪_S)`, which by itself says nothing about which elements of a Hom group the pure maps hit.
What it needs in addition — the value of that morphism at a pure tensor — is now proved, as
`Stacks.Cohomology.DerivedKunnethExt.homEquiv_symm_kunnethExtMap` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethExtPureTensor`. It still does
not give `himage`, and the obstruction is no longer a missing computation but the model of the
derived categories: the arguments of `Stacks.Cohomology.DerivedKunnethExt.kunnethExtMap` are
objects of `DerivedCategory.{u + 1, u, u + 1}`, the standard model's, whereas the Hom groups
`himage` is about are between objects of `DerivedCategory.{u, u, u + 1}`, the locally small
model's, which is what `AlgebraicGeometry.DiagonalResolution.transformedTerm` is read at. The
morphism universes differ, so there is no statement of [Stacks, Tag 0FXZ] at the model `himage`
lives at to apply, and supplying one would mean re-declaring every constituent of `kunnethExtMap`
with its model as a binder and re-proving four of 0FXZ's five theorem inputs there. The
implementation notes of that file and of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Kunneth` say what closing
that would take.

*The shape of the argument.* The two clauses of `AlgebraicGeometry.IsTensorPairing` are read off
one commuting square: the pairing followed by the injection out of the Hom group is the
bijection `Hom(ℰ, ℰ') ⊗_k Hom(𝒢, 𝒢') ⟶ Γ(X ×_k Y, P ⊠ Q)` precomposed with
`AlgebraicGeometry.freeAbelianGroupToTensor`. Both maps are additive and the square commutes on
the generators of the free abelian group, so it commutes; surjectivity then follows from
`AlgebraicGeometry.surjective_freeAbelianGroupToTensor` and the equality of kernels from
injectivity of the bijection in one direction and injectivity of the comparison in the other.

## References

* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0G08](https://stacks.math.columbia.edu/tag/0G08)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.FiniteLocallyFree Stacks.Cohomology.PerfectComplexes
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Tag01VSPullbackTensor

universe u

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ReflexiveModules AlgebraicGeometry.VectorBundleKZero

attribute [local instance] onSpaceModulesMonoidal


/-! ### The duality bijections as `k`-linear equivalences on global sections -/

section LinearEquivs

variable (k : Type u) [Field k]

/-- **Morphisms out of the structure sheaf are the global sections, `k`-linearly.** The
bijection is `AlgebraicGeometry.Scheme.Modules.unitHomEquivTop` read backwards — a morphism out
of the structure sheaf goes to its value at the unit section — and what is added here is that it
is `k`-linear: the scalar action of `AlgebraicGeometry.modulesLinear` on a Hom group is
precomposition with multiplication by the image of the scalar among the global functions, and
that of `AlgebraicGeometry.globalSectionsOverField` on sections is multiplication by the same
global function. -/
def unitHomLinearEquiv (X : Over (Spec (.of k))) (M : X.left.Modules) :
    letI := modulesLinear k X
    (𝟙_ X.left.Modules ⟶ M) ≃ₗ[k] ↑(globalSectionsOverField k X.hom M) :=
  letI := modulesLinear k X
  { toFun := fun φ => Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X.left, ⊤))
    map_add' := fun _ _ => rfl
    map_smul' := fun c φ => by
      rw [RingHom.id_apply]
      change Scheme.Modules.Hom.app ((baseScalar k X c).app _ ≫ φ) ⊤ (1 : Γ(X.left, ⊤)) = _
      exact (φ.val.app (op ⊤)).hom.map_smul (baseRingToSections k X (op ⊤) c)
        (1 : Γ(X.left, ⊤))
    invFun := Scheme.Modules.unitHomEquivTop M
    left_inv := fun φ => (Scheme.Modules.unitHomEquivTop M).apply_symm_apply φ
    right_inv := fun x => (Scheme.Modules.unitHomEquivTop M).symm_apply_apply x }

/-- **`Hom(P, ℱ) ≃ Γ(X, ℱ ⊗ P^∨)` is `k`-linear**, as a `k`-linear equivalence: this is
`AlgebraicGeometry.dualTensorHomEquiv` with the additivity of
`AlgebraicGeometry.dualTensorHomEquiv_add` and the `k`-linearity of
`AlgebraicGeometry.dualTensorHomEquiv_smul` attached to it. -/
def dualTensorHomLinearEquivHom (X : Over (Spec (.of k))) (P F : X.left.Modules)
    (hP : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) P) :
    letI := modulesLinear k X
    (P ⟶ F) ≃ₗ[k] (𝟙_ X.left.Modules ⟶ F ⊗ dualSheaf P) :=
  letI := modulesLinear k X
  { dualTensorHomEquiv X.left P F hP with
    map_add' := dualTensorHomEquiv_add X.left P F hP
    map_smul' := fun c q => dualTensorHomEquiv_smul k X P F hP c q }

/-- **`Hom(P, ℱ) ≃ₗ[k] Γ(X, ℱ ⊗ P^∨)` for a finite locally free `P`** on a scheme over `k`:
`AlgebraicGeometry.dualTensorHomLinearEquivHom` read into global sections by
`AlgebraicGeometry.unitHomLinearEquiv`. -/
def dualTensorHomLinearEquiv (X : Over (Spec (.of k))) (P F : X.left.Modules)
    (hP : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) P) :
    letI := modulesLinear k X
    (P ⟶ F) ≃ₗ[k] ↑(globalSectionsOverField k X.hom (F ⊗ dualSheaf P)) :=
  letI := modulesLinear k X
  (dualTensorHomLinearEquivHom k X P F hP).trans (unitHomLinearEquiv k X (F ⊗ dualSheaf P))

variable (X Y : Over (Spec (.of k)))

/-- **The duality bijection carries the zero morphism to zero**, being additive. -/
theorem externalTensorDualTensorHomEquiv_zero
    (E E₂ : X.left.Modules) (G G₂ : Y.left.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.left.ringCatSheaf) G) :
    externalTensorDualTensorHomEquiv X.hom Y.hom E G
        (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG 0 = 0 := by
  have h := externalTensorDualTensorHomEquiv_add X.hom Y.hom E G
    (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG 0 0
  rw [add_zero] at h
  exact (add_left_cancel ((add_zero (externalTensorDualTensorHomEquiv X.hom Y.hom E G
    (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG 0)).trans h)).symm

/-- **The duality bijection carries a negative to the negative**, being additive. -/
theorem externalTensorDualTensorHomEquiv_neg
    (E E₂ : X.left.Modules) (G G₂ : Y.left.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.left.ringCatSheaf) G)
    (φ : externalTensorProduct X.hom Y.hom E G ⟶
      externalTensorProduct X.hom Y.hom E₂ G₂) :
    externalTensorDualTensorHomEquiv X.hom Y.hom E G
          (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG (-φ)
      = -externalTensorDualTensorHomEquiv X.hom Y.hom E G
          (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG φ := by
  refine add_eq_zero_iff_eq_neg.mp ?_
  rw [← externalTensorDualTensorHomEquiv_add, neg_add_cancel,
    externalTensorDualTensorHomEquiv_zero]

/-- **The duality bijection followed by the interchange of [Stacks, Tag 0G46] is additive.**
`AlgebraicGeometry.externalTensorDualTensorHomEquiv_add` and additivity of composition. -/
theorem externalTensorDualTensorHomEquiv_tensorIso_add
    (E E₂ : X.left.Modules) (G G₂ : Y.left.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.left.ringCatSheaf) G)
    (φ φ' : externalTensorProduct X.hom Y.hom E G ⟶
      externalTensorProduct X.hom Y.hom E₂ G₂) :
    externalTensorDualTensorHomEquiv X.hom Y.hom E G
          (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG (φ + φ') ≫
        (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom
      = externalTensorDualTensorHomEquiv X.hom Y.hom E G
            (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG φ ≫
          (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom
        + externalTensorDualTensorHomEquiv X.hom Y.hom E G
            (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG φ' ≫
          (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom := by
  rw [externalTensorDualTensorHomEquiv_add]
  exact Preadditive.add_comp _ _ _ _ _ _

/-- **The global section of a morphism out of the structure sheaf depends only on the morphism.** -/
private theorem app_one_congr {W : Scheme.{u}} {M : W.Modules} {α β : 𝟙_ W.Modules ⟶ M}
    (h : α = β) :
    Scheme.Modules.Hom.app α ⊤ (1 : Γ(W, ⊤)) = Scheme.Modules.Hom.app β ⊤ (1 : Γ(W, ⊤)) :=
  congrArg (fun z : 𝟙_ W.Modules ⟶ M => Scheme.Modules.Hom.app z ⊤ (1 : Γ(W, ⊤))) h

/-- **The duality bijection followed by the interchange, read on global sections, is
additive.** -/
theorem app_externalTensorDualTensorHomEquiv_tensorIso_add
    (E E₂ : X.left.Modules) (G G₂ : Y.left.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.left.ringCatSheaf) G)
    (φ φ' : externalTensorProduct X.hom Y.hom E G ⟶
      externalTensorProduct X.hom Y.hom E₂ G₂) :
    Scheme.Modules.Hom.app (N := externalTensorProduct X.hom Y.hom
        (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G))
        (externalTensorDualTensorHomEquiv X.hom Y.hom E G
          (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG (φ + φ') ≫
        (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom) ⊤
        (1 : Γ(Limits.pullback X.hom Y.hom, ⊤))
      = Scheme.Modules.Hom.app (N := externalTensorProduct X.hom Y.hom
          (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G))
        (externalTensorDualTensorHomEquiv X.hom Y.hom E G
            (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG φ ≫
          (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom) ⊤
          (1 : Γ(Limits.pullback X.hom Y.hom, ⊤))
        + Scheme.Modules.Hom.app (N := externalTensorProduct X.hom Y.hom
            (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G))
        (externalTensorDualTensorHomEquiv X.hom Y.hom E G
            (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG φ' ≫
          (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom) ⊤
          (1 : Γ(Limits.pullback X.hom Y.hom, ⊤)) := by
  exact (app_one_congr
    (externalTensorDualTensorHomEquiv_tensorIso_add k X Y E E₂ G G₂ hE hG φ φ')).trans
    (app_one_add _ _)

/-- **The duality bijection followed by the interchange, read on global sections, carries the
zero morphism to zero.** -/
theorem app_externalTensorDualTensorHomEquiv_tensorIso_zero
    (E E₂ : X.left.Modules) (G G₂ : Y.left.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.left.ringCatSheaf) G) :
    Scheme.Modules.Hom.app (N := externalTensorProduct X.hom Y.hom
          (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G))
        (externalTensorDualTensorHomEquiv X.hom Y.hom E G
            (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG 0 ≫
          (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom) ⊤
        (1 : Γ(Limits.pullback X.hom Y.hom, ⊤)) = 0 := by
  refine (app_one_congr (β := 0) ?_).trans app_one_zero
  rw [externalTensorDualTensorHomEquiv_zero]
  exact Limits.zero_comp

/-- **The duality bijection followed by the interchange, read on global sections, carries a
negative to the negative.** -/
theorem app_externalTensorDualTensorHomEquiv_tensorIso_neg
    (E E₂ : X.left.Modules) (G G₂ : Y.left.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.left.ringCatSheaf) G)
    (φ : externalTensorProduct X.hom Y.hom E G ⟶
      externalTensorProduct X.hom Y.hom E₂ G₂) :
    Scheme.Modules.Hom.app (N := externalTensorProduct X.hom Y.hom
          (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G))
        (externalTensorDualTensorHomEquiv X.hom Y.hom E G
            (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG (-φ) ≫
          (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom) ⊤
        (1 : Γ(Limits.pullback X.hom Y.hom, ⊤))
      = -Scheme.Modules.Hom.app (N := externalTensorProduct X.hom Y.hom
          (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G))
        (externalTensorDualTensorHomEquiv X.hom Y.hom E G
            (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG φ ≫
          (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom) ⊤
        (1 : Γ(Limits.pullback X.hom Y.hom, ⊤)) := by
  refine (app_one_congr ?_).trans (app_one_neg _)
  rw [externalTensorDualTensorHomEquiv_neg]
  exact Preadditive.neg_comp _ _

/-- **The duality bijection followed by the interchange, read on global sections, is
injective.** Each of its three steps is: the duality bijection, composition with an isomorphism,
and `AlgebraicGeometry.Scheme.Modules.unitHomEquivTop`. -/
theorem eq_of_app_externalTensorDualTensorHomEquiv_tensorIso_eq
    (E E₂ : X.left.Modules) (G G₂ : Y.left.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.left.ringCatSheaf) G)
    (φ ψ : externalTensorProduct X.hom Y.hom E G ⟶
      externalTensorProduct X.hom Y.hom E₂ G₂)
    (h : Scheme.Modules.Hom.app (N := externalTensorProduct X.hom Y.hom
        (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G))
        (externalTensorDualTensorHomEquiv X.hom Y.hom E G
            (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG φ ≫
          (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom) ⊤
          (1 : Γ(Limits.pullback X.hom Y.hom, ⊤))
        = Scheme.Modules.Hom.app (N := externalTensorProduct X.hom Y.hom
            (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G))
        (externalTensorDualTensorHomEquiv X.hom Y.hom E G
            (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG ψ ≫
          (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom) ⊤
          (1 : Γ(Limits.pullback X.hom Y.hom, ⊤))) :
    φ = ψ := by
  have h' : externalTensorDualTensorHomEquiv X.hom Y.hom E G
          (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG φ ≫
        (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom
      = externalTensorDualTensorHomEquiv X.hom Y.hom E G
          (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG ψ ≫
        (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom :=
    injective_app_one _ _ h
  exact (externalTensorDualTensorHomEquiv X.hom Y.hom E G
      (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG).injective
    ((Iso.homToEquiv
      (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G))).injective h')

/-- **The duality bijection followed by the interchange carries a pure map `a ⊠ b` to the
external tensor section of the two one-factor duality sections**, which is the value of
`AlgebraicGeometry.globalBoxSectionMap` at the pure tensor of the two global sections. -/
theorem app_externalTensorDualTensorHomEquiv_tensorIso_externalTensorProductMap
    (E E₂ : X.left.Modules) (G G₂ : Y.left.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.left.ringCatSheaf) G)
    (a : E ⟶ E₂) (b : G ⟶ G₂) :
    letI := modulesLinear k X
    letI := modulesLinear k Y
    Scheme.Modules.Hom.app (N := externalTensorProduct X.hom Y.hom
        (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G))
        (externalTensorDualTensorHomEquiv X.hom Y.hom E G
          (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG
            (externalTensorProductMap X.hom Y.hom a b) ≫
        (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom) ⊤
        (1 : Γ(Limits.pullback X.hom Y.hom, ⊤))
      = globalBoxSectionMap k X.hom Y.hom (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G)
        (dualTensorHomLinearEquiv k X E E₂ hE a ⊗ₜ[k]
          dualTensorHomLinearEquiv k Y G G₂ hG b) := by
  let := modulesLinear k X
  let := modulesLinear k Y
  refine Eq.trans (app_externalTensorDualTensorHomEquiv_externalTensorProductMap
    X.hom Y.hom E E₂ G G₂ hE hG a b) ?_
  exact app_box_of_unitHom X.hom Y.hom (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G)
    (dualTensorHomEquiv X.left E E₂ hE a) (dualTensorHomEquiv Y.left G G₂ hG b)

end LinearEquivs

/-! ### The Künneth input on a product of two proper schemes over a field -/

/-- **The pairing `(a, b) ↦ a ⊠ b` exhibits `Hom(ℰ ⊠ 𝒢, ℰ' ⊠ 𝒢')` as
`Hom(ℰ, ℰ') ⊗_k Hom(𝒢, 𝒢')`** for `X` and `Y` proper over a field `k` and `ℰ`, `ℰ'`, `𝒢`, `𝒢'`
finite locally free: the pure maps span the Hom group, and the relations among them are exactly
the `k`-bilinear ones.

Properness is consumed in
`AlgebraicGeometry.bijective_globalBoxSectionMap_of_isProper`, and without it the statement is
false; see the module documentation. Smoothness is not used. -/
theorem isTensorPairing_externalTensorProductPairing (k : Type u) [Field k]
    (X Y : Over (Spec (.of k))) [IsProper X.hom] [IsProper Y.hom]
    (E E₂ : X.left.Modules) (G G₂ : Y.left.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) E)
    (hE₂ : IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) E₂)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.left.ringCatSheaf) G)
    (hG₂ : IsFiniteLocallyFree.{u, u, u} (R := Y.left.ringCatSheaf) G₂) :
    letI := modulesLinear k X
    letI := modulesLinear k Y
    letI : Linear k (Limits.pullback X.hom Y.hom).Modules :=
      modulesLinear k (externalTensorOver k X Y)
    IsTensorPairing k (E ⟶ E₂) (G ⟶ G₂)
      (FreeAbelianGroup.lift fun p : (E ⟶ E₂) × (G ⟶ G₂) =>
        externalTensorProductMap X.hom Y.hom p.1 p.2) := by
  let := modulesLinear k X
  let := modulesLinear k Y
  let : Linear k (Limits.pullback X.hom Y.hom).Modules :=
    modulesLinear k (externalTensorOver k X Y)
  have key : ∀ {Z : Scheme.{u}} (M : Z.Modules),
      IsFiniteLocallyFree.{u, u, u} (R := Z.ringCatSheaf) M →
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M ∧ M.IsQuasicoherent :=
    fun M h => have := (isFiniteLocallyFree_iff_algebraicGeometry M).1 h
      ⟨this, Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M⟩
  obtain ⟨_, hqE₂⟩ := key E₂ hE₂
  obtain ⟨_, hqG₂⟩ := key G₂ hG₂
  obtain ⟨_, hqdE⟩ := key _ (isFiniteLocallyFree_dualSheaf' E hE)
  obtain ⟨_, hqdG⟩ := key _ (isFiniteLocallyFree_dualSheaf' G hG)
  have : (E₂ ⊗ dualSheaf E).IsQuasicoherent :=
    @tensorSheaf_isQuasicoherent X.left.toRingedSpace E₂ (dualSheaf E) hqE₂ hqdE
  have : (G₂ ⊗ dualSheaf G).IsQuasicoherent :=
    @tensorSheaf_isQuasicoherent Y.left.toRingedSpace G₂ (dualSheaf G) hqG₂ hqdG
  set Φ := dualTensorHomLinearEquiv k X E E₂ hE with hΦ
  set Ψ := dualTensorHomLinearEquiv k Y G G₂ hG with hΨ
  set D : (externalTensorProduct X.hom Y.hom E G ⟶ externalTensorProduct X.hom Y.hom E₂ G₂) →
      Γ(externalTensorProduct X.hom Y.hom (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G), ⊤) :=
    fun φ => Scheme.Modules.Hom.app (N := externalTensorProduct X.hom Y.hom
          (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G))
        (externalTensorDualTensorHomEquiv X.hom Y.hom E G
            (externalTensorProduct X.hom Y.hom E₂ G₂) hE hG φ ≫
          (externalTensorProductTensorIso X.hom Y.hom E₂ (dualSheaf E) G₂ (dualSheaf G)).hom) ⊤
        (1 : Γ(Limits.pullback X.hom Y.hom, ⊤)) with hD
  have hDinj : Function.Injective D := fun φ ψ h =>
    eq_of_app_externalTensorDualTensorHomEquiv_tensorIso_eq k X Y E E₂ G G₂ hE hG φ ψ h
  have hDadd : ∀ φ φ', D (φ + φ') = D φ + D φ' :=
    app_externalTensorDualTensorHomEquiv_tensorIso_add k X Y E E₂ G G₂ hE hG
  have hDzero : D 0 = 0 :=
    app_externalTensorDualTensorHomEquiv_tensorIso_zero k X Y E E₂ G G₂ hE hG
  have hDneg : ∀ φ, D (-φ) = -D φ :=
    app_externalTensorDualTensorHomEquiv_tensorIso_neg k X Y E E₂ G G₂ hE hG
  set p : FreeAbelianGroup ((E ⟶ E₂) × (G ⟶ G₂)) →+
      (externalTensorProduct X.hom Y.hom E G ⟶ externalTensorProduct X.hom Y.hom E₂ G₂) :=
    FreeAbelianGroup.lift fun q : (E ⟶ E₂) × (G ⟶ G₂) =>
      externalTensorProductMap X.hom Y.hom q.1 q.2 with hp
  -- the comparison bijection out of the tensor product of the two Hom groups
  set Θ := (globalBoxSectionMap k X.hom Y.hom (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G)).comp
    (TensorProduct.congr Φ Ψ).toLinearMap with hΘ
  have hΘbij : Function.Bijective Θ :=
    (bijective_globalBoxSectionMap_of_isProper k X.hom Y.hom
      (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G)).comp (TensorProduct.congr Φ Ψ).bijective
  -- the square commutes
  have hsq : ∀ u, D (p u) = Θ (freeAbelianGroupToTensor k (E ⟶ E₂) (G ⟶ G₂) u) := by
    intro u
    induction u using FreeAbelianGroup.induction_on with
    | zero =>
      simp only [map_zero, hDzero]
      rfl
    | of q =>
      rw [hp, FreeAbelianGroup.lift_apply_of, freeAbelianGroupToTensor_of, hΘ]
      refine Eq.trans (app_externalTensorDualTensorHomEquiv_tensorIso_externalTensorProductMap
        k X Y E E₂ G G₂ hE hG q.1 q.2) ?_
      exact congrArg _ (TensorProduct.congr_tmul Φ Ψ q.1 q.2).symm
    | neg q hq =>
      simp only [map_neg, hDneg, hq]
      rfl
    | add x y hx hy =>
      simp only [map_add, hDadd, hx, hy]
      rfl
  refine ⟨fun φ => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hΘbij.2 (D φ)
    obtain ⟨u, hu⟩ := surjective_freeAbelianGroupToTensor k (E ⟶ E₂) (G ⟶ G₂) t
    exact ⟨u, hDinj ((hsq u).trans (by rw [hu, ht]))⟩
  · refine le_antisymm (fun u hu => ?_) (fun u hu => ?_)
    · simp only [AddMonoidHom.mem_ker] at hu ⊢
      refine hΘbij.1 ?_
      rw [← hsq u, hu, hDzero, map_zero]
      rfl
    · simp only [AddMonoidHom.mem_ker] at hu ⊢
      refine hDinj ?_
      rw [hsq u, hu, hDzero, map_zero]
      rfl

namespace DiagonalResolution

/-- **The hypothesis `hbox` of
`AlgebraicGeometry.exists_kunnethComplex_of_tensorPairings`, discharged.** For `X` proper
over a field `k` and `R` a resolution of the diagonal of `X`, the pairing `(a, b) ↦ a ⊠ b`
exhibits `Hom(ℰᵢ ⊠ 𝒢ᵢ, ℰⱼ ⊠ 𝒢ⱼ)` as `Hom(ℰᵢ, ℰⱼ) ⊗_k Hom(𝒢ᵢ, 𝒢ⱼ)`.

The terms of a `AlgebraicGeometry.DiagonalResolution` are finite locally free by
`AlgebraicGeometry.DiagonalResolution.left_finiteLocallyFree` and `…right_finiteLocallyFree`, so
this is `AlgebraicGeometry.isTensorPairing_externalTensorProductPairing` at `Y = X`. -/
theorem isTensorPairing_boxPairing {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [IsProper X.hom] (R : DiagonalResolution X.hom) (i j : ℕ) :
    letI := modulesLinear k X
    IsTensorPairing k (R.left i ⟶ R.left j) (R.right i ⟶ R.right j) (R.boxPairing i j) :=
  isTensorPairing_externalTensorProductPairing k X X (R.left i) (R.left j) (R.right i)
    (R.right j)
    ((isFiniteLocallyFree_iff_algebraicGeometry (R.left i)).2 (R.left_finiteLocallyFree i))
    ((isFiniteLocallyFree_iff_algebraicGeometry (R.left j)).2 (R.left_finiteLocallyFree j))
    ((isFiniteLocallyFree_iff_algebraicGeometry (R.right i)).2 (R.right_finiteLocallyFree i))
    ((isFiniteLocallyFree_iff_algebraicGeometry (R.right j)).2 (R.right_finiteLocallyFree j))

end DiagonalResolution

/-! ### [Stacks, Tag 0G0A] from the Künneth input on `X ×_k Y` alone -/

attribute [local instance] CategoryTheory.Linear.fullSubcategory
attribute [local instance] isTriangulated_isPerfect_locallySmall

open DiagonalResolution in
/-- **The complex of [Stacks, Tag 0G0A], at the hypotheses of Situation [Stacks, Tag 0G08], from
the Künneth input on `X ×_k Y` alone.** Let `k` be a field, let `X` and `Y` be proper and smooth
over `k`, let `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` be `k`-linear, exact and fully faithful, and let
`R` be a resolution of the diagonal of `X` by external tensor products of finite locally free
modules. Then there is a complex

`… ⟶ ℰ₂ ⊠ F(𝒢₂) ⟶ ℰ₁ ⊠ F(𝒢₁) ⟶ ℰ₀ ⊠ F(𝒢₀)`

on `X ×_k Y` whose term of index `i` is `ℰᵢ ⊠ F(𝒢ᵢ)` and whose differentials are those of `R`,
read through an identification of Hom groups that carries each pure map `a ⊠ b` to `a ⊠ F(b)`.

This is `AlgebraicGeometry.exists_kunnethComplex_of_tensorPairings` with its `hbox` hypothesis
discharged by `AlgebraicGeometry.DiagonalResolution.isTensorPairing_boxPairing`: properness of
`X` over `k` and finite local freeness of the terms of the resolution make the pairing
`(a, b) ↦ a ⊠ b` on `X ×_k X` exhibit `Hom(ℰᵢ ⊠ 𝒢ᵢ, ℰⱼ ⊠ 𝒢ⱼ)` as
`Hom(ℰᵢ, ℰⱼ) ⊗_k Hom(𝒢ᵢ, 𝒢ⱼ)`. The equality of the kernels of the two pairings, the third input
of `AlgebraicGeometry.DiagonalResolution.KunnethHomData`, is discharged there from the
`k`-linearity of `F`.

**The one input still carried is `himage`**, the Künneth formula for Ext of [Stacks, Tag 0FXZ] in
degree `q = 0` at the *other* product: that the pairing `(a, c) ↦ a ⊠ c` exhibits
`Hom_{D(𝒪_{X ×_k Y})}(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))` as `Hom(ℰᵢ, ℰⱼ) ⊗_k Hom(F(𝒢ᵢ), F(𝒢ⱼ))`. It is
carried because it does not follow from the input discharged here: the duality bijection that
proof runs on applies to a finite locally free module in degree zero and `F(𝒢ᵢ)` is an arbitrary
perfect complex, and the Künneth formula on `X ×_k Y` is not a consequence of the one on
`X ×_k X`. What Situation [Stacks, Tag 0G08] *does* give at that product is the second equality
of the source's display, the vanishing of `Ext^{-p}_Y(F(𝒢ᵢ), F(𝒢ⱼ))` for `p > 0`, which is
`AlgebraicGeometry.DiagonalResolution.subsingleton_hom_map_secondFactor_shift`.

`k`-linearity of `F` is with respect to the canonical structures of
`AlgebraicGeometry.modulesLinear`, and exactness is the pair `[F.CommShift ℤ]`,
`[F.IsTriangulated]` that
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Basic` fixes as the convention
for an exact functor of triangulated categories. -/
theorem exists_kunnethComplex_of_imagePairing (k : Type u) [Field k]
    (X Y : Over (Spec (.of k))) [Smooth X.hom] [Smooth Y.hom]
    [IsProper X.hom] [IsProper Y.hom] :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    ∀ (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] [F.IsTriangulated],
      F.Linear k → Nonempty F.FullyFaithful →
      ∀ (R : DiagonalResolution X.hom),
        (∀ i j, IsTensorPairing k (R.left i ⟶ R.left j)
          (F.obj (R.secondFactor i) ⟶ F.obj (R.secondFactor j))
          (R.transformedImagePairing Y.hom F i j)) →
        ∃ T : ImageHomTransport R Y.hom F,
          (∀ i, T.complex.X i = R.imageTerm Y.hom F i) ∧
          (∀ i, T.complex.d (i + 1) i = T.hom (i + 1) i (R.boxDifferential i)) ∧
          ∀ (i j : ℕ) (a : R.left i ⟶ R.left j) (b : R.right i ⟶ R.right j),
            T.hom i j (externalTensorProductMap X.hom X.hom a b) =
              R.transformedMap Y.hom F a b := by
  let _ : Linear k X.left.Modules := modulesLinear k X
  let _ : Linear k Y.left.Modules := modulesLinear k Y
  intro F _ _ hlin hff R himage
  exact exists_kunnethComplex_of_tensorPairings k X Y F hlin hff R
    (fun i j => DiagonalResolution.isTensorPairing_boxPairing X R i j) himage

end AlgebraicGeometry

end
