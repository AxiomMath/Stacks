module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.ChartBoxSectionGeneration
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors

/-!
# The canonical map from a tensor product of global sections to the global sections of a box
product

Let `k` be a field, let `a : X ⟶ Spec k` and `b : Y ⟶ Spec k`, and let `P` and `Q` be modules on
`X` and on `Y`. The section of `P ⊠ Q` attached to a pair of global sections,
`Stacks.Tag01VSPullbackTensor.externalTensorSection` read over `⊤`, is additive in each argument;
this file proves it `k`-*bilinear* and so assembles from it the canonical comparison map

`Γ(X, P) ⊗_k Γ(Y, Q) ⟶ Γ(X ×_k Y, P ⊠ Q)`,  `s ⊗ t ↦ s ⊠ t`,

which the library did not previously construct. It is a map of `k`-vector spaces between the
objects `AlgebraicGeometry.globalSectionsOverField` names, so no transport along
`AlgebraicGeometry.Scheme.ΓSpecIso` is owed by its consumers: that transport is built into
`AlgebraicGeometry.globalSectionsOverField` itself and is discharged here once, in
`AlgebraicGeometry.appLE_fst_comp_scalars` and `AlgebraicGeometry.appLE_snd_comp_scalars`.

## Main definitions

* `AlgebraicGeometry.globalBoxSectionBilin`: the pairing `(s, t) ↦ s ⊠ t` as a `k`-bilinear map.
* `AlgebraicGeometry.globalBoxSectionMap`: the induced map out of `Γ(X, P) ⊗_k Γ(Y, Q)`, with
  `AlgebraicGeometry.globalBoxSectionMap_tmul` its value on a pure tensor.

## Main results

* `Stacks.Tag01VSPullbackTensor.modulesPullbackUnit_smul`: the unit of `g ^* ⊣ g _*` on sections
  is semilinear over `g`.
* `Stacks.Tag01VSPullbackTensor.externalTensorSection_smul_left` and `..._smul_right`: the
  section of `F ⊠ G` attached to a pair of local sections is semilinear in each argument, over
  the respective projection.
* `AlgebraicGeometry.externalTensorSection_top_smul_left` and `..._smul_right`: over a field
  those two laws become the two `k`-linearity laws, because both projections carry the ground
  field into the structure sheaf of `X ×_k Y` by the same ring map.

## Implementation notes

The `k`-action on `Γ(X, P)` is `ModuleCat.restrictScalars` along
`AlgebraicGeometry.globalSectionsScalars`, so `c • s` is *definitionally* the action of
`globalSectionsScalars k a c` on `s`. The two `k`-linearity fields of
`AlgebraicGeometry.globalBoxSectionBilin` are therefore the `Γ`-level semilinearity lemmas
applied directly, with no rewriting: stating them at the `k`-level instead fails, because
`Module ↑Γ(X, ⊤) ↑(globalSectionsOverField k a P)` is not found by instance search — the same
failure recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.BoxProductSections`.

The two inclusions `⊤ ≤ pullback.fst a b ⁻¹ᵁ ⊤` are named, as
`AlgebraicGeometry.boxTopFst` and `AlgebraicGeometry.boxTopSnd`, rather than written `le_top`:
`le_top` forces its right-hand side to be literally `⊤`, so the resulting proof term has a type
only definitionally equal to the one `externalTensorSection` expects, and `rw` then fails on a
motive that is not type-correct.

## References

* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry CommRingCat RingHomClass
open Stacks.Tag01VSPullbackTensor

universe u

namespace Stacks.Tag01VSPullbackTensor

/-- The unit of `g ^* ⊣ g _*` on sections is semilinear over `g`. -/
theorem modulesPullbackUnit_smul {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules) (U : Y.Opens)
    (r : Γ(Y, U)) (s : Γ(F, U)) :
    modulesPullbackUnit g F U (r • s)
      = g.app U r • modulesPullbackUnit g F U s := by
  unfold modulesPullbackUnit
  rw [Scheme.Modules.Hom.app_smul]
  rfl

/-- The section of `F ⊠ G` attached to a pair of local sections is semilinear in its first
argument. -/
theorem externalTensorSection_smul_left {S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S)
    (F : P.Modules) (G : Q.Modules) {U : P.Opens} {V : Q.Opens} (r : Γ(P, U)) (x : Γ(F, U))
    (y : Γ(G, V)) (W : (pullback p q).Opens) (hW₁ : W ≤ pullback.fst p q ⁻¹ᵁ U)
    (hW₂ : W ≤ pullback.snd p q ⁻¹ᵁ V) :
    externalTensorSection p q F G (r • x) y W hW₁ hW₂
      = (pullback.fst p q).appLE U W hW₁ r • externalTensorSection p q F G x y W hW₁ hW₂ := by
  unfold externalTensorSection
  rw [modulesPullbackUnit_smul, Scheme.Modules.map_smul]
  exact Stacks.Cohomology.Generators.toTensorSheafSection_smul_left _ _ _ _ _ _ _

/-- The section of `F ⊠ G` attached to a pair of local sections is semilinear in its second
argument. -/
theorem externalTensorSection_smul_right {S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S)
    (F : P.Modules) (G : Q.Modules) {U : P.Opens} {V : Q.Opens} (r : Γ(Q, V)) (x : Γ(F, U))
    (y : Γ(G, V)) (W : (pullback p q).Opens) (hW₁ : W ≤ pullback.fst p q ⁻¹ᵁ U)
    (hW₂ : W ≤ pullback.snd p q ⁻¹ᵁ V) :
    externalTensorSection p q F G x (r • y) W hW₁ hW₂
      = (pullback.snd p q).appLE V W hW₂ r • externalTensorSection p q F G x y W hW₁ hW₂ := by
  unfold externalTensorSection
  rw [modulesPullbackUnit_smul, Scheme.Modules.map_smul]
  exact Stacks.Cohomology.Generators.toTensorSheafSection_smul_right _ _ _ _ _ _ _

end Stacks.Tag01VSPullbackTensor

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k))

/-- The structure morphism of the fibre product `X ×_k Y` over `Spec k`. -/
abbrev boxBase : pullback a b ⟶ Spec (.of k) := pullback.fst a b ≫ a

/-- The first projection carries the `k`-structure of `X` to that of `X ×_k Y`. -/
theorem appLE_fst_comp_scalars :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ a.appLE ⊤ ⊤ (by simp)) ≫
        (pullback.fst a b).appLE ⊤ ⊤ (by simp)
      = (Scheme.ΓSpecIso (.of k)).inv ≫ (boxBase k a b).appLE ⊤ ⊤ (by simp) := by
  rw [Category.assoc, Scheme.Hom.appLE_comp_appLE]

/-- The second projection carries the `k`-structure of `Y` to that of `X ×_k Y`. -/
theorem appLE_snd_comp_scalars :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ b.appLE ⊤ ⊤ (by simp)) ≫
        (pullback.snd a b).appLE ⊤ ⊤ (by simp)
      = (Scheme.ΓSpecIso (.of k)).inv ≫ (boxBase k a b).appLE ⊤ ⊤ (by simp) := by
  rw [Category.assoc, Scheme.Hom.appLE_comp_appLE, boxBase, pullback.condition]

/-- The whole of `X ×_k Y` lies in the preimage of the whole of `X`. -/
theorem boxTopFst : (⊤ : (pullback a b).Opens) ≤ pullback.fst a b ⁻¹ᵁ (⊤ : X.Opens) :=
  (Scheme.Hom.preimage_top (pullback.fst a b)).ge

/-- The whole of `X ×_k Y` lies in the preimage of the whole of `Y`. -/
theorem boxTopSnd : (⊤ : (pullback a b).Opens) ≤ pullback.snd a b ⁻¹ᵁ (⊤ : Y.Opens) :=
  (Scheme.Hom.preimage_top (pullback.snd a b)).ge

variable (P : X.Modules) (Q : Y.Modules)

/-- The ring map along which `AlgebraicGeometry.globalSectionsOverField` restricts scalars:
the ground field into the global functions of `X`. -/
abbrev globalSectionsScalars : CommRingCat.of k ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ a.appLE ⊤ ⊤ (by simp)

/-- **The global box section is `k`-linear in its first argument.** -/
theorem externalTensorSection_top_smul_left (c : k) (s : ↑Γ(P, ⊤)) (t : ↑Γ(Q, ⊤)) :
    externalTensorSection a b P Q (globalSectionsScalars k a c • s) t ⊤
        (boxTopFst k a b) (boxTopSnd k a b)
      = globalSectionsScalars k (boxBase k a b) c
          • externalTensorSection a b P Q s t ⊤ (boxTopFst k a b) (boxTopSnd k a b) := by
  rw [Stacks.Tag01VSPullbackTensor.externalTensorSection_smul_left]
  exact congrArg (· • externalTensorSection a b P Q s t ⊤ (boxTopFst k a b) (boxTopSnd k a b))
    (ConcreteCategory.congr_hom (appLE_fst_comp_scalars k a b) c)

/-- **The global box section is `k`-linear in its second argument.** -/
theorem externalTensorSection_top_smul_right (c : k) (s : ↑Γ(P, ⊤)) (t : ↑Γ(Q, ⊤)) :
    externalTensorSection a b P Q s (globalSectionsScalars k b c • t) ⊤
        (boxTopFst k a b) (boxTopSnd k a b)
      = globalSectionsScalars k (boxBase k a b) c
          • externalTensorSection a b P Q s t ⊤ (boxTopFst k a b) (boxTopSnd k a b) := by
  rw [Stacks.Tag01VSPullbackTensor.externalTensorSection_smul_right]
  exact congrArg (· • externalTensorSection a b P Q s t ⊤ (boxTopFst k a b) (boxTopSnd k a b))
    (ConcreteCategory.congr_hom (appLE_snd_comp_scalars k a b) c)

/-- **The canonical pairing of global sections into the global sections of a box product.** -/
def globalBoxSectionBilin :
    ↑(globalSectionsOverField k a P) →ₗ[k] ↑(globalSectionsOverField k b Q) →ₗ[k]
      ↑(globalSectionsOverField k (boxBase k a b) (externalTensorProduct a b P Q)) :=
  LinearMap.mk₂ k
    (fun s t => externalTensorSection a b P Q s t ⊤ (boxTopFst k a b) (boxTopSnd k a b))
    (fun s s' t => Stacks.Tag01VSPullbackTensor.externalTensorSection_add_left
      a b P Q s s' t ⊤ (boxTopFst k a b) (boxTopSnd k a b))
    (fun c s t => externalTensorSection_top_smul_left k a b P Q c s t)
    (fun s t t' => Stacks.Tag01VSPullbackTensor.externalTensorSection_add_right
      a b P Q s t t' ⊤ (boxTopFst k a b) (boxTopSnd k a b))
    (fun c s t => externalTensorSection_top_smul_right k a b P Q c s t)

/-- **The canonical comparison map `Γ(X, P) ⊗_k Γ(Y, Q) ⟶ Γ(X ×_k Y, P ⊠ Q)`.** -/
def globalBoxSectionMap :
    TensorProduct k ↑(globalSectionsOverField k a P) ↑(globalSectionsOverField k b Q) →ₗ[k]
      ↑(globalSectionsOverField k (boxBase k a b) (externalTensorProduct a b P Q)) :=
  TensorProduct.lift (globalBoxSectionBilin k a b P Q)

/-- The comparison map `globalBoxSectionMap` sends `s ⊗ t` to the external tensor product
section `s ⊠ t` over the whole box product. -/
@[simp] theorem globalBoxSectionMap_tmul (s : ↑(globalSectionsOverField k a P))
    (t : ↑(globalSectionsOverField k b Q)) :
    globalBoxSectionMap k a b P Q (s ⊗ₜ[k] t)
      = externalTensorSection a b P Q s t ⊤ (boxTopFst k a b) (boxTopSnd k a b) := rfl

end AlgebraicGeometry

end
