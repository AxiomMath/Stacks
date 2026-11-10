module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CechKunneth.BoxSections
public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.ChartBoxSectionGeneration

/-!
# The sections of a box product over a product of affine opens

Let `S` be affine, `a : X ⟶ S`, `b : Y ⟶ S`, let `ℱ` and `𝒢` be quasi-coherent, and let
`ψ : k ⟶ Γ(S, 𝒪_S)` be an isomorphism of rings. For affine opens `A ⊆ X` and `B ⊆ Y` the map
`Γ(A, ℱ) ⊗_k Γ(B, 𝒢) ⟶ Γ(pr₁⁻¹A ∩ pr₂⁻¹B, ℱ ⊠ 𝒢)`, `s ⊗ t ↦ s ⊠ t`, is bijective. This is the
statement "the result is true when `X` and `Y` are affine by the definitions (of pullbacks of
quasi-coherent modules and tensor products of quasi-coherent modules)" in the proof of
[Stacks, Tag 0BED], in degree zero; it is what identifies the Čech complex of the product covering
with the Čech complex of the presheaf `(A, B) ↦ Γ(A, ℱ) ⊗_k Γ(B, 𝒢)`.

## Main results

* `Stacks.FibreProductAffineChart.Chart.bijective_modulesPullbackUnitTop_left` and `_right`: the
  sections of `ℱ` over the first factor of a chart are the global sections of its inverse image.
* `Stacks.FibreProductAffineChart.Chart.bijective_boxSectionOfTensor`.
* `Stacks.CechKunneth.bijective_boxMap_app`: the statement above.

## Implementation notes

The proof goes through the chart of `X ×_S Y` whose three opens are `⊤ ⊆ S`, `A` and `B`, where
`Stacks.FibreProductAffineChart.Chart.boxSectionOfTensor` identifies the sections of `ℱ ⊠ 𝒢` with
`Γ(Spec Γ(A), ℱ) ⊗_{Γ(S)} Γ(Spec Γ(B), 𝒢)`. The tensor product over `k` and the one over `Γ(S)`
are compared by hand, along the inverse of `ψ`, as maps of abelian groups: only bijectivity is
claimed, and the two module structures never have to be identified.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry TensorProduct
open Stacks.Tag01VSPullbackTensor
open CommRingCat (ofHom)

universe u

namespace Stacks.FibreProductAffineChart.Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

/-- The component at an open of an isomorphism of modules is injective. -/
private theorem injective_hom_app_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) : Function.Injective (Scheme.Modules.Hom.app e.hom U) :=
  Function.LeftInverse.injective (g := Scheme.Modules.Hom.app e.inv U)
    fun y => congrArg (fun φ : M ⟶ M ↦ Scheme.Modules.Hom.app φ U y) e.hom_inv_id

/-- Restriction between two opens that are each contained in the other is bijective. -/
private theorem bijective_presheaf_map_of_le_of_le {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (h' : U ≤ V) :
    Function.Bijective (M.presheaf.map (homOfLE h).op) :=
  ⟨fun w w' hw => (presheaf_map_map_self M _ (homOfLE h') w).symm.trans
    ((congrArg (M.presheaf.map (homOfLE h').op) hw).trans (presheaf_map_map_self M _ _ w')),
    fun w => ⟨M.presheaf.map (homOfLE h').op w, presheaf_map_map_self M _ _ w⟩⟩

/-- The global section of the inverse image along `Spec Γ(X, U) ⟶ X` attached to a section over
`U` is bijective as soon as it is surjective. -/
private theorem bijective_modulesPullbackUnitTop_fromSpec {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (F : X.Modules) (h : hU.fromSpec ⁻¹ᵁ U = ⊤)
    (himg : hU.fromSpec ''ᵁ ⊤ = U)
    (hs : Function.Surjective (modulesPullbackUnitTop hU.fromSpec F U h)) :
    Function.Bijective (modulesPullbackUnitTop hU.fromSpec F U h) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  refine ⟨fun s s' hss => (bijective_presheaf_map_of_le_of_le F himg.le himg.ge).1 ?_, hs⟩
  have e := fun s => modulesPullbackUnitTop_restrictFunctorIsoPullback hU.fromSpec F U h s himg.le
  exact injective_hom_app_of_iso _ ⊤ (((e s).symm.trans hss).trans (e s'))

/-- **The sections of a module over the first factor of a chart are the global sections of its
inverse image.** -/
theorem bijective_modulesPullbackUnitTop_left (F : X.Modules) :
    Function.Bijective
      (modulesPullbackUnitTop c.fromSpecLeft F c.left c.preimage_fromSpecLeft_left) :=
  bijective_modulesPullbackUnitTop_fromSpec _ F _ c.image_fromSpecLeft_top
    (c.surjective_modulesPullbackUnitTop_left F)

/-- **The sections of a module over the second factor of a chart are the global sections of its
inverse image.** -/
theorem bijective_modulesPullbackUnitTop_right (G : Y.Modules) :
    Function.Bijective
      (modulesPullbackUnitTop c.fromSpecRight G c.right c.preimage_fromSpecRight_right) :=
  bijective_modulesPullbackUnitTop_fromSpec _ G _ c.image_fromSpecRight_top
    (c.surjective_modulesPullbackUnitTop_right G)

/-- The global section of the inverse image along `Spec Γ(X, U) ⟶ X` attached to `r • s` is
`r • s`, the function `r` being read on `Spec Γ(X, U)`. -/
private theorem modulesPullbackUnitTop_fromSpec_smul {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (F : X.Modules) (h : hU.fromSpec ⁻¹ᵁ U = ⊤) (r : Γ(X, U))
    (s : Γ(F, U)) :
    modulesPullbackUnitTop hU.fromSpec F U h (r • s) =
      (Scheme.ΓSpecIso Γ(X, U)).inv.hom r • modulesPullbackUnitTop hU.fromSpec F U h s := by
  refine (congrArg _ (Scheme.Modules.Hom.app_smul _ r s)).trans
    ((Scheme.Modules.map_smul _ _ _ _).trans (congrArg (· • _) ?_))
  change (hU.fromSpec.app U ≫ (Spec Γ(X, U)).presheaf.map (homOfLE h.ge).op).hom r = _
  rw [hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp,
    (Spec Γ(X, U)).presheaf.congr_map (Subsingleton.elim _ (𝟙 _)),
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The global section of the inverse image attached to `r • s` is `r • s`, the function `r` being
read on `Spec Γ(X, U)`. -/
theorem modulesPullbackUnitTop_left_smul (F : X.Modules) (r : Γ(X, c.left)) (s : Γ(F, c.left)) :
    modulesPullbackUnitTop c.fromSpecLeft F c.left c.preimage_fromSpecLeft_left (r • s) =
      (Scheme.ΓSpecIso Γ(X, c.left)).inv.hom r •
        modulesPullbackUnitTop c.fromSpecLeft F c.left c.preimage_fromSpecLeft_left s :=
  modulesPullbackUnitTop_fromSpec_smul c.isAffineOpen_left F _ r s

/-- The global section of the inverse image attached to `r • t` is `r • t`, the function `r` being
read on `Spec Γ(Y, V)`. -/
theorem modulesPullbackUnitTop_right_smul (G : Y.Modules) (r : Γ(Y, c.right)) (t : Γ(G, c.right)) :
    modulesPullbackUnitTop c.fromSpecRight G c.right c.preimage_fromSpecRight_right (r • t) =
      (Scheme.ΓSpecIso Γ(Y, c.right)).inv.hom r •
        modulesPullbackUnitTop c.fromSpecRight G c.right c.preimage_fromSpecRight_right t :=
  modulesPullbackUnitTop_fromSpec_smul c.isAffineOpen_right G _ r t

/-- The global section of an inverse image attached to a local section is additive in it. -/
theorem modulesPullbackUnitTop_add {Z W : Scheme.{u}} (g : Z ⟶ W) (M : W.Modules) (U : W.Opens)
    (hU : g ⁻¹ᵁ U = ⊤) (s s' : Γ(M, U)) :
    modulesPullbackUnitTop g M U hU (s + s') =
      modulesPullbackUnitTop g M U hU s + modulesPullbackUnitTop g M U hU s' :=
  (congrArg _ (map_add _ s s')).trans (map_add _ _ _)

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] leftModuleAlg leftModuleBase leftTower
attribute [local instance] rightModuleAlg rightModuleBase rightTower
attribute [local instance] Stacks.TensorProductPushout.rightModule
  Stacks.TensorProductPushout.rightModule_isScalarTower
  Stacks.TensorProductPushout.smulCommClass_right
  Stacks.TensorProductPushout.pushoutModule
  Stacks.TensorProductPushout.pushoutModule_isScalarTower
attribute [local instance] boxModuleAlg boxModuleBase boxTower

/-- The inverse of the comparison of the restriction along a chart with the inverse image along
it, followed by the comparison, is the identity on the global sections of the inverse image. -/
theorem restrictFunctorIsoPullback_app_hom_inv [Algebra Γ(S, c.base) Γ(X, c.left)]
    [Algebra Γ(S, c.base) Γ(Y, c.right)]
    (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
    (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)
    (M : (pullback a b).Modules)
    (y : Γ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M, ⊤)) :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback ((c.specIso hl hr).inv ≫ c.ι)).app M).hom ⊤
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback
            ((c.specIso hl hr).inv ≫ c.ι)).app M).inv ⊤ y) = y :=
  congrArg
    (fun φ : (Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M ⟶
        (Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M ↦
      Scheme.Modules.Hom.app φ ⊤ y)
    ((Scheme.Modules.restrictFunctorIsoPullback ((c.specIso hl hr).inv ≫ c.ι)).app M).inv_hom_id

/-- The inverse of the comparison of the restriction along a chart with the inverse image along
it is injective on global sections. -/
theorem injective_restrictFunctorIsoPullback_app_inv [Algebra Γ(S, c.base) Γ(X, c.left)]
    [Algebra Γ(S, c.base) Γ(Y, c.right)]
    (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
    (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)
    (M : (pullback a b).Modules) :
    Function.Injective (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback ((c.specIso hl hr).inv ≫ c.ι)).app M).inv ⊤) :=
  injective_hom_app_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback ((c.specIso hl hr).inv ≫ c.ι)).app M).symm ⊤

/-- **The identification of the sections of `ℱ ⊠ 𝒢` over a chart with
`Γ(Spec A, ℱ) ⊗_R Γ(Spec B, 𝒢)` is bijective.** -/
theorem bijective_boxSectionOfTensor [Algebra Γ(S, c.base) Γ(X, c.left)]
    [Algebra Γ(S, c.base) Γ(Y, c.right)]
    (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
    (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (c.boxSectionOfTensor hl hr F G) :=
  ⟨(c.injective_restrictFunctorIsoPullback_app_inv hl hr (externalTensorProduct a b F G)).comp
    (c.boxSectionsEquiv hl hr F G).symm.injective, c.boxSectionOfTensor_surjective hl hr F G⟩

end Stacks.FibreProductAffineChart.Chart


namespace Stacks.CechKunneth

open Stacks.FibreProductAffineChart Stacks.FibreProductAffineChart.Chart

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
attribute [local instance] leftModuleAlg leftModuleBase leftTower
attribute [local instance] rightModuleAlg rightModuleBase rightTower

variable {k : Type u} [CommRing k] {S : Scheme.{u}} (ψ : k →+* Γ(S, ⊤)) {X Y : Scheme.{u}}
  (a : X ⟶ S) (b : Y ⟶ S) (F : X.Modules) (G : Y.Modules)

/-- The chart of `X ×_S Y` with base `⊤` and factors the two components of a pair of affine
opens. -/
def topChart [IsAffine S] (Z : LatProd X.Opens Y.Opens) (hA : IsAffineOpen Z.fst)
    (hB : IsAffineOpen Z.snd) : Chart a b where
  base := ⊤
  left := Z.fst
  right := Z.snd
  isAffineOpen_base := isAffineOpen_top S
  isAffineOpen_left := hA
  isAffineOpen_right := hB
  le_left := show Z.fst ≤ a ⁻¹ᵁ ⊤ from le_top
  le_right := show Z.snd ≤ b ⁻¹ᵁ ⊤ from le_top

section Affine

variable [IsAffine S] (Z : LatProd X.Opens Y.Opens) (hA : IsAffineOpen Z.fst)
  (hB : IsAffineOpen Z.snd)

/-- The algebra structure of the first factor of `topChart` over its base. -/
@[instance_reducible]
def topChartAlgLeft : Algebra Γ(S, (topChart a b Z hA hB).base) Γ(X, (topChart a b Z hA hB).left) :=
  (topChart a b Z hA hB).leftHom.hom.toAlgebra

/-- The algebra structure of the second factor of `topChart` over its base. -/
@[instance_reducible]
def topChartAlgRight :
    Algebra Γ(S, (topChart a b Z hA hB).base) Γ(Y, (topChart a b Z hA hB).right) :=
  (topChart a b Z hA hB).rightHom.hom.toAlgebra

attribute [local instance] topChartAlgLeft topChartAlgRight

/-- The algebra map `Γ(S, ⊤) → Γ(X, A)` of `topChart` is its left structure map. -/
theorem topChart_hl : CommRingCat.ofHom (algebraMap Γ(S, (topChart a b Z hA hB).base)
    Γ(X, (topChart a b Z hA hB).left)) = (topChart a b Z hA hB).leftHom :=
  rfl

/-- The algebra map `Γ(S, ⊤) → Γ(Y, B)` of `topChart` is its right structure map. -/
theorem topChart_hr : CommRingCat.ofHom (algebraMap Γ(S, (topChart a b Z hA hB).base)
    Γ(Y, (topChart a b Z hA hB).right)) = (topChart a b Z hA hB).rightHom :=
  rfl

/-- The sections of `ℱ` over `A`, read as global sections of the inverse image to `Spec Γ(A)`. -/
def leftUnit : (sectionsK X (baseRingHom ψ a) F).obj (op Z.fst) →
    Γ((Scheme.Modules.pullback (topChart a b Z hA hB).fromSpecLeft).obj F, ⊤) :=
  modulesPullbackUnitTop (topChart a b Z hA hB).fromSpecLeft F Z.fst
    (topChart a b Z hA hB).preimage_fromSpecLeft_left

/-- The sections of `𝒢` over `B`, read as global sections of the inverse image to `Spec Γ(B)`. -/
def rightUnit : (sectionsK Y (baseRingHom ψ b) G).obj (op Z.snd) →
    Γ((Scheme.Modules.pullback (topChart a b Z hA hB).fromSpecRight).obj G, ⊤) :=
  modulesPullbackUnitTop (topChart a b Z hA hB).fromSpecRight G Z.snd
    (topChart a b Z hA hB).preimage_fromSpecRight_right

/-- `leftUnit` is bijective. -/
theorem bijective_leftUnit : Function.Bijective (leftUnit ψ a b F Z hA hB) :=
  (topChart a b Z hA hB).bijective_modulesPullbackUnitTop_left F

/-- `rightUnit` is bijective. -/
theorem bijective_rightUnit : Function.Bijective (rightUnit ψ a b G Z hA hB) :=
  (topChart a b Z hA hB).bijective_modulesPullbackUnitTop_right G

/-- `leftUnit` is additive. -/
theorem leftUnit_add (s s' : (sectionsK X (baseRingHom ψ a) F).obj (op Z.fst)) :
    leftUnit ψ a b F Z hA hB (s + s') = leftUnit ψ a b F Z hA hB s + leftUnit ψ a b F Z hA hB s' :=
  modulesPullbackUnitTop_add _ F Z.fst _ s s'

/-- `rightUnit` is additive. -/
theorem rightUnit_add (t t' : (sectionsK Y (baseRingHom ψ b) G).obj (op Z.snd)) :
    rightUnit ψ a b G Z hA hB (t + t') =
      rightUnit ψ a b G Z hA hB t + rightUnit ψ a b G Z hA hB t' :=
  modulesPullbackUnitTop_add _ G Z.snd _ t t'

/-- `leftUnit` carries the action of `x : k` to the action of `ψ x : Γ(S, ⊤)`. -/
theorem leftUnit_smul (x : k) (s : (sectionsK X (baseRingHom ψ a) F).obj (op Z.fst)) :
    leftUnit ψ a b F Z hA hB (x • s) =
      (show Γ(S, (topChart a b Z hA hB).base) from ψ x) • leftUnit ψ a b F Z hA hB s :=
  ((topChart a b Z hA hB).modulesPullbackUnitTop_left_smul F _ s).trans
    (congrArg (· • leftUnit ψ a b F Z hA hB s)
      (congrArg (Scheme.ΓSpecIso Γ(X, Z.fst)).inv.hom (map_baseRingHom ψ a Z.fst x)))

/-- `rightUnit` carries the action of `x : k` to the action of `ψ x : Γ(S, ⊤)`. -/
theorem rightUnit_smul (x : k) (t : (sectionsK Y (baseRingHom ψ b) G).obj (op Z.snd)) :
    rightUnit ψ a b G Z hA hB (x • t) =
      (show Γ(S, (topChart a b Z hA hB).base) from ψ x) • rightUnit ψ a b G Z hA hB t :=
  ((topChart a b Z hA hB).modulesPullbackUnitTop_right_smul G _ t).trans
    (congrArg (· • rightUnit ψ a b G Z hA hB t)
      (congrArg (Scheme.ΓSpecIso Γ(Y, Z.snd)).inv.hom (map_baseRingHom ψ b Z.snd x)))

/-- The comparison `Γ(A, ℱ) ⊗_k Γ(B, 𝒢) ⟶ Γ(Spec Γ(A), ℱ) ⊗_{Γ(S)} Γ(Spec Γ(B), 𝒢)`. -/
def toChartTensor :
    (sectionsK X (baseRingHom ψ a) F).obj (op Z.fst) ⊗[k]
        (sectionsK Y (baseRingHom ψ b) G).obj (op Z.snd) →+
      Γ((Scheme.Modules.pullback (topChart a b Z hA hB).fromSpecLeft).obj F, ⊤) ⊗[
        Γ(S, (topChart a b Z hA hB).base)]
        Γ((Scheme.Modules.pullback (topChart a b Z hA hB).fromSpecRight).obj G, ⊤) :=
  TensorProduct.liftAddHom (R := k)
    (AddMonoidHom.mk' (fun s => AddMonoidHom.mk'
      (fun t => leftUnit ψ a b F Z hA hB s ⊗ₜ rightUnit ψ a b G Z hA hB t)
      fun t t' => by rw [rightUnit_add, tmul_add])
      fun s s' => AddMonoidHom.ext fun t => by
        simp only [AddMonoidHom.add_apply, AddMonoidHom.mk'_apply]
        rw [leftUnit_add, add_tmul])
    fun x s t => by
      change leftUnit ψ a b F Z hA hB (x • s) ⊗ₜ rightUnit ψ a b G Z hA hB t =
        leftUnit ψ a b F Z hA hB s ⊗ₜ rightUnit ψ a b G Z hA hB (x • t)
      rw [leftUnit_smul, rightUnit_smul, smul_tmul]

/-- `toChartTensor` sends `s ⊗ₜ t` to `leftUnit s ⊗ₜ rightUnit t`. -/
theorem toChartTensor_tmul (s : (sectionsK X (baseRingHom ψ a) F).obj (op Z.fst))
    (t : (sectionsK Y (baseRingHom ψ b) G).obj (op Z.snd)) :
    toChartTensor ψ a b F G Z hA hB (s ⊗ₜ t) =
      leftUnit ψ a b F Z hA hB s ⊗ₜ rightUnit ψ a b G Z hA hB t :=
  rfl

/-- The inverse of `leftUnit`. -/
def leftUnitInv : Γ((Scheme.Modules.pullback (topChart a b Z hA hB).fromSpecLeft).obj F, ⊤) →
    (sectionsK X (baseRingHom ψ a) F).obj (op Z.fst) :=
  (Equiv.ofBijective _ (bijective_leftUnit ψ a b F Z hA hB)).symm

/-- The inverse of `rightUnit`. -/
def rightUnitInv : Γ((Scheme.Modules.pullback (topChart a b Z hA hB).fromSpecRight).obj G, ⊤) →
    (sectionsK Y (baseRingHom ψ b) G).obj (op Z.snd) :=
  (Equiv.ofBijective _ (bijective_rightUnit ψ a b G Z hA hB)).symm

/-- `leftUnitInv` is a right inverse of `leftUnit`. -/
theorem leftUnit_leftUnitInv (m) : leftUnit ψ a b F Z hA hB (leftUnitInv ψ a b F Z hA hB m) = m :=
  (Equiv.ofBijective _ (bijective_leftUnit ψ a b F Z hA hB)).apply_symm_apply m

/-- `rightUnitInv` is a right inverse of `rightUnit`. -/
theorem rightUnit_rightUnitInv (n) :
    rightUnit ψ a b G Z hA hB (rightUnitInv ψ a b G Z hA hB n) = n :=
  (Equiv.ofBijective _ (bijective_rightUnit ψ a b G Z hA hB)).apply_symm_apply n

/-- `leftUnitInv` is a left inverse of `leftUnit`. -/
theorem leftUnitInv_leftUnit (s) : leftUnitInv ψ a b F Z hA hB (leftUnit ψ a b F Z hA hB s) = s :=
  (Equiv.ofBijective _ (bijective_leftUnit ψ a b F Z hA hB)).symm_apply_apply s

/-- `rightUnitInv` is a left inverse of `rightUnit`. -/
theorem rightUnitInv_rightUnit (t) :
    rightUnitInv ψ a b G Z hA hB (rightUnit ψ a b G Z hA hB t) = t :=
  (Equiv.ofBijective _ (bijective_rightUnit ψ a b G Z hA hB)).symm_apply_apply t

/-- The comparison back, along the inverse of `ψ`. -/
def ofChartTensor (hψ : Function.Bijective ψ) :
    Γ((Scheme.Modules.pullback (topChart a b Z hA hB).fromSpecLeft).obj F, ⊤) ⊗[
        Γ(S, (topChart a b Z hA hB).base)]
        Γ((Scheme.Modules.pullback (topChart a b Z hA hB).fromSpecRight).obj G, ⊤) →+
      (sectionsK X (baseRingHom ψ a) F).obj (op Z.fst) ⊗[k]
        (sectionsK Y (baseRingHom ψ b) G).obj (op Z.snd) :=
  TensorProduct.liftAddHom (R := Γ(S, (topChart a b Z hA hB).base))
    (AddMonoidHom.mk' (fun m => AddMonoidHom.mk'
      (fun n => leftUnitInv ψ a b F Z hA hB m ⊗ₜ rightUnitInv ψ a b G Z hA hB n)
      fun n n' => by
        rw [← tmul_add]
        refine congrArg _ ((bijective_rightUnit ψ a b G Z hA hB).1 ?_)
        rw [rightUnit_add, rightUnit_rightUnitInv, rightUnit_rightUnitInv,
          rightUnit_rightUnitInv])
      fun m m' => AddMonoidHom.ext fun n => by
        simp only [AddMonoidHom.add_apply, AddMonoidHom.mk'_apply]
        rw [← add_tmul]
        refine congrArg (· ⊗ₜ[k] _) ((bijective_leftUnit ψ a b F Z hA hB).1 ?_)
        rw [leftUnit_add, leftUnit_leftUnitInv, leftUnit_leftUnitInv, leftUnit_leftUnitInv])
    fun r m n => by
      obtain ⟨x, rfl⟩ := hψ.2 r
      have e1 : leftUnitInv ψ a b F Z hA hB ((show Γ(S, (topChart a b Z hA hB).base) from ψ x) • m)
          = x • leftUnitInv ψ a b F Z hA hB m :=
        (bijective_leftUnit ψ a b F Z hA hB).1 (by
          rw [leftUnit_leftUnitInv, leftUnit_smul, leftUnit_leftUnitInv])
      have e2 : rightUnitInv ψ a b G Z hA hB
          ((show Γ(S, (topChart a b Z hA hB).base) from ψ x) • n) =
          x • rightUnitInv ψ a b G Z hA hB n :=
        (bijective_rightUnit ψ a b G Z hA hB).1 (by
          rw [rightUnit_rightUnitInv, rightUnit_smul, rightUnit_rightUnitInv])
      change leftUnitInv ψ a b F Z hA hB ((show Γ(S, (topChart a b Z hA hB).base) from ψ x) • m) ⊗ₜ
          rightUnitInv ψ a b G Z hA hB n =
        leftUnitInv ψ a b F Z hA hB m ⊗ₜ rightUnitInv ψ a b G Z hA hB
          ((show Γ(S, (topChart a b Z hA hB).base) from ψ x) • n)
      rw [e1, e2, smul_tmul]

/-- `ofChartTensor` is a left inverse of `toChartTensor`. -/
theorem ofChartTensor_toChartTensor (hψ : Function.Bijective ψ)
    (y : (sectionsK X (baseRingHom ψ a) F).obj (op Z.fst) ⊗[k]
      (sectionsK Y (baseRingHom ψ b) G).obj (op Z.snd)) :
    ofChartTensor ψ a b F G Z hA hB hψ (toChartTensor ψ a b F G Z hA hB y) = y := by
  induction y using TensorProduct.inductionOn with
  | tmul s t =>
    change leftUnitInv ψ a b F Z hA hB (leftUnit ψ a b F Z hA hB s) ⊗ₜ
      rightUnitInv ψ a b G Z hA hB (rightUnit ψ a b G Z hA hB t) = s ⊗ₜ t
    rw [leftUnitInv_leftUnit, rightUnitInv_rightUnit]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']

/-- `ofChartTensor` is a right inverse of `toChartTensor`. -/
theorem toChartTensor_ofChartTensor (hψ : Function.Bijective ψ)
    (z : Γ((Scheme.Modules.pullback (topChart a b Z hA hB).fromSpecLeft).obj F, ⊤) ⊗[Γ(S,
        (topChart a b Z hA hB).base)]
        Γ((Scheme.Modules.pullback (topChart a b Z hA hB).fromSpecRight).obj G, ⊤)) :
    toChartTensor ψ a b F G Z hA hB (ofChartTensor ψ a b F G Z hA hB hψ z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
    change leftUnit ψ a b F Z hA hB (leftUnitInv ψ a b F Z hA hB m) ⊗ₜ
      rightUnit ψ a b G Z hA hB (rightUnitInv ψ a b G Z hA hB n) = m ⊗ₜ n
    rw [leftUnit_leftUnitInv, rightUnit_rightUnitInv]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- The image of `Spec (Γ(X, A) ⊗_{Γ(S)} Γ(Y, B)) ⟶ X ×_S Y` through `topChart` is the open
`pr₁⁻¹A ∩ pr₂⁻¹B`. -/
theorem image_topChart :
    (((topChart a b Z hA hB).specIso (topChart_hl a b Z hA hB) (topChart_hr a b Z hA hB)).inv ≫
      (topChart a b Z hA hB).ι) ''ᵁ ⊤ = (boxOpen a b).obj Z :=
  ((topChart a b Z hA hB).image_specIso_inv_ι_top _ _).trans (topChart a b Z hA hB).opensRange_ι

/-- The box section map, followed by the restriction to the image of the chart, is the chart
identification of `Γ(Spec Γ(A), ℱ) ⊗_{Γ(S)} Γ(Spec Γ(B), 𝒢)` after `toChartTensor`. -/
theorem restrict_boxMap_app [F.IsQuasicoherent] [G.IsQuasicoherent]
    (y : (sectionsK X (baseRingHom ψ a) F).obj (op Z.fst) ⊗[k]
      (sectionsK Y (baseRingHom ψ b) G).obj (op Z.snd)) :
    (externalTensorProduct a b F G).presheaf.map
        (homOfLE (image_topChart a b Z hA hB).le).op (((boxMap ψ a b F G).app (op Z)).hom y) =
      (topChart a b Z hA hB).boxSectionOfTensor (topChart_hl a b Z hA hB)
        (topChart_hr a b Z hA hB) F G (toChartTensor ψ a b F G Z hA hB y) := by
  induction y using TensorProduct.inductionOn with
  | tmul s t =>
    refine (externalTensorSection_presheaf_map a b F G (U := Z.fst) (V := Z.snd) s t _ _
      ((image_topChart a b Z hA hB).le.trans (boxOpen_le_fst a b Z))
      ((image_topChart a b Z hA hB).le.trans (boxOpen_le_snd a b Z)) _).trans ?_
    exact ((topChart a b Z hA hB).boxSectionOfTensor_tmul _ _ F G
      ((image_topChart a b Z hA hB).le.trans (boxOpen_le_fst a b Z))
      ((image_topChart a b Z hA hB).le.trans (boxOpen_le_snd a b Z)) s t).symm
  | add y y' hy hy' =>
    refine ((congrArg ((externalTensorProduct a b F G).presheaf.map
      (homOfLE (image_topChart a b Z hA hB).le).op)
      (map_add ((boxMap ψ a b F G).app (op Z)).hom y y')).trans (map_add _ _ _)).trans ?_
    refine (congrArg₂ (· + ·) hy hy').trans ?_
    refine Eq.trans ?_ (congrArg ((topChart a b Z hA hB).boxSectionOfTensor _ _ F G)
      (map_add (toChartTensor ψ a b F G Z hA hB) y y')).symm
    exact ((topChart a b Z hA hB).boxSectionOfTensor_add _ _ F G _ _).symm

/-- **For a pair of affine opens of `X` and `Y` over an affine `S`, and `ψ : k ≅ Γ(S, 𝒪_S)`, the
map `Γ(A, ℱ) ⊗_k Γ(B, 𝒢) ⟶ Γ(pr₁⁻¹A ∩ pr₂⁻¹B, ℱ ⊠ 𝒢)`, `s ⊗ t ↦ s ⊠ t`, is bijective.** -/
theorem bijective_boxMap_app (hψ : Function.Bijective ψ) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (hA : IsAffineOpen Z.fst) (hB : IsAffineOpen Z.snd) :
    Function.Bijective ((boxMap ψ a b F G).app (op Z)).hom := by
  have hρ := bijective_presheaf_map_of_le_of_le (externalTensorProduct a b F G)
    (image_topChart a b Z hA hB).le (image_topChart a b Z hA hB).ge
  have hβ := (topChart a b Z hA hB).bijective_boxSectionOfTensor (topChart_hl a b Z hA hB)
    (topChart_hr a b Z hA hB) F G
  refine ⟨fun y y' h => ?_, fun w => ?_⟩
  · have h' := congrArg ((externalTensorProduct a b F G).presheaf.map
      (homOfLE (image_topChart a b Z hA hB).le).op) h
    have e := (restrict_boxMap_app ψ a b F G Z hA hB y).symm.trans
      (h'.trans (restrict_boxMap_app ψ a b F G Z hA hB y'))
    exact (ofChartTensor_toChartTensor ψ a b F G Z hA hB hψ y).symm.trans
      ((congrArg (ofChartTensor ψ a b F G Z hA hB hψ) (hβ.1 e)).trans
        (ofChartTensor_toChartTensor ψ a b F G Z hA hB hψ y'))
  · obtain ⟨z, hz⟩ := hβ.2 ((externalTensorProduct a b F G).presheaf.map
      (homOfLE (image_topChart a b Z hA hB).le).op w)
    exact ⟨ofChartTensor ψ a b F G Z hA hB hψ z,
      hρ.1 ((restrict_boxMap_app ψ a b F G Z hA hB _).trans
        ((congrArg _ (toChartTensor_ofChartTensor ψ a b F G Z hA hB hψ z)).trans hz))⟩

end Affine

end Stacks.CechKunneth

end
