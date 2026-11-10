module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingCategory
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.Localization.Glueing.Modules
public import StacksFrontier.Topology.Sheaves.Glueing.Equivalence
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence.BaseChangeFunctor
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence.LeftQuasiInverse
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence.UnitIdeal
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence.BaseChangeFunctor

/-!
# Formal glueing of module categories: base change

Flat base change carries module glueing data for `R → S` to module glueing data for the
base-changed map `R' → S ⊗[R] R'`, compatibly with both `Can` and `H⁰`. This file constructs the
two natural isomorphisms making the squares of the canonical diagram commute.

It then begins the general case of the formal glueing theorem: the local components of the counit
of compatible sections are bijective, and its generic component is injective and becomes
bijective after localization away from each `fᵢ`.

## Main results

* `FormalGlueing.exists_baseChange_commuting_with_canonical_and_sections`: flat base change gives
  a functor between the glueing categories and makes both squares of the canonical diagram
  commute.

## Implementation notes

For base change, the middle vertical functor is characterized componentwise: its generic module
is scalar extension along `S → S ⊗[R] R'`, its local module at `fᵢ` is scalar extension along
`R[1/fᵢ] → R'[1/fᵢ]`, and these identifications intertwine its action on every morphism with
scalar extension. Canonical base-change comparisons for the generic localization, the
generic/local tensor product, and the local/local overlaps are specified on their generators,
and the two families of overlap isomorphisms are required to commute with those comparisons.
Commutativity of each square of functors is expressed by a natural isomorphism. All module
categories are taken in a common universe large enough for the rings involved.

## References

* [Stacks Project, Tag 05EQ](https://stacks.math.columbia.edu/tag/05EQ)
-/

section

namespace FormalGlueing

universe u v x w

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TensorProduct
open scoped ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem genericLocalTensorEquiv_tensor
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (a : R) (M : ModuleCat (Localization.Away a))
    (t : S ⊗[R] B) (b : B)
    (m : (ModuleCat.restrictScalars (algebraMap R (Localization.Away a))).obj M) :
    genericLocalTensorEquiv S B a M
      (t ⊗ₜ[B] (awayTensorEquiv B a M).symm (b ⊗ₜ[R] m)) =
      (b • t) ⊗ₜ[S] (1 ⊗ₜ[R] m) := by
  dsimp only [genericLocalTensorEquiv, LinearEquiv.trans_apply]
  rw [AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    LinearEquiv.apply_symm_apply]
  rw [AlgebraTensorModule.cancelBaseChange_tmul,
    AlgebraTensorModule.cancelBaseChange_symm_tmul]

private theorem genericLocalTensorEquiv_one_tmul
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (a : R) (M : ModuleCat (Localization.Away a))
    (b : B) (m : (ModuleCat.restrictScalars (algebraMap R (Localization.Away a))).obj M) :
    genericLocalTensorEquiv S B a M
      (1 ⊗ₜ[B] (awayTensorEquiv B a M).symm (b ⊗ₜ[R] m)) =
      algebraMap B (S ⊗[R] B) b ⊗ₜ[S] (1 ⊗ₜ[R] m) := by
  rw [genericLocalTensorEquiv_tensor, Algebra.smul_def, mul_one]

private theorem sectionDefect_baseChange
    {R : Type u} (S : Type v) (B : Type x)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons.{u, max u v x w} f}
    (X : FormalGlueing.ModuleGlueingDatum.{u, v, max u v x w} S f c)
    (z : sectionAmbient (S ⊗[R] B) (fun i => algebraMap R B (f i))
      (baseChangeDatum.{u, v, x, w} S B f X)) :
    relationsBaseEquiv.{u, v, x, w} S B f X
      (sectionDefect (S ⊗[R] B) (fun i => algebraMap R B (f i))
        (baseChangeDatum.{u, v, x, w} S B f X) z) =
      (sectionDefect S f X).baseChange B (ambientBaseEquiv.{u, v, x, w} S B f X z) := by
  obtain ⟨y, rfl⟩ := (ambientBaseEquiv.{u, v, x, w} S B f X).symm.surjective z
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => simpa only [map_add] using congrArg₂ (· + ·) hy hy'
  | tmul b z =>
    rw [LinearEquiv.apply_symm_apply, LinearMap.baseChange_tmul,
      ambientBaseEquiv_symm_tmul]
    apply (TensorProduct.prodRight R B B _ _).injective
    simp only [relationsBaseEquiv, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.prodCongr_apply, TensorProduct.prodRight_tmul]
    apply Prod.ext
    · apply (TensorProduct.piRight R B B _).injective
      simp only [LinearEquiv.apply_symm_apply,
        TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
      funext i
      change pushoutTensorEquiv R S B (S ⊗[R] B) _
        (genericLocalTensorEquiv S B (f i) (X.localPiece i)
          (baseChangeAlpha S B f X i (LocalizedModule.mkLinearMap _ _
            ((genericBaseEquiv S B X.generic).symm (b ⊗ₜ[R] z.1))) -
              1 ⊗ₜ[B] (awayTensorEquiv B (f i) (X.localPiece i)).symm (b ⊗ₜ[R] z.2 i))) =
        b ⊗ₜ[R] (X.alpha i (LocalizedModule.mkLinearMap _ _ z.1) - 1 ⊗ₜ[R] z.2 i)
      rw [map_sub, map_sub, baseChangeAlpha_commutes, genericBaseEquiv_symm_tmul,
        genericLocalizationEquiv_mk, genericLocalTensorEquiv_one_tmul]
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
        pushoutTensorEquiv_tmul, tmul_sub]
    · apply (TensorProduct.piRight R B B _).injective
      simp only [LinearEquiv.apply_symm_apply,
        TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
      funext i
      apply (TensorProduct.piRight R B B _).injective
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.piCongrRight_apply,
        TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
      funext j
      change localOverlapEquiv B f j (X.localPiece j) {i}
        (baseChangeAlphaIJ S B f X i j (LocalizedModule.mkLinearMap _ _
          ((awayTensorEquiv B (f i) (X.localPiece i)).symm (b ⊗ₜ[R] z.2 i))) -
          LocalizedModule.mkLinearMap _ _
            ((awayTensorEquiv B (f j) (X.localPiece j)).symm (b ⊗ₜ[R] z.2 j))) =
        b ⊗ₜ[R] (X.alphaIJ i j (LocalizedModule.mkLinearMap _ _ (z.2 i)) -
          LocalizedModule.mkLinearMap _ _ (z.2 j))
      rw [map_sub, baseChangeAlphaIJ_commutes, localOverlapEquiv_mk_tensor,
        localOverlapEquiv_mk_tensor]
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe, tmul_sub]

private noncomputable def sectionsBaseEquiv
    {R : Type u} (S : Type v) (B : Type x)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    [Module.Flat R B] {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons.{u, max u v x w} f}
    (X : FormalGlueing.ModuleGlueingDatum.{u, v, max u v x w} S f c) :
    B ⊗[R] FormalGlueing.compatibleSections S f c X ≃ₗ[B]
      FormalGlueing.compatibleSections (S ⊗[R] B) (fun i => algebraMap R B (f i))
        (FormalGlueing.localizationComparisons _) (baseChangeDatum.{u, v, x, w} S B f X) :=
  AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (LinearEquiv.ofEq _ _ (compatibleSections_eq_ker S f X)) ≪≫ₗ
    flatKernelEquiv B (sectionDefect S f X)
      (sectionDefect (S ⊗[R] B) (fun i => algebraMap R B (f i))
        (baseChangeDatum.{u, v, x, w} S B f X))
      (ambientBaseEquiv.{u, v, x, w} S B f X)
      (relationsBaseEquiv.{u, v, x, w} S B f X)
      (sectionDefect_baseChange.{u, v, x, w} S B f X) ≪≫ₗ
    LinearEquiv.ofEq _ _ (compatibleSections_eq_ker _ _ _).symm

private theorem sectionsBaseEquiv_tmul
    {R : Type u} (S : Type v) (B : Type x)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    [Module.Flat R B] {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons.{u, max u v x w} f}
    (X : FormalGlueing.ModuleGlueingDatum.{u, v, max u v x w} S f c)
    (b : B) (z : FormalGlueing.compatibleSections S f c X) :
    (sectionsBaseEquiv.{u, v, x, w} S B f X (b ⊗ₜ[R] z)).1 =
      ((genericBaseEquiv S B X.generic).symm (b ⊗ₜ[R] z.1.1),
        fun i => (awayTensorEquiv B (f i) (X.localPiece i)).symm (b ⊗ₜ[R] z.1.2 i)) := by
  dsimp only [sectionsBaseEquiv, LinearEquiv.trans_apply]
  simp only [LinearEquiv.coe_ofEq_apply, AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    flatKernelEquiv_tmul]
  exact ambientBaseEquiv_symm_tmul.{u, v, x, w} S B f X b z.1

private theorem sectionsBaseEquiv_naturality
    {R : Type u} (S : Type v) (B : Type x)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    [Module.Flat R B] {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons.{u, max u v x w} f}
    {X Y : FormalGlueing.ModuleGlueingDatum.{u, v, max u v x w} S f c}
    (g : FormalGlueing.ModuleGlueingMap S f c X Y)
    (b : B) (z : FormalGlueing.compatibleSections S f c X) :
    FormalGlueing.compatibleSectionsMap _ _ (baseChangeMap.{u, v, x, w} S B f g)
        (sectionsBaseEquiv.{u, v, x, w} S B f X (b ⊗ₜ[R] z)) =
      sectionsBaseEquiv.{u, v, x, w} S B f Y
        (b ⊗ₜ[R] FormalGlueing.compatibleSectionsMap S f g z) := by
  apply Subtype.ext
  change ((baseChangeMap.{u, v, x, w} S B f g).generic
      (sectionsBaseEquiv.{u, v, x, w} S B f X (b ⊗ₜ[R] z)).1.1,
    fun i => (baseChangeMap.{u, v, x, w} S B f g).localPiece i
      ((sectionsBaseEquiv.{u, v, x, w} S B f X (b ⊗ₜ[R] z)).1.2 i)) = _
  rw [sectionsBaseEquiv_tmul, sectionsBaseEquiv_tmul]
  apply Prod.ext
  · dsimp only [Prod.fst]
    rw [genericBaseEquiv_symm_tmul, genericBaseEquiv_symm_tmul]
    rfl
  · funext i
    exact awayTensorEquiv_symm_map B (f i) (g.localPiece i) b (z.1.2 i)

private noncomputable def sectionsBaseChangeIso
    {R : Type u} (S : Type v) (B : Type x)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    [Module.Flat R B] {r : ℕ} (f : Fin r → R)
    (c : FormalGlueing.LocalizationComparisons.{u, max u v x w} f) :
    letI := FormalGlueing.moduleGlueingCategory.{u, v, max u v x w} S f c
    letI := FormalGlueing.moduleGlueingCategory.{x, max v x, max u v x w}
      (S ⊗[R] B) (fun i => algebraMap R B (f i)) (FormalGlueing.localizationComparisons _)
    FormalGlueing.compatibleSectionsFunctor.{u, v, max u v x w} S f c ⋙
        ModuleCat.extendScalars (algebraMap R B) ≅
      baseChangeFunctor.{u, v, x, w} S B f c ⋙
        FormalGlueing.compatibleSectionsFunctor.{x, max v x, max u v x w}
          (S ⊗[R] B) (fun i => algebraMap R B (f i)) (FormalGlueing.localizationComparisons _) := by
  letI := FormalGlueing.moduleGlueingCategory.{u, v, max u v x w} S f c
  letI := FormalGlueing.moduleGlueingCategory.{x, max v x, max u v x w}
    (S ⊗[R] B) (fun i => algebraMap R B (f i)) (FormalGlueing.localizationComparisons _)
  refine NatIso.ofComponents (fun X =>
    (extendScalarsEquiv B (ModuleCat.of R (FormalGlueing.compatibleSections S f c X)) ≪≫ₗ
      sectionsBaseEquiv.{u, v, x, w} S B f X).toModuleIso) ?_
  intro X Y g
  ext t
  change sectionsBaseEquiv.{u, v, x, w} S B f Y
      (extendScalarsEquiv B _
        ((ModuleCat.extendScalars (algebraMap R B)).map
          (ModuleCat.ofHom (FormalGlueing.compatibleSectionsMap S f g)) t)) =
    FormalGlueing.compatibleSectionsMap _ _ (baseChangeMap.{u, v, x, w} S B f g)
      (sectionsBaseEquiv.{u, v, x, w} S B f X (extendScalarsEquiv B _ t))
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
  | tmul b z => exact (sectionsBaseEquiv_naturality.{u, v, x, w} S B f g b z).symm

private noncomputable def moduleGlueingIso
    {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons.{u, max u v w} f}
    {X Y : FormalGlueing.ModuleGlueingDatum.{u, v, w} S f c}
    (g : FormalGlueing.ModuleGlueingMap S f c X Y)
    (eg : X.generic ≅ Y.generic) (el : ∀ i, X.localPiece i ≅ Y.localPiece i)
    (hg : g.generic = eg.hom) (hl : ∀ i, g.localPiece i = (el i).hom) :
    letI := FormalGlueing.moduleGlueingCategory.{u, v, w} S f c
    X ≅ Y := by
  letI := FormalGlueing.moduleGlueingCategory.{u, v, w} S f c
  let e i := ((ModuleCat.restrictScalars
    (algebraMap R (Localization.Away (f i)))).mapIso (el i)).toLinearEquiv
  let gi : FormalGlueing.ModuleGlueingMap S f c Y X :=
    { generic := eg.inv
      localPiece i := (el i).inv
      alpha_compatibility i m := by
        apply (AlgebraTensorModule.congr (LinearEquiv.refl S S) (e i)).injective
        have h := g.alpha_compatibility i (eg.inv m)
        rw [hg, hl i] at h
        rw [Iso.inv_hom_id_apply] at h
        change (AlgebraTensorModule.congr (LinearEquiv.refl S S) (e i)) _ =
          (AlgebraTensorModule.congr (LinearEquiv.refl S S) (e i))
            ((AlgebraTensorModule.congr (LinearEquiv.refl S S) (e i)).symm _)
        rw [LinearEquiv.apply_symm_apply]
        exact h.symm
      alphaIJ_compatibility i j m := by
        apply (localizedEquiv (Cech.cechSub f {i}) (e j)).injective
        have h := g.alphaIJ_compatibility i j ((el i).inv m)
        rw [hl i, hl j] at h
        rw [Iso.inv_hom_id_apply] at h
        change FormalGlueing.localizedMap f {i} (e j).toLinearMap _ =
          ((FormalGlueing.localizedMap f {i} (e j).toLinearMap).comp
            (FormalGlueing.localizedMap f {i} (e j).symm.toLinearMap)) _
        rw [← FormalGlueing.localizedMap_comp]
        have hi : (e j).toLinearMap.comp (e j).symm.toLinearMap = LinearMap.id := by
          ext z
          exact (e j).apply_symm_apply z
        rw [hi, FormalGlueing.localizedMap_id, LinearMap.id_apply]
        exact h.symm }
  exact
    { hom := g
      inv := gi
      hom_inv_id := by
        apply FormalGlueing.ModuleGlueingMap.ext
        · change g.generic ≫ eg.inv = 𝟙 _
          rw [hg, eg.hom_inv_id]
        · funext i
          change g.localPiece i ≫ (el i).inv = 𝟙 _
          rw [hl i, (el i).hom_inv_id]
      inv_hom_id := by
        apply FormalGlueing.ModuleGlueingMap.ext
        · change eg.inv ≫ g.generic = 𝟙 _
          rw [hg, eg.inv_hom_id]
        · funext i
          change (el i).inv ≫ g.localPiece i = 𝟙 _
          rw [hl i, (el i).inv_hom_id] }

private theorem canonicalGenericBaseEquiv_symm_tmul
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (M : ModuleCat R)
    (t : S ⊗[R] B) (b : B) (m : M) :
    (canonicalGenericBaseEquiv S B M).symm
      (t ⊗ₜ[B] (b ⊗ₜ[R, algebraMap R B] m)) =
      (b • t) ⊗ₜ[S, Algebra.TensorProduct.includeLeftRingHom] (1 ⊗ₜ[R] m) := by
  simp only [canonicalGenericBaseEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm]
  rfl

private theorem canonicalLocalBaseEquiv_symm_mk
    {R : Type*} (B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    (a : R) (M : ModuleCat R) (b : B) (m : M) :
    (canonicalLocalBaseEquiv B a M).symm
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R B a)) _
        (b ⊗ₜ[R, algebraMap R B] m)) =
      (awayTensorEquiv B a
        (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M))).symm
        (b ⊗ₜ[R] (FormalGlueing.restrictModuleOfEquiv (Localization.Away a)
          (LocalizedModule.Away a M)).symm
          (LocalizedModule.mkLinearMap (Submonoid.powers a) _ m)) := by
  apply (canonicalLocalBaseEquiv B a M).injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = localizedEquiv (Submonoid.powers (algebraMap R B a))
      (extendScalarsEquiv B M).symm
      ((awayLocalizationBaseChange B a M).symm
        (AlgebraTensorModule.congr (LinearEquiv.refl B B)
          (FormalGlueing.restrictModuleOfEquiv (Localization.Away a) (LocalizedModule.Away a M))
          (awayTensorEquiv B a
            (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M)) _)))
  rw [LinearEquiv.apply_symm_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.apply_symm_apply,
    ← awayLocalizationBaseChange_mk, LinearEquiv.symm_apply_apply, localizedEquiv_mk]
  rfl

set_option maxHeartbeats 800000 in
-- Elaborating the scalar restrictions of glueing data needs a larger budget.
private noncomputable def canonicalBaseChangeMap
    {R : Type u} (S : Type v) (B : Type x)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    {r : ℕ} (f : Fin r → R) (M : ModuleCat.{max u v x w} R) :
    FormalGlueing.ModuleGlueingMap (S ⊗[R] B) (fun i => algebraMap R B (f i))
      (FormalGlueing.localizationComparisons _)
      (FormalGlueing.canonicalDatum.{x, max v x, max u v x w} (S ⊗[R] B)
        (fun i => algebraMap R B (f i)) ((ModuleCat.extendScalars (algebraMap R B)).obj M))
      (baseChangeDatum.{u, v, x, w} S B f (FormalGlueing.canonicalDatum.{u, v, max u v x w} S f M))
        where
  generic := ModuleCat.ofHom (canonicalGenericBaseEquiv S B M).symm.toLinearMap
  localPiece i := ModuleCat.ofHom (canonicalLocalBaseEquiv B (f i) M).symm.toLinearMap
  alpha_compatibility i z := by
    change baseChangeAlpha S B f (FormalGlueing.canonicalDatum.{u, v, max u v x w} S f M) i
        (LocalizedModule.mkLinearMap _ _ ((canonicalGenericBaseEquiv S B M).symm z)) =
      TensorProduct.map LinearMap.id
        (((ModuleCat.restrictScalars
          (algebraMap B (Localization.Away (algebraMap R B (f i))))).map
          (ModuleCat.ofHom (canonicalLocalBaseEquiv B (f i) M).symm.toLinearMap)).hom)
        (FormalGlueing.canonicalAlpha (S ⊗[R] B) (fun i => algebraMap R B (f i))
          ((ModuleCat.extendScalars (algebraMap R B)).obj M) i (LocalizedModule.mkLinearMap _ _ z))
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
    | tmul t n =>
      induction n using TensorProduct.inductionOn with
      | add n n' hn hn' => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hn hn'
      | tmul b m =>
        change B at b
        rw [canonicalGenericBaseEquiv_symm_tmul, FormalGlueing.canonicalAlpha_mk]
        apply (genericLocalTensorEquiv S B (f i)
          ((FormalGlueing.canonicalDatum.{u, v, max u v x w} S f M).localPiece i)).injective
        rw [baseChangeAlpha_commutes, genericLocalizationEquiv_mk]
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe]
        change ((show B from b) • t) ⊗ₜ[S]
            (FormalGlueing.canonicalAlpha S f M i (LocalizedModule.mkLinearMap _ _ (1 ⊗ₜ[R] m))) =
          genericLocalTensorEquiv S B (f i) (FormalGlueing.canonicalLocalPiece f M i)
            (t ⊗ₜ[B] (canonicalLocalBaseEquiv B (f i) M).symm
              (LocalizedModule.mkLinearMap _ _ (b ⊗ₜ[R, algebraMap R B] m)))
        rw [FormalGlueing.canonicalAlpha_mk, canonicalLocalBaseEquiv_symm_mk]
        exact (genericLocalTensorEquiv_tensor S B (f i)
          (FormalGlueing.canonicalLocalPiece f M i) t (show B from b)
          (FormalGlueing.canonicalLocalMk f M i m)).symm
  alphaIJ_compatibility i j z := by
    let fB := fun i => algebraMap R B (f i)
    let MB := (ModuleCat.extendScalars (algebraMap R B)).obj M
    let h k : FormalGlueing.restrictFromAway fB k (FormalGlueing.canonicalLocalPiece fB MB k) →ₗ[B]
        FormalGlueing.restrictFromAway fB k
          ((ModuleCat.extendScalars (awayMap B (f k))).obj
            (FormalGlueing.canonicalLocalPiece f M k)) :=
      ((ModuleCat.restrictScalars
      (algebraMap B (Localization.Away (fB k)))).map
      (ModuleCat.ofHom (canonicalLocalBaseEquiv B (f k) M).symm.toLinearMap)).hom
    suffices (baseChangeAlphaIJ S B f (FormalGlueing.canonicalDatum.{u, v, max u v x w} S f M) i
      j).toLinearMap.comp
        ((LocalizedModule.mkLinearMap (Cech.cechSub fB {j}) _).comp (h i)) =
      (FormalGlueing.localizedMap fB {i} (h j)).comp
        ((FormalGlueing.canonicalAlphaIJ fB MB i j).toLinearMap.comp
          (LocalizedModule.mkLinearMap (Cech.cechSub fB {j}) _)) from
      DFunLike.congr_fun this z
    apply IsLocalizedModule.ext (Submonoid.powers (fB i)) (FormalGlueing.canonicalLocalMk fB MB i)
      (fun a => IsLocalizedModule.map_units (S := Cech.cechSub fB {i})
        (LocalizedModule.mkLinearMap (Cech.cechSub fB {i}) _)
        ⟨a, by simpa only [Cech.cechSub, Finset.prod_singleton] using a.2⟩)
    apply LinearMap.ext
    intro n
    change baseChangeAlphaIJ S B f (FormalGlueing.canonicalDatum.{u, v, max u v x w} S f M) i j
        (LocalizedModule.mkLinearMap _ _ (h i (FormalGlueing.canonicalLocalMk fB MB i n))) =
      FormalGlueing.localizedMap fB {i} (h j)
        (FormalGlueing.canonicalAlphaIJ fB MB i j
          (LocalizedModule.mkLinearMap _ _ (FormalGlueing.canonicalLocalMk fB MB i n)))
    conv_rhs => rw [FormalGlueing.canonicalAlphaIJ_mk]
    conv_rhs => rw [FormalGlueing.localizedMap_mk]
    induction n using TensorProduct.inductionOn with
    | add n n' hn hn' => simpa only [map_add] using congrArg₂ (· + ·) hn hn'
    | tmul b m =>
      change B at b
      apply (localOverlapEquiv B f j (FormalGlueing.canonicalLocalPiece f M j) {i}).injective
      change localOverlapEquiv B f j (FormalGlueing.canonicalLocalPiece f M j) {i}
          (baseChangeAlphaIJ S B f (FormalGlueing.canonicalDatum.{u, v, max u v x w} S f M) i j
            (LocalizedModule.mkLinearMap _ _ ((canonicalLocalBaseEquiv B (f i) M).symm
              (LocalizedModule.mkLinearMap _ _ (b ⊗ₜ[R, algebraMap R B] m))))) =
        localOverlapEquiv B f j (FormalGlueing.canonicalLocalPiece f M j) {i}
          (LocalizedModule.mkLinearMap _ _ ((canonicalLocalBaseEquiv B (f j) M).symm
            (LocalizedModule.mkLinearMap _ _ (b ⊗ₜ[R, algebraMap R B] m))))
      rw [canonicalLocalBaseEquiv_symm_mk, canonicalLocalBaseEquiv_symm_mk]
      erw [baseChangeAlphaIJ_commutes S B f
        (FormalGlueing.canonicalDatum.{u, v, max u v x w} S f M) i j]
      conv_lhs =>
        erw [localOverlapEquiv_mk_tensor B f i (FormalGlueing.canonicalLocalPiece f M i)
          {j} b (FormalGlueing.canonicalLocalMk f M i m)]
      conv_rhs =>
        erw [localOverlapEquiv_mk_tensor B f j (FormalGlueing.canonicalLocalPiece f M j)
          {i} b (FormalGlueing.canonicalLocalMk f M j m)]
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe]
      exact congrArg (fun value => b ⊗ₜ[R] value) (FormalGlueing.canonicalAlphaIJ_mk f M i j m)

private theorem localizedLinearMap_ext
    {A : Type*} [CommRing A] (T : Submonoid A)
    {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module (Localization T) N]
    {g h : LocalizedModule T M →ₗ[Localization T] N}
    (he : ∀ m, g (LocalizedModule.mkLinearMap T M m) =
      h (LocalizedModule.mkLinearMap T M m)) : g = h := by
  ext z
  induction z using LocalizedModule.induction_on with
  | h m s =>
    have hz : LocalizedModule.mk m s =
        (Localization.mk 1 s) • (LocalizedModule.mkLinearMap T M m) := by
      change _ = (Localization.mk 1 s) • (LocalizedModule.mk m 1)
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [hz, map_smul, map_smul, he]

private theorem canonicalBaseChangeMap_naturality
    {R : Type u} (S : Type v) (B : Type x)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    {r : ℕ} (f : Fin r → R) {M N : ModuleCat.{max u v x w} R} (g : M ⟶ N) :
    letI := FormalGlueing.moduleGlueingCategory.{x, max v x, max u v x w}
      (S ⊗[R] B) (fun i => algebraMap R B (f i)) (FormalGlueing.localizationComparisons _)
    FormalGlueing.ModuleGlueingMap.comp
      (FormalGlueing.canonicalDatumMap.{x, max v x, max u v x w}
        (S ⊗[R] B) (fun i => algebraMap R B (f i))
        ((ModuleCat.extendScalars (algebraMap R B)).map g))
      (canonicalBaseChangeMap.{u, v, x, w} S B f N) =
    FormalGlueing.ModuleGlueingMap.comp (canonicalBaseChangeMap.{u, v, x, w} S B f M)
      (baseChangeMap.{u, v, x, w} S B f
        (FormalGlueing.canonicalDatumMap.{u, v, max u v x w} S f g)) := by
  let := FormalGlueing.moduleGlueingCategory.{x, max v x, max u v x w}
    (S ⊗[R] B) (fun i => algebraMap R B (f i)) (FormalGlueing.localizationComparisons _)
  apply FormalGlueing.ModuleGlueingMap.ext
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change (canonicalGenericBaseEquiv S B N).symm
        ((AlgebraTensorModule.lTensor (S ⊗[R] B) (S ⊗[R] B)
          ((ModuleCat.extendScalars (algebraMap R B)).map g).hom) t) =
      ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)).map
        (FormalGlueing.canonicalDatumMap.{u, v, max u v x w} S f g).generic)
        ((canonicalGenericBaseEquiv S B M).symm t)
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
    | tmul t n =>
      induction n using TensorProduct.inductionOn with
      | add n n' hn hn' => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hn hn'
      | tmul b m =>
        change B at b
        change (canonicalGenericBaseEquiv S B N).symm
            (t ⊗ₜ[B] (b ⊗ₜ[R, algebraMap R B] g m)) = _
        rw [canonicalGenericBaseEquiv_symm_tmul, canonicalGenericBaseEquiv_symm_tmul]
        rfl
  · funext i
    apply ModuleCat.hom_ext
    apply localizedLinearMap_ext (Submonoid.powers (algebraMap R B (f i)))
    intro n
    change (canonicalLocalBaseEquiv B (f i) N).symm
        (FormalGlueing.canonicalLocalMap (fun i => algebraMap R B (f i))
          ((ModuleCat.extendScalars (algebraMap R B)).map g) i
          (FormalGlueing.canonicalLocalMk (fun i => algebraMap R B (f i))
            ((ModuleCat.extendScalars (algebraMap R B)).obj M) i n)) =
      ((ModuleCat.extendScalars (awayMap B (f i))).map (FormalGlueing.canonicalLocalMap f g i))
        ((canonicalLocalBaseEquiv B (f i) M).symm (LocalizedModule.mkLinearMap _ _ n))
    rw [FormalGlueing.canonicalLocalMap_mk]
    induction n using TensorProduct.inductionOn with
    | add n n' hn hn' => simpa only [map_add] using congrArg₂ (· + ·) hn hn'
    | tmul b m =>
      change B at b
      change (canonicalLocalBaseEquiv B (f i) N).symm
          (LocalizedModule.mkLinearMap _ _ (b ⊗ₜ[R, algebraMap R B] g m)) = _
      rw [canonicalLocalBaseEquiv_symm_mk, canonicalLocalBaseEquiv_symm_mk]
      simp only
      exact congrArg
        (fun value : (ModuleCat.restrictScalars
            (algebraMap R (Localization.Away (f i)))).obj
            (FormalGlueing.canonicalLocalPiece f N i) =>
          (awayTensorEquiv B (f i) (FormalGlueing.canonicalLocalPiece f N i)).symm
            (b ⊗ₜ[R] value))
        (FormalGlueing.canonicalLocalMap_mk f g i m).symm

private noncomputable def canonicalBaseChangeIso
    {R : Type u} (S : Type v) (B : Type x)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    {r : ℕ} (f : Fin r → R) :
    letI := FormalGlueing.moduleGlueingCategory.{u, v, max u v x w}
      S f (FormalGlueing.localizationComparisons f)
    letI := FormalGlueing.moduleGlueingCategory.{x, max v x, max u v x w}
      (S ⊗[R] B) (fun i => algebraMap R B (f i)) (FormalGlueing.localizationComparisons _)
    FormalGlueing.canonicalFunctor.{u, v, max u v x w} S f ⋙
        baseChangeFunctor.{u, v, x, w} S B f (FormalGlueing.localizationComparisons f) ≅
      ModuleCat.extendScalars (algebraMap R B) ⋙
        FormalGlueing.canonicalFunctor.{x, max v x, max u v x w}
          (S ⊗[R] B) (fun i => algebraMap R B (f i)) := by
  letI := FormalGlueing.moduleGlueingCategory.{u, v, max u v x w}
    S f (FormalGlueing.localizationComparisons f)
  letI := FormalGlueing.moduleGlueingCategory.{x, max v x, max u v x w}
    (S ⊗[R] B) (fun i => algebraMap R B (f i)) (FormalGlueing.localizationComparisons _)
  apply Iso.symm
  refine NatIso.ofComponents (fun M => moduleGlueingIso.{x, max v x, max u v x w} _ _
    (canonicalBaseChangeMap.{u, v, x, w} S B f M)
    (canonicalGenericBaseEquiv S B M).symm.toModuleIso
    (fun i => (canonicalLocalBaseEquiv B (f i) M).symm.toModuleIso)
    rfl (fun _ => rfl)) ?_
  intro M N g
  exact canonicalBaseChangeMap_naturality.{u, v, x, w} S B f g

/-- **Stacks 05EQ.** Flat base change defines a functor on module glueing data which commutes,
up to natural isomorphism, with the canonical glueing-data functor and compatible global
sections. Its generic and local components, including their action on morphisms, are the
corresponding scalar-extension functors. -/
@[stacks 05EQ]
public theorem exists_baseChange_commuting_with_canonical_and_sections
    (R : Type u) (S : Type v) (R' : Type x)
    [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
    {r : ℕ} (f : Fin r → R) (hR' : Module.Flat R R') :
    let upper := FormalGlueing.moduleGlueingConstruction.{u, v, max u v x w} S f
    let lower := FormalGlueing.moduleGlueingConstruction.{x, max v x, max u v x w}
      (TensorProduct R S R') (fun i ↦ algebraMap R R' (f i))
    letI := upper.category
    letI := lower.category
    let genericMap : S →+* TensorProduct R S R' :=
      Algebra.TensorProduct.includeLeftRingHom
    let localMap : ∀ i, Localization.Away (f i) →+*
        Localization.Away (algebraMap R R' (f i)) := fun i ↦
      IsLocalization.Away.map (Localization.Away (f i))
        (Localization.Away (algebraMap R R' (f i))) (algebraMap R R') (f i)
    ∃ (baseChange :
        FormalGlueing.ModuleGlueingDatum S f upper.comparison ⥤
          FormalGlueing.ModuleGlueingDatum (TensorProduct R S R')
            (fun i ↦ algebraMap R R' (f i)) lower.comparison)
      (genericIso : ∀ X, (baseChange.obj X).generic ≅
        (ModuleCat.extendScalars genericMap).obj X.generic)
      (localIso : ∀ X i, (baseChange.obj X).localPiece i ≅
        (ModuleCat.extendScalars (localMap i)).obj (X.localPiece i))
      (genericLocalizationIso : ∀ X i,
        LocalizedModule.Away
            (algebraMap R' (TensorProduct R S R') (algebraMap R R' (f i)))
            (baseChange.obj X).generic ≃ₗ[TensorProduct R S R']
          TensorProduct S (TensorProduct R S R')
            (LocalizedModule.Away (algebraMap R S (f i)) X.generic))
      (genericLocalTensorIso : ∀ X i,
        TensorProduct R' (TensorProduct R S R')
            (FormalGlueing.restrictFromAway
              (R := R') (fun i ↦ algebraMap R R' (f i)) i
              ((baseChange.obj X).localPiece i)) ≃ₗ[TensorProduct R S R']
          TensorProduct S (TensorProduct R S R')
            (TensorProduct R S
              (FormalGlueing.restrictFromAway (R := R) f i (X.localPiece i))))
      (localOverlapIso : ∀ X i j,
        Cech.cechMod (fun i ↦ algebraMap R R' (f i))
            (FormalGlueing.restrictFromAway
              (R := R') (fun i ↦ algebraMap R R' (f i)) i
              ((baseChange.obj X).localPiece i)) {j} ≃ₗ[R']
          TensorProduct R R'
            (Cech.cechMod f
              (FormalGlueing.restrictFromAway (R := R) f i (X.localPiece i)) {j})),
      (∀ {X Y} (g : X ⟶ Y),
        (lower.homEquiv (baseChange.obj X) (baseChange.obj Y)
              (baseChange.map g)).generic ≫ (genericIso Y).hom =
          (genericIso X).hom ≫
            (ModuleCat.extendScalars genericMap).map
              (upper.homEquiv X Y g).generic) ∧
        (∀ {X Y} (g : X ⟶ Y) i,
          (lower.homEquiv (baseChange.obj X) (baseChange.obj Y)
                (baseChange.map g)).localPiece i ≫ (localIso Y i).hom =
            (localIso X i).hom ≫
              (ModuleCat.extendScalars (localMap i)).map
                ((upper.homEquiv X Y g).localPiece i)) ∧
        (∀ X i (m : X.generic) (t : TensorProduct R S R'),
          genericLocalizationIso X i
              (LocalizedModule.mkLinearMap
                (Submonoid.powers
                  (algebraMap R' (TensorProduct R S R') (algebraMap R R' (f i)))) _
                ((genericIso X).inv (t ⊗ₜ[S] m))) =
            t ⊗ₜ[S]
              LocalizedModule.mkLinearMap
                (Submonoid.powers (algebraMap R S (f i))) _ m) ∧
        (∀ (X : FormalGlueing.ModuleGlueingDatum S f upper.comparison) i,
          letI : Module R (X.localPiece i) :=
            Module.compHom _ (algebraMap R (Localization.Away (f i)))
          ∀ (m : X.localPiece i) (t : TensorProduct R S R'),
          genericLocalTensorIso X i
              (t ⊗ₜ[R'] (localIso X i).inv
                ((1 : Localization.Away (algebraMap R R' (f i)))
                  ⊗ₜ[Localization.Away (f i)] m)) =
            t ⊗ₜ[S] (1 ⊗ₜ[R] m)) ∧
        (∀ (X : FormalGlueing.ModuleGlueingDatum S f upper.comparison) i j,
          letI : Module R (X.localPiece i) :=
            Module.compHom _ (algebraMap R (Localization.Away (f i)))
          ∀ (m : X.localPiece i),
          localOverlapIso X i j
              (LocalizedModule.mkLinearMap
                (Cech.cechSub (fun i ↦ algebraMap R R' (f i)) {j}) _
                ((localIso X i).inv
                  ((1 : Localization.Away (algebraMap R R' (f i)))
                    ⊗ₜ[Localization.Away (f i)] m))) =
            1 ⊗ₜ[R]
              LocalizedModule.mkLinearMap (Cech.cechSub f {j}) _ m) ∧
        (∀ X i d,
          genericLocalTensorIso X i ((baseChange.obj X).alpha i d) =
            TensorProduct.map LinearMap.id (X.alpha i).toLinearMap
              (genericLocalizationIso X i d)) ∧
        (∀ X i j d,
          localOverlapIso X j i ((baseChange.obj X).alphaIJ i j d) =
            TensorProduct.map LinearMap.id (X.alphaIJ i j).toLinearMap
              (localOverlapIso X i j d)) ∧
        Nonempty
          (upper.canonical ⋙ baseChange ≅
            ModuleCat.extendScalars (algebraMap R R') ⋙ lower.canonical) ∧
        Nonempty
          (upper.sections ⋙ ModuleCat.extendScalars (algebraMap R R') ≅
            baseChange ⋙ lower.sections) := by
  let : Module.Flat R R' := hR'
  refine ⟨baseChangeFunctor.{u, v, x, w} S R' f (FormalGlueing.localizationComparisons f),
    (fun X => Iso.refl _), (fun X i => Iso.refl _),
    (fun X i => genericLocalizationEquiv S R' (f i) X.generic),
    (fun X i => genericLocalTensorEquiv S R' (f i) (X.localPiece i)),
    (fun X i j => localOverlapEquiv R' f i (X.localPiece i) {j}),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y g
    ext z
    rfl
  · intro X Y g i
    ext z
    rfl
  · intro X i m t
    exact genericLocalizationEquiv_mk S R' (f i) X.generic t m
  · intro X i m t
    exact genericLocalTensorEquiv_tmul S R' (f i) (X.localPiece i) t m
  · intro X i j m
    exact localOverlapEquiv_mk R' f i (X.localPiece i) {j} m
  · intro X i d
    exact baseChangeAlpha_commutes S R' f X i d
  · intro X i j d
    exact baseChangeAlphaIJ_commutes S R' f X i j d
  · exact ⟨canonicalBaseChangeIso.{u, v, x, w} S R' f⟩
  · exact ⟨sectionsBaseChangeIso.{u, v, x, w} S R' f (FormalGlueing.localizationComparisons f)⟩


end FormalGlueing


end

/-! ### Formal glueing of module categories -/

section

@[expose] public section

open CategoryTheory FormalGlueing TensorProduct

namespace FormalGlueing

universe u v w

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R)

attribute [local instance] FormalGlueing.restrictScalars_isScalarTower

private theorem localCounit_bijective
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r) :
    Function.Bijective (FormalGlueing.sectionsLocalCounit S f X i) :=
  FormalGlueing.sectionsLocalCounit_bijective_of_isLocalized S f X i
    (FormalGlueing.sectionsLocalProjection_isLocalized S f X i)

-- Elaborating the scalar restrictions of glueing data needs a larger budget.
private theorem canonicalAlpha_eq_zero_of_genericCounit_eq_zero
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (z : S ⊗[R] FormalGlueing.sections S f X) (hz : FormalGlueing.sectionsGenericCounit S f X z = 0)
    (i : Fin r) :
    canonicalAlpha S f (ModuleCat.of R (FormalGlueing.sections S f X)) i
      (LocalizedModule.mkLinearMap _ _ z) = 0 := by
  have hc := (FormalGlueing.sectionsCounit S f X).alpha_compatibility i z
  have hz' : (FormalGlueing.sectionsCounit S f X).generic z = 0 := hz
  rw [hz', map_zero, map_zero] at hc
  let e := LinearEquiv.ofBijective (((ModuleCat.restrictScalars
    (algebraMap R (Localization.Away (f i)))).map
      ((FormalGlueing.sectionsCounit S f X).localPiece i)).hom) (localCounit_bijective S f X i)
  have hinj := (LinearEquiv.lTensor S e).injective
  exact hinj (hc.symm.trans (map_zero _).symm)

private theorem canonicalSectionsUnit_bijective (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap
        ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (M : ModuleCat.{max u v w} R) :
    Function.Bijective (canonicalToCompatibleSections.{u, v, w} S f M) := by
  let := moduleGlueingCategory.{u, v, w} S f (localizationComparisons f)
  have h : IsIso (canonicalSectionsUnit.{u, v, w} S f) :=
    FormalGlueing.canonicalSectionsUnit_isIso R S f hflat hq
  exact ConcreteCategory.bijective_of_isIso ((canonicalSectionsUnit.{u, v, w} S f).app M)

-- Elaborating the scalar restrictions of glueing data needs a larger budget.
private theorem genericCounit_injective (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap
        ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) :
    Function.Injective (FormalGlueing.sectionsGenericCounit S f X) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  let H := ModuleCat.of R (FormalGlueing.sections S f X)
  let t : compatibleSections S f (localizationComparisons f) (canonicalDatum S f H) :=
    ⟨(z, 0), fun i ↦ (canonicalAlpha_eq_zero_of_genericCounit_eq_zero S f X z hz i).trans
      (by simp; rfl), fun i j ↦ by simp⟩
  obtain ⟨h, hh⟩ := (canonicalSectionsUnit_bijective S f hflat hq H).2 t
  have hg : (1 : S) ⊗ₜ[R] h = z := congrArg (fun x ↦ x.1.1) hh
  have hl i : canonicalLocalMk f H i h = 0 := congrArg (fun x ↦ x.1.2 i) hh
  have h0 : h = 0 := by
    apply Subtype.ext
    apply Prod.ext
    · have := congrArg (FormalGlueing.sectionsGenericCounit S f X) hg
      rw [FormalGlueing.sectionsGenericCounit_tmul, one_smul, hz] at this
      exact this
    · funext i
      have := FormalGlueing.sectionsLocalCounit_mk S f X i h
      rw [hl] at this
      exact this.symm.trans (map_zero _)
  rw [← hg, h0, TensorProduct.tmul_zero]

-- Elaborating the scalar restrictions of glueing data needs a larger budget.
private theorem genericCounit_localized_bijective
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r) :
    Function.Bijective ((LocalizedModule.map (Submonoid.powers (algebraMap R S (f i)))
      (FormalGlueing.sectionsGenericCounit S f X)).restrictScalars S) := by
  let M := ModuleCat.of R (FormalGlueing.sections S f X)
  let li := (((ModuleCat.restrictScalars
    (algebraMap R (Localization.Away (f i)))).map
      (ModuleCat.ofHom (FormalGlueing.sectionsLocalCounit S f X i))).hom)
  let e := (canonicalAlpha S f M i).trans
    ((AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (LinearEquiv.ofBijective li (localCounit_bijective S f X i))).trans (X.alpha i).symm)
  have h : (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i)))
      (FormalGlueing.sectionsGenericCounit S f X)).restrictScalars S = e.toLinearMap := by
    apply IsLocalizedModule.ext (Submonoid.powers (algebraMap R S (f i)))
      (LocalizedModule.mkLinearMap _ (S ⊗[R] FormalGlueing.sections S f X))
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap
        (Submonoid.powers (algebraMap R S (f i))) X.generic))
    ext m
    apply (X.alpha i).injective
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk,
      LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, e]
    exact (FormalGlueing.sectionsCounit S f X).alpha_compatibility i m
  rw [h]
  exact e.bijective

private theorem genericCounit_pow_smul_mem_range
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r)
    (x : X.generic) :
    ∃ n : ℕ, algebraMap R S (f i) ^ n • x ∈
      LinearMap.range (FormalGlueing.sectionsGenericCounit S f X) := by
  obtain ⟨y, hy⟩ := (genericCounit_localized_bijective S f X i).2
    (LocalizedModule.mk x 1)
  induction y using LocalizedModule.induction_on with
  | h z s =>
    rw [LinearMap.restrictScalars_apply, LocalizedModule.map_mk] at hy
    obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.mp hy
    obtain ⟨n, hn⟩ := (t * s).2
    refine ⟨n, ⟨(t : S) • z, ?_⟩⟩
    rw [map_smul]
    have ht' : (t : S) • FormalGlueing.sectionsGenericCounit S f X z = ((t : S) * s) • x := by
      simpa [Submonoid.smul_def, mul_smul] using ht
    rw [ht']
    exact congrArg (· • x) hn.symm

end FormalGlueing

end

end
