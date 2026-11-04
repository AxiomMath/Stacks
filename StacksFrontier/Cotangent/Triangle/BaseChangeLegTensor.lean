module

public import StacksFrontier.Cotangent.StandardResolutionFrobeniusHomotopy
public import StacksFrontier.Cotangent.Triangle.KeyFact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FlatBaseChangeRows

/-!
# The base-changed resolution as a tensor product

Let `A → B → C` be ring maps, let `P_•` and `Q_•` be the standard resolutions of `B` and of `C`
over `A`, and let `Q̄_• = Q_• ⊗_{P_•} B` be the base-changed simplicial `B`-algebra of
[Stacks, Tag 08SD]. The Δ-instance of [Stacks, Tag 08RX] proved in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/FlatBaseChangeRows.lean` speaks about the
*base-change unit* of a simplicial module over a simplicial ring, whereas `Q̄_•` is built in this
library as a degreewise *pushout of commutative rings*. This file identifies the two.

The identification is in two halves.

* `CommAlgCat.resolutionModule`: `Q_•` presented as an object of
  `Stacks.SimplicialModules.SMod (P_•)`, i.e. as a presheaf of modules on `Δ` over the presheaf of
  rings underlying `P_•`. No new presheaf of modules is built by hand: `Q_•` *is* the structure
  presheaf of `Q_•` with its scalars restricted along `P_• ⟶ Q_•`
  (`PresheafOfModules.restrictScalars` of `PresheafOfModules.unit`), and `Q̄_•` likewise
  (`CommAlgCat.baseChangedModule`) over the constant simplicial ring `B̲`. Since
  `PresheafOfModules.restrictScalarsCompToPresheaf` is the identity, the underlying presheaves of
  abelian groups come out *equal* to `Q_•` and `Q̄_•` read additively, which is what lets the leg
  of the pushout and the base-change unit be compared at all. The pushout leg becomes a morphism
  of simplicial `P_•`-modules, `CommAlgCat.baseChangeLegModuleHom`: its `P_n`-linearity is the
  commutativity of the pushout square (`CommAlgCat.baseChanged_isPushout`) and its naturality in
  `n` is `CommAlgCat.canonicalBaseChangeMap_naturality_apply`.

* `CommAlgCat.baseChangeComparison`: the morphism `B ⊗_{P_•} Q_• ⟶ Q̄_•` corresponding to the leg
  under the change-of-rings adjunction. It is an isomorphism, by
  `CommAlgCat.bijective_baseChangeComparison_app`: in each simplicial degree both sides are
  pushouts of the span `Q_n ← P_n → B` of commutative rings — the tensor product by Mathlib's
  `CommRingCat.isPushout_tensorProduct`, and `Q̄_n` by `CommAlgCat.baseChanged_isPushout` — and
  the comparison map is the canonical map between the two, which
  `CategoryTheory.IsPushout.isoIsPushout` makes invertible. Naturality in `n` costs nothing: the
  comparison map is produced by the adjunction, not degreewise.

Together (`CommAlgCat.mooreCochain_baseChangedLeg_eq`) the pushout leg `s(Q_•) ⟶ s(Q̄_•)` is the
base-change unit of Tag 08RX followed by an isomorphism, so
`CommAlgCat.quasiIso_baseChangedLeg` discharges the hypothesis `hleg` of
`CommAlgCat.exists_distTriang_fundamentalVertex_of_quasiIso_leg`: its two inputs, the flatness of
`Q_n` over `P_n` (`CommAlgCat.flat_standardResolution`, which consumes the injectivity of
`B → C`) and the quasi-isomorphy of `s(P_•) ⟶ s(B̲)`
(`CommAlgCat.quasiIso_unitMap_resolutionAug`), are already theorems.

## Main definitions

* `CommAlgCat.resolutionAug`, `CommAlgCat.resolutionRingMap`: the augmentation of `P_•` to `B̲`,
  and the map `P_• ⟶ Q_•`. The simplicial commutative ring `P_•` itself is
  `CommAlgCat.resolutionRing`, in
  `StacksFrontier/Cotangent/StandardResolutionFrobeniusHomotopy.lean`, used here at `{u, u}`.
* `CommAlgCat.resolutionModule`: `Q_•` as a simplicial `P_•`-module.
* `CommAlgCat.baseChangedRing`, `CommAlgCat.baseChangedStructureMap`,
  `CommAlgCat.baseChangedModule`: the same for `Q̄_•` over the constant simplicial ring `B̲`.
* `CommAlgCat.baseChangeLegModuleHom`: the pushout leg as a morphism of simplicial `P_•`-modules.
* `CommAlgCat.baseChangeComparison`: the comparison map `B ⊗_{P_•} Q_• ⟶ Q̄_•`.

## Main results

* `CommAlgCat.bijective_baseChangeComparison_app`: **`Q̄_n` is `B ⊗_{P_n} Q_n`.**
* `CommAlgCat.mooreCochain_baseChangedLeg_eq`: the pushout leg on Moore complexes is the
  base-change unit of Tag 08RX followed by an isomorphism.
* `CommAlgCat.quasiIso_baseChangedLeg`: **the pushout leg `Q_• ⟶ Q̄_•` is a quasi-isomorphism on
  Moore complexes** — the Δ-instance of Tag 08RX, applied.
* `CommAlgCat.isResolution_baseChangedStandardResolution_of_injective`: **the key fact of
  [Stacks, Tag 08SD]**, with nothing carried beyond the injectivity of `B → C` that Tag 08SD
  itself assumes.
* `CommAlgCat.baseChangedCotangentComplexIsoOfInjective`: **the identification of
  [Stacks, Remark 08SE]**, with its two trivial-Kan-fibration hypotheses discharged.
* `CommAlgCat.exists_distTriang_fundamentalVertex_of_injective`: **the triangle of
  [Stacks, Tag 08QX] for `B → C` injective** — the display of [Stacks, Tag 08QS], third arrow
  included.

## No `@[stacks]` attribute

Nothing here is registered. Tag 08RX is stated at a general site with a cosimplicial point
resolution and for an arbitrary object of `D(𝒪)`; what the Δ-instance gives is one special case of
it. Tags 08QX and 08QS assume nothing of `A → B → C`, whereas the statements here assume `B → C`
injective; they are registered in
`StacksFrontier/Cotangent/Triangle/ProductDescent.lean`, which drops the hypothesis by the passage to
`A → B → B × C` of Remark 08SD and the product decomposition of Tag 08SC
(`CommAlgCat.isIso_Q_map_cotangentComplexProductMap`).

## References

* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD), the key fact.
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX), what it rests on.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), the fundamental triangle.
* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS), its display.
* [Stacks Project, Tag 08SE](https://stacks.math.columbia.edu/tag/08SE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.PresheafOfModules.ChangeOfRings
open scoped TensorProduct

universe u

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B C : CommAlgCat.{u} A}

/-- The augmentation `P_• ⟶ B̲`. -/
def resolutionAug (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) :
    resolutionRing.{u, u} A B ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (CommRingCat.of ↥B) where
  app n := CommRingCat.ofHom (standardResolutionAugmentationHom A B n)
  naturality i j g := by
    ext x
    exact RingHom.congr_fun (standardResolutionAugmentationHom_naturality A B g) x

/-- The map of simplicial rings `P_• ⟶ Q_•`. -/
def resolutionRingMap (f : B ⟶ C) : resolutionRing.{u, u} A B ⟶ resolutionRing.{u, u} A C :=
  Functor.whiskerRight ((standardResolutionFunctor A).map f).left
    (forget₂ (CommAlgCat.{u} A) CommRingCat.{u})

/-- `Q_•` as a simplicial `P_•`-module. -/
def resolutionModule (f : B ⟶ C) : Stacks.SimplicialModules.SMod (resolutionRing.{u, u} A B) :=
  (PresheafOfModules.restrictScalars
      (Functor.whiskerRight (resolutionRingMap f) (forget₂ CommRingCat.{u} RingCat.{u}))).obj
    (PresheafOfModules.unit (ringPresheaf (resolutionRing.{u, u} A C)))

/-- `Q̄_•` as a simplicial commutative ring. -/
abbrev baseChangedRing (A : Type u) [CommRing A] {B C : CommAlgCat.{u} A} (f : B ⟶ C) :
    SimplexCategoryᵒᵖ ⥤ CommRingCat.{u} :=
  (baseChangedStandardResolution A f).left ⋙ forget₂ (CommAlgCat.{u} ↥B) CommRingCat.{u}

/-- The structure map `B̲ ⟶ Q̄_•`. -/
def baseChangedStructureMap (f : B ⟶ C) :
    (Functor.const SimplexCategoryᵒᵖ).obj (CommRingCat.of ↥B) ⟶ baseChangedRing A f where
  app n := CommRingCat.ofHom (algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n))
  naturality i j g := by
    ext b
    exact (((baseChangedStandardResolution A f).left.map g).hom.commutes b).symm

/-- `Q̄_•` as a simplicial `B`-module. -/
def baseChangedModule (f : B ⟶ C) :
    Stacks.SimplicialModules.SMod ((Functor.const SimplexCategoryᵒᵖ).obj (CommRingCat.of ↥B)) :=
  (PresheafOfModules.restrictScalars
      (Functor.whiskerRight (baseChangedStructureMap f) (forget₂ CommRingCat.{u} RingCat.{u}))).obj
    (PresheafOfModules.unit (ringPresheaf (baseChangedRing A f)))

/-- The pushout square, on sections. -/
theorem canonicalBaseChangeMap_resolutionRingMap (f : B ⟶ C) (n : SimplexCategoryᵒᵖ)
    (r : (standardResolution A B).left.obj n) :
    canonicalBaseChangeMap A f n
        ((((standardResolutionFunctor A).map f).left.app n).hom r) =
      algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n)
        (standardResolutionAugmentationHom A B n r) := by
  have hw := congrArg CommRingCat.Hom.hom (baseChanged_isPushout f n).w
  exact RingHom.congr_fun hw r

/-- The pushout leg is `P_n`-linear, read as an identity of products. -/
theorem canonicalBaseChangeMap_mul_resolutionRingMap (f : B ⟶ C) (n : SimplexCategoryᵒᵖ)
    (r : (standardResolution A B).left.obj n) (x : (standardResolution A C).left.obj n) :
    canonicalBaseChangeMap A f n
        ((show (standardResolution A C).left.obj n from
          (((standardResolutionFunctor A).map f).left.app n).hom r) * x) =
      algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n)
          (standardResolutionAugmentationHom A B n r) *
        canonicalBaseChangeMap A f n x := by
  rw [map_mul, canonicalBaseChangeMap_resolutionRingMap]

/-- The leg `Q_n ⟶ Q̄_n`, as a `P_n`-linear map. -/
def baseChangeLegApp (f : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    (resolutionModule f).obj n ⟶
      ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (resolutionAug A B)).obj
        (baseChangedModule f)).obj n :=
  ModuleCat.ofHom
    (R := (ringPresheaf (resolutionRing.{u, u} A B)).obj n)
    (X := (resolutionModule f).obj n)
    (Y := ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (resolutionAug A B)).obj
      (baseChangedModule f)).obj n)
    { toFun := fun x => canonicalBaseChangeMap A f n x
      map_add' := fun x y => map_add (canonicalBaseChangeMap A f n) x y
      map_smul' := fun r x => canonicalBaseChangeMap_mul_resolutionRingMap f n r x }

/-- The leg `Q_• ⟶ Q̄_•` as a map of simplicial `P_•`-modules. -/
def baseChangeLegModuleHom (f : B ⟶ C) :
    resolutionModule f ⟶
      (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (resolutionAug A B)).obj
        (baseChangedModule f) :=
  PresheafOfModules.Hom.mk (fun n => baseChangeLegApp f n)
    (fun {i j} g => by
      ext x
      exact (canonicalBaseChangeMap_naturality_apply f g x).symm)

/-! ### The comparison map `B ⊗_{P_•} Q_• ⟶ Q̄_•` -/

/-- **The comparison map `B ⊗_{P_•} Q_• ⟶ Q̄_•`**: the morphism of simplicial `B`-modules which
corresponds, under the change-of-rings adjunction
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`, to the pushout leg
`CommAlgCat.baseChangeLegModuleHom`. -/
def baseChangeComparison (f : B ⟶ C) :
    (changeOfRings (resolutionAug A B)).obj (resolutionModule f) ⟶ baseChangedModule f :=
  counitHom (resolutionAug A B) (baseChangeLegModuleHom f)

/-- The comparison map on pure tensors: `b ⊗ x ↦ b · leg(x)`. -/
theorem baseChangeComparison_app_tmul (f : B ⟶ C) (n : SimplexCategoryᵒᵖ)
    (b : ↥B) (x : ↥((standardResolution A C).left.obj n)) :
    letI := ((resolutionAug A B).app n).hom.toAlgebra
    ((baseChangeComparison f).app n).hom (b ⊗ₜ[↥((resolutionRing.{u, u} A B).obj n)] x) =
      algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n) b *
        canonicalBaseChangeMap A f n x := by
  let := ((resolutionAug A B).app n).hom.toAlgebra
  exact counitApp_tmul (resolutionAug A B) (baseChangeLegModuleHom f) n b x

/-- **`Q̄_n` is `B ⊗_{P_n} Q_n`**: the comparison map is bijective in every simplicial degree.
Both sides are pushouts of the span `Q_n ← P_n → B` of commutative rings — the left one by
Mathlib's `CommRingCat.isPushout_tensorProduct`, the right one by
`CommAlgCat.baseChanged_isPushout` — and the comparison map is the canonical map between them,
being `b ⊗ 1 ↦ b` and `1 ⊗ x ↦ leg(x)` on the two legs. -/
theorem bijective_baseChangeComparison_app (f : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((baseChangeComparison f).app n).hom := by
  let : Algebra ↥((resolutionRing.{u, u} A B).obj n) ↥B :=
    ((resolutionAug A B).app n).hom.toAlgebra
  let : Algebra ↥((resolutionRing.{u, u} A B).obj n) ↥((resolutionRing.{u, u} A C).obj n) :=
    ((resolutionRingMap f).app n).hom.toAlgebra
  have h2 : IsPushout
      (CommRingCat.ofHom (algebraMap ↥((resolutionRing.{u, u} A B).obj n) ↥B))
      (CommRingCat.ofHom
        (algebraMap ↥((resolutionRing.{u, u} A B).obj n) ↥((resolutionRing.{u, u} A C).obj n)))
      (CommRingCat.ofHom (algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n)))
      (CommRingCat.ofHom (canonicalBaseChangeMap A f n)) :=
    (baseChanged_isPushout f n).flip
  have h1 := CommRingCat.isPushout_tensorProduct ↥((resolutionRing.{u, u} A B).obj n) ↥B
    ↥((resolutionRing.{u, u} A C).obj n)
  set e := h1.isoIsPushout _ _ h2
  have hl : ∀ b : ↥B,
      e.hom.hom (Algebra.TensorProduct.includeLeftRingHom b) =
        algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n) b := fun b =>
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom (h1.inl_isoIsPushout_hom _ _ h2)) b
  have hr : ∀ x : ↥((resolutionRing.{u, u} A C).obj n),
      e.hom.hom (Algebra.TensorProduct.includeRight.toRingHom x) =
        canonicalBaseChangeMap A f n x := fun x =>
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom (h1.inr_isoIsPushout_hom _ _ h2)) x
  have htmul : ∀ (b : ↥B) (x : ↥((resolutionRing.{u, u} A C).obj n)),
      e.hom.hom (b ⊗ₜ[↥((resolutionRing.{u, u} A B).obj n)] x) =
        algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n) b *
          canonicalBaseChangeMap A f n x := by
    intro b x
    have hmul : (b ⊗ₜ[↥((resolutionRing.{u, u} A B).obj n)] x) =
        Algebra.TensorProduct.includeLeftRingHom b *
          Algebra.TensorProduct.includeRight.toRingHom x := by
      show _ =
        (b ⊗ₜ[↥((resolutionRing.{u, u} A B).obj n)] (1 : ↥((resolutionRing.{u, u} A C).obj n))) *
          ((1 : ↥B) ⊗ₜ[↥((resolutionRing.{u, u} A B).obj n)] x)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hmul, map_mul, hl, hr]
  have key : ∀ t : ↥B ⊗[↥((resolutionRing.{u, u} A B).obj n)] ↥((resolutionRing.{u, u} A C).obj n),
      ((baseChangeComparison f).app n).hom t = e.hom.hom t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add a b ha hb =>
      exact ((map_add ((baseChangeComparison f).app n).hom a b).trans
        (congrArg₂ (· + ·) ha hb)).trans (map_add e.hom.hom a b).symm
    | tmul b x =>
      exact (baseChangeComparison_app_tmul f n b x).trans (htmul b x).symm
  have hbij : Function.Bijective e.hom.hom := ConcreteCategory.bijective_of_isIso e.hom
  refine ⟨fun a b hab => hbij.injective ?_, fun y => ?_⟩
  · exact (key a).symm.trans (hab.trans (key b))
  · obtain ⟨t, ht⟩ := hbij.surjective y
    exact ⟨t, (key t).trans ht⟩

/-- **The comparison map is an isomorphism of presheaves of abelian groups**, read after
restriction of scalars back to `P_•` — which changes nothing, `restrictScalars ⋙ toPresheaf`
being `toPresheaf` (`PresheafOfModules.restrictScalarsCompToPresheaf`). This is the shape the
Moore complex of the pushout leg asks for. -/
theorem isIso_toPresheaf_baseChangeComparison (f : B ⟶ C) :
    IsIso ((PresheafOfModules.toPresheaf (ringPresheaf (resolutionRing.{u, u} A B))).map
      ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (resolutionAug A B)).map
        (baseChangeComparison f))) := by
  have happ : ∀ X : SimplexCategoryᵒᵖ,
      IsIso ((((PresheafOfModules.toPresheaf (ringPresheaf (resolutionRing.{u, u} A B))).map
        ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (resolutionAug A B)).map
          (baseChangeComparison f)))).app X) := by
    intro n
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_baseChangeComparison_app f n
  exact NatIso.isIso_of_isIso_app _

/-! ### The pushout leg is the base-change unit -/

/-- **The pushout leg `Q_• ⟶ Q̄_•` is the base-change unit followed by the comparison map.**
This is the adjunction's own triangle: the unit is `x ↦ 1 ⊗ x` and the comparison map takes
`1 ⊗ x` to `leg(x)`. -/
theorem baseChangeLegModuleHom_eq (f : B ⟶ C) :
    baseChangeLegModuleHom f =
      (changeOfRingsAdjunction (resolutionAug A B)).unit.app (resolutionModule f) ≫
        (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (resolutionAug A B)).map
          (baseChangeComparison f) := by
  refine PresheafOfModules.hom_ext (fun n => ModuleCat.hom_ext (LinearMap.ext (fun x => ?_)))
  let := ((resolutionAug A B).app n).hom.toAlgebra
  have key : ∀ y : ↥((standardResolution A C).left.obj n),
      ((baseChangeComparison f).app n).hom ((1 : ↥B) ⊗ₜ[↥((resolutionRing.{u, u} A B).obj n)] y) =
        canonicalBaseChangeMap A f n y := by
    intro y
    rw [baseChangeComparison_app_tmul, map_one, one_mul]
  show canonicalBaseChangeMap A f n x =
    ((baseChangeComparison f).app n).hom
      ((((changeOfRingsAdjunction (resolutionAug A B)).unit.app
        (resolutionModule f)).app n).hom x)
  rw [changeOfRingsAdjunction_unit_app_apply]
  exact (key x).symm

/-- The same factorisation, on reindexed Moore complexes: `s(Q_•) ⟶ s(Q̄_•)` is the base-change
unit of [Stacks, Tag 08RX] followed by an isomorphism. -/
theorem mooreCochain_baseChangedLeg_eq (f : B ⟶ C) :
    (Stacks.SimplicialModules.mooreCochainBaseChange' (resolutionAug A B)).app
          (resolutionModule f) ≫
        (alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf (ringPresheaf (resolutionRing.{u, u} A B))).map
            ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (resolutionAug A B)).map
              (baseChangeComparison f))) =
      (alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map (baseChangedLeg f) := by
  have h := congrArg
    (fun g : resolutionModule f ⟶
        (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (resolutionAug A B)).obj
          (baseChangedModule f) =>
      (alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf (ringPresheaf (resolutionRing.{u, u} A B))).map g))
    (baseChangeLegModuleHom_eq f)
  refine Eq.trans ?_ h.symm
  rw [Functor.map_comp, Functor.map_comp]
  rfl

/-- The augmentation `s(P_•) ⟶ s(B̲)` is a quasi-isomorphism of reindexed Moore complexes: it is
`CommAlgCat.quasiIso_standardResolution_hom` at `B`, read on the cochain complex. -/
theorem quasiIso_unitMap_resolutionAug (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) :
    QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
      (unitMap' (resolutionAug A B))) :=
  (HomologicalComplex.quasiIso_extendMap_iff
    ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight (standardResolution A B).hom (forgetAlgToAddCommGrp A)))
    (ComplexShape.embeddingUpIntLE (0 : ℤ))).mpr (quasiIso_standardResolution_hom A B)

/-- **The Δ-instance of [Stacks, Tag 08RX], applied: the pushout leg `Q_• ⟶ Q̄_•` is a
quasi-isomorphism on Moore complexes.**

This is the one open input of
`CommAlgCat.exists_distTriang_fundamentalVertex_of_quasiIso_leg`, discharged. The leg is the
base-change unit of the simplicial `P_•`-module `Q_•` along the augmentation `P_• ⟶ B̲` followed
by an isomorphism (`CommAlgCat.mooreCochain_baseChangedLeg_eq`), and the two hypotheses of
Tag 08RX hold: `Q_n` is a polynomial, hence free, hence flat `P_n`-algebra
(`CommAlgCat.flat_standardResolution`, where the injectivity of `B → C` is consumed) and
`s(P_•) ⟶ s(B̲)` is a quasi-isomorphism (`CommAlgCat.quasiIso_unitMap_resolutionAug`). -/
theorem quasiIso_baseChangedLeg (f : B ⟶ C) (hf : Function.Injective f.hom) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map (baseChangedLeg f)) := by
  have hcochain : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
      (baseChangedLeg f)) := by
    have h08RX : QuasiIso ((Stacks.SimplicialModules.mooreCochainBaseChange'
        (resolutionAug A B)).app (resolutionModule f)) :=
      Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app (resolutionAug A B)
        (resolutionModule f) (fun n => flat_standardResolution f hf n)
        (quasiIso_unitMap_resolutionAug A B)
    have := isIso_toPresheaf_baseChangeComparison f
    have hiso : IsIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf (ringPresheaf (resolutionRing.{u, u} A B))).map
          ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (resolutionAug A B)).map
            (baseChangeComparison f)))) := inferInstance
    have hqiso : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf (ringPresheaf (resolutionRing.{u, u} A B))).map
          ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (resolutionAug A B)).map
            (baseChangeComparison f)))) := quasiIso_of_isIso _
    have hq : QuasiIso ((Stacks.SimplicialModules.mooreCochainBaseChange'
          (resolutionAug A B)).app (resolutionModule f) ≫
        (alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf (ringPresheaf (resolutionRing.{u, u} A B))).map
            ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (resolutionAug A B)).map
              (baseChangeComparison f)))) :=
      quasiIso_comp _ _ (hφ := h08RX) (hφ' := hqiso)
    exact mooreCochain_baseChangedLeg_eq f ▸ hq
  exact (HomologicalComplex.quasiIso_extendMap_iff
    ((alternatingFaceMapComplex AddCommGrpCat.{u}).map (baseChangedLeg f))
    (ComplexShape.embeddingUpIntLE (0 : ℤ))).mp hcochain

/-! ### What the hypothesis was blocking -/

/-- **The key fact of [Stacks, Tag 08SD], with nothing carried.** For `B → C` injective — the
hypothesis Tag 08SD itself makes — the base-changed resolution `Q̄_• = Q_• ⊗_{P_•} B` is a
resolution of `C` over `B`. This is
`CommAlgCat.isResolution_baseChangedStandardResolution_of_quasiIso_leg` with its hypothesis
discharged by `CommAlgCat.quasiIso_baseChangedLeg`. -/
theorem isResolution_baseChangedStandardResolution_of_injective (f : B ⟶ C)
    (hf : Function.Injective f.hom) :
    @IsResolution ↥B B.commRing ↥(algebraOver f) (algebraOver f).commRing (algebraOver f).algebra
      (baseChangedStandardResolution A f).left (baseChangedStandardResolution A f).hom :=
  isResolution_baseChangedStandardResolution_of_quasiIso_leg f hf (quasiIso_baseChangedLeg f hf)

/-- **The hypothesis `hεQ` of Remark 08SE, discharged.** -/
theorem trivialKanFibrations_baseChangedStandardResolution_of_injective (f : B ⟶ C)
    (hf : Function.Injective f.hom) :
    SSet.trivialKanFibrations (Functor.whiskerRight (baseChangedStandardResolution A f).hom
      (forget (CommAlgCat.{u} ↥B))) :=
  trivialKanFibrations_baseChangedStandardResolution f
    (quasiIso_baseChangedStandardResolution_hom_of_quasiIso_leg f (quasiIso_baseChangedLeg f hf))

/-- **The hypothesis `hεR` of Remark 08SE, discharged.** `R̄_• = R_• ⊗_{S_•} B` is the
base-changed resolution at the base ring `B` and the map `CommAlgCat.overBase f`, which is `f` on
sections, so `CommAlgCat.quasiIso_baseChangedLeg` applies to it verbatim. -/
theorem trivialKanFibrations_relativeBaseChange_of_injective (f : B ⟶ C)
    (hf : Function.Injective f.hom) :
    SSet.trivialKanFibrations (Functor.whiskerRight (relativeBaseChange f).hom
      (forget (CommAlgCat.{u} ↥B))) :=
  trivialKanFibrations_relativeBaseChange_of_quasiIso_leg f
    (quasiIso_baseChangedLeg (overBase f) hf)

attribute [local instance] HasDerivedCategory.standard

/-- **The identification of Remark 08SE, with nothing carried.** `Ω[Q̄_•⁄B] ⊗_{Q̄_•} C` is
canonically isomorphic to `L_{C/B}` in `D(C)` for `B → C` injective; the remark's two
trivial-Kan-fibration hypotheses are now theorems. -/
noncomputable def baseChangedCotangentComplexIsoOfInjective (f : B ⟶ C)
    (hf : Function.Injective f.hom) :
    DerivedCategory.Q.obj
        (augmentedCotangentCochainComplex (baseChangedStandardResolution A f).hom) ≅
      DerivedCategory.Q.obj (cotangentComplex ↥B (algebraOver f)) :=
  baseChangedCotangentComplexIso f hf
    (trivialKanFibrations_baseChangedStandardResolution_of_injective f hf)
    (trivialKanFibrations_relativeBaseChange_of_injective f hf)

section Tower

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

open CategoryTheory.Pretriangulated in
/-- **[Stacks, Tag 08QX] for `B → C` injective.** Let `A → B → C` be ring maps with `B → C`
injective. Then there is a distinguished triangle

`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`

in `D(C)`, on the three vertices of the display of [Stacks, Tag 08QS]. In particular the display's
third arrow `L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]` exists and closes the triangle; it is named, as data,
by `CommAlgCat.fundamentalMor₃` of `StacksFrontier/Cotangent/Triangle/DisplayedTriangle.lean`.

This is `CommAlgCat.exists_distTriang_fundamentalVertex_of_isResolution` with BOTH of its carried
hypotheses discharged: `hP` by `CommAlgCat.isPolynomialAlgebra_baseChangedStandardResolution` and
`hε` by the Δ-instance of [Stacks, Tag 08RX] through `CommAlgCat.quasiIso_baseChangedLeg`.

NO `@[stacks 08QX]` ATTRIBUTE HERE. The source assumes nothing of `A → B → C`, and `B → C` is
assumed injective here. The statement for arbitrary `A → B → C` is
`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier/Cotangent/Triangle/ProductDescent.lean`, which carries `@[stacks 08QX]`: it is this
statement at the tower `A → B → B × C`, where the map is the split injection `b ↦ (b, f b)`, base
changed along the flat projection `B × C → C` by the product decomposition of Tag 08SC. -/
theorem exists_distTriang_fundamentalVertex_of_injective
    (hf : Function.Injective (algebraMap B C)) :
    ∃ (α : fundamentalVertex₁.{u, u, u + 1, u + 1} A B C ⟶ fundamentalVertex₂.{u, u, u + 1} A C)
      (β : fundamentalVertex₂.{u, u, u + 1} A C ⟶ fundamentalVertex₃.{u, u, u + 1} B C)
      (δ : fundamentalVertex₃.{u, u, u + 1} B C ⟶
        (fundamentalVertex₁.{u, u, u + 1, u + 1} A B C)⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) :=
  exists_distTriang_fundamentalVertex_of_quasiIso_leg A B C hf
    (quasiIso_baseChangedLeg (towerHom A B C) hf)

end Tower

end CommAlgCat

end
