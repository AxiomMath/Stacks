module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsRingEquivSquare
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutModules
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFlatEquivalence.GluingFunctor

/-!
# The affine charts of the three restrictions as base-change rings

Over an affine open `W` of `Y'` and an affine open `U` of `V'` above it, the sections over the
charts of `V`, `U'` and `U` are base changes of `Γ(V', U)` (`Stacks.Pushout.targetChart_isPushout`
and its siblings); `Γ(Y', W)` is the fibre product of `Stacks.Pushout.chartToBase` and
`Stacks.Pushout.chartSurjection`, giving a relative Milnor patching situation
(`Stacks.Pushout.exists_chartSituation`) whose three base-change rings are the chart section
rings.
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace Stacks.Pushout

variable {X X' Y V' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f]
  (g : V' ⟶ pushout i f)

variable (hi : Stacks.Thickenings.IsThickening i) [IsAffineHom f]

/-! ### The affine charts of the three restrictions -/

/-- The chart of a fibre product cut out by an open `T` of `A` lying over `W` lies over
`u ⁻¹ᵁ W`. -/
theorem preimage_snd_le_preimage_fst {A B S : Scheme.{u}} (u : B ⟶ S) (v : A ⟶ S)
    {W : S.Opens} {T : A.Opens} (hWT : T ≤ v ⁻¹ᵁ W) :
    pullback.snd u v ⁻¹ᵁ T ≤ pullback.fst u v ⁻¹ᵁ (u ⁻¹ᵁ W) := by
  have h : pullback.fst u v ⁻¹ᵁ (u ⁻¹ᵁ W) = pullback.snd u v ⁻¹ᵁ (v ⁻¹ᵁ W) :=
    congrArg (fun k : pullback u v ⟶ S ↦ k ⁻¹ᵁ W) pullback.condition
  rw [h]
  intro x hx
  exact hWT hx

/-- The chart of `Stacks.Pushout.affinePullbackChart_isPushout` is the preimage of `T`. -/
theorem affinePullbackChart_eq {A B S : Scheme.{u}} (u : B ⟶ S) (v : A ⟶ S)
    {W : S.Opens} {T : A.Opens} (hWT : T ≤ v ⁻¹ᵁ W) :
    pullback.fst u v ⁻¹ᵁ (u ⁻¹ᵁ W) ⊓ pullback.snd u v ⁻¹ᵁ T = pullback.snd u v ⁻¹ᵁ T :=
  inf_eq_right.mpr (preimage_snd_le_preimage_fst u v hWT)

/-- For an affine morphism `u : B ⟶ S`, an affine open `W` of `S` and an affine open `T` of `A`
lying over `W`, the square of coordinate rings of `W`, of `u ⁻¹ᵁ W`, of `T` and of the chart
`(B ×_S A ⟶ A) ⁻¹ᵁ T` of the fibre product is cocartesian. -/
theorem affineChart_isPushout {A B S : Scheme.{u}} (u : B ⟶ S) (v : A ⟶ S) [IsAffineHom u]
    {W : S.Opens} (hW : IsAffineOpen W) {T : A.Opens} (hT : IsAffineOpen T)
    (hWT : T ≤ v ⁻¹ᵁ W) :
    IsPushout (u.app W) (v.appLE W T hWT)
      ((pullback.fst u v).appLE (u ⁻¹ᵁ W) (pullback.snd u v ⁻¹ᵁ T)
        (preimage_snd_le_preimage_fst u v hWT))
      ((pullback.snd u v).appLE T (pullback.snd u v ⁻¹ᵁ T) le_rfl) := by
  have he := affinePullbackChart_eq u v hWT
  rw [Scheme.Hom.app_eq_appLE]
  refine (affinePullbackChart_isPushout u v hW hT hWT).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ((pullback u v).presheaf.mapIso (eqToIso he.symm).op) ?_ ?_ ?_ ?_
  all_goals simp

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- Over an affine open `W` of `Y'` and an affine open `U` of `V'` lying above it,
`Γ(V, (V ⟶ V') ⁻¹ᵁ U)` is the base change of `Γ(V', U)` along
`Γ(Y', W) ⟶ Γ(Y, (Y ⟶ Y') ⁻¹ᵁ W)`. -/
theorem targetChart_isPushout (hi : IsThickening i) [IsAffineHom f]
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W) :
    IsPushout ((pushout.inr i f).app W) (g.appLE W U hUW)
      ((targetBase i f g).appLE (pushout.inr i f ⁻¹ᵁ W) (targetRestriction i f g ⁻¹ᵁ U)
        (preimage_snd_le_preimage_fst (pushout.inr i f) g hUW))
      ((targetRestriction i f g).appLE U (targetRestriction i f g ⁻¹ᵁ U) le_rfl) := by
  have : IsClosedImmersion (pushout.inr i f) :=
    (pushout_inr_isThickening forall_isAffine_of_isThickening i f hi).1
  exact affineChart_isPushout (pushout.inr i f) g hW hU hUW

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- Over an affine open `W` of `Y'` and an affine open `U` of `V'` lying above it,
`Γ(U', (U' ⟶ V') ⁻¹ᵁ U)` is the base change of `Γ(V', U)` along
`Γ(Y', W) ⟶ Γ(X', (X' ⟶ Y') ⁻¹ᵁ W)`. -/
theorem ambientChart_isPushout (hi : IsThickening i) [IsAffineHom f]
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W) :
    IsPushout ((pushout.inl i f).app W) (g.appLE W U hUW)
      ((ambientBase i f g).appLE (pushout.inl i f ⁻¹ᵁ W) (ambientRestriction i f g ⁻¹ᵁ U)
        (preimage_snd_le_preimage_fst (pushout.inl i f) g hUW))
      ((ambientRestriction i f g).appLE U (ambientRestriction i f g ⁻¹ᵁ U) le_rfl) := by
  have : IsAffineHom (pushout.inl i f) := isAffineHom_pushout_inl_of_isThickening i f hi
  exact affineChart_isPushout (pushout.inl i f) g hW hU hUW

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- Over an affine open `W` of `Y'` and an affine open `U` of `V'` lying above it,
`Γ(U, (U ⟶ V') ⁻¹ᵁ U)` is the base change of `Γ(V', U)` along
`Γ(Y', W) ⟶ Γ(X, (X ⟶ Y') ⁻¹ᵁ W)`. -/
theorem commonChart_isPushout (hi : IsThickening i) [IsAffineHom f]
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W) :
    IsPushout ((i ≫ pushout.inl i f).app W) (g.appLE W U hUW)
      ((pullback.fst (i ≫ pushout.inl i f) g).appLE ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
        (commonRestriction i f g ⁻¹ᵁ U)
        (preimage_snd_le_preimage_fst (i ≫ pushout.inl i f) g hUW))
      ((commonRestriction i f g).appLE U (commonRestriction i f g ⁻¹ᵁ U) le_rfl) := by
  have : IsClosedImmersion i := hi.1
  have : IsAffineHom (pushout.inl i f) := isAffineHom_pushout_inl_of_isThickening i f hi
  have : IsAffineHom (i ≫ pushout.inl i f) := inferInstance
  exact affineChart_isPushout (i ≫ pushout.inl i f) g hW hU hUW

/-! ### The affine charts as the three base-change rings -/

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- The fourth assertion of [Stacks Project, Tag 07RT] over the common chart: for an open `W`
of `Y'`, the square of the two restrictions `Γ(Y', W) ⟶ Γ(Y, (Y ⟶ Y') ⁻¹ᵁ W)` and
`Γ(Y', W) ⟶ Γ(X', (X' ⟶ Y') ⁻¹ᵁ W)` against `Stacks.Pushout.chartToBase` and
`Stacks.Pushout.chartSurjection` is cartesian. -/
theorem chartSections_isPullback (hi : IsThickening i) [IsAffineHom f]
    (W : (pushout i f).Opens) :
    IsPullback ((pushout.inr i f).app W) ((pushout.inl i f).app W)
      (f.appLE (pushout.inr i f ⁻¹ᵁ W) ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
        (commonBase_le_targetBase i f W))
      (i.appLE (pushout.inl i f ⁻¹ᵁ W) ((i ≫ pushout.inl i f) ⁻¹ᵁ W) le_rfl) := by
  have hΓ : Γ(X, (i ≫ pushout.inl i f) ⁻¹ᵁ W) = Γ(X, f ⁻¹ᵁ (pushout.inr i f ⁻¹ᵁ W)) :=
    congrArg (fun V : X.Opens ↦ Γ(X, V)) (commonBase_eq_targetBase i f W)
  have hmap : X.presheaf.map (homOfLE (commonBase_le_targetBase i f W)).op =
      eqToHom hΓ.symm := by
    rw [show (homOfLE (commonBase_le_targetBase i f W)).op =
      eqToHom (congrArg Opposite.op (commonBase_eq_targetBase i f W)).symm from
        Subsingleton.elim _ _, eqToHom_map]
  refine (pushout_structureSheaf_isPullback forall_isAffine_of_isThickening i f hi W).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (eqToIso hΓ).symm ?_ ?_ ?_ ?_
  · simp
  · simp
  · rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, eqToIso.inv, Scheme.Hom.appLE, hmap]
  · rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, eqToIso.inv, Category.assoc,
      eqToHom_trans, ← Scheme.Hom.appLE_eq_app]
    exact Category.comp_id _

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- For an affine open `W` of `Y'` and an open `U` of `V'` lying above it, there is a relative
fibre-product situation `MilnorPatching.RelativeModuleFibreProductSituation` with
`D' = Γ(V', U)` over the ring fibre product of `Stacks.Pushout.chartToBase` and
`Stacks.Pushout.chartSurjection`, together with a ring isomorphism from `Γ(Y', W)` to that fibre
product carrying its structure maps to restriction along `g`, along `Y ⟶ Y'` and along
`X' ⟶ Y'`. -/
theorem exists_chartSituation (hi : IsThickening i) [IsAffineHom f]
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hUW : U ≤ g ⁻¹ᵁ W) :
    ∃ (I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W))
      (base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I)
      (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
      (e : Γ(pushout i f, W) ≃+* base.fibreProduct),
      s.toD'.comp e.toRingHom = (g.appLE W U hUW).hom ∧
        (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).comp
            e.toRingHom = ((pushout.inr i f).app W).hom ∧
          (MilnorPatching.RelativeModuleFibreProductSituation.toA' (base := base)).comp
            e.toRingHom = ((pushout.inl i f).app W).hom := by
  have : IsClosedImmersion i := hi.1
  have : IsAffineHom (pushout.inl i f) := isAffineHom_pushout_inl_of_isThickening i f hi
  have hA' : IsAffineOpen (pushout.inl i f ⁻¹ᵁ W) := hW.preimage (pushout.inl i f)
  have hsurj : Function.Surjective (chartSurjection i f W) := by
    have h := i.app_surjective (pushout.inl i f ⁻¹ᵁ W) hA'
    rwa [← Scheme.Hom.appLE_eq_app] at h
  refine ⟨RingHom.ker (chartSurjection i f W), ⟨hsurj, rfl⟩, ?_⟩
  have hsq := chartSections_isPullback i f hi W
  have hcan := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit
    (CommRingCat.ofHom (chartToBase i f W)) (CommRingCat.ofHom (chartSurjection i f W)))
  let E := hsq.isoIsPullback _ _ hcan
  let e := E.commRingCatIsoToRingEquiv
  refine ⟨⟨(g.appLE W U hUW).hom.comp e.symm.toRingHom⟩, e, ?_, ?_, ?_⟩
  · exact RingHom.ext fun r ↦ congrArg (fun z ↦ (g.appLE W U hUW).hom z) (e.symm_apply_apply r)
  · exact congrArg CommRingCat.Hom.hom (hsq.isoIsPullback_hom_fst _ _ hcan)
  · exact congrArg CommRingCat.Hom.hom (hsq.isoIsPullback_hom_snd _ _ hcan)

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- In a situation as produced by `Stacks.Pushout.exists_chartSituation`,
`D = Γ(V', U) ⊗_{Γ(Y', W)} Γ(Y, (Y ⟶ Y') ⁻¹ᵁ W)` is `Γ(V, (V ⟶ V') ⁻¹ᵁ U)`, by a ring isomorphism
carrying the canonical map out of `Γ(V', U)` to restriction along `V ⟶ V'` and the canonical map
out of `Γ(Y, (Y ⟶ Y') ⁻¹ᵁ W)` to restriction along `V ⟶ Y`. -/
theorem exists_targetChartRingEquiv (hi : IsThickening i) [IsAffineHom f]
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W)
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    (base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I)
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
    (e : Γ(pushout i f, W) ≃+* base.fibreProduct)
    (hD' : s.toD'.comp e.toRingHom = (g.appLE W U hUW).hom)
    (heB : (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).comp
      e.toRingHom = ((pushout.inr i f).app W).hom) :
    ∃ kD : s.D ≃+* Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U),
      (∀ d : Γ(V', U), kD (s.toD d) =
          (targetRestriction i f g).appLE U (targetRestriction i f g ⁻¹ᵁ U) le_rfl d) ∧
        (∀ x : Γ(Y, pushout.inr i f ⁻¹ᵁ W), kD (s.BtoD x) =
          (targetBase i f g).appLE (pushout.inr i f ⁻¹ᵁ W) (targetRestriction i f g ⁻¹ᵁ U)
            (preimage_snd_le_preimage_fst (pushout.inr i f) g hUW) x) :=
  exists_tensorEquiv_of_isPushout
    (g.appLE W U hUW).hom ((pushout.inr i f).app W).hom
    ((targetRestriction i f g).appLE U (targetRestriction i f g ⁻¹ᵁ U) le_rfl).hom
    ((targetBase i f g).appLE (pushout.inr i f ⁻¹ᵁ W) (targetRestriction i f g ⁻¹ᵁ U)
      (preimage_snd_le_preimage_fst (pushout.inr i f) g hUW)).hom
    (targetChart_isPushout i f g hi hW hU hUW).flip
    e s.toD' (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)) hD' heB

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- In a situation as produced by `Stacks.Pushout.exists_chartSituation`,
`C' = Γ(V', U) ⊗_{Γ(Y', W)} Γ(X', (X' ⟶ Y') ⁻¹ᵁ W)` is `Γ(U', (U' ⟶ V') ⁻¹ᵁ U)`, by a ring
isomorphism carrying the canonical map out of `Γ(V', U)` to restriction along `U' ⟶ V'` and the
canonical map out of `Γ(X', (X' ⟶ Y') ⁻¹ᵁ W)` to restriction along `U' ⟶ X'`. -/
theorem exists_ambientChartRingEquiv (hi : IsThickening i) [IsAffineHom f]
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W)
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    (base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I)
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
    (e : Γ(pushout i f, W) ≃+* base.fibreProduct)
    (hD' : s.toD'.comp e.toRingHom = (g.appLE W U hUW).hom)
    (heA' : (MilnorPatching.RelativeModuleFibreProductSituation.toA' (base := base)).comp
      e.toRingHom = ((pushout.inl i f).app W).hom) :
    ∃ kC' : s.C' ≃+* Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U),
      (∀ d : Γ(V', U), kC' (s.toC' d) =
          (ambientRestriction i f g).appLE U (ambientRestriction i f g ⁻¹ᵁ U) le_rfl d) ∧
        (∀ x : Γ(X', pushout.inl i f ⁻¹ᵁ W), kC' (s.A'toC' x) =
          (ambientBase i f g).appLE (pushout.inl i f ⁻¹ᵁ W) (ambientRestriction i f g ⁻¹ᵁ U)
            (preimage_snd_le_preimage_fst (pushout.inl i f) g hUW) x) :=
  exists_tensorEquiv_of_isPushout
    (g.appLE W U hUW).hom ((pushout.inl i f).app W).hom
    ((ambientRestriction i f g).appLE U (ambientRestriction i f g ⁻¹ᵁ U) le_rfl).hom
    ((ambientBase i f g).appLE (pushout.inl i f ⁻¹ᵁ W) (ambientRestriction i f g ⁻¹ᵁ U)
      (preimage_snd_le_preimage_fst (pushout.inl i f) g hUW)).hom
    (ambientChart_isPushout i f g hi hW hU hUW).flip
    e s.toD' (MilnorPatching.RelativeModuleFibreProductSituation.toA' (base := base)) hD' heA'

omit [IsAffineHom f] in
/-- The composite of the chart fibre product with its first leg is the restriction
`Γ(Y', W) ⟶ Γ(X, (X ⟶ Y') ⁻¹ᵁ W)` along `X ⟶ Y'`. -/
theorem toA_comp_ringEquiv {W : (pushout i f).Opens}
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    {base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I}
    (e : Γ(pushout i f, W) ≃+* base.fibreProduct)
    (heB : (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).comp
      e.toRingHom = ((pushout.inr i f).app W).hom) :
    (MilnorPatching.RelativeModuleFibreProductSituation.toA (base := base)).comp
      e.toRingHom = ((i ≫ pushout.inl i f).app W).hom := by
  have hassoc : (MilnorPatching.RelativeModuleFibreProductSituation.toA (base := base)).comp
      e.toRingHom =
      (chartToBase i f W).comp
        ((MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).comp
          e.toRingHom) := rfl
  rw [hassoc, heB]
  exact congrArg CommRingCat.Hom.hom (app_comp_chartToBase i f W)

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- In a situation as produced by `Stacks.Pushout.exists_chartSituation`,
`C = Γ(V', U) ⊗_{Γ(Y', W)} Γ(X, (X ⟶ Y') ⁻¹ᵁ W)` is `Γ(U, (U ⟶ V') ⁻¹ᵁ U)`, by a ring isomorphism
carrying the canonical map out of `Γ(V', U)` to restriction along `U ⟶ V'` and the canonical map
out of `Γ(X, (X ⟶ Y') ⁻¹ᵁ W)` to restriction along `U ⟶ X`. -/
theorem exists_commonChartRingEquiv (hi : IsThickening i) [IsAffineHom f]
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W)
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    (base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I)
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
    (e : Γ(pushout i f, W) ≃+* base.fibreProduct)
    (hD' : s.toD'.comp e.toRingHom = (g.appLE W U hUW).hom)
    (heB : (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).comp
      e.toRingHom = ((pushout.inr i f).app W).hom) :
    ∃ kC : s.C ≃+* Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U),
      (∀ d : Γ(V', U), kC (s.DtoC (s.toD d)) =
          (commonRestriction i f g).appLE U (commonRestriction i f g ⁻¹ᵁ U) le_rfl d) ∧
        (∀ x : Γ(X, (i ≫ pushout.inl i f) ⁻¹ᵁ W), kC (s.AtoC x) =
          (pullback.fst (i ≫ pushout.inl i f) g).appLE ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
            (commonRestriction i f g ⁻¹ᵁ U)
            (preimage_snd_le_preimage_fst (i ≫ pushout.inl i f) g hUW) x) := by
  obtain ⟨kC, hkC1, hkC2⟩ := exists_tensorEquiv_of_isPushout
    (g.appLE W U hUW).hom ((i ≫ pushout.inl i f).app W).hom
    ((commonRestriction i f g).appLE U (commonRestriction i f g ⁻¹ᵁ U) le_rfl).hom
    ((pullback.fst (i ≫ pushout.inl i f) g).appLE ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
      (commonRestriction i f g ⁻¹ᵁ U)
      (preimage_snd_le_preimage_fst (i ≫ pushout.inl i f) g hUW)).hom
    (commonChart_isPushout i f g hi hW hU hUW).flip
    e s.toD' (MilnorPatching.RelativeModuleFibreProductSituation.toA (base := base)) hD'
    (toA_comp_ringEquiv i f e heB)
  refine ⟨kC, fun d ↦ ?_, hkC2⟩
  let : Algebra base.fibreProduct Γ(V', U) := s.toD'.toAlgebra
  let : Algebra base.fibreProduct Γ(Y, pushout.inr i f ⁻¹ᵁ W) :=
    (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).toAlgebra
  let : Algebra base.fibreProduct Γ(X, (i ≫ pushout.inl i f) ⁻¹ᵁ W) :=
    (MilnorPatching.RelativeModuleFibreProductSituation.toA (base := base)).toAlgebra
  have hz : s.DtoC (s.toD d) =
      (d ⊗ₜ[base.fibreProduct] (1 : Γ(X, (i ≫ pushout.inl i f) ⁻¹ᵁ W))) :=
    tensorMap_includeLeft _ d
  rw [hz]
  exact hkC1 d

omit [IsAffineHom f] in
/-- Under the isomorphisms of `Stacks.Pushout.exists_targetChartRingEquiv` and
`Stacks.Pushout.exists_commonChartRingEquiv`, the base-changed map `D ⟶ C` of the situation is
restriction along `U ⟶ V`. -/
theorem chartRingEquiv_DtoC {W : (pushout i f).Opens} {U : V'.Opens} (hUW : U ≤ g ⁻¹ᵁ W)
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    {base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
    (kD : s.D ≃+* Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U))
    (kC : s.C ≃+* Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U))
    (hkD1 : ∀ d : Γ(V', U), kD (s.toD d) =
      (targetRestriction i f g).appLE U (targetRestriction i f g ⁻¹ᵁ U) le_rfl d)
    (hkD2 : ∀ x : Γ(Y, pushout.inr i f ⁻¹ᵁ W), kD (s.BtoD x) =
      (targetBase i f g).appLE (pushout.inr i f ⁻¹ᵁ W) (targetRestriction i f g ⁻¹ᵁ U)
        (preimage_snd_le_preimage_fst (pushout.inr i f) g hUW) x)
    (hkC1 : ∀ d : Γ(V', U), kC (s.DtoC (s.toD d)) =
      (commonRestriction i f g).appLE U (commonRestriction i f g ⁻¹ᵁ U) le_rfl d)
    (hkC2 : ∀ x : Γ(X, (i ≫ pushout.inl i f) ⁻¹ᵁ W), kC (s.AtoC x) =
      (pullback.fst (i ≫ pushout.inl i f) g).appLE ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
        (commonRestriction i f g ⁻¹ᵁ U)
        (preimage_snd_le_preimage_fst (i ≫ pushout.inl i f) g hUW) x) :
    ∀ z : s.D, kC (s.DtoC z) =
      (commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U) (kD z) := by
  let : Algebra base.fibreProduct Γ(V', U) := s.toD'.toAlgebra
  let : Algebra base.fibreProduct Γ(Y, pushout.inr i f ⁻¹ᵁ W) :=
    (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).toAlgebra
  have id1 : (targetRestriction i f g).appLE U (targetRestriction i f g ⁻¹ᵁ U) le_rfl ≫
      (commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U) =
      (commonRestriction i f g).appLE U (commonRestriction i f g ⁻¹ᵁ U) le_rfl :=
    (Scheme.Hom.appLE_comp_appLE (commonToTarget i f g) (targetRestriction i f g)
      _ _ _ _ _).trans
      (appLE_congr_morphism (commonToTarget_comp_restriction i f g) U _ _ le_rfl)
  have id2 : (targetBase i f g).appLE (pushout.inr i f ⁻¹ᵁ W) (targetRestriction i f g ⁻¹ᵁ U)
        (preimage_snd_le_preimage_fst (pushout.inr i f) g hUW) ≫
      (commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U) =
      f.appLE (pushout.inr i f ⁻¹ᵁ W) ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
          (commonBase_le_targetBase i f W) ≫
        (pullback.fst (i ≫ pushout.inl i f) g).appLE ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
          (commonRestriction i f g ⁻¹ᵁ U)
          (preimage_snd_le_preimage_fst (i ≫ pushout.inl i f) g hUW) :=
    (Scheme.Hom.appLE_comp_appLE (commonToTarget i f g) (targetBase i f g) _ _ _ _ _).trans
      ((appLE_congr_morphism (commonToTarget_comp_base i f g) _ _ _ _).trans
        (Scheme.Hom.appLE_comp_appLE (pullback.fst (i ≫ pushout.inl i f) g) f
          _ _ _ _ _).symm)
  have id1' : ∀ d : Γ(V', U),
      ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U))
          ((targetRestriction i f g).appLE U (targetRestriction i f g ⁻¹ᵁ U) le_rfl d) =
      (commonRestriction i f g).appLE U (commonRestriction i f g ⁻¹ᵁ U) le_rfl d := fun d ↦ by
    have h := congrArg (fun k : Γ(V', U) ⟶
      Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U) ↦ k d) id1
    simpa only [CommRingCat.comp_apply] using h
  have id2' : ∀ x : Γ(Y, pushout.inr i f ⁻¹ᵁ W),
      ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U))
          ((targetBase i f g).appLE (pushout.inr i f ⁻¹ᵁ W) (targetRestriction i f g ⁻¹ᵁ U)
            (preimage_snd_le_preimage_fst (pushout.inr i f) g hUW) x) =
      (pullback.fst (i ≫ pushout.inl i f) g).appLE ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
          (commonRestriction i f g ⁻¹ᵁ U)
          (preimage_snd_le_preimage_fst (i ≫ pushout.inl i f) g hUW)
        (chartToBase i f W x) := fun x ↦ by
    have h := congrArg (fun k : Γ(Y, pushout.inr i f ⁻¹ᵁ W) ⟶
      Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U) ↦ k x) id2
    simpa only [CommRingCat.comp_apply] using h
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul d x =>
    have h1 : (s.toD d : s.D) = d ⊗ₜ[base.fibreProduct] (1 : Γ(Y, pushout.inr i f ⁻¹ᵁ W)) := rfl
    have h2 : (s.BtoD x : s.D) = (1 : Γ(V', U)) ⊗ₜ[base.fibreProduct] x := rfl
    have hmul : (d ⊗ₜ[base.fibreProduct] x) = s.toD d * s.BtoD x := by
      rw [h1, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hright : s.DtoC (s.BtoD x) = s.AtoC (chartToBase i f W x) :=
      congrArg (fun k : Γ(Y, pushout.inr i f ⁻¹ᵁ W) →+* s.C ↦ k x) s.DtoC_BtoD
    rw [hmul]
    simp only [map_mul]
    rw [hkC1, hright, hkC2, hkD1, hkD2, id1', id2']
  | add z w hz hw => simp only [map_add, hz, hw]

omit [IsAffineHom f] in
/-- Under the isomorphisms of `Stacks.Pushout.exists_ambientChartRingEquiv` and
`Stacks.Pushout.exists_commonChartRingEquiv`, the base-changed map `C' ⟶ C` of the situation is
restriction along `U ⟶ U'`. -/
theorem chartRingEquiv_C'toC {W : (pushout i f).Opens} {U : V'.Opens} (hUW : U ≤ g ⁻¹ᵁ W)
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    {base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
    (kC' : s.C' ≃+* Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U))
    (kC : s.C ≃+* Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U))
    (hkC'1 : ∀ d : Γ(V', U), kC' (s.toC' d) =
      (ambientRestriction i f g).appLE U (ambientRestriction i f g ⁻¹ᵁ U) le_rfl d)
    (hkC'2 : ∀ x : Γ(X', pushout.inl i f ⁻¹ᵁ W), kC' (s.A'toC' x) =
      (ambientBase i f g).appLE (pushout.inl i f ⁻¹ᵁ W) (ambientRestriction i f g ⁻¹ᵁ U)
        (preimage_snd_le_preimage_fst (pushout.inl i f) g hUW) x)
    (hkC1 : ∀ d : Γ(V', U), kC (s.C'toC (s.toC' d)) =
      (commonRestriction i f g).appLE U (commonRestriction i f g ⁻¹ᵁ U) le_rfl d)
    (hkC2 : ∀ x : Γ(X, (i ≫ pushout.inl i f) ⁻¹ᵁ W), kC (s.AtoC x) =
      (pullback.fst (i ≫ pushout.inl i f) g).appLE ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
        (commonRestriction i f g ⁻¹ᵁ U)
        (preimage_snd_le_preimage_fst (i ≫ pushout.inl i f) g hUW) x) :
    ∀ z : s.C', kC (s.C'toC z) =
      (commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U) (kC' z) := by
  let : Algebra base.fibreProduct Γ(V', U) := s.toD'.toAlgebra
  let : Algebra base.fibreProduct Γ(X', pushout.inl i f ⁻¹ᵁ W) :=
    (MilnorPatching.RelativeModuleFibreProductSituation.toA' (base := base)).toAlgebra
  have id3 : (ambientRestriction i f g).appLE U (ambientRestriction i f g ⁻¹ᵁ U) le_rfl ≫
      (commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U) =
      (commonRestriction i f g).appLE U (commonRestriction i f g ⁻¹ᵁ U) le_rfl :=
    (Scheme.Hom.appLE_comp_appLE (commonToAmbient i f g) (ambientRestriction i f g)
      _ _ _ _ _).trans
      (appLE_congr_morphism (commonToAmbient_comp_restriction i f g) U _ _ le_rfl)
  have id4 : (ambientBase i f g).appLE (pushout.inl i f ⁻¹ᵁ W) (ambientRestriction i f g ⁻¹ᵁ U)
        (preimage_snd_le_preimage_fst (pushout.inl i f) g hUW) ≫
      (commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U) =
      i.appLE (pushout.inl i f ⁻¹ᵁ W) ((i ≫ pushout.inl i f) ⁻¹ᵁ W) le_rfl ≫
        (pullback.fst (i ≫ pushout.inl i f) g).appLE ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
          (commonRestriction i f g ⁻¹ᵁ U)
          (preimage_snd_le_preimage_fst (i ≫ pushout.inl i f) g hUW) :=
    (Scheme.Hom.appLE_comp_appLE (commonToAmbient i f g) (ambientBase i f g) _ _ _ _ _).trans
      ((appLE_congr_morphism (commonToAmbient_comp_base i f g) _ _ _ _).trans
        (Scheme.Hom.appLE_comp_appLE (pullback.fst (i ≫ pushout.inl i f) g) i
          _ _ _ _ _).symm)
  have id3' : ∀ d : Γ(V', U),
      ((commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U))
          ((ambientRestriction i f g).appLE U (ambientRestriction i f g ⁻¹ᵁ U) le_rfl d) =
      (commonRestriction i f g).appLE U (commonRestriction i f g ⁻¹ᵁ U) le_rfl d := fun d ↦ by
    have h := congrArg (fun k : Γ(V', U) ⟶
      Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U) ↦ k d) id3
    simpa only [CommRingCat.comp_apply] using h
  have id4' : ∀ x : Γ(X', pushout.inl i f ⁻¹ᵁ W),
      ((commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U))
          ((ambientBase i f g).appLE (pushout.inl i f ⁻¹ᵁ W) (ambientRestriction i f g ⁻¹ᵁ U)
            (preimage_snd_le_preimage_fst (pushout.inl i f) g hUW) x) =
      (pullback.fst (i ≫ pushout.inl i f) g).appLE ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
          (commonRestriction i f g ⁻¹ᵁ U)
          (preimage_snd_le_preimage_fst (i ≫ pushout.inl i f) g hUW)
        (chartSurjection i f W x) := fun x ↦ by
    have h := congrArg (fun k : Γ(X', pushout.inl i f ⁻¹ᵁ W) ⟶
      Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U) ↦ k x) id4
    simpa only [CommRingCat.comp_apply] using h
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul d x =>
    have h1 : (s.toC' d : s.C') =
      d ⊗ₜ[base.fibreProduct] (1 : Γ(X', pushout.inl i f ⁻¹ᵁ W)) := rfl
    have h2 : (s.A'toC' x : s.C') = (1 : Γ(V', U)) ⊗ₜ[base.fibreProduct] x := rfl
    have hmul : (d ⊗ₜ[base.fibreProduct] x) = s.toC' d * s.A'toC' x := by
      rw [h1, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hright : s.C'toC (s.A'toC' x) = s.AtoC (chartSurjection i f W x) :=
      congrArg (fun k : Γ(X', pushout.inl i f ⁻¹ᵁ W) →+* s.C ↦ k x) s.C'toC_A'toC'
    rw [hmul]
    simp only [map_mul]
    rw [hkC1, hright, hkC2, hkC'1, hkC'2, id3', id4']
  | add z w hz hw => simp only [map_add, hz, hw]

end Stacks.Pushout

end
