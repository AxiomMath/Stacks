module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.OpenCover
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsPerfectIsCompact
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# Lifting perfect complexes from a quasi-compact open, with support

Let `S` be a quasi-compact quasi-separated scheme, `W ⊆ S` a quasi-compact open, `E` an object of
`D_QCoh(𝒪_S)` and `α : P ⟶ E|_W` a morphism from a perfect object of `D(𝒪_W)`. Then there is a
perfect object `Q` of `D(𝒪_S)` with `Q|_W ≅ P ⊕ P[1]` and a morphism `Q ⟶ E` restricting to `α`
on the summand `P`. If moreover `P` vanishes on `W ∩ Y` for a second quasi-compact open `Y`, then
`Q` can be chosen to vanish on `Y`.

This is the lifting step of the proofs of [Stacks, Tag 08ER] and [Stacks, Tag 09IM] on the affine
member `V` of the cover, where the source cites [Stacks, Tag 08EK] for `Q` and
[Stacks, Tag 08EH] for the lift of the morphism; the support condition is the case
`Y = V ∖ T`.

## Main results

* `Stacks.Duality.OpenImmersion.exists_isPerfect_lift`: the lift without support condition.
* `Stacks.Duality.OpenImmersion.exists_isPerfect_lift_of_isZero_stalk`: the lift vanishing on
  `Y`.

## Implementation notes

Everything is at the locally small model, where `D_QCoh(𝒪_S)` is compactly generated. The object
`Q` comes from `CategoryTheory.Pretriangulated.exists_isCompactObject_iso_biprod_shift`, for the
adjunction `j^* ⊣ Rj_*` and the compact objects detecting its kernel
(`Stacks.Duality.SupportedGeneration.kernelDetected`), and the morphism from
`CategoryTheory.Pretriangulated.exists_roof`, whose target need not be compact; compact objects
of `D_QCoh` are the perfect ones by [Stacks, Tag 09M1]. The support condition is obtained by
lifting first from `W` to `W ∪ Y` by `Rj_*`, which vanishes on `Y`
(`Stacks.Duality.OpenImmersion.exists_extension_of_isZero_derivedRestrict`), so that the lift to
`S` restricts on `Y` to a sum of objects vanishing there.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty
open Stacks.Duality.QcqsGeneration Stacks.Duality.SupportedGeneration ZeroObject

universe u

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

namespace Stacks.Duality.OpenImmersion

/-- **Lifting a perfect object with a morphism from a quasi-compact open.** Let `S` be a
quasi-compact quasi-separated scheme, `j : U ⟶ S` a quasi-compact open immersion, `E` an object of
`D(𝒪_S)` with quasi-coherent cohomology and `α : P ⟶ E|_U` a morphism from a perfect object.
Then there are a perfect object `Q` of `D(𝒪_S)`, an isomorphism `Q|_U ≅ P ⊕ P[1]` and a morphism
`β : Q ⟶ E` whose restriction to `U` is `α` on the first summand and zero on the second. -/
theorem exists_isPerfect_lift {S U : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace U] [QuasiSeparatedSpace U] (j : U ⟶ S) [IsOpenImmersion j]
    [AlgebraicGeometry.QuasiCompact j] (P : DerivedCategory U.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := U.toRingedSpace) P)
    (E : DerivedCategory S.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor S.Modules i).obj E).IsQuasicoherent)
    (α : P ⟶ (derivedRestrict j).obj E) :
    ∃ (Q : DerivedCategory S.Modules) (e : (derivedRestrict j).obj Q ≅ P ⊞ P⟦(1 : ℤ)⟧)
      (β : Q ⟶ E), Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace) Q ∧
        (derivedRestrict j).map β = e.hom ≫ biprod.fst ≫ α := by
  let ιU := (DerivedCategoryB.derivedCategoryB (A := U.Modules)
    (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι
  let P' : Stacks.Duality.quasiCoherentDerivedCategory U :=
    ⟨P, isQuasicoherentDerived_of_isPseudoCoherent U P
      (show AlgebraicGeometry.RingedSpace.IsPerfect (X := U.toRingedSpace) P from
        hP).isPseudoCoherent⟩
  let E' : Stacks.Duality.quasiCoherentDerivedCategory S := ⟨E, hE⟩
  have hP' : IsCompactObject.{u} P' :=
    Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect _ P' hP
  let α' : P' ⟶ (restrictedDerivedRestrict j).obj E' := ObjectProperty.homMk α
  obtain ⟨ι₁, K, hKc, hK0, hKdet⟩ := kernelDetected j
  let adj := restrictedDerivedRestrictAdjunction j
  have : (Stacks.Duality.quasiCoherentDerivedPushforward j
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)).Additive :=
    adj.right_adjoint_additive
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward j
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward j
  obtain ⟨ι₀, G, hGc, hGgen⟩ :=
    Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory S
  let G' : Option ι₀ → Stacks.Duality.quasiCoherentDerivedCategory S := fun o => o.elim 0 G
  have hG'c : ∀ o, IsCompactObject.{u} (G' o) := fun o => by
    cases o with
    | none => exact isCompactObject_zero' (T := Stacks.Duality.quasiCoherentDerivedCategory S)
    | some k => exact hGc k
  have hG'gen : (ofObj G').IsWeakTriangulatedGenerator := fun F hF => hGgen F <| by
    rw [rightOrthogonal_shiftClosure_ofObj_iff] at hF ⊢
    exact fun k n g => hF (some k) n g
  obtain ⟨c, hc, ⟨e₀⟩⟩ :=
    exists_isCompactObject_iso_biprod_shift adj K hKc hK0 hKdet G' hG'c hG'gen P' hP'
  have : IsCompactObject.{u} c := hc
  obtain ⟨c', s, g', hc', hs, hg'⟩ :=
    exists_roof adj K hKc hK0 hKdet (c₁ := c) (c₂ := E') (e₀.hom ≫ biprod.fst ≫ α')
  have := hs
  let e' : (restrictedDerivedRestrict j).obj c' ≅ P' ⊞ P'⟦(1 : ℤ)⟧ :=
    asIso ((restrictedDerivedRestrict j).map s) ≪≫ e₀
  have hβ' : (restrictedDerivedRestrict j).map g' = e'.hom ≫ biprod.fst ≫ α' := by
    rw [hg']
    simp [e']
  have : ιU.Additive := inferInstance
  let e : (derivedRestrict j).obj c'.obj ≅ P ⊞ P⟦(1 : ℤ)⟧ :=
    ιU.mapIso e' ≪≫ ιU.mapBiprod _ _ ≪≫ biprod.mapIso (Iso.refl _) ((ιU.commShiftIso 1).app P')
  refine ⟨c'.obj, e, g'.hom, Stacks.Duality.isPerfect_of_isCompactObject c' hc', ?_⟩
  rw [show (derivedRestrict j).map g'.hom = ιU.map ((restrictedDerivedRestrict j).map g') from rfl,
    hβ', ιU.map_comp, ιU.map_comp]
  simp only [e, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, biprod.mapIso_hom,
    Functor.mapBiprod_hom, biprod.lift_map_assoc, biprod.lift_fst_assoc, Iso.refl_hom,
    Category.comp_id]
  rfl

/-- The restriction along an open immersion of an object whose cohomology sheaves vanish at the
points of its image vanishes. -/
theorem isZero_derivedRestrict_of_isZero_stalk {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (K : DerivedCategory Y.Modules)
    (hK : ∀ (i : ℤ) (x : U), IsZero (TopCat.Presheaf.stalk (X := Y)
      (((DerivedCategory.homologyFunctor Y.Modules i).obj K).val.presheaf) (j x))) :
    IsZero ((derivedRestrict j).obj K) :=
  (DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun i =>
    (isZero_homology_iff_forall_isZero_stalk _ i).2 fun x =>
      (hK i x).of_iso (stalkHomologyDerivedRestrictIso j K i x)

/-- The cohomology sheaves of an object whose restriction along an open immersion vanishes have
vanishing stalks at the points of its image. -/
theorem isZero_stalk_of_isZero_derivedRestrict {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (K : DerivedCategory Y.Modules) (hK : IsZero ((derivedRestrict j).obj K))
    (i : ℤ) (x : U) :
    IsZero (TopCat.Presheaf.stalk (X := Y)
      (((DerivedCategory.homologyFunctor Y.Modules i).obj K).val.presheaf) (j x)) :=
  ((isZero_homology_iff_forall_isZero_stalk _ i).1
    ((DerivedCategory.homologyFunctor U.Modules i).map_isZero hK) x).of_iso
      (stalkHomologyDerivedRestrictIso j K i x).symm

/-- **Lifting a perfect object with a morphism from a quasi-compact open, with support.** Let `S`
be a quasi-compact quasi-separated scheme, `W` and `Y` quasi-compact opens of `S`, `E` an object
of `D(𝒪_S)` with quasi-coherent cohomology and `α : P ⟶ E|_W` a morphism from a perfect object
whose cohomology sheaves vanish at the points of `W ∩ Y`. Then there are a perfect object `Q` of
`D(𝒪_S)` whose cohomology sheaves vanish at the points of `Y`, an isomorphism `Q|_W ≅ P ⊕ P[1]`
and a morphism `β : Q ⟶ E` whose restriction to `W` is `α` on the first summand and zero on the
second. -/
theorem exists_isPerfect_lift_of_isZero_stalk {S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] (W Y : S.Opens) (hW : IsCompact (W : Set S))
    (hY : IsCompact (Y : Set S)) (P : DerivedCategory W.toScheme.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toScheme.toRingedSpace) P)
    (hPY : ∀ (i : ℤ) (x : W.toScheme), x.1 ∈ Y → IsZero (TopCat.Presheaf.stalk
      (((DerivedCategory.homologyFunctor W.toScheme.Modules i).obj P).val.presheaf) x))
    (E : DerivedCategory S.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor S.Modules i).obj E).IsQuasicoherent)
    (α : P ⟶ (derivedRestrict W.ι).obj E) :
    ∃ (Q : DerivedCategory S.Modules) (e : (derivedRestrict W.ι).obj Q ≅ P ⊞ P⟦(1 : ℤ)⟧)
      (β : Q ⟶ E), Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace) Q ∧
        (∀ (i : ℤ) (x : S), x ∈ Y → IsZero (TopCat.Presheaf.stalk (X := S)
          (((DerivedCategory.homologyFunctor S.Modules i).obj Q).val.presheaf) x)) ∧
        (derivedRestrict W.ι).map β = e.hom ≫ biprod.fst ≫ α := by
  let W' : S.Opens := W ⊔ Y
  have : CompactSpace W'.toScheme := isCompact_iff_compactSpace.mp (hW.union hY)
  have : QuasiSeparatedSpace W'.toScheme := W'.ι.isOpenEmbedding.quasiSeparatedSpace
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  have : QuasiSeparatedSpace W.toScheme := W.ι.isOpenEmbedding.quasiSeparatedSpace
  let ι := S.homOfLE (le_sup_left : W ≤ W')
  let κ := S.homOfLE (le_sup_right : Y ≤ W')
  let a := S.homOfLE (inf_le_left : W ⊓ Y ≤ W)
  let b := S.homOfLE (inf_le_right : W ⊓ Y ≤ Y)
  have hsq : IsPullback a b ι κ := isPullback_opens_inf_le le_sup_left le_sup_right
  have hcov : ∀ y : W'.toScheme, (∃ x, ι x = y) ∨ (∃ x, κ x = y) := by
    intro y
    rcases y.2 with h | h
    · exact Or.inl ⟨⟨y.1, h⟩, Subtype.ext (S.homOfLE_apply _ _)⟩
    · exact Or.inr ⟨⟨y.1, h⟩, Subtype.ext (S.homOfLE_apply _ _)⟩
  let θ : derivedRestrict W.ι ≅ derivedRestrict W'.ι ⋙ derivedRestrict ι :=
    derivedRestrictCongr (S.homOfLE_ι (le_sup_left : W ≤ W')).symm ≪≫
      derivedRestrictCompIso ι W'.ι
  let E' := (derivedRestrict W'.ι).obj E
  let α₁ : P ⟶ (derivedRestrict ι).obj E' := α ≫ θ.hom.app E
  have hp : IsZero ((derivedRestrict a).obj P) :=
    isZero_derivedRestrict_of_isZero_stalk a P fun i x =>
      hPY i (a x) ((S.homOfLE_apply _ x : (a x).1 = x.1) ▸ x.2.2)
  obtain ⟨g, eg, γ, hgY, hγ⟩ :=
    exists_extension_of_isZero_derivedRestrict ι κ a b hsq hcov P hp E' α₁
  have hg : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W'.toScheme.toRingedSpace) g :=
    isPerfect_of_isPerfect_derivedRestrict_two ι κ hcov g
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso eg.symm hP)
      (AlgebraicGeometry.RingedSpace.isPerfect_of_isZero hgY)
  obtain ⟨Q, e', β, hQ, hβ⟩ := exists_isPerfect_lift W'.ι g hg E hE γ
  have hQκ : IsZero ((derivedRestrict κ).obj ((derivedRestrict W'.ι).obj Q)) := by
    refine IsZero.of_iso ?_ ((derivedRestrict κ).mapIso e')
    refine IsZero.of_iso ?_ ((derivedRestrict κ).mapBiprod _ _)
    exact (biprod_isZero_iff _ _).2 ⟨hgY, isZero_map_shift_of_isZero_map hgY 1⟩
  let e : (derivedRestrict W.ι).obj Q ≅ P ⊞ P⟦(1 : ℤ)⟧ :=
    θ.app Q ≪≫ (derivedRestrict ι).mapIso e' ≪≫ (derivedRestrict ι).mapBiprod _ _ ≪≫
      biprod.mapIso eg (((derivedRestrict ι).commShiftIso 1).app g ≪≫
        (shiftFunctor _ (1 : ℤ)).mapIso eg)
  have hQY : IsZero ((derivedRestrict Y.ι).obj Q) :=
    hQκ.of_iso (((derivedRestrictCongr (S.homOfLE_ι (le_sup_right : Y ≤ W'))).symm ≪≫
      derivedRestrictCompIso κ W'.ι).app Q)
  refine ⟨Q, e, β, hQ, fun i x hx =>
    isZero_stalk_of_isZero_derivedRestrict Y.ι Q hQY i ⟨x, hx⟩, ?_⟩
  rw [← NatIso.naturality_2 θ β, Functor.comp_map, hβ, Functor.map_comp, Functor.map_comp, hγ]
  simp only [e, α₁, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
    biprod.mapIso_hom, Functor.mapBiprod_hom, biprod.lift_map_assoc, biprod.lift_fst_assoc,
    Iso.hom_inv_id_app, Category.comp_id]

end Stacks.Duality.OpenImmersion

end
