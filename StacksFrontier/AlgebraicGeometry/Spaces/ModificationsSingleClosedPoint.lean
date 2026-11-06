module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedFibreGlueing

/-!
# Modifications at a single closed point, through one elementary étale neighbourhood

Let `Z` be a decent algebraic space over `S`, `z ∈ |Z|` a closed point and `(E, e) → (Z, z)` an
elementary étale neighbourhood with `E` affine and `e` the only point of `E` above `z`. The case
of a single point of Stacks 0BHB says that base change along `E ⟶ Z` is an equivalence from the
algebraic spaces over `Z` unchanged over `Z ∖ {z}` onto those over `E` unchanged over
`E ∖ {e}`; Stacks 0BGZ says that finite presentation can be read on either side.

This file restates these facts elementwise, as the three properties of the slice-level base change
`Over.pullback (E ⟶ Z)` of a faithful, full and essentially surjective functor, without passing
through the product category of Stacks 0BHA. It also records two facts about base change in the
slice category of presheaves: how a morphism over a factorisation of a base change transports
along a further factorisation, and that the base change of the inclusion of a subfunctor along a
morphism is the inclusion of the preimage.

## Main definitions

* `AlgebraicGeometry.Space.singleClosedPointNeighborhoods`: the datum of Stacks 0BH9 for the
  single point `z` and the neighbourhood `E`.

## Main results

* `AlgebraicGeometry.Space.isModification_pullback_single`,
  `AlgebraicGeometry.Space.eq_of_pullback_map_eq_single`,
  `AlgebraicGeometry.Space.exists_eq_pullback_map_single`,
  `AlgebraicGeometry.Space.exists_pullback_obj_iso_single` and
  `AlgebraicGeometry.Space.isFinitePresentation_iff_pullback_single`: the base change along `E ⟶ Z`
  of the modifications of `Z` away from `z` lands in the modifications of `E` away from `e`, is
  faithful, full and essentially surjective there, and preserves and reflects finite
  presentation.
* `CategoryTheory.Over.eq_pullbackFactor_of_compat`: transport of a morphism over a factorisation
  of a base change along a further factorisation.
* `CategoryTheory.isIso_pullback_map_toSubfunctor_iff`: the base change of the restriction
  of an object to a subfunctor is an isomorphism exactly when the base change of the object is an
  isomorphism over the preimage subfunctor.

## References

* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
* [Stacks Project, Tag 0BGZ](https://stacks.math.columbia.edu/tag/0BGZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Over

variable {C : Type*} [Category C] [HasPullbacks C]

/-- **Transport of a morphism over a factorisation of a base change.** Let `t = c₁ ≫ τ₁` and let
`φ` be a morphism between base changes along `t`. If a morphism `k` over a further factorisation
`c₁ = c₂ ≫ g` represents `φ` through the comparison of `c₁ = c₂ ≫ g`, then `φ` is represented over
the factorisation `t = c₂ ≫ (g ≫ τ₁)` by `k` transported along the comparison of
`g ≫ τ₁ = τ₂`. -/
theorem eq_pullbackFactor_of_compat {P Q₁ Q₂ T : C} {t : P ⟶ T} {c₁ : P ⟶ Q₁} {τ₁ : Q₁ ⟶ T}
    {c₂ : P ⟶ Q₂} {g : Q₂ ⟶ Q₁} {τ₂ : Q₂ ⟶ T} (h₁ : c₁ ≫ τ₁ = t) (hg : c₂ ≫ g = c₁)
    (hτ : g ≫ τ₁ = τ₂) (h₂ : c₂ ≫ τ₂ = t) {A A' : Over T}
    (φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj A')
    (k : (Over.pullback g).obj ((Over.pullback τ₁).obj A) ⟶
      (Over.pullback g).obj ((Over.pullback τ₁).obj A'))
    (hk : (pullbackFactorObjIso hg ((Over.pullback τ₁).obj A)).hom ≫ (Over.pullback c₂).map k =
      ((pullbackFactorObjIso h₁ A).inv ≫ φ ≫ (pullbackFactorObjIso h₁ A').hom) ≫
        (pullbackFactorObjIso hg ((Over.pullback τ₁).obj A')).hom) :
    φ = (pullbackFactorObjIso h₂ A).hom ≫
      (Over.pullback c₂).map ((pullbackFactorObjIso hτ A).hom ≫ k ≫
        (pullbackFactorObjIso hτ A').inv) ≫ (pullbackFactorObjIso h₂ A').inv := by
  have hA := pullbackFactorObjIso_assoc hg hτ h₂ h₁ A
  have hA' := pullbackFactorObjIso_assoc hg hτ h₂ h₁ A'
  have hk' : (Over.pullback c₂).map k = (pullbackFactorObjIso hg ((Over.pullback τ₁).obj A)).inv ≫
      ((pullbackFactorObjIso h₁ A).inv ≫ φ ≫ (pullbackFactorObjIso h₁ A').hom) ≫
        (pullbackFactorObjIso hg ((Over.pullback τ₁).obj A')).hom := by
    rw [← hk, Iso.inv_hom_id_assoc]
  rw [Functor.map_comp, Functor.map_comp, hk']
  have hX : (pullbackFactorObjIso h₂ A).hom ≫ (Over.pullback c₂).map
      (pullbackFactorObjIso hτ A).hom ≫
        (pullbackFactorObjIso hg ((Over.pullback τ₁).obj A)).inv =
      (pullbackFactorObjIso h₁ A).hom := by
    rw [← Category.assoc, hA, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hY : (pullbackFactorObjIso h₁ A').hom ≫
      (pullbackFactorObjIso hg ((Over.pullback τ₁).obj A')).hom ≫
        (Over.pullback c₂).map (pullbackFactorObjIso hτ A').inv ≫
          (pullbackFactorObjIso h₂ A').inv = 𝟙 _ := by
    rw [← Category.assoc, ← hA', Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  simp only [Category.assoc]
  rw [reassoc_of% hX, Iso.hom_inv_id_assoc, hY, Category.comp_id]

end CategoryTheory.Over

namespace CategoryTheory

/-- Pullbacks of presheaves of types (instance search times out without this shortcut). -/
local instance (priority := high) hasLimit_cospan_presheaf_ModificationsSingleClosedPoint
    {D : Type*} [Category.{u} D] {X Y Z : D ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Pullbacks in presheaves of types (instance search times out without this shortcut). -/
local instance (priority := high) hasPullbacks_presheaf_ModificationsSingleClosedPoint
    {D : Type*} [Category.{u} D] : HasPullbacks (D ⥤ Type u) :=
  ⟨inferInstance⟩

/-- **Restricting to a subfunctor commutes with base change.** For an object `Y` over `U`, a
subfunctor `U₀` of `U` and a morphism `c : P ⟶ U`, the base change along `c` of the restriction
`Y ×_U U₀ ⟶ U₀` is an isomorphism exactly when the base change of `Y` along `c` is an isomorphism
over the preimage of `U₀`: both are base changes of `Y ×_U U₀ ⟶ U₀` along the same morphism. -/
theorem isIso_pullback_map_toSubfunctor_iff {D : Type*} [Category.{u} D]
    {P U : D ⥤ Type u} (c : P ⟶ U) (U₀ : Subfunctor U) (Y : Over U) :
    IsIso ((Over.pullback c).map (Over.homMk (pullback.snd Y.hom U₀.ι) rfl :
        Over.mk (pullback.snd Y.hom U₀.ι ≫ U₀.ι) ⟶ Over.mk U₀.ι)) ↔
      IsIso (pullback.snd ((Over.pullback c).obj Y).hom (U₀.preimage c).ι) := by
  set snd₀ := pullback.snd Y.hom U₀.ι
  let π : Over.mk (snd₀ ≫ U₀.ι) ⟶ Over.mk U₀.ι := Over.homMk snd₀ rfl
  have hV : IsPullback (U₀.fromPreimage c) (U₀.preimage c).ι U₀.ι c :=
    Subfunctor.isPullback_fromPreimage U₀ c
  -- the left-hand side
  let L := ((Over.pullback c).map π).left
  have hLfst : L ≫ pullback.fst U₀.ι c = pullback.fst (snd₀ ≫ U₀.ι) c ≫ snd₀ := by
    simp only [L, π, Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hLsnd : L ≫ pullback.snd U₀.ι c = pullback.snd (snd₀ ≫ U₀.ι) c := by
    simp only [L, π, Over.pullback_map_left]
    exact pullback.lift_snd _ _ _
  have hL : IsPullback (pullback.fst (snd₀ ≫ U₀.ι) c) L snd₀ (pullback.fst U₀.ι c) :=
    IsPullback.of_bot (by rw [hLsnd]; exact IsPullback.of_hasPullback _ _) hLfst.symm
      (IsPullback.of_hasPullback U₀.ι c)
  let e : pullback U₀.ι c ≅ (U₀.preimage c).toFunctor :=
    (IsPullback.of_hasPullback U₀.ι c).isoIsPullback _ _ hV
  have he₁ : e.hom ≫ U₀.fromPreimage c = pullback.fst U₀.ι c :=
    IsPullback.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback U₀.ι c) hV
  have hL' : IsPullback (pullback.fst (snd₀ ≫ U₀.ι) c) (L ≫ e.hom) snd₀ (U₀.fromPreimage c) :=
    hL.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id, he₁])
  -- the right-hand side
  have hs : IsPullback (pullback.fst (pullback.snd Y.hom c) (U₀.preimage c).ι ≫
      pullback.fst Y.hom c) (pullback.snd (pullback.snd Y.hom c) (U₀.preimage c).ι) Y.hom
      (U₀.fromPreimage c ≫ U₀.ι) := by
    rw [hV.w]
    exact (IsPullback.of_hasPullback (pullback.snd Y.hom c) (U₀.preimage c).ι).paste_horiz
      (IsPullback.of_hasPullback Y.hom c)
  have hR := IsPullback.of_right' hs (IsPullback.of_hasPullback Y.hom U₀.ι)
  have hfinal : IsIso (L ≫ e.hom) ↔
      IsIso (pullback.snd ((Over.pullback c).obj Y).hom (U₀.preimage c).ι) := by
    change IsIso (L ≫ e.hom) ↔ IsIso (pullback.snd (pullback.snd Y.hom c) (U₀.preimage c).ι)
    rw [← IsPullback.isoIsPullback_hom_snd _ _ hL' hR]
    exact ⟨fun _ ↦ IsIso.of_isIso_comp_left (hL'.isoIsPullback _ _ hR).hom _, fun _ ↦ inferInstance⟩
  rw [← hfinal]
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : IsIso L := (Over.forget _).map_isIso ((Over.pullback c).map π)
    infer_instance
  · have : IsIso L := IsIso.of_isIso_comp_right L e.hom
    have : IsIso ((Over.forget P).map ((Over.pullback c).map π)) := this
    exact isIso_of_reflects_iso ((Over.pullback c).map π) (Over.forget _)

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (Zs : AlgebraicSpaces B S hS) (hdec : IsDecentSpace B S hS Zs.obj) (z : points B S hS Zs.obj)
  (hz : IsClosed ({z} : Set (points B S hS Zs.obj)))
  (E : ElementaryEtaleNeighborhood B S hS Zs.obj Zs.property z)
  (hEaff : IsAffine E.scheme.left.1)
  (hEu : ∀ y : points B S hS (yoneda.obj E.scheme),
    pointsMap B S hS (yoneda.obj E.scheme) E.toSpace y = z →
      y = presheafPoint B S hS E.scheme E.point E.residueField_contained)

/-- The datum of Stacks 0BH9 for a single closed point and one elementary étale neighbourhood of
it whose distinguished point is the only point above it. -/
def singleClosedPointNeighborhoods : ClosedPointNeighborhoods B S hS 1 where
  space := Zs
  decent := hdec
  point _ := z
  point_injective a b _ := Subsingleton.elim a b
  isClosed_point _ := hz
  neighborhood _ := E
  isAffine_neighborhood _ := hEaff
  eq_of_map_eq_point _ := hEu
  map_ne_point i j hij := absurd (Subsingleton.elim i j) hij

/-- The complement of the chosen points of the single-point datum is the complement of the
point. -/
theorem singleClosedPointNeighborhoods_openAwayFromPoints :
    (singleClosedPointNeighborhoods B S hS Zs hdec z hz E hEaff hEu).openAwayFromPoints =
      openSubspaceOfPoints B S hS Zs.obj {z}ᶜ := by
  change openSubspaceOfPoints B S hS Zs.obj (Set.range fun _ : Fin 1 ↦ z)ᶜ = _
  rw [Set.range_const]

include hdec hz hEaff hEu

/-- **Base change of a modification away from `z` is a modification away from `e`.** -/
theorem isModification_pullback_single {M : Over Zs.obj}
    (hM : IsModification B S hS (openSubspaceOfPoints B S hS Zs.obj {z}ᶜ) M) :
    IsModification B S hS
      (openSubspaceOfPoints B S hS (yoneda.obj E.scheme)
        {presheafPoint B S hS E.scheme E.point E.residueField_contained}ᶜ)
      ((Over.pullback E.toSpace).obj M) := by
  let D₁ := singleClosedPointNeighborhoods B S hS Zs hdec z hz E hEaff hEu
  have hM' : IsModification B S hS D₁.openAwayFromPoints M := by
    rwa [singleClosedPointNeighborhoods_openAwayFromPoints]
  exact ((D₁.restrictionComponent 0).obj ⟨M, hM'⟩).property

/-- **Faithfulness.** Two morphisms of modifications away from `z` with the same base change
along `E ⟶ Z` are equal. -/
theorem eq_of_pullback_map_eq_single {M N : Over Zs.obj}
    (hM : IsModification B S hS (openSubspaceOfPoints B S hS Zs.obj {z}ᶜ) M)
    (hN : IsModification B S hS (openSubspaceOfPoints B S hS Zs.obj {z}ᶜ) N) (f g : M ⟶ N)
    (h : (Over.pullback E.toSpace).map f = (Over.pullback E.toSpace).map g) : f = g := by
  let D₁ := singleClosedPointNeighborhoods B S hS Zs hdec z hz E hEaff hEu
  have hM' : IsModification B S hS D₁.openAwayFromPoints M := by
    rwa [singleClosedPointNeighborhoods_openAwayFromPoints]
  have hN' : IsModification B S hS D₁.openAwayFromPoints N := by
    rwa [singleClosedPointNeighborhoods_openAwayFromPoints]
  have := D₁.faithful_restrictionFunctor
  let f' : (⟨M, hM'⟩ : D₁.modificationsAwayFromPoints) ⟶ ⟨N, hN'⟩ := ObjectProperty.homMk f
  let g' : (⟨M, hM'⟩ : D₁.modificationsAwayFromPoints) ⟶ ⟨N, hN'⟩ := ObjectProperty.homMk g
  have hfg : D₁.restrictionFunctor.map f' = D₁.restrictionFunctor.map g' :=
    funext fun _ ↦ ObjectProperty.hom_ext _ h
  exact congrArg InducedCategory.Hom.hom (D₁.restrictionFunctor.map_injective hfg)

/-- **Fullness.** A morphism between the base changes along `E ⟶ Z` of two modifications away
from `z` is the base change of a morphism. -/
theorem exists_eq_pullback_map_single {M N : Over Zs.obj}
    (hM : IsModification B S hS (openSubspaceOfPoints B S hS Zs.obj {z}ᶜ) M)
    (hN : IsModification B S hS (openSubspaceOfPoints B S hS Zs.obj {z}ᶜ) N)
    (h : (Over.pullback E.toSpace).obj M ⟶ (Over.pullback E.toSpace).obj N) :
    ∃ ψ : M ⟶ N, (Over.pullback E.toSpace).map ψ = h := by
  let D₁ := singleClosedPointNeighborhoods B S hS Zs hdec z hz E hEaff hEu
  have hM' : IsModification B S hS D₁.openAwayFromPoints M := by
    rwa [singleClosedPointNeighborhoods_openAwayFromPoints]
  have hN' : IsModification B S hS D₁.openAwayFromPoints N := by
    rwa [singleClosedPointNeighborhoods_openAwayFromPoints]
  have := D₁.full_restrictionFunctor
  let h' : D₁.restrictionFunctor.obj ⟨M, hM'⟩ ⟶ D₁.restrictionFunctor.obj ⟨N, hN'⟩ :=
    fun _ ↦ ObjectProperty.homMk h
  obtain ⟨ψ, hψ⟩ := D₁.restrictionFunctor.map_surjective h'
  exact ⟨ψ.hom, (congrArg InducedCategory.Hom.hom (congrFun hψ 0) :)⟩

/-- **Essential surjectivity.** Every modification of `E` away from `e` is, up to isomorphism, the
base change along `E ⟶ Z` of a modification of `Z` away from `z`. -/
theorem exists_pullback_obj_iso_single {Y : Over (yoneda.obj E.scheme)}
    (hY : IsModification B S hS
      (openSubspaceOfPoints B S hS (yoneda.obj E.scheme)
        {presheafPoint B S hS E.scheme E.point E.residueField_contained}ᶜ) Y) :
    ∃ M : Over Zs.obj, IsModification B S hS (openSubspaceOfPoints B S hS Zs.obj {z}ᶜ) M ∧
      Nonempty ((Over.pullback E.toSpace).obj M ≅ Y) := by
  let D₁ := singleClosedPointNeighborhoods B S hS Zs hdec z hz E hEaff hEu
  let Y' : ∀ i : Fin 1, D₁.modificationsAt i := fun _ ↦ ⟨Y, hY⟩
  obtain ⟨M, ⟨eM⟩⟩ := D₁.essSurj_restrictionFunctor_of_excision.mem_essImage Y'
  refine ⟨M.obj, ?_, ⟨(ObjectProperty.ι _).mapIso (Pi.isoApp eM 0)⟩⟩
  rw [← singleClosedPointNeighborhoods_openAwayFromPoints B S hS Zs hdec z hz E hEaff hEu]
  exact M.property

/-- **Stacks 0BGZ for finite presentation.** A modification of `Z` away from `z` is of finite
presentation exactly when its base change along `E ⟶ Z` is. -/
theorem isFinitePresentation_iff_pullback_single {M : Over Zs.obj}
    (hM : IsModification B S hS (openSubspaceOfPoints B S hS Zs.obj {z}ᶜ) M) :
    IsFinitePresentation B S hS M.hom ↔
      IsFinitePresentation B S hS ((Over.pullback E.toSpace).obj M).hom := by
  let D₁ := singleClosedPointNeighborhoods B S hS Zs hdec z hz E hEaff hEu
  have hM' : IsModification B S hS (openComplement B S hS (D₁.pointSubspace 0)) M := by
    rwa [D₁.openComplement_pointSubspace_eq 0]
  exact isFinitePresentation_iff_baseChangeFunctor_obj B S hS (D₁.toSpaceHom 0)
    (D₁.pointSubspace 0) (D₁.isClosedSubspace_pointSubspace 0)
    (D₁.isIso_fromPreimage_pointSubspace 0) E.etale_toSpace ⟨M, hM'⟩

end AlgebraicGeometry.Space

end
