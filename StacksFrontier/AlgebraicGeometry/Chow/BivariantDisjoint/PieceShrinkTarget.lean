module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceGysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent

/-!
# Restricting a bivariant class to a piece with a smaller target

Let `f : X ⟶ Y` be a morphism of schemes locally of finite type over the base of chapter 42 of the
Stacks Project, `c` a bivariant class for `f`, `X_i ⊆ X` open, and `V' ⊆ V ⊆ Y` opens with
`f(X_i) ⊆ V'`. The restrictions of `c` to `X_i ⟶ V` and to `X_i ⟶ V'` (Stacks 0FDZ) determine one
another: for a test scheme `t : T ⟶ V` the base change `X_i ×_V T` lies over the open
`T' = t⁻¹(V') ⊆ T`, so `X_i ×_{V'} T' ⟶ X_i ×_V T` is an isomorphism, and along it the cap
operation at `t` is the cap operation at `T' ⟶ V'` of the restriction of the class to `T'`
(the flat pullback axiom of Stacks 0B76 along the open immersion `T' ⟶ T`). In particular the
restriction to `X_i ⟶ V` vanishes as soon as the restriction to `X_i ⟶ V'` does.

## Main definitions

* `Stacks.Chow.shrinkComparison` — the isomorphism `X_i ×_{V'} T' ⟶ X_i ×_V T`.

## Main results

* `Stacks.Chow.chowGroupRestrict_bivariantPieceRestrictionCap_shrink` — the two cap operations
  correspond along it.
* `Stacks.Chow.bivariantPieceRestriction_eq_zero_of_shrink` — vanishing on the smaller target
  gives vanishing on the larger one.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Geometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I J J' : Type u} (UX : I → X.Opens)
  (UY : J → Y.Opens) (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (UY' : J' → Y.Opens)
  (a' : I → J') (ha' : ∀ i, UX i ≤ f ⁻¹ᵁ UY' (a' i)) (i : I) {T : Scheme.{u}}
  (t : T ⟶ (UY (a i) : Scheme.{u}))

/-- The open `T' = t⁻¹(V')` of a test scheme over `V`, for `V'` the smaller target. -/
abbrev shrinkOpens : T.Opens := (t ≫ (UY (a i)).ι) ⁻¹ᵁ UY' (a' i)

/-- The test morphism `T' ⟶ V'`. -/
abbrev shrinkTest : (shrinkOpens UY a UY' a' i t : Scheme.{u}) ⟶ (UY' (a' i) : Scheme.{u}) :=
  (t ≫ (UY (a i)).ι).resLE (UY' (a' i)) (shrinkOpens UY a UY' a' i t) le_rfl

/-- The composite `T' ⟶ V' ⟶ Y` is the composite `T' ⟶ T ⟶ V ⟶ Y`. -/
@[reassoc]
theorem shrinkTest_comp_ι :
    shrinkTest UY a UY' a' i t ≫ (UY' (a' i)).ι =
      (shrinkOpens UY a UY' a' i t).ι ≫ t ≫ (UY (a i)).ι :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The comparison `X_i ×_{V'} T' ⟶ X_i ×_V T`. -/
def shrinkComparison :
    pullback (pieceMap f UX UY' a' ha' i) (shrinkTest UY a UY' a' i t) ⟶
      pullback (pieceMap f UX UY a ha i) t :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ (shrinkOpens UY a UY' a' i t).ι) (by
    rw [← cancel_mono (UY (a i)).ι, Category.assoc, pieceMap_comp_ι,
      ← pieceMap_comp_ι f UX UY' a' ha' i, pullback.condition_assoc, shrinkTest_comp_ι]
    simp only [Category.assoc])

/-- `Stacks.Chow.shrinkComparison` commutes with the projections to `X_i`. -/
@[reassoc (attr := simp)]
theorem shrinkComparison_fst :
    shrinkComparison f UX UY a ha UY' a' ha' i t ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The projection of `Stacks.Chow.shrinkComparison` to `T` is the projection to `T'` followed by
the inclusion `T' ⟶ T`. -/
@[reassoc (attr := simp)]
theorem shrinkComparison_snd :
    shrinkComparison f UX UY a ha UY' a' ha' i t ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (shrinkOpens UY a UY' a' i t).ι :=
  pullback.lift_snd _ _ _

include ha' in
/-- The base change `X_i ×_V T ⟶ T` lands in `T' = t⁻¹(V')`. -/
theorem range_pullbackSnd_subset :
    Set.range (pullback.snd (pieceMap f UX UY a ha i) t).base ⊆
      Set.range (shrinkOpens UY a UY' a' i t).ι.base := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  change ((pullback.snd (pieceMap f UX UY a ha i) t ≫ t ≫ (UY (a i)).ι).base y) ∈ UY' (a' i)
  rw [← pullback.condition_assoc, pieceMap_comp_ι]
  have hmem : (UX i).ι.base ((pullback.fst (pieceMap f UX UY a ha i) t).base y) ∈ UX i := by
    change _ ∈ (UX i : Set X)
    rw [← Scheme.Opens.range_ι (UX i)]
    exact ⟨_, rfl⟩
  exact ha' i hmem

/-- The inverse of `Stacks.Chow.shrinkComparison`. -/
def shrinkComparisonInv :
    pullback (pieceMap f UX UY a ha i) t ⟶
      pullback (pieceMap f UX UY' a' ha' i) (shrinkTest UY a UY' a' i t) :=
  pullback.lift (pullback.fst _ _)
    (IsOpenImmersion.lift (shrinkOpens UY a UY' a' i t).ι (pullback.snd _ _)
      (range_pullbackSnd_subset f UX UY a ha UY' a' ha' i t)) (by
    rw [← cancel_mono (UY' (a' i)).ι, Category.assoc, pieceMap_comp_ι,
      ← pieceMap_comp_ι f UX UY a ha i, pullback.condition_assoc, Category.assoc,
      shrinkTest_comp_ι, IsOpenImmersion.lift_fac_assoc])

/-- The comparison `X_i ×_{V'} T' ⟶ X_i ×_V T` is an isomorphism. -/
instance isIso_shrinkComparison : IsIso (shrinkComparison f UX UY a ha UY' a' ha' i t) := by
  refine ⟨⟨shrinkComparisonInv f UX UY a ha UY' a' ha' i t, ?_, ?_⟩⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, shrinkComparisonInv, pullback.lift_fst, shrinkComparison_fst,
        Category.id_comp]
    · rw [← cancel_mono (shrinkOpens UY a UY' a' i t).ι, Category.assoc, Category.assoc,
        shrinkComparisonInv, pullback.lift_snd_assoc, IsOpenImmersion.lift_fac,
        shrinkComparison_snd, Category.id_comp]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, shrinkComparison_fst, shrinkComparisonInv, pullback.lift_fst,
        Category.id_comp]
    · rw [Category.assoc, shrinkComparison_snd, shrinkComparisonInv, pullback.lift_snd_assoc,
        IsOpenImmersion.lift_fac, Category.id_comp]

end Geometry

section Cap

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)
  {I J J' : Type u} (UX : I → X.Opens) (UY : J → Y.Opens) (a : I → J)
  (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (UY' : J' → Y.Opens) (a' : I → J')
  (ha' : ∀ i, UX i ≤ f ⁻¹ᵁ UY' (a' i)) (i : I) {T : Scheme.{u}}
  (t : T ⟶ (UY (a i) : Scheme.{u})) [LocallyOfFiniteType t]

/-- The test morphism `T' ⟶ V'` is locally of finite type. -/
instance locallyOfFiniteType_shrinkTest :
    LocallyOfFiniteType (shrinkTest UY a UY' a' i t) := by
  have : LocallyOfFiniteType (shrinkTest UY a UY' a' i t ≫ (UY' (a' i)).ι) := by
    rw [shrinkTest_comp_ι]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (UY' (a' i)).ι

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType t] in
/-- The structure morphisms of `T'` to the base through `V'` and through `T` coincide. -/
theorem shrinkTest_comp_structure :
    shrinkTest UY a UY' a' i t ≫ ((UY' (a' i)).ι ≫ sY) =
      (shrinkOpens UY a UY' a' i t).ι ≫ (t ≫ ((UY (a i)).ι ≫ sY)) := by
  rw [shrinkTest_comp_ι_assoc]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f] [LocallyOfFiniteType t] in
/-- `Stacks.Chow.shrinkComparison` is compatible with the structure morphisms to the base through
`X_i`. -/
theorem shrinkComparison_comp_structure :
    shrinkComparison f UX UY a ha UY' a' ha' i t ≫
        (pullback.fst (pieceMap f UX UY a ha i) t ≫ ((UX i).ι ≫ sX)) =
      pullback.fst (pieceMap f UX UY' a' ha' i) (shrinkTest UY a UY' a' i t) ≫
        ((UX i).ι ≫ sX) := by
  rw [shrinkComparison_fst_assoc]

/-- Restriction along an open immersion commutes with the transport of the structure
morphisms. -/
theorem chowGroupCongr_chowGroupRestrict_comm {Z W : Scheme.{u}} (sZ sZ' : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType sZ'] (sW sW' : W ⟶ C.S)
    [LocallyOfFiniteType sW] [LocallyOfFiniteType sW'] (v : W ⟶ Z) [IsOpenImmersion v]
    (hv : v ≫ sZ = sW) (hv' : v ≫ sZ' = sW') (hZ : sZ = sZ') (hW : sW = sW') (k : ℤ)
    (α : chowGroup C sZ k) :
    chowGroupCongr C hW k (chowGroupRestrict C sZ sW v hv k α) =
      chowGroupRestrict C sZ' sW' v hv' k (chowGroupCongr C hZ k α) := by
  subst hZ hW
  rfl

/-- The cap operation of the restriction to a piece at `g`, read through the comparison with the
base change along a morphism `m` equal to `g ≫ (Y_{a(i)} ⟶ Y)`. -/
private theorem bivariantPieceRestrictionCap_eq_pieceComparisonCongr
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ (UY (a i) : Scheme.{u})) [LocallyOfFiniteType g] (m : T ⟶ Y)
    [LocallyOfFiniteType m] (hm : g ≫ (UY (a i)).ι = m) (hmY : g ≫ ((UY (a i)).ι ≫ sY) = m ≫ sY)
    (k : ℤ) (β : chowGroup C (g ≫ ((UY (a i)).ι ≫ sY)) k) :
    bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c g k β =
      chowGroupRestrict C (pullback.fst f m ≫ sX)
        (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
        (pieceComparisonCongr f UX UY a ha i g m hm)
        (pieceComparisonCongr_comp_structureMorphism _ _ _ _ _ _ _ _ hm sX) (k - p)
        (c.cap m k (chowGroupCongr C hmY k β)) :=
  bivariantPieceRestrictionCap_eq C G sX sY f hf p UX UY a ha i c g m hm hmY _
    (pieceComparisonCongr_fst _ _ _ _ _ _ _ _ _) (pieceComparisonCongr_snd _ _ _ _ _ _ _ _ _) k
    (pieceComparisonCongr_comp_structureMorphism _ _ _ _ _ _ _ _ hm sX) β

/-- **Stacks 0FDZ, restriction to a smaller target**: along `X_i ×_{V'} T' ≅ X_i ×_V T`, the cap
operation of the restriction of `c` to `X_i ⟶ V` at `t` is the cap operation of the restriction
of `c` to `X_i ⟶ V'` at `T' ⟶ V'`, applied to the restriction of the class to `T'`. -/
theorem chowGroupRestrict_bivariantPieceRestrictionCap_shrink
    (c : BivariantClass C G sX sY f hf p) (k : ℤ)
    (β : chowGroup C (t ≫ ((UY (a i)).ι ≫ sY)) k) :
    chowGroupRestrict C (pullback.fst (pieceMap f UX UY a ha i) t ≫ ((UX i).ι ≫ sX))
        (pullback.fst (pieceMap f UX UY' a' ha' i) (shrinkTest UY a UY' a' i t) ≫
          ((UX i).ι ≫ sX))
        (shrinkComparison f UX UY a ha UY' a' ha' i t)
        (shrinkComparison_comp_structure C sX f UX UY a ha UY' a' ha' i t) (k - p)
        (bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c t k β) =
      bivariantPieceRestrictionCap C G sX sY f hf p UX UY' a' ha' i c
        (shrinkTest UY a UY' a' i t) k
        (chowGroupCongr C (shrinkTest_comp_structure C sY UY a UY' a' i t).symm k
          (chowGroupRestrict C (t ≫ ((UY (a i)).ι ≫ sY))
            ((shrinkOpens UY a UY' a' i t).ι ≫ (t ≫ ((UY (a i)).ι ≫ sY)))
            (shrinkOpens UY a UY' a' i t).ι rfl k β)) := by
  have hm : shrinkTest UY a UY' a' i t ≫ (UY' (a' i)).ι =
      (shrinkOpens UY a UY' a' i t).ι ≫ (t ≫ (UY (a i)).ι) := shrinkTest_comp_ι UY a UY' a' i t
  have hmY : shrinkTest UY a UY' a' i t ≫ ((UY' (a' i)).ι ≫ sY) =
      ((shrinkOpens UY a UY' a' i t).ι ≫ (t ≫ (UY (a i)).ι)) ≫ sY := by
    rw [← hm, Category.assoc]
  have hcap := BivariantClass.cap_chowGroupRestrict C G sX sY f hf p c (t ≫ (UY (a i)).ι)
    (shrinkOpens UY a UY' a' i t).ι ((shrinkOpens UY a UY' a' i t).ι ≫ (t ≫ (UY (a i)).ι)) rfl
    (bivariantBaseChangeMap f (t ≫ (UY (a i)).ι) (shrinkOpens UY a UY' a' i t).ι)
    (isPullback_bivariantBaseChangeMap f _ _) (bivariantBaseChangeMap_fst f _ _) k
    (by simp only [Category.assoc])
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ sX) (bivariantBaseChangeMap_fst f _ _)))
    (chowGroupCongr C (Category.assoc t (UY (a i)).ι sY).symm k β)
  rw [bivariantPieceRestrictionCap_eq_pieceComparisonCongr C G sX sY f hf p UX UY' a' ha' i c
    (shrinkTest UY a UY' a' i t) ((shrinkOpens UY a UY' a' i t).ι ≫ (t ≫ (UY (a i)).ι)) hm hmY,
    chowGroupCongr_chowGroupCongr, chowGroupCongr_chowGroupRestrict_comm C _ _ _ _ _ _
      (by simp only [Category.assoc]) (Category.assoc t (UY (a i)).ι sY).symm, ← hcap,
    bivariantPieceRestrictionCap_apply, chowGroupRestrict_comp, chowGroupRestrict_comp]
  refine DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _ ?_ _) _
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullbackMap_fst, Category.comp_id, pieceComparisonCongr_fst,
      opensPullbackComparison_fst, shrinkComparison_fst_assoc]
  · simp only [Category.assoc, pullbackMap_snd, pieceComparisonCongr_snd_assoc,
      opensPullbackComparison_snd, shrinkComparison_snd]

/-- **Vanishing on a smaller target gives vanishing on a larger one**: if the restriction of `c`
to `X_i ⟶ V'` is zero then so is its restriction to `X_i ⟶ V`, for opens `V' ⊆ V` of `Y` both
containing `f(X_i)`. -/
theorem bivariantPieceRestriction_eq_zero_of_shrink (hgysO : G.IsNaturalUnderOpenImmersion)
    (c : BivariantClass C G sX sY f hf p)
    (h0 : bivariantPieceRestriction C G sX sY f hf p UX UY' a' ha' i hgysO c = 0) :
    bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO c = 0 := by
  refine BivariantClass.ext C G _ _ _ _ p fun t _ k β => ?_
  rw [BivariantClass.zero_cap]
  have h1 := chowGroupRestrict_bivariantPieceRestrictionCap_shrink C G sX sY f hf p UX UY a ha
    UY' a' ha' i t c k β
  have h3 := h1.trans (by
    rw [← bivariantPieceRestriction_cap C G sX sY f hf p UX UY' a' ha' i hgysO c, h0,
      BivariantClass.zero_cap])
  rw [chowGroupRestrict_of_isIso] at h3
  exact chowPushforwardOfIso_injective C _ _ _ _ _ (h3.trans (map_zero _).symm)

/-- **Two classes agreeing on a smaller target agree on a larger one**: if the restrictions of `c`
and `d` to `X_i ⟶ V'` coincide then so do their restrictions to `X_i ⟶ V`. -/
theorem bivariantPieceRestriction_eq_of_shrink (hgysO : G.IsNaturalUnderOpenImmersion)
    (c d : BivariantClass C G sX sY f hf p)
    (h : bivariantPieceRestriction C G sX sY f hf p UX UY' a' ha' i hgysO c =
      bivariantPieceRestriction C G sX sY f hf p UX UY' a' ha' i hgysO d) :
    bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO c =
      bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO d := by
  have h0 := bivariantPieceRestriction_eq_zero_of_shrink C G sX sY f hf p UX UY a ha UY' a' ha'
    i hgysO (c - d) (by
      rw [sub_eq_add_neg, bivariantPieceRestriction_add, bivariantPieceRestriction_neg, h,
        add_neg_cancel])
  rwa [sub_eq_add_neg, bivariantPieceRestriction_add, bivariantPieceRestriction_neg,
    add_neg_eq_zero] at h0

end Cap

/-! ### Restriction to a piece with a smaller target, as a restriction -/

section Grow

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I J J' : Type u} (UX : I → X.Opens)
  (UY : J → Y.Opens) (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (UY' : J' → Y.Opens)
  (a' : I → J') (ha' : ∀ i, UX i ≤ f ⁻¹ᵁ UY' (a' i)) (i : I) (hle : UY' (a' i) ≤ UY (a i))
  {T : Scheme.{u}} (s : T ⟶ (UY' (a' i) : Scheme.{u}))

/-- The comparison `X_i ×_{V'} T ⟶ X_i ×_V T` for a test scheme `T ⟶ V' ⊆ V`. -/
def growComparison :
    pullback (pieceMap f UX UY' a' ha' i) s ⟶
      pullback (pieceMap f UX UY a ha i) (s ≫ Y.homOfLE hle) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    rw [← cancel_mono (UY (a i)).ι, Category.assoc, pieceMap_comp_ι,
      ← pieceMap_comp_ι f UX UY' a' ha' i, pullback.condition_assoc]
    simp only [Category.assoc, Scheme.homOfLE_ι])

/-- `Stacks.Chow.growComparison` commutes with the projections to `X_i`. -/
@[reassoc (attr := simp)]
theorem growComparison_fst :
    growComparison f UX UY a ha UY' a' ha' i hle s ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- `Stacks.Chow.growComparison` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem growComparison_snd :
    growComparison f UX UY a ha UY' a' ha' i hle s ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The inverse of `Stacks.Chow.growComparison`. -/
def growComparisonInv :
    pullback (pieceMap f UX UY a ha i) (s ≫ Y.homOfLE hle) ⟶
      pullback (pieceMap f UX UY' a' ha' i) s :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    rw [← cancel_mono (UY' (a' i)).ι, Category.assoc, pieceMap_comp_ι,
      ← pieceMap_comp_ι f UX UY a ha i, pullback.condition_assoc]
    simp only [Category.assoc, Scheme.homOfLE_ι])

/-- The comparison `X_i ×_{V'} T ⟶ X_i ×_V T` is an isomorphism. -/
instance isIso_growComparison : IsIso (growComparison f UX UY a ha UY' a' ha' i hle s) := by
  refine ⟨⟨growComparisonInv f UX UY a ha UY' a' ha' i hle s, ?_, ?_⟩⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, growComparisonInv, pullback.lift_fst, growComparison_fst,
        Category.id_comp]
    · rw [Category.assoc, growComparisonInv, pullback.lift_snd, growComparison_snd,
        Category.id_comp]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, growComparison_fst, growComparisonInv, pullback.lift_fst,
        Category.id_comp]
    · rw [Category.assoc, growComparison_snd, growComparisonInv, pullback.lift_snd,
        Category.id_comp]

end Grow

section GrowCap

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)
  {I J J' : Type u} (UX : I → X.Opens) (UY : J → Y.Opens) (a : I → J)
  (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (UY' : J' → Y.Opens) (a' : I → J')
  (ha' : ∀ i, UX i ≤ f ⁻¹ᵁ UY' (a' i)) (i : I) (hle : UY' (a' i) ≤ UY (a i)) {T : Scheme.{u}}
  (s : T ⟶ (UY' (a' i) : Scheme.{u})) [LocallyOfFiniteType s]

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType s] in
/-- The structure morphisms of `T` to the base through `V'` and through `V` coincide. -/
theorem homOfLE_comp_structure :
    s ≫ ((UY' (a' i)).ι ≫ sY) = (s ≫ Y.homOfLE hle) ≫ ((UY (a i)).ι ≫ sY) := by
  rw [Category.assoc, Scheme.homOfLE_ι_assoc]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f] [LocallyOfFiniteType s] in
/-- `Stacks.Chow.growComparison` is compatible with the structure morphisms to the base through
`X_i`. -/
theorem growComparison_comp_structure :
    growComparison f UX UY a ha UY' a' ha' i hle s ≫
        (pullback.fst (pieceMap f UX UY a ha i) (s ≫ Y.homOfLE hle) ≫ ((UX i).ι ≫ sX)) =
      pullback.fst (pieceMap f UX UY' a' ha' i) s ≫ ((UX i).ι ≫ sX) := by
  rw [growComparison_fst_assoc]

/-- **Restriction to a smaller target is a restriction**: for opens `V' ⊆ V` of `Y` containing
`f(X_i)` and a test scheme `s : T ⟶ V'`, the cap operation of the restriction of `c` to
`X_i ⟶ V'` at `s` is the cap operation of its restriction to `X_i ⟶ V` at `T ⟶ V' ⊆ V`, read
through `X_i ×_{V'} T ≅ X_i ×_V T`. -/
theorem bivariantPieceRestrictionCap_grow (c : BivariantClass C G sX sY f hf p) (k : ℤ)
    (β : chowGroup C (s ≫ ((UY' (a' i)).ι ≫ sY)) k) :
    bivariantPieceRestrictionCap C G sX sY f hf p UX UY' a' ha' i c s k β =
      chowGroupRestrict C
        (pullback.fst (pieceMap f UX UY a ha i) (s ≫ Y.homOfLE hle) ≫ ((UX i).ι ≫ sX))
        (pullback.fst (pieceMap f UX UY' a' ha' i) s ≫ ((UX i).ι ≫ sX))
        (growComparison f UX UY a ha UY' a' ha' i hle s)
        (growComparison_comp_structure C sX f UX UY a ha UY' a' ha' i hle s) (k - p)
        (bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c (s ≫ Y.homOfLE hle) k
          (chowGroupCongr C (homOfLE_comp_structure C sY UY a UY' a' i hle s) k β)) := by
  have hm : (s ≫ Y.homOfLE hle) ≫ (UY (a i)).ι = s ≫ (UY' (a' i)).ι := by
    rw [Category.assoc, Scheme.homOfLE_ι]
  have hmY : (s ≫ Y.homOfLE hle) ≫ ((UY (a i)).ι ≫ sY) = (s ≫ (UY' (a' i)).ι) ≫ sY := by
    rw [← Category.assoc, hm]
  rw [bivariantPieceRestrictionCap_eq_pieceComparisonCongr C G sX sY f hf p UX UY a ha i c
    (s ≫ Y.homOfLE hle) (s ≫ (UY' (a' i)).ι) hm hmY,
    chowGroupCongr_chowGroupCongr, chowGroupRestrict_comp, bivariantPieceRestrictionCap_apply]
  refine DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _ ?_ _) _
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pieceComparisonCongr_fst, growComparison_fst_assoc,
      opensPullbackComparison_fst]
  · simp only [Category.assoc, pieceComparisonCongr_snd, growComparison_snd,
      opensPullbackComparison_snd]

end GrowCap


end Stacks.Chow

end
