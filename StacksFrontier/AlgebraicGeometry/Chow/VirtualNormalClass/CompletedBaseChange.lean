module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.CompletedConstantRank

/-!
# The completed class of a virtual normal bundle is compatible with base change

Let `i : Z ⟶ X` be a closed immersion of schemes locally of finite type over the base of chapter
42 of the Stacks Project, `𝒩` a virtual normal bundle for `i`, `h : X' ⟶ X` locally of finite
type, `Z' = Z ×_X X'` and `𝒩' = g^*𝒩` the virtual normal bundle of Stacks 0FBJ for
`i' : Z' ⟶ X'`. The base change clause of Stacks 0FBK says that `c(Z' ⟶ X', 𝒩')` is the
restriction `res(c(Z ⟶ X, 𝒩))` of Stacks 0F9Z, here on the completed groups of Stacks 0FE0.

Degree by degree this is a comparison of classes in `A^p(Z' ⟶ X')`, made on the pieces
`Z'_{k'} ⟶ W'_{k'}` of the connected components of `Z'` (Stacks 0FDZ). A component `Z'_{k'}` lies
over a component `Z_k` of `Z`, on which `𝒩` has some rank `r`; then `𝒩'` has rank `r` on `Z'_{k'}`.
Both classes are compared after shrinking the target to `W'' = W'_{k'} ∩ h⁻¹(W_k)`, which is
allowed because `Z'_{k'} ⊆ i'⁻¹(W'')`. Over `W''` the square of `Z'_{k'} ⟶ W''` over
`Z_k ⟶ W_k` is cartesian, and so is the square of `Z'_{k'} ⟶ W''` over `Z'_{k'} ⟶ W'_{k'}`; the
virtual normal bundle `𝒩''` of `Z'_{k'} ⟶ W''` compares to `𝒩|_{Z_k}` and to `𝒩'|_{Z'_{k'}}`, and
the constant-rank base change clause identifies both restricted classes with
`c(Z'_{k'} ⟶ W'', 𝒩'')`.

## Main results

* `Stacks.Chow.VirtualNormalBundle.completedClass_baseChange` — **Stacks 0FBK**, compatibility
  with base change: `c(Z' ⟶ X', 𝒩') = res(c(Z ⟶ X, 𝒩))` in `A^*(Z' ⟶ X')^∧`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow.VirtualNormalBundle

section RestrictionPiece

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (h : Y' ⟶ Y) {I J I' J' : Type u}
  (UX : I → X.Opens) (UY : J → Y.Opens) (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i))
  (UX' : I' → (pullback f h).Opens) (UY' : J' → Y'.Opens) (a' : I' → J')
  (ha' : ∀ i', UX' i' ≤ pullback.snd f h ⁻¹ᵁ UY' (a' i')) (i : I) (i' : I')
  (hX : UX' i' ≤ pullback.fst f h ⁻¹ᵁ UX i) (hY : UY' (a' i') ≤ h ⁻¹ᵁ UY (a i))
  {T : Scheme.{u}} (s : T ⟶ (UY' (a' i') : Scheme.{u}))

/-- The test morphism `T ⟶ V' ⟶ V` of the larger piece. -/
abbrev restrictionPieceTest : T ⟶ (UY (a i) : Scheme.{u}) := s ≫ h.resLE (UY (a i)) (UY' (a' i')) hY

/-- The composite `T ⟶ V ⟶ Y` of the test morphism is `T ⟶ V' ⟶ Y' ⟶ Y`. -/
theorem restrictionPieceTest_comp_ι :
    restrictionPieceTest h UY a UY' a' i i' hY s ≫ (UY (a i)).ι = (s ≫ (UY' (a' i')).ι) ≫ h := by
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

/-- The comparison `X'_{i'} ×_{V'} T ⟶ X_i ×_V T` of the base changes of the two pieces. -/
def restrictionPieceComparison :
    pullback (pieceMap (pullback.snd f h) UX' UY' a' ha' i') s ⟶
      pullback (pieceMap f UX UY a ha i) (restrictionPieceTest h UY a UY' a' i i' hY s) :=
  pullback.lift (pullback.fst _ _ ≫ (pullback.fst f h).resLE (UX i) (UX' i') hX)
    (pullback.snd _ _) (by
      have e₁ : pieceMap f UX UY a ha i ≫ (UY (a i)).ι = (UX i).ι ≫ f := pieceMap_comp_ι _ _ _ _ _ _
      have e₂ : (pullback.fst f h).resLE (UX i) (UX' i') hX ≫ (UX i).ι =
          (UX' i').ι ≫ pullback.fst f h := Scheme.Hom.resLE_comp_ι _ _
      have e₃ : pieceMap (pullback.snd f h) UX' UY' a' ha' i' ≫ (UY' (a' i')).ι =
          (UX' i').ι ≫ pullback.snd f h := pieceMap_comp_ι _ _ _ _ _ _
      rw [← cancel_mono (UY (a i)).ι]
      simp only [Category.assoc]
      rw [e₁, reassoc_of% e₂, pullback.condition (f := f) (g := h), ← reassoc_of% e₃,
        pullback.condition_assoc, Scheme.Hom.resLE_comp_ι])

/-- The first projection of the comparison is the restriction of `X' ⟶ X` to the pieces. -/
@[reassoc (attr := simp)]
theorem restrictionPieceComparison_fst :
    restrictionPieceComparison f h UX UY a ha UX' UY' a' ha' i i' hX hY s ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (pullback.fst f h).resLE (UX i) (UX' i') hX :=
  pullback.lift_fst _ _ _

/-- The comparison commutes with the second projections to `T`. -/
@[reassoc (attr := simp)]
theorem restrictionPieceComparison_snd :
    restrictionPieceComparison f h UX UY a ha UX' UY' a' ha' i i' hX hY s ≫ pullback.snd _ _ =
      pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- Followed by the identification of `X_i ×_V T` with `X_i ×_Y T`, the comparison is the
open immersion `X'_{i'} ×_{V'} T ⟶ X' ×_{Y'} T ≅ X ×_Y T`. -/
theorem restrictionPieceComparison_comp :
    restrictionPieceComparison f h UX UY a ha UX' UY' a' ha' i i' hX hY s ≫
        pieceComparisonCongr f UX UY a ha i (restrictionPieceTest h UY a UY' a' i i' hY s)
          ((s ≫ (UY' (a' i')).ι) ≫ h) (restrictionPieceTest_comp_ι h UY a UY' a' i i' hY s) =
      pieceComparison (pullback.snd f h) UX' UY' a' ha' i' s ≫
        (pullbackLeftPullbackSndIso f h (s ≫ (UY' (a' i')).ι)).hom := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pieceComparisonCongr_fst, restrictionPieceComparison_fst_assoc,
      Scheme.Hom.resLE_comp_ι, pullbackLeftPullbackSndIso_hom_fst,
      opensPullbackComparison_fst_assoc]
  · simp only [Category.assoc, pieceComparisonCongr_snd, restrictionPieceComparison_snd,
      pullbackLeftPullbackSndIso_hom_snd, opensPullbackComparison_snd]

/-- The comparison `X'_{i'} ×_{V'} T ⟶ X_i ×_V T` is an open immersion. -/
instance isOpenImmersion_restrictionPieceComparison :
    IsOpenImmersion (restrictionPieceComparison f h UX UY a ha UX' UY' a' ha' i i' hX hY s) := by
  have : IsOpenImmersion (restrictionPieceComparison f h UX UY a ha UX' UY' a' ha' i i' hX hY s ≫
      pieceComparisonCongr f UX UY a ha i (restrictionPieceTest h UY a UY' a' i i' hY s)
        ((s ≫ (UY' (a' i')).ι) ≫ h) (restrictionPieceTest_comp_ι h UY a UY' a' i i' hY s)) := by
    rw [restrictionPieceComparison_comp]
    infer_instance
  exact IsOpenImmersion.of_comp _
    (pieceComparisonCongr f UX UY a ha i (restrictionPieceTest h UY a UY' a' i i' hY s)
      ((s ≫ (UY' (a' i')).ι) ≫ h) (restrictionPieceTest_comp_ι h UY a UY' a' i i' hY s))

end RestrictionPiece

section RestrictionPieceCap

variable (C : ChowSituation.{u}) {X Y Y' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) (h : Y' ⟶ Y) [LocallyOfFiniteType h] (p : ℤ) {I J I' J' : Type u}
  (UX : I → X.Opens) (UY : J → Y.Opens) (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i))
  (UX' : I' → (pullback f h).Opens) (UY' : J' → Y'.Opens) (a' : I' → J')
  (ha' : ∀ i', UX' i' ≤ pullback.snd f h ⁻¹ᵁ UY' (a' i')) (i : I) (i' : I')
  (hX : UX' i' ≤ pullback.fst f h ⁻¹ᵁ UX i) (hY : UY' (a' i') ≤ h ⁻¹ᵁ UY (a i))
  {T : Scheme.{u}} (s : T ⟶ (UY' (a' i') : Scheme.{u})) [LocallyOfFiniteType s]

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType h] [LocallyOfFiniteType s] in
/-- The structure morphisms `T ⟶ S` through `V'` and through `V` agree. -/
theorem restrictionPieceTest_comp_structure :
    s ≫ ((UY' (a' i')).ι ≫ (h ≫ sY)) =
      restrictionPieceTest h UY a UY' a' i i' hY s ≫ ((UY (a i)).ι ≫ sY) := by
  rw [← Category.assoc (restrictionPieceTest h UY a UY' a' i i' hY s),
    restrictionPieceTest_comp_ι]
  simp only [Category.assoc]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f] [LocallyOfFiniteType h]
  [LocallyOfFiniteType s] in
/-- The comparison is compatible with the structure morphisms of `X'_{i'} ×_{V'} T` and
`X_i ×_V T` to `S`. -/
theorem restrictionPieceComparison_comp_structure :
    restrictionPieceComparison f h UX UY a ha UX' UY' a' ha' i i' hX hY s ≫
        (pullback.fst (pieceMap f UX UY a ha i) (restrictionPieceTest h UY a UY' a' i i' hY s) ≫
          ((UX i).ι ≫ sX)) =
      pullback.fst (pieceMap (pullback.snd f h) UX' UY' a' ha' i') s ≫
        ((UX' i').ι ≫ (pullback.fst f h ≫ sX)) := by
  rw [restrictionPieceComparison_fst_assoc, Scheme.Hom.resLE_comp_ι_assoc]

/-- **The restriction of `res(c)` to a piece**: for pieces `X'_{i'} ⟶ V'` of the base change
`X' = X ×_Y Y' ⟶ Y'` and `X_i ⟶ V` of `f` with `X'_{i'}` over `X_i` and `V'` over `V`, the cap
operation of the restriction of `res(c)` to `X'_{i'} ⟶ V'` at `s : T ⟶ V'` is the cap operation of
the restriction of `c` to `X_i ⟶ V` at `T ⟶ V' ⟶ V`, restricted along the open immersion
`X'_{i'} ×_{V'} T ⟶ X_i ×_V T`. -/
theorem bivariantPieceRestrictionCap_bivariantRestrictionOfInvertible
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) (k : ℤ)
    (β : chowGroup C (s ≫ ((UY' (a' i')).ι ≫ (h ≫ sY))) k) :
    bivariantPieceRestrictionCap C (gysinSystemOfInvertible C) (pullback.fst f h ≫ sX) (h ≫ sY)
        (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p UX' UY' a'
        ha' i' (bivariantRestrictionOfInvertible C sX sY f hf h p c) s k β =
      chowGroupRestrict C
        (pullback.fst (pieceMap f UX UY a ha i) (restrictionPieceTest h UY a UY' a' i i' hY s) ≫
          ((UX i).ι ≫ sX))
        (pullback.fst (pieceMap (pullback.snd f h) UX' UY' a' ha' i') s ≫
          ((UX' i').ι ≫ (pullback.fst f h ≫ sX)))
        (restrictionPieceComparison f h UX UY a ha UX' UY' a' ha' i i' hX hY s)
        (restrictionPieceComparison_comp_structure C sX f h UX UY a ha UX' UY' a' ha' i i' hX hY s)
        (k - p)
        (bivariantPieceRestrictionCap C (gysinSystemOfInvertible C) sX sY f hf p UX UY a ha i c
          (restrictionPieceTest h UY a UY' a' i i' hY s) k
          (chowGroupCongr C (restrictionPieceTest_comp_structure C sY h UY a UY' a' i i' hY s) k
            β)) := by
  have hm := restrictionPieceTest_comp_ι h UY a UY' a' i i' hY s
  have hmY : restrictionPieceTest h UY a UY' a' i i' hY s ≫ ((UY (a i)).ι ≫ sY) =
      ((s ≫ (UY' (a' i')).ι) ≫ h) ≫ sY := by
    rw [← Category.assoc, hm]
  rw [bivariantPieceRestrictionCap_apply, bivariantRestrictionOfInvertible_cap,
    bivariantRestrictionCap_apply,
    chowPushforwardOfIso_inv_eq_chowGroupRestrict C _ _ (pullbackLeftPullbackSndIso f h _) _
      (by simp),
    chowGroupRestrict_comp,
    bivariantPieceRestrictionCap_eq C (gysinSystemOfInvertible C) sX sY f hf p UX UY a ha i c
      (restrictionPieceTest h UY a UY' a' i i' hY s) ((s ≫ (UY' (a' i')).ι) ≫ h) hm hmY
      (pieceComparisonCongr f UX UY a ha i _ _ hm)
      (pieceComparisonCongr_fst _ _ _ _ _ _ _ _ _) (pieceComparisonCongr_snd _ _ _ _ _ _ _ _ _) k
      (pieceComparisonCongr_comp_structureMorphism _ _ _ _ _ _ _ _ hm sX),
    chowGroupRestrict_comp, chowGroupCongr_chowGroupCongr, chowGroupCongr_chowGroupCongr]
  exact DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _
    (restrictionPieceComparison_comp f h UX UY a ha UX' UY' a' ha' i i' hX hY s).symm _) _

end RestrictionPieceCap

section Geometry

variable {Z X X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (h : X' ⟶ X)
  [LocallyConnectedSpace Z] [LocallyConnectedSpace X] [LocallyConnectedSpace X']
  [LocallyConnectedSpace ↥(pullback i h)]

/-- The open `W'' = W'_{k'} ∩ h⁻¹(W_k)` of `X'` attached to a connected component `Z'_{k'}` of
`Z' = Z ×_X X'`, where `Z_k` is the connected component of `Z` below `Z'_{k'}`. -/
def midAmbient (k' : _root_.ConnectedComponents ↥(pullback i h)) : X'.Opens :=
  componentAmbient (pullback.snd i h) k' ⊓
    h ⁻¹ᵁ componentAmbient i ((pullback.fst i h).continuous.connectedComponentsMap k')

/-- The preimage of `W''` in `Z'` is the connected component `Z'_{k'}`. -/
theorem preimage_midAmbient (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    pullback.snd i h ⁻¹ᵁ midAmbient i h k' = (pullback i h).connectedComponentOpens k' := by
  refine le_antisymm (fun z hz => (preimage_componentAmbient (pullback.snd i h) k').le hz.1)
    fun z hz => ⟨(preimage_componentAmbient (pullback.snd i h) k').ge hz, ?_⟩
  change (pullback.snd i h ≫ h).base z ∈ componentAmbient i _
  rw [← pullback.condition]
  exact (preimage_componentAmbient i _).ge
    ((pullback.fst i h).connectedComponentOpens_le_preimage k' hz)

/-- The connected component `Z'_{k'}` lies in the preimage of `W''`. -/
theorem le_preimage_midAmbient (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    (pullback i h).connectedComponentOpens k' ≤ pullback.snd i h ⁻¹ᵁ midAmbient i h k' :=
  (preimage_midAmbient i h k').ge

/-- The closed immersion `Z'_{k'} ⟶ W''`. -/
abbrev midPiece (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    ((pullback i h).connectedComponentOpens k' : Scheme.{u}) ⟶ (midAmbient i h k' : Scheme.{u}) :=
  pieceMap (pullback.snd i h) (pullback i h).connectedComponentOpens (midAmbient i h) id
    (le_preimage_midAmbient i h) k'

/-- `Z'_{k'}` is the base change of `Z' ⟶ X'` along the open immersion `W'' ⟶ X'`. -/
theorem isPullback_midPiece (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    IsPullback (midPiece i h k') ((pullback i h).connectedComponentOpens k').ι
      (midAmbient i h k').ι (pullback.snd i h) :=
  Stacks.Thickenings.isPullback_resLE_of_preimage_eq (pullback.snd i h) (preimage_midAmbient i h k')

/-- `Z'_{k'} ⟶ W''` is a closed immersion. -/
instance isClosedImmersion_midPiece (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    IsClosedImmersion (midPiece i h k') :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_midPiece i h k').flip
    inferInstance

/-- The inclusion `W'' ⟶ W'_{k'}`. -/
abbrev midIncl (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    (midAmbient i h k' : Scheme.{u}) ⟶ (componentAmbient (pullback.snd i h) k' : Scheme.{u}) :=
  X'.homOfLE inf_le_left

/-- The square of `Z'_{k'} ⟶ W''` over `Z'_{k'} ⟶ W'_{k'}` is cartesian. -/
theorem isPullback_midA (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    IsPullback (midPiece i h k') (𝟙 _) (midIncl i h k') (componentPiece (pullback.snd i h) k') := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_componentPiece (pullback.snd i h) k')
  · have e₁ : 𝟙 _ ≫ ((pullback i h).connectedComponentOpens k').ι =
        ((pullback i h).connectedComponentOpens k').ι := Category.id_comp _
    have e₂ : midIncl i h k' ≫ (componentAmbient (pullback.snd i h) k').ι =
        (midAmbient i h k').ι := Scheme.homOfLE_ι _ _
    rw [e₁, e₂]
    exact isPullback_midPiece i h k'
  · have e₂ : midIncl i h k' ≫ (componentAmbient (pullback.snd i h) k').ι =
        (midAmbient i h k').ι := Scheme.homOfLE_ι _ _
    have e₃ : midPiece i h k' ≫ (midAmbient i h k').ι =
        ((pullback i h).connectedComponentOpens k').ι ≫ pullback.snd i h :=
      pieceMap_comp_ι _ _ _ _ _ _
    have e₄ : componentPiece (pullback.snd i h) k' ≫ (componentAmbient (pullback.snd i h) k').ι =
        ((pullback i h).connectedComponentOpens k').ι ≫ pullback.snd i h :=
      pieceMap_comp_ι _ _ _ _ _ _
    rw [← cancel_mono (componentAmbient (pullback.snd i h) k').ι, Category.assoc, e₂,
      Category.id_comp, e₃, e₄]

/-- The morphism `Z'_{k'} ⟶ Z_k` of components. -/
abbrev midSource (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    ((pullback i h).connectedComponentOpens k' : Scheme.{u}) ⟶
      (Z.connectedComponentOpens ((pullback.fst i h).continuous.connectedComponentsMap k') :
        Scheme.{u}) :=
  (pullback.fst i h).resLE _ _ ((pullback.fst i h).connectedComponentOpens_le_preimage k')

/-- The morphism `W'' ⟶ W_k` of ambient opens. -/
abbrev midTarget (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    (midAmbient i h k' : Scheme.{u}) ⟶
      (componentAmbient i ((pullback.fst i h).continuous.connectedComponentsMap k') :
        Scheme.{u}) :=
  h.resLE _ _ inf_le_right

/-- The square of `Z'_{k'} ⟶ W''` over `Z_k ⟶ W_k` is cartesian. -/
theorem isPullback_midB (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    IsPullback (midPiece i h k') (midSource i h k') (midTarget i h k')
      (componentPiece i ((pullback.fst i h).continuous.connectedComponentsMap k')) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_componentPiece i _)
  · have e₁ : midSource i h k' ≫ (Z.connectedComponentOpens _).ι =
        ((pullback i h).connectedComponentOpens k').ι ≫ pullback.fst i h :=
      Scheme.Hom.resLE_comp_ι _ _
    have e₂ : midTarget i h k' ≫ (componentAmbient i _).ι = (midAmbient i h k').ι ≫ h :=
      Scheme.Hom.resLE_comp_ι _ _
    rw [e₁, e₂]
    exact (isPullback_midPiece i h k').paste_vert (IsPullback.of_hasPullback i h).flip
  · have e₁ : midSource i h k' ≫ (Z.connectedComponentOpens _).ι =
        ((pullback i h).connectedComponentOpens k').ι ≫ pullback.fst i h :=
      Scheme.Hom.resLE_comp_ι _ _
    have e₂ : midTarget i h k' ≫ (componentAmbient i _).ι = (midAmbient i h k').ι ≫ h :=
      Scheme.Hom.resLE_comp_ι _ _
    have e₃ : midPiece i h k' ≫ (midAmbient i h k').ι =
        ((pullback i h).connectedComponentOpens k').ι ≫ pullback.snd i h :=
      pieceMap_comp_ι _ _ _ _ _ _
    have e₄ : componentPiece i ((pullback.fst i h).continuous.connectedComponentsMap k') ≫
        (componentAmbient i ((pullback.fst i h).continuous.connectedComponentsMap k')).ι =
        (Z.connectedComponentOpens ((pullback.fst i h).continuous.connectedComponentsMap k')).ι ≫
          i := pieceMap_comp_ι _ _ _ _ _ _
    rw [← cancel_mono (componentAmbient i _).ι, Category.assoc, e₂, reassoc_of% e₃,
      Category.assoc, e₄, reassoc_of% e₁, pullback.condition]

end Geometry

section Bundles

variable {Z X X' : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (h : X' ⟶ X)
  [LocallyConnectedSpace Z] [LocallyConnectedSpace X] [LocallyConnectedSpace X']
  [LocallyConnectedSpace ↥(pullback i h)] (𝒩 : VirtualNormalBundle i)

/-- The virtual normal bundle `g^*𝒩` of Stacks 0FBJ for `Z' = Z ×_X X' ⟶ X'`. -/
abbrev baseChangePullback : VirtualNormalBundle (pullback.snd i h) :=
  𝒩.baseChangeAlong (IsPullback.of_hasPullback i h).flip

/-- The virtual normal bundle `𝒩''` of `Z'_{k'} ⟶ W''`. -/
abbrev midBundle (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    VirtualNormalBundle (midPiece i h k') :=
  ((𝒩.baseChangePullback h).restrictComponent k').baseChangeAlong (isPullback_midA i h k')

/-- `𝒩''` compares to `𝒩|_{Z_k}` over the square of `Z'_{k'} ⟶ W''` over `Z_k ⟶ W_k`. -/
def midComparison (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    Comparison (isPullback_midB i h k')
      (𝒩.restrictComponent ((pullback.fst i h).continuous.connectedComponentsMap k'))
      (𝒩.midBundle h k') :=
  Comparison.cancel (sq₁ := isPullback_componentPiece i _)
    (sq₁₂ := (isPullback_midB i h k').paste_vert (isPullback_componentPiece i _))
    (Comparison.ofBaseChange _ 𝒩)
    (Comparison.congr (sq := (isPullback_midA i h k').paste_vert
        ((isPullback_componentPiece (pullback.snd i h) k').paste_vert
          (IsPullback.of_hasPullback i h).flip))
      ((Category.id_comp _).trans (Scheme.Hom.resLE_comp_ι _ _).symm)
      (((Scheme.homOfLE_ι_assoc _ _ _).trans (Scheme.Hom.resLE_comp_ι _ _).symm))
      (((Comparison.ofBaseChange (IsPullback.of_hasPullback i h).flip 𝒩).trans
          (sq₁₂ := (isPullback_componentPiece (pullback.snd i h) k').paste_vert
            (IsPullback.of_hasPullback i h).flip)
          (Comparison.ofBaseChange (isPullback_componentPiece (pullback.snd i h) k')
            (𝒩.baseChangePullback h))).trans
        (Comparison.ofBaseChange (isPullback_midA i h k')
          ((𝒩.baseChangePullback h).restrictComponent k'))))

end Bundles

section Main

variable {Z X X' : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (h : X' ⟶ X)
  [LocallyOfFiniteType h] (𝒩 : VirtualNormalBundle i) (C : ChowSituation.{u}) (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)
  [IsLocallyNoetherian Z] [IsLocallyNoetherian X] [IsLocallyNoetherian X']
  [IsLocallyNoetherian (pullback i h)]

omit [LocallyOfFiniteType h] in
/-- **The rank of `g^*𝒩` on a component `Z'_{k'}`** is the rank of `𝒩` on the component of `Z`
below it: the comparison of `𝒩''` with `𝒩|_{Z_k}` is an isomorphism of the duals. -/
theorem componentRank_baseChangePullback (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    (𝒩.baseChangePullback h).componentRank k' =
      𝒩.componentRank ((pullback.fst i h).continuous.connectedComponentsMap k') := by
  obtain ⟨x', rfl⟩ := ConnectedComponents.surjective_coe k'
  have := (𝒩.midComparison h (ConnectedComponents.mk x')).isIso
  have hsrc : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (midSource i h (ConnectedComponents.mk x'))).obj
        (dualSheaf (𝒩.restrictComponent
          ((pullback.fst i h).continuous.connectedComponentsMap
            (ConnectedComponents.mk x'))).bundle))
      (𝒩.componentRank ((pullback.fst i h).continuous.connectedComponentsMap
        (ConnectedComponents.mk x'))) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Stacks.ProjectiveBundleQuotients.pullbackIso _).app _).symm
      (isFiniteLocallyFreeOfRank_modulePullback _ _ _
        (isFiniteLocallyFreeOfRank_dualSheaf _ _ inferInstance))
  have htgt : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualSheaf (𝒩.midBundle h (ConnectedComponents.mk x')).bundle)
      ((𝒩.baseChangePullback h).componentRank (ConnectedComponents.mk x')) :=
    isFiniteLocallyFreeOfRank_dualSheaf _ _
      (isFiniteLocallyFreeOfRank_modulePullback _ _ _ inferInstance)
  have e := asIso (𝒩.midComparison h (ConnectedComponents.mk x')).map
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_unique _ htgt
    (SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e hsrc) ⟨x', rfl⟩

/-- The restriction of `g^*𝒩` to `Z'_{k'}` is finite locally free of the rank of `𝒩` on the
component of `Z` below `Z'_{k'}`. -/
instance isFiniteLocallyFreeOfRank_restrictComponent_baseChangePullback
    (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.baseChangePullback h).restrictComponent k').bundle
      (𝒩.componentRank ((pullback.fst i h).continuous.connectedComponentsMap k')) := by
  rw [← 𝒩.componentRank_baseChangePullback h k']
  infer_instance

/-- The bundle of `𝒩''` is finite locally free of the rank of `𝒩` on the component of `Z`
below `Z'_{k'}`. -/
instance isFiniteLocallyFreeOfRank_midBundle (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.midBundle h k').bundle
      (𝒩.componentRank ((pullback.fst i h).continuous.connectedComponentsMap k')) :=
  isFiniteLocallyFreeOfRank_modulePullback _ _ _
    (𝒩.isFiniteLocallyFreeOfRank_restrictComponent_baseChangePullback h k')

/-- **The degree `p` parts of `c(Z' ⟶ X', 𝒩')` and of `res(c(Z ⟶ X, 𝒩))` agree on
`Z'_{k'} ⟶ W''`**: both are `c(Z'_{k'} ⟶ W'', 𝒩'')` when `p` is the rank `r` of `𝒩` on the
component `Z_k` below `Z'_{k'}`, and zero otherwise. -/
theorem midRestriction_degreeClass (p : ℤ) (k' : _root_.ConnectedComponents ↥(pullback i h)) :
    bivariantPieceRestrictionOfInvertible C (pullback.fst i h ≫ sZ) (h ≫ sX) (pullback.snd i h)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) p
        (pullback i h).connectedComponentOpens (midAmbient i h) id (le_preimage_midAmbient i h) k'
        ((𝒩.baseChangePullback h).degreeClass C (h ≫ sX) (pullback.fst i h ≫ sZ)
          (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) p) =
      bivariantPieceRestrictionOfInvertible C (pullback.fst i h ≫ sZ) (h ≫ sX) (pullback.snd i h)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) p
        (pullback i h).connectedComponentOpens (midAmbient i h) id (le_preimage_midAmbient i h) k'
        (bivariantRestrictionOfInvertible C sZ sX i hZ h p (𝒩.degreeClass C sX sZ hZ p)) := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun s _ n β => ?_
  change bivariantPieceRestrictionCap C (gysinSystemOfInvertible C) (pullback.fst i h ≫ sZ)
      (h ≫ sX) (pullback.snd i h) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) p
      (pullback i h).connectedComponentOpens (midAmbient i h) id (le_preimage_midAmbient i h) k'
      _ s n β =
    bivariantPieceRestrictionCap C (gysinSystemOfInvertible C) (pullback.fst i h ≫ sZ) (h ≫ sX)
      (pullback.snd i h) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) p
      (pullback i h).connectedComponentOpens (midAmbient i h) id (le_preimage_midAmbient i h) k'
      _ s n β
  rw [bivariantPieceRestrictionCap_grow C (gysinSystemOfInvertible C) (pullback.fst i h ≫ sZ)
      (h ≫ sX) (pullback.snd i h) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) p
      (pullback i h).connectedComponentOpens (componentAmbient (pullback.snd i h)) id
      (le_preimage_componentAmbient (pullback.snd i h)) (midAmbient i h) id
      (le_preimage_midAmbient i h) k' inf_le_left s,
    bivariantPieceRestrictionCap_bivariantRestrictionOfInvertible C sZ sX i hZ h p
      Z.connectedComponentOpens (componentAmbient i) id (le_preimage_componentAmbient i)
      (pullback i h).connectedComponentOpens (midAmbient i h) id (le_preimage_midAmbient i h)
      ((pullback.fst i h).continuous.connectedComponentsMap k') k'
      ((pullback.fst i h).connectedComponentOpens_le_preimage k') inf_le_right s,
    ← componentFamily_cap, ← componentFamily_cap]
  by_cases hp : (𝒩.componentRank ((pullback.fst i h).continuous.connectedComponentsMap k') : ℤ) = p
  · subst hp
    rw [(𝒩.baseChangePullback h).componentFamily_eq C (h ≫ sX) (pullback.fst i h ≫ sZ)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) k'
        (𝒩.componentRank ((pullback.fst i h).continuous.connectedComponentsMap k')) _ rfl,
      𝒩.componentFamily_rank C sX sZ hZ]
    have : LocallyOfFiniteType (midTarget i h k') := by
      have e : midTarget i h k' ≫ (componentAmbient i
          ((pullback.fst i h).continuous.connectedComponentsMap k')).ι =
          (midAmbient i h k').ι ≫ h := Scheme.Hom.resLE_comp_ι _ _
      have : LocallyOfFiniteType (midTarget i h k' ≫ (componentAmbient i
          ((pullback.fst i h).continuous.connectedComponentsMap k')).ι) := by
        rw [e]
        infer_instance
      exact locallyOfFiniteType_of_comp _ (componentAmbient i _).ι
    have : LocallyOfFiniteType (midIncl i h k') := by
      have e : midIncl i h k' ≫ (componentAmbient (pullback.snd i h) k').ι =
          (midAmbient i h k').ι := Scheme.homOfLE_ι _ _
      have : LocallyOfFiniteType (midIncl i h k' ≫
          (componentAmbient (pullback.snd i h) k').ι) := by
        rw [e]
        infer_instance
      exact locallyOfFiniteType_of_comp _ (componentAmbient (pullback.snd i h) k').ι
    have := isOpenImmersion_restrictionPieceComparison i h Z.connectedComponentOpens
      (componentAmbient i) id (le_preimage_componentAmbient i)
      (pullback i h).connectedComponentOpens (midAmbient i h) id (le_preimage_midAmbient i h)
      ((pullback.fst i h).continuous.connectedComponentsMap k') k'
      ((pullback.fst i h).connectedComponentOpens_le_preimage k') inf_le_right s
    have := isIso_growComparison (pullback.snd i h) (pullback i h).connectedComponentOpens
      (componentAmbient (pullback.snd i h)) id (le_preimage_componentAmbient (pullback.snd i h))
      (midAmbient i h) id (le_preimage_midAmbient i h) k' inf_le_left s
    have hZ'' := baseChange_structure (isPullback_midPiece i h k') C (h ≫ sX)
      (pullback.fst i h ≫ sZ) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h)
    have eA := (Comparison.ofBaseChange (isPullback_midA i h k')
      ((𝒩.baseChangePullback h).restrictComponent k')).virtualNormalClass_cap_eq_chowGroupRestrict'
      C ((componentAmbient (pullback.snd i h) k').ι ≫ (h ≫ sX))
      (((pullback i h).connectedComponentOpens k').ι ≫ (pullback.fst i h ≫ sZ))
      (baseChange_structure (isPullback_componentPiece (pullback.snd i h) k') C (h ≫ sX)
        (pullback.fst i h ≫ sZ) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h))
      (𝒩.componentRank ((pullback.fst i h).continuous.connectedComponentsMap k'))
      ((midAmbient i h k').ι ≫ (h ≫ sX))
      (((pullback i h).connectedComponentOpens k').ι ≫ (pullback.fst i h ≫ sZ))
      (Scheme.homOfLE_ι_assoc _ _ _) (Category.id_comp _) hZ'' s (s ≫ midIncl i h k') rfl
      (growComparison (pullback.snd i h) (pullback i h).connectedComponentOpens
        (componentAmbient (pullback.snd i h)) id (le_preimage_componentAmbient (pullback.snd i h))
        (midAmbient i h) id (le_preimage_midAmbient i h) k' inf_le_left s)
      ((growComparison_fst _ _ _ _ _ _ _ _ _ _ _).trans (Category.comp_id _).symm)
      (growComparison_snd _ _ _ _ _ _ _ _ _ _ _) (growComparison_fst_assoc _ _ _ _ _ _ _ _ _ _ _ _)
      (homOfLE_comp_structure C (h ≫ sX) (componentAmbient (pullback.snd i h)) id
        (midAmbient i h) id k' inf_le_left s) n β
    have eB := (𝒩.midComparison h k').virtualNormalClass_cap_eq_chowGroupRestrict' C
      ((componentAmbient i ((pullback.fst i h).continuous.connectedComponentsMap k')).ι ≫ sX)
      ((Z.connectedComponentOpens ((pullback.fst i h).continuous.connectedComponentsMap k')).ι ≫ sZ)
      (baseChange_structure (isPullback_componentPiece i _) C sX sZ hZ)
      (𝒩.componentRank ((pullback.fst i h).continuous.connectedComponentsMap k'))
      ((midAmbient i h k').ι ≫ (h ≫ sX))
      (((pullback i h).connectedComponentOpens k').ι ≫ (pullback.fst i h ≫ sZ))
      (Scheme.Hom.resLE_comp_ι_assoc _ _ _) (Scheme.Hom.resLE_comp_ι_assoc _ _ _) hZ'' s
      (s ≫ midTarget i h k') rfl
      (restrictionPieceComparison i h Z.connectedComponentOpens (componentAmbient i) id
        (le_preimage_componentAmbient i) (pullback i h).connectedComponentOpens (midAmbient i h) id
        (le_preimage_midAmbient i h) ((pullback.fst i h).continuous.connectedComponentsMap k') k'
        ((pullback.fst i h).connectedComponentOpens_le_preimage k') inf_le_right s)
      (restrictionPieceComparison_fst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (restrictionPieceComparison_snd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (restrictionPieceComparison_comp_structure C sZ i h _ _ _ _ _ _ _ _ _ _ _ _ s)
      (restrictionPieceTest_comp_structure C sX h _ _ _ _ _ _ _ s) n β
    exact eA.symm.trans eB
  · rw [(𝒩.baseChangePullback h).componentFamily_of_ne C (h ≫ sX) (pullback.fst i h ≫ sZ)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h)
        (by rwa [𝒩.componentRank_baseChangePullback h k']),
      𝒩.componentFamily_of_ne C sX sZ hZ hp]
    simp only [BivariantClass.zero_cap, map_zero]

/-- **Stacks 0FBK, compatibility with base change**: for `h : X' ⟶ X` locally of finite type,
`Z' = Z ×_X X'` and the virtual normal bundle `𝒩' = g^*𝒩` of Stacks 0FBJ for `Z' ⟶ X'`, the class
`c(Z' ⟶ X', 𝒩') ∈ A^*(Z' ⟶ X')^∧` is the restriction (Stacks 0F9Z) of
`c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧`. The rank of `𝒩` need not be constant. -/
theorem completedClass_baseChange :
    (𝒩.baseChangePullback h).completedClass C (h ≫ sX) (pullback.fst i h ≫ sZ)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) =
      completedBivariantRestrictionOfInvertible C sZ sX i hZ h (𝒩.completedClass C sX sZ hZ) := by
  refine eq_completedBivariantRestrictionOfInvertible C sZ sX i hZ h _ _ fun p => ?_
  rw [completedBivariantSequenceOfInvertible_completedClass,
    completedBivariantSequenceOfInvertible_completedClass]
  refine (bivariantPieceEquivOfInvertible C (pullback.fst i h ≫ sZ) (h ≫ sX) (pullback.snd i h)
    (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) p
    (pullback i h).connectedComponentOpens (componentAmbient (pullback.snd i h)) id
    (le_preimage_componentAmbient (pullback.snd i h))
    (pullback i h).isClopenDecomposition_connectedComponentOpens).injective
    (funext fun k' => ?_)
  exact bivariantPieceRestriction_eq_of_shrink C (gysinSystemOfInvertible C)
    (pullback.fst i h ≫ sZ) (h ≫ sX) (pullback.snd i h)
    (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) p
    (pullback i h).connectedComponentOpens (componentAmbient (pullback.snd i h)) id
    (le_preimage_componentAmbient (pullback.snd i h)) (midAmbient i h) id
    (le_preimage_midAmbient i h) k' (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _ _
    (𝒩.midRestriction_degreeClass h C sX sZ hZ p k')

end Main

end Stacks.Chow.VirtualNormalBundle

end
