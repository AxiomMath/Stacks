module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedComponentReduction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedConstantRank
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessNormalSheafBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.TopChernClassOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.GysinAtInfinityRestriction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The excess intersection formula, for a virtual normal sheaf of arbitrary rank

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed immersion with a virtual normal sheaf `𝒩` in the
sense of Stacks 0FBQ, of arbitrary rank, and let `g : Y ⟶ X` be locally of finite type such that
the base change `Z' = Z ×_X Y ⟶ Y` is a regular closed immersion whose conormal sheaf
`𝒞_{Z'/Y}` has constant rank `r`. Let `ℰ` be the excess normal sheaf,
`0 ⟶ ℰ^∨ ⟶ 𝒩^∨|_{Z'} ⟶ 𝒞_{Z'/Y} ⟶ 0`. **Stacks 0FBM** asserts that if `dim_δ(Y) = n` then

  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_top(ℰ) ∩ [Z ×_X Y]_{n - r}`

in `CH_*(Z ×_X Y)`, for the class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of Stacks 0FBK and the top Chern
class of Stacks 0FA4. The rank of `𝒩` is only locally constant, so neither side is homogeneous:
both are read degree by degree, the degree-`p` part of `c(Z ⟶ X, 𝒩)` capping into
`CH_{n - p}(Z ×_X Y)`. In degree `n - (r + e)` the degree-`(r + e)` part of
`c(Z ⟶ X, 𝒩) ∩ [Y]_n` is the degree-`e` part of `c_top(ℰ)` capped with `[Z']_{n - r}`
(`Stacks.Chow.topChernCap`), and in degree `n - p` for `p < r` the left-hand side vanishes. The
formula is proved under the hypothesis `dim_δ(Y) ≤ n`, with `Z ×_X Y` an arbitrary cartesian
square `Z'`.

## Main results

* `Stacks.Chow.pieceExcessNormalSheafIso` — the excess normal sheaf of the piece over `Z_a` is the
  restriction of `ℰ`.
* `Stacks.Chow.completedVirtualNormalGysinCap_fundamentalChowClass_excess` — the excess
  intersection formula `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_top(ℰ) ∩ [Z ×_X Y]_{n - r}`, degree by degree.

## References

* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

/-! ### The pieces of a base change over the connected components -/

section Piece

variable {Z X Z' Y : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] [LocallyConnectedSpace Z]
  [LocallyConnectedSpace X] {g : Y ⟶ X} {i' : Z' ⟶ Y} {g' : Z' ⟶ Z}
  (sq : IsPullback i' g' g i) (a : _root_.ConnectedComponents Z)

omit [IsClosedImmersion i] in
/-- The restriction of a regular immersion to an open subscheme of the target is regular. -/
theorem isRegularImmersion_morphismRestrict {Z' Y : Scheme.{u}} {i' : Z' ⟶ Y} [IsImmersion i']
    (hreg : IsRegularImmersion i') (V : Y.Opens) : IsRegularImmersion (i' ∣_ V) :=
  Stacks.AlgebraicGeometry.isRegularImmersion_of_isPullback_of_flat
    (isPullback_morphismRestrict i' V) hreg

omit [IsClosedImmersion i] in
/-- The conormal sheaf of the restriction of an immersion to an open subscheme of the target is
the pullback of the conormal sheaf (Stacks 0473, flat base change). -/
@[sga "3 I 6.8.5" "special case"]
def conormalModuleMorphismRestrictIso {Z' Y : Scheme.{u}} (i' : Z' ⟶ Y) [IsImmersion i']
    (V : Y.Opens) :
    @Iso (i' ⁻¹ᵁ V : Scheme.{u}).Modules _
      ((RingedSpaceModuleAdjunction.modulePullback (i' ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        (conormalModule i'))
      (conormalModule (i' ∣_ V)) :=
  @asIso _ _ _ _ (Stacks.Immersion.immersionConormalSheafMap (i' ∣_ V) i' (i' ⁻¹ᵁ V).ι V.ι
      (Stacks.Immersion.toShHom_square (isPullback_morphismRestrict i' V).w))
    (Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat (i' ∣_ V) i' (i' ⁻¹ᵁ V).ι V.ι
      (isPullback_morphismRestrict i' V))

omit [IsClosedImmersion i] in
/-- The conormal sheaf of the restriction of an immersion to an open subscheme of the target has
the rank of the conormal sheaf. -/
theorem isFiniteLocallyFreeOfRank_conormalModule_morphismRestrict {Z' Y : Scheme.{u}}
    (i' : Z' ⟶ Y) [IsImmersion i'] (V : Y.Opens) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i') r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule (i' ∣_ V)) r :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (conormalModuleMorphismRestrictIso i' V)
    (isFiniteLocallyFreeOfRank_modulePullback _ (conormalModule i') r inferInstance)

/-- The excess normal sheaf of the base change of `𝒩|_{Z_a}` along the piece `Z'_a ⟶ Z_a` of the
cartesian square over a connected component `Z_a` of `Z` is the pullback to `Z'_a` of the excess
normal sheaf of `𝒩|_{Z'}`. -/
def pieceExcessNormalSheafIso [IsImmersion i'] (𝒩 : VirtualNormalBundle i)
    (hC : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (conormalModule i')) :
    ((𝒩.toComponent i a).baseChange (componentRestriction i a)
        (i' ∣_ (g ⁻¹ᵁ componentNeighbourhood i a)) (pieceProjection sq a)
        (g ∣_ componentNeighbourhood i a) (isPullback_pieceProjection sq a)).excessNormalSheaf ≅
      (Scheme.Modules.pullback (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι).obj
        (𝒩.baseChange i i' g' g sq).excessNormalSheaf :=
  𝒩.excessNormalSheafBaseChangeCompIso (isPullback_componentRestriction i a)
      (isPullback_pieceProjection sq a) ≪≫
    eqToIso (congrArg VirtualNormalBundle.excessNormalSheaf (𝒩.baseChange_congr
      ((Scheme.Hom.resLE_comp_ι g' _).trans rfl) (morphismRestrict_ι g _) _
      ((isPullback_morphismRestrict i' (g ⁻¹ᵁ componentNeighbourhood i a)).paste_vert sq))) ≪≫
    (𝒩.excessNormalSheafBaseChangeCompIso sq
      (isPullback_morphismRestrict i' (g ⁻¹ᵁ componentNeighbourhood i a))).symm ≪≫
    (𝒩.baseChange i i' g' g sq).excessNormalSheafBaseChangeOpenIso
      (isPullback_morphismRestrict i' (g ⁻¹ᵁ componentNeighbourhood i a)) hC

end Piece

/-! ### The rank of a virtual normal sheaf bounds that of the conormal sheaf -/

/-- If a virtual normal sheaf `N` of an immersion `j : W ⟶ V` has rank `m`, the conormal sheaf of
`j` has rank `r` and `W` has a point, then `r ≤ m`. -/
theorem VirtualNormalBundle.le_of_isFiniteLocallyFreeOfRank {W V : Scheme.{u}} {j : W ⟶ V}
    [IsImmersion j] (N : VirtualNormalBundle j) (m r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle m]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule j) r] (x : W) :
    r ≤ m := by
  have hfl := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi
    N.conormalSurjection inferInstance N.isFiniteLocallyFree_dualSheaf
    (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r)
  obtain ⟨U, hx, e, he⟩ :=
    Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict _ hfl x
  have := Stacks.ProjectiveBundleSplitting.rank_restrict_kernel_add_eq N.conormalSurjection
    inferInstance m r e inferInstance inferInstance U x hx he
  omega

/-! ### The two sides of the excess intersection formula on a piece -/

section PieceSides

variable (C : ChowSituation.{u}) {Z X Z' Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  [IsLocallyNoetherian Z] [IsLocallyNoetherian X] (𝒩 : VirtualNormalBundle i)
  (g : Y ⟶ X) [LocallyOfFiniteType g] (i' : Z' ⟶ Y) [IsClosedImmersion i'] (g' : Z' ⟶ Z)
  (sq : IsPullback i' g' g i) (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
  (hi' : i' ≫ (g ≫ sX) = sZ') (a : _root_.ConnectedComponents Z)

/-- Let `Z_a` be a connected component of `Z` on which `𝒩` has rank `r + e`, and `Z'_a ⊆ Z'` the
piece over it. If `dim_δ(Y) ≤ n`, the restriction to `Z'_a` of the degree-`(r + e)` part of
`c(Z ⟶ X, 𝒩) ∩ [Y]_n` is `c_e(ℰ|_{Z'_a}) ∩ [Z'_a]_{n - r}`. -/
theorem chowGroupRestrict_completedVirtualNormalGysinCap_piece (hreg : IsRegularImmersion i')
    (r e : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i') r]
    (hm : componentRank 𝒩.bundle a = r + e)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι).obj
        (𝒩.baseChange i i' g' g sq).excessNormalSheaf) e]
    (n : ℤ) (hY : schemeDeltaDimension C (g ≫ sX) ≤ (n : EInt)) :
    chowGroupRestrict C (pullback.fst i g ≫ sZ)
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sq.flip.isoPullback.hom)
        (pieceInclusion_comp_structureMorphism C sZ sX i hi g i' g' sq sZ' hi' a)
        (n - ((r + e : ℕ) : ℤ))
        ((completedBivariantSequenceOfInvertible C sZ sX i hi
          (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) ((r + e : ℕ) : ℤ)).cap g n
          (fundamentalChowClass C (g ≫ sX) n)) =
      chowGroupDegreeEquiv C ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
        (by push_cast; ring)
        (GenuineChern.chernCap C e ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
          ((Scheme.Modules.pullback (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι).obj
            (𝒩.baseChange i i' g' g sq).excessNormalSheaf) (n - (r : ℤ)) (Fin.last e)
          (fundamentalChowClass C ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
            (n - (r : ℤ)))) := by
  have hg' : g' ≫ sZ = sZ' := by rw [← hi, ← Category.assoc, ← sq.w, Category.assoc, hi']
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.toComponent i a).bundle
      (r + e) := hm ▸ 𝒩.isFiniteLocallyFreeOfRank_toComponent i a
  have := isFiniteLocallyFreeOfRank_conormalModule_morphismRestrict i'
    (g ⁻¹ᵁ componentNeighbourhood i a) r
  have hreg' := isRegularImmersion_morphismRestrict hreg (g ⁻¹ᵁ componentNeighbourhood i a)
  have hgU : (g ∣_ componentNeighbourhood i a) ≫ (componentNeighbourhood i a).ι =
      (g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g := morphismRestrict_ι g _
  have hYa : schemeDeltaDimension C ((g ∣_ componentNeighbourhood i a) ≫
      ((componentNeighbourhood i a).ι ≫ sX)) ≤ (n : EInt) :=
    schemeDeltaDimension_le_of_isOpenImmersion C (g ≫ sX) _
      (g ⁻¹ᵁ componentNeighbourhood i a).ι (by rw [← Category.assoc (g ∣_ _), hgU, Category.assoc])
      hY
  have hi'a : (i' ∣_ (g ⁻¹ᵁ componentNeighbourhood i a)) ≫ ((g ∣_ componentNeighbourhood i a) ≫
      ((componentNeighbourhood i a).ι ≫ sX)) =
      (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ' := by
    rw [← Category.assoc (g ∣_ _), hgU, Category.assoc, ← Category.assoc, morphismRestrict_ι,
      Category.assoc, hi']
  have hK := virtualNormalBundleClass_cap_fundamentalChowClass_excess C
    ((Z.connectedComponentOpens a).ι ≫ sZ) ((componentNeighbourhood i a).ι ≫ sX)
    (componentRestriction i a) (componentRestriction_comp_structureMorphism C sZ sX i hi a)
    (𝒩.toComponent i a) r e
    (isVirtualNormalBundleClass_virtualNormalBundleClass C _ _ _
      (componentRestriction_comp_structureMorphism C sZ sX i hi a) (𝒩.toComponent i a) (r + e))
    (g ∣_ componentNeighbourhood i a) (i' ∣_ (g ⁻¹ᵁ componentNeighbourhood i a))
    (pieceProjection sq a) (isPullback_pieceProjection sq a)
    ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ') hi'a hreg' n hYa
  have hC := chowGroupRestrict_completedVirtualNormalGysinClass_cap_of_eq C sZ sX i hi 𝒩 a
    (r + e) hm (g ∣_ componentNeighbourhood i a) ((g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g) hgU n
    (fundamentalChowClass C ((g ∣_ componentNeighbourhood i a) ≫
      ((componentNeighbourhood i a).ι ≫ sX)) n)
  rw [chowGroupCongr_fundamentalChowClass, hK] at hC
  have : IsOpenImmersion (baseChangeMapOfEq i g (g ⁻¹ᵁ componentNeighbourhood i a).ι
      ((g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g) rfl) :=
    MorphismProperty.of_isPullback (isPullback_baseChangeMapOfEq i g _ _ rfl)
      (P := @IsOpenImmersion) inferInstance
  have h1 := BivariantClass.cap_chowGroupRestrict C (gysinSystemOfInvertible C) sZ sX i hi _
    (completedBivariantSequenceOfInvertible C sZ sX i hi
      (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) ((r + e : ℕ) : ℤ)) g
    (g ⁻¹ᵁ componentNeighbourhood i a).ι ((g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g) rfl
    (baseChangeMapOfEq i g (g ⁻¹ᵁ componentNeighbourhood i a).ι _ rfl)
    (isPullback_baseChangeMapOfEq i g _ _ rfl) (baseChangeMapOfEq_fst _ _ _ _ _) n
    (Category.assoc _ _ _).symm (baseChangeMapOfEq_comp_structure sZ i g _ _ rfl)
    (fundamentalChowClass C (g ≫ sX) n)
  rw [chowGroupRestrict_fundamentalChowClass C _ _ _ _ n hY] at h1
  have hw : (isPullback_pieceProjection sq a).flip.isoPullback.hom ≫
      (componentTestIso i a (g ∣_ componentNeighbourhood i a)
        ((g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g) hgU).hom ≫
      baseChangeMapOfEq i g (g ⁻¹ᵁ componentNeighbourhood i a).ι _ rfl =
      (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sq.flip.isoPullback.hom := by
    apply pullback.hom_ext
    · simp
    · simp [morphismRestrict_ι]
  have hθ := isoPullback_hom_comp_structureMorphism C ((Z.connectedComponentOpens a).ι ≫ sZ)
    ((componentNeighbourhood i a).ι ≫ sX) (isPullback_pieceProjection sq a)
    (componentRestriction_comp_structureMorphism C sZ sX i hi a)
    ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ') hi'a
  have hEv : ((componentTestIso i a (g ∣_ componentNeighbourhood i a)
        ((g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g) hgU).hom ≫
      baseChangeMapOfEq i g (g ⁻¹ᵁ componentNeighbourhood i a).ι _ rfl) ≫
        (pullback.fst i g ≫ sZ) =
      pullback.fst (componentRestriction i a) (g ∣_ componentNeighbourhood i a) ≫
        ((Z.connectedComponentOpens a).ι ≫ sZ) := by
    rw [Category.assoc, baseChangeMapOfEq_comp_structure, componentTestIso_hom_fst_assoc]
  rw [← chowGroupRestrict_congr C (pullback.fst i g ≫ sZ)
      ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ') _
      (by rw [hw]; exact pieceInclusion_comp_structureMorphism C sZ sX i hi g i' g' sq sZ' hi' a)
      _ _ hw,
    ← chowGroupRestrict_comp C (pullback.fst i g ≫ sZ) _ _ hEv _ _ _ hθ,
    ← chowGroupRestrict_comp C (pullback.fst i g ≫ sZ) _ _
      (baseChangeMapOfEq_comp_structure sZ i g _ _ rfl) _ _ _
      (by rw [componentTestIso_hom_fst_assoc]),
    h1, hC, chowGroupRestrict_chowPushforwardOfIso]
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.toComponent i a).baseChange (componentRestriction i a)
        (i' ∣_ (g ⁻¹ᵁ componentNeighbourhood i a)) (pieceProjection sq a)
        (g ∣_ componentNeighbourhood i a) (isPullback_pieceProjection sq a)).bundle (r + e) :=
    isFiniteLocallyFreeOfRank_modulePullback _ _ (r + e) inferInstance
  have := ((𝒩.toComponent i a).baseChange (componentRestriction i a)
    (i' ∣_ (g ⁻¹ᵁ componentNeighbourhood i a)) (pieceProjection sq a)
    (g ∣_ componentNeighbourhood i a)
    (isPullback_pieceProjection sq a)).isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add r e
  rw [GenuineChern.chernCap_congr C _ e (pieceExcessNormalSheafIso sq a 𝒩
    (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r))]

/-- If the excess normal sheaf `ℰ` has rank `e` on the piece `Z'_a` and `dim_δ(Y) ≤ n`, the
restriction of `c_top(ℰ) ∩ [Z']_{n - r}` in degree `e` to `Z'_a` is
`c_e(ℰ|_{Z'_a}) ∩ [Z'_a]_{n - r}`. -/
theorem chowGroupRestrict_topChernCap_piece (hreg : IsRegularImmersion i') (r e : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i') r]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} (𝒩.baseChange i i' g' g sq).excessNormalSheaf]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι).obj
        (𝒩.baseChange i i' g' g sq).excessNormalSheaf) e]
    (n : ℤ) (hY : schemeDeltaDimension C (g ≫ sX) ≤ (n : EInt)) :
    chowGroupRestrict C (pullback.fst i g ≫ sZ)
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sq.flip.isoPullback.hom)
        (pieceInclusion_comp_structureMorphism C sZ sX i hi g i' g' sq sZ' hi' a)
        (n - ((r + e : ℕ) : ℤ))
        (chowPushforwardOfIso C sZ' (pullback.fst i g ≫ sZ) sq.flip.isoPullback.hom
          (isoPullback_hom_comp_structureMorphism C sZ sX sq hi sZ' hi') (n - ((r + e : ℕ) : ℤ))
          (chowGroupDegreeEquiv C sZ' (by push_cast; ring)
            (topChernCap C sZ' (𝒩.baseChange i i' g' g sq).excessNormalSheaf (n - (r : ℤ)) e
              (fundamentalChowClass C sZ' (n - (r : ℤ)))))) =
      chowGroupDegreeEquiv C ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
        (by push_cast; ring)
        (GenuineChern.chernCap C e ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
          ((Scheme.Modules.pullback (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι).obj
            (𝒩.baseChange i i' g' g sq).excessNormalSheaf) (n - (r : ℤ)) (Fin.last e)
          (fundamentalChowClass C ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
            (n - (r : ℤ)))) := by
  rw [← chowGroupRestrict_comp C (pullback.fst i g ≫ sZ) sZ' _
      (isoPullback_hom_comp_structureMorphism C sZ sX sq hi sZ' hi') _ _ _ rfl,
    chowGroupRestrict_chowPushforwardOfIso, chowGroupRestrict_chowGroupDegreeEquiv,
    chowGroupRestrict_topChernCap, chowGroupRestrict_fundamentalChowClass C _ _ _ _ _
      (schemeDeltaDimension_le_sub_of_isRegularImmersion C sZ' (g ≫ sX) i' hi' hreg r n hY)]

omit [LocallyOfFiniteType sX] in
/-- If the excess normal sheaf `ℰ` has rank `s` on the piece `Z'_a` and `e ≠ s`, the restriction
of `c_top(ℰ) ∩ [Z']_{n - r}` in degree `e` to `Z'_a` vanishes. -/
theorem chowGroupRestrict_topChernCap_piece_of_ne (r e s : ℕ)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} (𝒩.baseChange i i' g' g sq).excessNormalSheaf]
    (hs : i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a) ≤
      rankLocus (𝒩.baseChange i i' g' g sq).excessNormalSheaf s) (he : e ≠ s) (n : ℤ) :
    chowGroupRestrict C (pullback.fst i g ≫ sZ)
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sq.flip.isoPullback.hom)
        (pieceInclusion_comp_structureMorphism C sZ sX i hi g i' g' sq sZ' hi' a)
        (n - ((r + e : ℕ) : ℤ))
        (chowPushforwardOfIso C sZ' (pullback.fst i g ≫ sZ) sq.flip.isoPullback.hom
          (isoPullback_hom_comp_structureMorphism C sZ sX sq hi sZ' hi') (n - ((r + e : ℕ) : ℤ))
          (chowGroupDegreeEquiv C sZ' (by push_cast; ring)
            (topChernCap C sZ' (𝒩.baseChange i i' g' g sq).excessNormalSheaf (n - (r : ℤ)) e
              (fundamentalChowClass C sZ' (n - (r : ℤ)))))) = 0 := by
  rw [← chowGroupRestrict_comp C (pullback.fst i g ≫ sZ) sZ' _
      (isoPullback_hom_comp_structureMorphism C sZ sX sq hi sZ' hi') _ _ _ rfl,
    chowGroupRestrict_chowPushforwardOfIso, chowGroupRestrict_chowGroupDegreeEquiv,
    chowGroupRestrict_topChernCap_of_ne C sZ' _ _ s e hs he, map_zero]

end PieceSides

/-! ### Stacks 0FBM -/

section Main

variable (C : ChowSituation.{u}) {Z X Z' Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  (𝒩 : VirtualNormalBundle i) (g : Y ⟶ X) [LocallyOfFiniteType g] (i' : Z' ⟶ Y)
  [IsClosedImmersion i'] (g' : Z' ⟶ Z) (sq : IsPullback i' g' g i) (sZ' : Z' ⟶ C.S)
  [LocallyOfFiniteType sZ'] (hi' : i' ≫ (g ≫ sX) = sZ')

/-- Let `i : Z ⟶ X` be a closed immersion of schemes locally of finite type over the base with a
virtual normal sheaf `𝒩` (Stacks 0FBQ), of arbitrary rank, and let `g : Y ⟶ X` be locally of
finite type such that the base change `i' : Z' = Z ×_X Y ⟶ Y` is a regular closed immersion whose
conormal sheaf `𝒞_{Z'/Y}` has constant rank `r`. Let `ℰ` be the excess normal sheaf,
`0 ⟶ ℰ^∨ ⟶ 𝒩^∨|_{Z'} ⟶ 𝒞_{Z'/Y} ⟶ 0`. If `dim_δ(Y) ≤ n` then

  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_top(ℰ) ∩ [Z']_{n - r}`

in `CH_*(Z ×_X Y)`, for the class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of Stacks 0FBK
(`Stacks.Chow.completedVirtualNormalGysinClass`) and the top Chern class of Stacks 0FA4: in
degree `n - (r + e)` the degree-`(r + e)` part of the left-hand side is the cap product of
`[Z']_{n - r}` with the degree-`e` part of `c_top(ℰ)` (`Stacks.Chow.topChernCap`), and in degree
`n - p` for `p < r` the left-hand side vanishes, as the right-hand side does. -/
@[stacks 0FBM "c(Z → X, N) ∩ [Y]_n = c_top(E) ∩ [Z ×_X Y]_{n-r} in CH_*(Z ×_X Y), for N a virtual \
normal sheaf of arbitrary rank, c(Z → X, N) ∈ A^*(Z → X)^∧, Z ×_X Y → Y regular with conormal \
sheaf of constant rank r, E the excess normal sheaf, and dim_δ(Y) ≤ n; stated degree by degree"]
theorem completedVirtualNormalGysinCap_fundamentalChowClass_excess
    (hreg : IsRegularImmersion i') (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i') r]
    (n : ℤ) (hY : schemeDeltaDimension C (g ≫ sX) ≤ (n : EInt)) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (𝒩.baseChange i i' g' g sq).excessNormalSheaf :=
      (𝒩.baseChange i i' g' g sq).isFiniteLocallyFree_excessNormalSheaf
        (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r)
    (∀ e : ℕ, (completedBivariantSequenceOfInvertible C sZ sX i hi
        (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) ((r + e : ℕ) : ℤ)).cap g n
          (fundamentalChowClass C (g ≫ sX) n) =
        chowPushforwardOfIso C sZ' (pullback.fst i g ≫ sZ) sq.flip.isoPullback.hom
          (isoPullback_hom_comp_structureMorphism C sZ sX sq hi sZ' hi') (n - ((r + e : ℕ) : ℤ))
          (chowGroupDegreeEquiv C sZ' (by push_cast; ring)
            (topChernCap C sZ' (𝒩.baseChange i i' g' g sq).excessNormalSheaf (n - (r : ℤ)) e
              (fundamentalChowClass C sZ' (n - (r : ℤ)))))) ∧
      ∀ p : ℤ, p < r → (completedBivariantSequenceOfInvertible C sZ sX i hi
        (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) p).cap g n
          (fundamentalChowClass C (g ≫ sX) n) = 0 := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hC : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (conormalModule i') :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (𝒩.baseChange i i' g' g sq).excessNormalSheaf :=
    (𝒩.baseChange i i' g' g sq).isFiniteLocallyFree_excessNormalSheaf hC
  have hpiece : ∀ a : _root_.ConnectedComponents Z,
      (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a) : Scheme.{u}) →
      r ≤ componentRank 𝒩.bundle a ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι).obj
            (𝒩.baseChange i i' g' g sq).excessNormalSheaf) (componentRank 𝒩.bundle a - r) := by
    intro a z
    have := isFiniteLocallyFreeOfRank_conormalModule_morphismRestrict i'
      (g ⁻¹ᵁ componentNeighbourhood i a) r
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((𝒩.toComponent i a).baseChange (componentRestriction i a)
          (i' ∣_ (g ⁻¹ᵁ componentNeighbourhood i a)) (pieceProjection sq a)
          (g ∣_ componentNeighbourhood i a) (isPullback_pieceProjection sq a)).bundle
        (componentRank 𝒩.bundle a) :=
      isFiniteLocallyFreeOfRank_modulePullback _ _ _ inferInstance
    exact ⟨VirtualNormalBundle.le_of_isFiniteLocallyFreeOfRank
        ((𝒩.toComponent i a).baseChange (componentRestriction i a)
          (i' ∣_ (g ⁻¹ᵁ componentNeighbourhood i a)) (pieceProjection sq a)
          (g ∣_ componentNeighbourhood i a) (isPullback_pieceProjection sq a))
        (componentRank 𝒩.bundle a) r z,
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
        (pieceExcessNormalSheafIso sq a 𝒩 hC)
        (VirtualNormalBundle.isFiniteLocallyFreeOfRank_excessNormalSheaf _
          (componentRank 𝒩.bundle a) r)⟩
  refine ⟨fun e ↦ eq_of_chowGroupRestrict_piece_eq C sZ sX i hi g i' g' sq sZ' hi' fun a ↦ ?_,
    fun p hp ↦ eq_of_chowGroupRestrict_piece_eq C sZ sX i hi g i' g' sq sZ' hi' fun a ↦ ?_⟩
  · by_cases hE : IsEmpty (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a) : Scheme.{u})
    · have := subsingleton_chowGroup_of_isEmpty C
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ') (n - ((r + e : ℕ) : ℤ))
      exact Subsingleton.elim _ _
    obtain ⟨z⟩ := not_isEmpty_iff.mp hE
    obtain ⟨hrm, hrank⟩ := hpiece a z
    by_cases hme : componentRank 𝒩.bundle a = r + e
    · have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι).obj
            (𝒩.baseChange i i' g' g sq).excessNormalSheaf) e := by
        rw [hme, Nat.add_sub_cancel_left] at hrank
        exact hrank
      rw [chowGroupRestrict_completedVirtualNormalGysinCap_piece C sZ sX i hi 𝒩 g i' g' sq sZ'
        hi' a hreg r e hme n hY, chowGroupRestrict_topChernCap_piece C sZ sX i hi 𝒩 g i' g' sq
        sZ' hi' a hreg r e n hY]
    · have hs : i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a) ≤
          rankLocus (𝒩.baseChange i i' g' g sq).excessNormalSheaf
            (componentRank 𝒩.bundle a - r) := fun x hx ↦
        mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback _
          (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι _ inferInstance ⟨x, hx⟩
      rw [chowGroupRestrict_completedVirtualNormalGysinCap_piece_eq_zero C sZ sX i hi 𝒩 g i' g'
        sq sZ' hi' a _ (by exact_mod_cast hme ∘ Eq.symm) n,
        chowGroupRestrict_topChernCap_piece_of_ne C sZ sX i hi 𝒩 g i' g' sq sZ' hi' a r e
          _ hs (by omega) n]
  · rw [map_zero]
    by_cases hE : IsEmpty (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a) : Scheme.{u})
    · have := subsingleton_chowGroup_of_isEmpty C
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ') (n - p)
      exact Subsingleton.elim _ _
    obtain ⟨z⟩ := not_isEmpty_iff.mp hE
    obtain ⟨hrm, -⟩ := hpiece a z
    exact chowGroupRestrict_completedVirtualNormalGysinCap_piece_eq_zero C sZ sX i hi 𝒩 g i' g'
      sq sZ' hi' a p (by omega) n _

end Main

end Stacks.Chow

end
