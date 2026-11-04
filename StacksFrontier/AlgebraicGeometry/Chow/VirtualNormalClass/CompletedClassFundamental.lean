module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.RegularFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Statement
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceShrinkTarget

/-!
# The entries of `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` on fundamental classes

Let `i : Z ⟶ X` be a regular closed immersion of schemes locally of finite type over the base and
`𝒩` a virtual normal bundle for `i` whose structural map `𝒩^∨ ⟶ 𝒞_{Z/X}` is an isomorphism (for
instance the normal sheaf of `i`). The completed class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of Stacks 0FBK
has, on a connected component `Z_k` of `Z` lying in the connected component `X_{a(k)}` of `X`, an
entry in `A^*(Z_k ⟶ X_{a(k)})`. This file computes that entry on fundamental classes: in the degree
`r_k` of the rank of `𝒩` on `Z_k` it caps `[X_{a(k)}]_n` to `[Z_k]_{n - r_k}`.

The entry is the restriction of the degree-`r_k` class `c_{r_k}` to `Z_k ⟶ X_{a(k)}`, and by
Stacks 0FDZ (`Stacks.Chow.chowGroupRestrict_bivariantPieceRestrictionCap_shrink`) it agrees with
the restriction to `Z_k ⟶ W_k` for the open `W_k ⊆ X_{a(k)}` cutting out `Z_k`, which is the class
`c(Z_k ⟶ W_k, 𝒩|_{Z_k})` of the construction. The latter is computed by the case `Y = X` of
Stacks 0FBM (`virtualNormalClass_cap_fundamentalChowClass_of_isIso_surjection_of_isIso`): the
normal sheaf of `Z_k ⟶ W_k` is again an isomorphism onto the conormal sheaf, by flat base change
of conormal sheaves (Stacks 0473).

## Main results

* `Stacks.Chow.VirtualNormalBundle.isIso_restrictComponent_surjection`
* `Stacks.Chow.VirtualNormalBundle.completedClass_rank_cap_fundamentalChowClass`

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow.VirtualNormalBundle

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] [LocallyConnectedSpace Z]
  [LocallyConnectedSpace X] (𝒩 : VirtualNormalBundle i)

/-- The restriction of a virtual normal bundle whose structural map is an isomorphism to a
connected component again has an isomorphism as structural map: the conormal sheaf commutes with
the flat base change along the open `W_k ⊆ X` (Stacks 0473). -/
theorem isIso_restrictComponent_surjection [IsIso 𝒩.surjection]
    (k : _root_.ConnectedComponents Z) : IsIso (𝒩.restrictComponent k).surjection := by
  have Φ := Comparison.ofBaseChange (isPullback_componentPiece i k) 𝒩
  have hc := Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat (componentPiece i k) i
    (Z.connectedComponentOpens k).ι (componentAmbient i k).ι (isPullback_componentPiece i k)
  have : (𝒩.restrictComponent k).surjection = inv Φ.map ≫
      ((Scheme.Modules.pullback (Z.connectedComponentOpens k).ι).map 𝒩.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap (componentPiece i k) i
          (Z.connectedComponentOpens k).ι (componentAmbient i k).ι
          (Stacks.Immersion.toShHom_square (isPullback_componentPiece i k).w)) := by
    rw [← Φ.comm]
    exact (IsIso.inv_hom_id_assoc Φ.map _).symm
  rw [this]
  exact Iso.isIso_hom ((asIso Φ.map).symm ≪≫
    (Scheme.Modules.pullback (Z.connectedComponentOpens k).ι).mapIso (asIso 𝒩.surjection) ≪≫
    @asIso _ _ _ _ (Stacks.Immersion.immersionConormalSheafMap (componentPiece i k) i
      (Z.connectedComponentOpens k).ι (componentAmbient i k).ι
      (Stacks.Immersion.toShHom_square (isPullback_componentPiece i k).w)) hc)

/-- The immersion `Z_k ⟶ W_k` of a connected component of a regularly embedded closed subscheme is
regular, as a flat base change of `i` (Stacks 067P). -/
theorem isRegularImmersion_componentPiece (hi : IsRegularImmersion i)
    (k : _root_.ConnectedComponents Z) : IsRegularImmersion (componentPiece i k) :=
  Stacks.AlgebraicGeometry.isRegularImmersion_of_isPullback_of_flat
    (isPullback_componentPiece i k) hi

end Stacks.Chow.VirtualNormalBundle

namespace Stacks.Chow

/-- An open subscheme has δ-dimension at most that of the ambient scheme. -/
theorem schemeDeltaDimension_comp_isOpenImmersion_le (C : ChowSituation.{u}) {X U : Scheme.{u}}
    (s : X ⟶ C.S) [LocallyOfFiniteType s] (j : U ⟶ X) [IsOpenImmersion j] {n : ℤ}
    (h : schemeDeltaDimension C s ≤ (n : EInt)) : schemeDeltaDimension C (j ≫ s) ≤ (n : EInt) := by
  have hpt : ∀ z : U, relativeDimension C.dimensionFunction (j ≫ s) z ≤ n := fun z => by
    rw [relativeDimension_comp_isOpenImmersion]
    exact relativeDimension_le_of_schemeDeltaDimension_le' C s h _
  exact (schemeDeltaDimension_congr C (Category.id_comp _)).symm.trans_le
    (schemeDeltaDimension_le_of_forall_point C (j ≫ s) (𝟙 U) (k := n) fun z => by
      simpa using hpt z)

end Stacks.Chow

namespace Stacks.Chow.VirtualNormalBundle

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (𝒩 : VirtualNormalBundle i)
  [IsIso 𝒩.surjection] (hi : IsRegularImmersion i) (C : ChowSituation.{u}) (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)

include hi in
/-- **The entry of `c(Z ⟶ X, 𝒩)` on a connected component, on a fundamental class.** For a
connected component `Z_k` of `Z`, lying in the connected component `A = X_{a(k)}` of `X`, with `𝒩`
of rank `r_k` on `Z_k`: if `dim_δ(A) ≤ n` and `dim_δ(Z_k) ≤ n - r_k`, the degree-`r_k` entry of
`c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` caps `[A]_n` to `[Z_k]_{n - r_k}` (read on `Z_k ×_A A`). -/
theorem completedClass_rank_cap_fundamentalChowClass (k : _root_.ConnectedComponents Z) (n : ℤ)
    (hA : haveI := LocallyOfFiniteType.isLocallyNoetherian sX
      schemeDeltaDimension C
        ((X.connectedComponentOpens (i.continuous.connectedComponentsMap k)).ι ≫ sX) ≤
          (n : EInt))
    (hZk : haveI := LocallyOfFiniteType.isLocallyNoetherian sZ
      schemeDeltaDimension C ((Z.connectedComponentOpens k).ι ≫ sZ) ≤
        ((n - 𝒩.componentRank k : ℤ) : EInt)) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    (𝒩.completedClass C sX sZ hZ k (𝒩.componentRank k)).cap (𝟙 _) n
        (fundamentalChowClass C
          (𝟙 _ ≫ ((X.connectedComponentOpens (i.continuous.connectedComponentsMap k)).ι ≫ sX)) n) =
      fundamentalChowClass C (pullback.fst (i.resConnectedComponent k) (𝟙 _) ≫
        ((Z.connectedComponentOpens k).ι ≫ sZ)) (n - 𝒩.componentRank k) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have hentry : 𝒩.completedClass C sX sZ hZ k (𝒩.componentRank k) =
      bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sZ sX i hZ
        (𝒩.componentRank k) (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (𝒩.degreeClass C sX sZ hZ (𝒩.componentRank k)) k := by
    rw [← completedBivariantSequenceOfInvertible_completedClass]
    exact (restriction_completedBivariantSequence C _ sZ sX i hZ _ _ _ _ _ k).symm
  rw [hentry]
  have h1 := chowGroupRestrict_bivariantPieceRestrictionCap_shrink C (gysinSystemOfInvertible C)
    sZ sX i hZ (𝒩.componentRank k) Z.connectedComponentOpens X.connectedComponentOpens
    i.continuous.connectedComponentsMap i.connectedComponentOpens_le_preimage
    (componentAmbient i) id (le_preimage_componentAmbient i) k (𝟙 _)
    (𝒩.degreeClass C sX sZ hZ (𝒩.componentRank k)) n
    (fundamentalChowClass C
      (𝟙 _ ≫ ((X.connectedComponentOpens (i.continuous.connectedComponentsMap k)).ι ≫ sX)) n)
  rw [chowGroupRestrict_fundamentalChowClass C _ _ _ _ n
      ((schemeDeltaDimension_congr C (Category.id_comp _)).trans_le hA),
    chowGroupCongr_fundamentalChowClass, ← 𝒩.componentFamily_cap, 𝒩.componentFamily_rank] at h1
  have := 𝒩.isIso_restrictComponent_surjection k
  have : IsLocallyNoetherian (Z.connectedComponentOpens k : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian ((Z.connectedComponentOpens k).ι ≫ sZ)
  have hst : IsIso (shrinkTest X.connectedComponentOpens i.continuous.connectedComponentsMap
      (componentAmbient i) id k (𝟙 _)) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨by unfold shrinkTest; infer_instance, ⟨fun w => ?_⟩⟩
    let a : (X.connectedComponentOpens (i.continuous.connectedComponentsMap k) : Scheme.{u}) :=
      ⟨(componentAmbient i k).ι w, componentAmbient_le i k w.2⟩
    have hmem : a ∈ shrinkOpens X.connectedComponentOpens i.continuous.connectedComponentsMap
        (componentAmbient i) id k (𝟙 _) := w.2
    refine ⟨⟨a, hmem⟩, ?_⟩
    apply (componentAmbient i (id k)).ι.isOpenEmbedding.injective
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun φ => φ.base ⟨a, hmem⟩)
      (shrinkTest_comp_ι X.connectedComponentOpens i.continuous.connectedComponentsMap
        (componentAmbient i) id k (𝟙 _)))
  have hW : schemeDeltaDimension C ((componentAmbient i k).ι ≫ sX) ≤ (n : EInt) :=
    (schemeDeltaDimension_congr C (by rw [← Category.assoc, Scheme.homOfLE_ι])).trans_le
      (Stacks.Chow.schemeDeltaDimension_comp_isOpenImmersion_le C
        ((X.connectedComponentOpens (i.continuous.connectedComponentsMap k)).ι ≫ sX)
        (X.homOfLE (componentAmbient_le i k)) hA)
  replace h1 := h1.trans (virtualNormalClass_cap_fundamentalChowClass_of_isIso_surjection_of_isIso
    (𝒩.restrictComponent k) (isQuasiRegularImmersion_of_isH1RegularImmersion _
      (isH1RegularImmersion_of_isKoszulRegularImmersion _
        (isKoszulRegularImmersion_of_isRegularImmersion _
          (isRegularImmersion_componentPiece hi k))))
    C ((componentAmbient i k).ι ≫ sX)
    ((Z.connectedComponentOpens k).ι ≫ sZ)
    (baseChange_structure (isPullback_componentPiece i k) C sX sZ hZ) (𝒩.componentRank k)
    (shrinkTest X.connectedComponentOpens i.continuous.connectedComponentsMap
      (componentAmbient i) id k (𝟙 _)) n hW hZk)
  have hdimT : schemeDeltaDimension C (pullback.fst (pieceMap i Z.connectedComponentOpens
      X.connectedComponentOpens i.continuous.connectedComponentsMap
      i.connectedComponentOpens_le_preimage k) (𝟙 _) ≫ ((Z.connectedComponentOpens k).ι ≫ sZ)) ≤
      ((n - 𝒩.componentRank k : ℤ) : EInt) :=
    (schemeDeltaDimension_comp_iso C (asIso (pullback.fst _ (𝟙 _))) _).trans_le hZk
  have hF := chowGroupRestrict_fundamentalChowClass C _ _ (shrinkComparison i
    Z.connectedComponentOpens X.connectedComponentOpens i.continuous.connectedComponentsMap
    i.connectedComponentOpens_le_preimage (componentAmbient i) id (le_preimage_componentAmbient i)
    k (𝟙 _)) (shrinkComparison_comp_structure C sZ i Z.connectedComponentOpens
    X.connectedComponentOpens i.continuous.connectedComponentsMap
    i.connectedComponentOpens_le_preimage (componentAmbient i) id (le_preimage_componentAmbient i)
    k (𝟙 _)) _ hdimT
  rw [chowGroupRestrict_of_isIso] at h1 hF
  have := isIso_shrinkComparison i Z.connectedComponentOpens X.connectedComponentOpens
    i.continuous.connectedComponentsMap i.connectedComponentOpens_le_preimage
    (componentAmbient i) id (le_preimage_componentAmbient i) k (𝟙 _)
  exact (chowPushforwardOfIso_injective C (pullback.fst (pieceMap i Z.connectedComponentOpens
      X.connectedComponentOpens i.continuous.connectedComponentsMap
      i.connectedComponentOpens_le_preimage k) (𝟙 _) ≫ ((Z.connectedComponentOpens k).ι ≫ sZ))
      _ (inv _) _ _) (h1.trans hF.symm)

end Stacks.Chow.VirtualNormalBundle

end
