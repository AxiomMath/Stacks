module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LocalizationSequence

/-!
# Restriction of cycles to an open subspace is flat pullback

In Situation 0EDT let `j : U → X` be an open immersion of good algebraic spaces over the base.
An open immersion is étale, hence flat of relative dimension `0`, and the flat pullback of cycles
along it, Stacks 0EP8, is the restriction of cycles `α ↦ α|_U` of Stacks 0EP9: for an integral
closed subspace `Z ⊆ X` the inverse image `j^{-1}(Z) = Z ∩ U` is irreducible when it is nonempty,
so by Stacks 0EPY the cycle `j^*[Z]` is `[W]` for the integral closed subspace `W ⊆ U` whose
closure in `X` is `Z`, and `0` when `Z` does not meet `U`.

Combined with Stacks 0EPA this gives the compatibility of flat pullback with restriction to open
subspaces: if `f : X → Y` is flat of relative dimension `r`, and `j_X : U → X`, `j_Y : V → Y` are
open immersions with `f ∘ j_X = j_Y ∘ g` for a flat `g : U → V` of relative dimension `r`, then
`(f^*β)|_U = g^*(β|_V)`.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponentsCycle_of_isOpenImmersion`:
  along an open immersion `j`, the components of `j^{-1}(Z)` are the integral closed subspaces
  whose closure is `Z`.
* `AlgebraicGeometry.Space.flatPullbackMap_eq_cycleGroupRestrict`: flat pullback along an open
  immersion is restriction of cycles.
* `AlgebraicGeometry.Space.flatPullbackMap_congr`: the flat pullback of cycles depends only on
  the morphism and on the relative dimension, not on how they are presented.
* `AlgebraicGeometry.Space.cycleGroupRestrict_flatPullbackMap`: flat pullback commutes with
  restriction to open subspaces.

## References

* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EP9](https://stacks.math.columbia.edu/tag/0EP9)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Components

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j)

include hj in
/-- **The components of an inverse image along an open immersion.** Let `j : U → X` be an open
immersion, `Z ⊆ X` an integral closed subspace and `W ⊆ U` an integral closed subspace. Then `W`
is an irreducible component of `j^{-1}(Z)` exactly when the closure of its image in `X` is `Z`:
the inverse image of the irreducible set `|Z|` along the open embedding `|j|` is irreducible
when nonempty, so it is its own only component, and it is recovered from its closure in `|X|`. -/
theorem IntegralClosedSubspace.exists_preimageComponent_eq_iff_closureImage_eq
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem U) :
    (∃ C, Z.preimageComponent D.site D.base D.base_mem j hU.1
        (D.isDecentSpace_of_isGood sU hU) hX.1 C = W) ↔
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
        (D.isDecentSpace_of_isGood sX hX) j W = Z := by
  have hemb := isOpenEmbedding_pointsMap_of_isOpenImmersion D hX.1 hj
  have hZirr := isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem Z
  have hZcl := isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1 Z
  have hWcl := isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hU.1 W
  have hWirr := isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem W
  set P := Z.preimagePointSet D.site D.base D.base_mem j with hP
  -- the point set of `W` is recovered from the closure of its image
  have hrec : pointsMap D.site D.base D.base_mem U j ⁻¹'
      closure (pointsMap D.site D.base D.base_mem U j ''
        subspacePointSet D.site D.base D.base_mem U W.subspace) =
      subspacePointSet D.site D.base D.base_mem U W.subspace := by
    rw [← hemb.isInducing.closure_eq_preimage_closure_image, hWcl.closure_eq]
  -- if `P` is irreducible, its only component is everything
  have hcomp : ∀ hPirr : IsIrreducible P, ∀ C : irreducibleComponents P,
      ((C : Set P)) = Set.univ := by
    intro hPirr C
    have : IrreducibleSpace P := Subtype.irreducibleSpace hPirr
    exact Set.eq_univ_of_univ_subset
      (C.2.2 (IrreducibleSpace.isIrreducible_univ P) (Set.subset_univ _))
  constructor
  · rintro ⟨C, rfl⟩
    have hPne : (subspacePointSet D.site D.base D.base_mem X Z.subspace ∩
        Set.range (pointsMap D.site D.base D.base_mem U j)).Nonempty := by
      obtain ⟨c, -⟩ := (C.2.1.nonempty : (C : Set P).Nonempty)
      exact ⟨_, c.2, c.1, rfl⟩
    have hPirr : IsIrreducible P := isIrreducible_preimage_of_isOpenEmbedding hemb hZirr hPne
    apply injective_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
    apply IrreducibleCloseds.ext
    show subspacePointSet D.site D.base D.base_mem X (IntegralClosedSubspace.closureImage
      D.site D.base D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) j _).subspace =
        subspacePointSet D.site D.base D.base_mem X Z.subspace
    rw [IntegralClosedSubspace.subspacePointSet_closureImage,
      IntegralClosedSubspace.subspacePointSet_preimageComponent, hcomp hPirr C, Set.image_univ,
      Subtype.range_coe]
    show closure (pointsMap D.site D.base D.base_mem U j '' (pointsMap D.site D.base D.base_mem
      U j ⁻¹' subspacePointSet D.site D.base D.base_mem X Z.subspace)) = _
    rw [Set.image_preimage_eq_inter_range]
    exact closure_inter_open_eq_of_isIrreducible hZirr hZcl hemb.isOpen_range hPne
  · intro h
    have hPW : P = subspacePointSet D.site D.base D.base_mem U W.subspace := by
      rw [hP]
      show pointsMap D.site D.base D.base_mem U j ⁻¹'
        subspacePointSet D.site D.base D.base_mem X Z.subspace = _
      rw [← h, IntegralClosedSubspace.subspacePointSet_closureImage, hrec]
    have hPirr : IsIrreducible P := hPW ▸ hWirr
    have : IrreducibleSpace P := Subtype.irreducibleSpace hPirr
    have huniv : (Set.univ : Set P) ∈ irreducibleComponents P :=
      ⟨IrreducibleSpace.isIrreducible_univ P, fun _ _ _ => Set.subset_univ _⟩
    refine ⟨⟨Set.univ, huniv⟩, ?_⟩
    apply injective_integralClosedSubspaceSupport D.site D.base D.base_mem hU.1
    apply IrreducibleCloseds.ext
    show subspacePointSet D.site D.base D.base_mem U (Z.preimageComponent D.site D.base
      D.base_mem j hU.1 (D.isDecentSpace_of_isGood sU hU) hX.1 _).subspace =
        subspacePointSet D.site D.base D.base_mem U W.subspace
    rw [IntegralClosedSubspace.subspacePointSet_preimageComponent]
    show Subtype.val '' (Set.univ : Set P) = _
    rw [Set.image_univ, Subtype.range_coe, hPW]

open Classical in
include hj in
/-- Along an open immersion `j : U → X` the formal sum of the components of `j^{-1}(Z)` is the
indicator of the integral closed subspace of `U` whose closure is `Z`. -/
theorem IntegralClosedSubspace.preimageComponentsCycle_of_isOpenImmersion
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem U) :
    Z.preimageComponentsCycle D sU hU sX hX j W =
      if IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
          (D.isDecentSpace_of_isGood sX hX) j W = Z then 1 else 0 := by
  unfold IntegralClosedSubspace.preimageComponentsCycle
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply,
    Z.exists_preimageComponent_eq_iff_closureImage_eq D sX hX sU hU hj W]

/-- **Flat pullback along an open immersion is restriction.** For an open immersion
`j : U → X` of good algebraic spaces over the base, the flat pullback of cycles along `j`, which
is étale and so flat of relative dimension `0`, is the restriction of cycles to `U` of
Stacks 0EP9: their coefficient families agree. -/
theorem flatPullbackMap_eq_cycleGroupRestrict (hjc : j ≫ sX = sU) (k n : ℤ)
    (hkn : k + ((0 : ℕ) : ℤ) = n) (α : CycleGroup D sX k) :
    (flatPullbackMap D sU hU sX hX j hjc 0
        (isFlat_of_isEtale D.site D.base D.base_mem
          (isEtale_of_isOpenImmersion D.site D.base D.base_mem hj))
        (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem j hX.1
          (isEtale_of_isOpenImmersion D.site D.base D.base_mem hj)) k n hkn α).1 =
      (cycleGroupRestrict D sX hX sU hU hj hjc k α).1 := by
  funext W
  rw [flatPullbackMap_apply, cycleGroupRestrict_apply]
  simp only [IntegralClosedSubspace.flatPullbackMult_eq_preimageComponentsCycle D sU hU sX hX
    (isEtale_of_isOpenImmersion D.site D.base D.base_mem hj) hjc,
    IntegralClosedSubspace.preimageComponentsCycle_of_isOpenImmersion D sX hX sU hU hj,
    mul_ite, mul_one, mul_zero]
  rw [finsum_eq_single _ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) j W) fun Z hZ => if_neg (Ne.symm hZ), if_pos rfl]

end Components

section Congr

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

/-- **The flat pullback depends only on the morphism, the relative dimension and the
coefficients.** Two presentations of the same flat morphism with the same relative dimension
give the same coefficient family on two cycles with the same coefficient family, whatever the
degrees in which these are read. -/
theorem flatPullbackMap_coe_congr {f f' : X ⟶ Y} (hff' : f = f') (hbase : f ≫ sY = sX)
    (hbase' : f' ≫ sY = sX) {r r' : ℕ} (hrr' : r = r')
    (hflat : IsFlat D.site D.base D.base_mem f) (hflat' : IsFlat D.site D.base D.base_mem f')
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hr' : HasRelativeDimension r' D.site D.base D.base_mem f') (m n m' n' : ℤ)
    (hmn : m + (r : ℤ) = n) (hmn' : m' + (r' : ℤ) = n') (β : CycleGroup D sY m)
    (β' : CycleGroup D sY m') (hββ' : β.1 = β'.1) :
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn β).1 =
      (flatPullbackMap D sX hX sY hY f' hbase' r' hflat' hr' m' n' hmn' β').1 := by
  subst hff' hrr'
  funext T
  rw [flatPullbackMap_apply, flatPullbackMap_apply, hββ']

end Congr

section Square

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y U V : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (sU : U ⟶ D.space) (hU : D.IsGood sU) (sV : V ⟶ D.space) (hV : D.IsGood sV)

/-- **Flat pullback commutes with restriction to open subspaces.** Let `f : X → Y` and
`g : U → V` be flat of relative dimension `r`, and `j_X : U → X`, `j_Y : V → Y` open immersions,
all over the base, with `f ∘ j_X = j_Y ∘ g`. Then `(f^*β)|_U = g^*(β|_V)` for every cycle `β` on
`Y`: both are the flat pullback along the common composite, by Stacks 0EPA, restriction being
flat pullback along an open immersion. -/
theorem cycleGroupRestrict_flatPullbackMap {f : X ⟶ Y} (hfbase : f ≫ sY = sX) (r : ℕ)
    (hff : IsFlat D.site D.base D.base_mem f)
    (hfr : HasRelativeDimension r D.site D.base D.base_mem f) {g : U ⟶ V}
    (hgbase : g ≫ sV = sU) (hgf : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g) {jX : U ⟶ X}
    (hjX : IsOpenImmersion D.site D.base D.base_mem jX) (hjXc : jX ≫ sX = sU) {jY : V ⟶ Y}
    (hjY : IsOpenImmersion D.site D.base D.base_mem jY) (hjYc : jY ≫ sY = sV)
    (hsq : jX ≫ f = g ≫ jY) (k : ℤ) (β : CycleGroup D sY k) :
    cycleGroupRestrict D sX hX sU hU hjX hjXc (k + (r : ℤ))
        (flatPullbackMap D sX hX sY hY f hfbase r hff hfr k (k + (r : ℤ)) rfl β) =
      flatPullbackMap D sU hU sV hV g hgbase r hgf hgr k (k + (r : ℤ)) rfl
        (cycleGroupRestrict D sY hY sV hV hjY hjYc k β) := by
  have hjXe := isEtale_of_isOpenImmersion D.site D.base D.base_mem hjX
  have hjYe := isEtale_of_isOpenImmersion D.site D.base D.base_mem hjY
  have h₁ := flatPullbackMap_comp D sU hU sX hX sY hY jX f hjXc hfbase 0 r
    (isFlat_of_isEtale D.site D.base D.base_mem hjXe)
    (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem jX hX.1 hjXe) hff hfr
    k (k + (r : ℤ)) (by push_cast; ring)
  have h₂ := flatPullbackMap_comp D sU hU sV hV sY hY g jY hgbase hjYc r 0 hgf hgr
    (isFlat_of_isEtale D.site D.base D.base_mem hjYe)
    (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem jY hY.1 hjYe)
    k (k + (r : ℤ)) (by push_cast; ring)
  have hgj := isFlat_and_hasRelativeDimension_comp D sU hU sV hV sY hY g jY hgbase hjYc r 0
    hgf hgr (isFlat_of_isEtale D.site D.base D.base_mem hjYe)
    (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem jY hY.1 hjYe)
  have e₁ := congrArg (fun φ => (φ β).1) h₁
  have e₂ := congrArg (fun φ => (φ β).1) h₂
  simp only [AddMonoidHom.comp_apply] at e₁ e₂
  apply Subtype.ext
  rw [← flatPullbackMap_eq_cycleGroupRestrict D sX hX sU hU hjX hjXc (k + (r : ℤ))
    (k + (r : ℤ)) (by simp), ← e₁,
    flatPullbackMap_coe_congr D sU hU sY hY hsq _
      (comp_structureMorphism_eq D sU sV sY g jY hgbase hjYc) (show 0 + r = r + 0 by omega) _
      hgj.2.1 _ hgj.2.2
      k (k + (r : ℤ)) k (k + (r : ℤ)) _ (by push_cast; ring) β β rfl, e₂]
  exact flatPullbackMap_coe_congr D sU hU sV hV rfl _ _ rfl _ _ _ _ _ _ _ _ _ _ _ _
    (flatPullbackMap_eq_cycleGroupRestrict D sY hY sV hV hjY hjYc k _ rfl β)

end Square

end AlgebraicGeometry.Space

end
