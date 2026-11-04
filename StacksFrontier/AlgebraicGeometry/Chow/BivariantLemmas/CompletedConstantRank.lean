module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CommutingAfterBaseChange

/-!
# The completed class of a virtual normal bundle of constant rank

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : Z ⟶ X` be a closed
immersion of schemes locally of finite type over `S` and let `𝒩` be a virtual normal bundle for
`i`. Stacks 0FBK defines `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧`; when `𝒩` has constant rank `r` it is also a
homogeneous class in `A^r(Z ⟶ X)`. This file proves that the two agree: the completed class is the
image of the homogeneous one under `A^r(Z ⟶ X) ⟶ A^*(Z ⟶ X)^∧`.

## Main definitions

* `Stacks.Chow.BivariantClass.toCompleted` — a homogeneous class as a completed class
  (Stacks 0FE0).

## Main results

* `Stacks.Chow.bivariantConnectedComponentRestriction_eq_openImmersionComposite` — the restriction
  of a class to a connected component `Z_a`, through an open `U ⊆ X_b` with `Z ×_X U = Z_a`: it is
  the restriction to `U` (Stacks 0F9Z), read on `Z_a`, composed with `(U ⟶ X_b)^*`.
* `Stacks.Chow.completedVirtualNormalGysinClass_eq_toCompleted` — the completed class at constant
  rank.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section ComponentThroughOpen

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [LocallyOfFiniteType i]
  (hi : i ≫ sX = sZ) [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (a : _root_.ConnectedComponents Z) (U : X.Opens)
  (hU : U ≤ X.connectedComponentOpens (i.continuous.connectedComponentsMap a))
  (iU : (Z.connectedComponentOpens a : Scheme.{u}) ⟶ U) [LocallyOfFiniteType iU]
  (sq : IsPullback iU (Z.connectedComponentOpens a).ι U.ι i) {p : ℤ}

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] [LocallyOfFiniteType i]
  [IsLocallyNoetherian X] [LocallyOfFiniteType iU] in
include sq hi in
/-- The map `Z_a ⟶ U` lies over `S`: its composite with `U ⟶ X ⟶ S` is the structure morphism
`Z_a ⟶ Z ⟶ S`. -/
theorem comp_ι_comp_structureMorphism_of_isPullback :
    iU ≫ (U.ι ≫ sX) = (Z.connectedComponentOpens a).ι ≫ sZ := by
  rw [← Category.assoc, sq.w, Category.assoc, hi]

omit [LocallyOfFiniteType i] [LocallyOfFiniteType iU] in
include sq in
/-- The map `Z_a ⟶ U` followed by the inclusion `U ⟶ X_b` is the restriction of `i` to the
connected component `Z_a`. -/
theorem comp_homOfLE_eq_resConnectedComponent :
    (Iso.refl _).hom ≫ i.resConnectedComponent a = iU ≫ X.homOfLE hU := by
  rw [← cancel_mono (X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι,
    Iso.refl_hom, Category.id_comp, Scheme.Hom.resConnectedComponent_comp_ι, Category.assoc,
    Scheme.homOfLE_ι, sq.w]

/-- **The restriction of a class to a connected component, through an open neighbourhood.** Let
`Z_a` be a connected component of `Z` lying over the connected component `X_b` of `X`, and let
`U ⊆ X_b` be open with `Z ×_X U = Z_a`. The restriction (Stacks 0FDZ) of `c ∈ A^p(Z ⟶ X)` to `Z_a`
is the restriction of `c` to `U` (Stacks 0F9Z), read on `Z_a`, composed (Stacks 0B75) with flat
pullback along the open immersion `U ⟶ X_b` (Stacks 0B78). -/
theorem bivariantConnectedComponentRestriction_eq_openImmersionComposite
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sZ sX i hi p
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) c a =
      bivariantTransport C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens a).ι ≫ sZ)
        ((Z.connectedComponentOpens a).ι ≫ sZ)
        ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX)
        (iU ≫ X.homOfLE hU)
        (comp_comp_structureMorphism_eq
          (comp_ι_comp_structureMorphism_of_isPullback C sZ sX i hi a U iU sq)
          (by rw [← Category.assoc, Scheme.homOfLE_ι]))
        (i.resConnectedComponent a) (i.resConnectedComponent_comp_ι_comp hi a) (Iso.refl _)
        (comp_homOfLE_eq_resConnectedComponent i a U hU iU sq) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (BivariantClass.copy C (gysinSystemOfInvertible C) _ _ rfl _ _ (add_zero p)
          (openImmersionComposite C ((Z.connectedComponentOpens a).ι ≫ sZ) (U.ι ≫ sX)
            ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX) iU
            (X.homOfLE hU) (comp_ι_comp_structureMorphism_of_isPullback C sZ sX i hi a U iU sq)
            (by rw [← Category.assoc, Scheme.homOfLE_ι]) p
            (bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst i U.ι ≫ sZ)
              ((Z.connectedComponentOpens a).ι ≫ sZ) (U.ι ≫ sX) (pullback.snd i U.ι)
              (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi U.ι) iU
              (comp_ι_comp_structureMorphism_of_isPullback C sZ sX i hi a U iU sq)
              sq.flip.isoPullback.symm sq.flip.isoPullback_inv_snd p
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
              (bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi U.ι p
                (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)))) := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {S} s _ k β ↦ ?_
  rw [bivariantConnectedComponentRestriction_cap, bivariantTransport_cap,
    bivariantTransportCap_apply]
  set ιb := (X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι
  set jU := X.homOfLE hU
  set t' := pullback.fst jU s
  have hm : pullback.snd jU s ≫ (s ≫ ιb) = t' ≫ U.ι := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Scheme.homOfLE_ι]
  have sqv := isPullback_baseChangeMapOfEq i (s ≫ ιb) (pullback.snd jU s) (t' ≫ U.ι) hm
  have : IsOpenImmersion (baseChangeMapOfEq i (s ≫ ιb) (pullback.snd jU s) (t' ≫ U.ι) hm) :=
    MorphismProperty.of_isPullback sqv (P := @IsOpenImmersion) inferInstance
  have hmX : pullback.snd jU s ≫ s ≫ ιb ≫ sX = t' ≫ U.ι ≫ sX := (reassoc_of% hm) sX
  have hcap := BivariantClass.cap_chowGroupRestrict C (gysinSystemOfInvertible C) sZ sX i hi p c
    (s ≫ ιb) (pullback.snd jU s) (t' ≫ U.ι) hm _ sqv (baseChangeMapOfEq_fst _ _ _ _ _) k
    (by simp only [Category.assoc]; exact hmX) (by rw [baseChangeMapOfEq_fst_assoc])
    (chowGroupCongr C (Category.assoc s ιb sX).symm k β)
  apply eq_of_heq
  symm
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by simp) _ _
    (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ s k β)).trans ?_
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by simp) _ _
    (openImmersionComposite_cap_heq C _ _ _ _ _ _ _ _ _ s k β)).trans (heq_of_eq ?_)
  rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestriction_cap,
    bivariantRestrictionCap_apply]
  rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply]
  let e := (pullbackLeftPullbackSndIso i U.ι t').symm ≪≫
    transportPullbackIso (pullback.snd i U.ι) iU sq.flip.isoPullback.symm
      sq.flip.isoPullback_inv_snd t' ≪≫ pullbackRightPullbackFstIso jU s iU ≪≫
    transportPullbackIso (iU ≫ jU) (i.resConnectedComponent a) (Iso.refl _)
      (comp_homOfLE_eq_resConnectedComponent i a U hU iU sq) s
  have hMbcm : e.inv ≫ baseChangeMapOfEq i (s ≫ ιb) (pullback.snd jU s) (t' ≫ U.ι) hm =
      opensPullbackComparison i (Z.connectedComponentOpens a) _
        (i.resConnectedComponent a) (Scheme.Hom.resConnectedComponent_comp_ι i a) s := by
    rw [Iso.inv_comp_eq]
    apply pullback.hom_ext
    · simp only [ιb, jU, t', e, Iso.trans_hom, Iso.symm_hom, Category.assoc, baseChangeMapOfEq_fst,
        opensPullbackComparison_fst, transportPullbackIso_hom_fst_assoc, Iso.refl_hom,
        Category.id_comp, pullbackRightPullbackFstIso_hom_fst_assoc,
        IsPullback.isoPullback_inv_fst, pullbackLeftPullbackSndIso_inv_fst]
    · simp only [ιb, jU, t', e, Iso.trans_hom, Iso.symm_hom, Category.assoc, baseChangeMapOfEq_snd,
        opensPullbackComparison_snd, transportPullbackIso_hom_snd,
        pullbackRightPullbackFstIso_hom_snd, transportPullbackIso_hom_snd_assoc,
        pullbackLeftPullbackSndIso_inv_snd_snd_assoc]
  refine (chowPushforwardOfIso_hom_eq_chowGroupRestrict C _ _ e _ _ _).trans ?_
  rw [chowGroupCongr_chowGroupRestrict C _ _ _ _ _ (by simp only [Category.assoc]; exact hmX) _,
    ← chowGroupRestrict_chowGroupCongr C _ _ _ _ _ (by simp only [Category.assoc]; exact hmX)
      (Category.assoc s ιb sX).symm, ← hcap, chowGroupRestrict_comp]
  exact DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _ hMbcm _) _

end ComponentThroughOpen

/-! ### Homogeneous classes as completed classes -/

section Homogeneous

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  {hf : f ≫ sY = sX} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] {n : ℤ}

/-- **A homogeneous class as a completed class** (Stacks 0FE0): `x ∈ A^n(X ⟶ Y)` is the element
of `A^*(X ⟶ Y)^∧` which on each connected component `X_w` is the restriction of `x` to `X_w`
(Stacks 0FDZ), placed in degree `n`. -/
def BivariantClass.toCompleted (x : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf n) :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf :=
  fun w ↦ DirectSum.of _ n (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C)
    sX sY f hf n (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) x w)

/-- The component of `x.toCompleted` at a connected component `X_w` is the restriction of `x` to
`X_w`, placed in degree `n`. -/
theorem BivariantClass.toCompleted_apply
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf n)
    (w : _root_.ConnectedComponents X) :
    x.toCompleted C w = DirectSum.of _ n (bivariantConnectedComponentRestriction C
      (gysinSystemOfInvertible C) sX sY f hf n
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) x w) :=
  rfl

end Homogeneous

/-! ### The completed class of a virtual normal bundle of constant rank -/

section ConstantRank

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  [IsLocallyNoetherian Z] [IsLocallyNoetherian X]

/-- **The completed class at constant rank** (Stacks 0FBK on Stacks 0FE0). If the virtual normal
bundle `𝒩` has constant rank `r`, the completed class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` is the
homogeneous class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)`: on a connected component `Z_a` both are
`c(Z_a ⟶ U_a, 𝒩|_{Z_a}) ∘ (U_a ⟶ X_b)^*`, the restriction of `c(Z ⟶ X, 𝒩)` to `U_a` being the
class of the base-changed bundle (Stacks 0FBK with Stacks 0FBJ). -/
theorem completedVirtualNormalGysinClass_eq_toCompleted (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    completedVirtualNormalGysinClass C sZ sX i hi 𝒩 =
      (virtualNormalBundleClass C sZ sX i hi 𝒩 r).toCompleted C := by
  funext a
  rw [completedVirtualNormalGysinClass_apply, BivariantClass.toCompleted_apply,
    bivariantConnectedComponentRestriction_eq_openImmersionComposite C sZ sX i hi a
      (componentNeighbourhood i a) (componentNeighbourhood_le i a) (componentRestriction i a)
      (isPullback_componentRestriction i a),
    bivariantTransport_bivariantRestriction_virtualNormalGysinClass C sZ sX i hi
      (componentRestriction i a) (Z.connectedComponentOpens a).ι (componentNeighbourhood i a).ι
      (isPullback_componentRestriction i a) 𝒩 r,
    bivariantTransport_refl (componentRestriction_comp_componentInclusion i a)]
  have hr : componentRank 𝒩.bundle a = r := componentRank_eq_of_isFiniteLocallyFreeOfRank _ a r
  subst hr
  rfl

end ConstantRank

end Stacks.Chow

end
