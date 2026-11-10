module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.Completion
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction on the completed bivariant groups

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` and
`h : Y' ⟶ Y` be morphisms of schemes locally of finite type over `S` and let
`X' = X ×_Y Y' ⟶ Y'` be the base change. The restriction `res : A^p(X ⟶ Y) ⟶ A^p(X' ⟶ Y')` of
Stacks 0F9Z extends, degree by degree, to the completed groups of Stacks 0FE0,

  `res : A^*(X ⟶ Y)^∧ ⟶ A^*(X' ⟶ Y')^∧`,  `(c_p)_p ↦ (res(c_p))_p`.

The point is that the tuple `(res(c_p))_p` is again almost vanishing on every connected component
of `X'`: a connected component `X'_k` lies over a single connected component `X_i` of `X`, and the
restriction of `res(c_p)` to `X'_k` vanishes as soon as the restriction of `c_p` to `X_i` does,
both being restrictions along open immersions of the cap operations of `c_p`
(`Stacks.Chow.bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero`).

## Main definitions

* `Stacks.Chow.completedBivariantRestriction` — the restriction on the completed groups, at an
  arbitrary Gysin system satisfying the compatibilities used by Stacks 0FDZ and 0F9Z.
* `Stacks.Chow.completedBivariantRestrictionOfInvertible` — the same at the Gysin system of the
  first Chern class rule, where nothing is assumed.

## Main results

* `Stacks.Chow.completedBivariantSequence_completedBivariantRestriction` — in degree `p` the
  restriction on the completed groups is the restriction of Stacks 0F9Z.

## References

* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Connected components of a base change -/

section Components

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (h : Y' ⟶ Y)

/-- A connected component `X'_k` of `X' = X ×_Y Y'` lies over a connected component of `X` and
one of `Y'`, and both lie over the same connected component of `Y`. -/
theorem connectedComponentsMap_pullbackSnd_eq (k : ConnectedComponents ↥(pullback f h)) :
    h.continuous.connectedComponentsMap
        ((pullback.snd f h).continuous.connectedComponentsMap k) =
      f.continuous.connectedComponentsMap
        ((pullback.fst f h).continuous.connectedComponentsMap k) := by
  rw [← Scheme.Hom.connectedComponentsMap_comp, ← Scheme.Hom.connectedComponentsMap_comp,
    pullback.condition]

variable [LocallyConnectedSpace Y] [LocallyConnectedSpace Y']

/-- `h` carries the connected component of `Y'` below `X'_k` into the connected component of `Y`
below the image of `X'_k` in `X`. -/
theorem connectedComponentOpens_le_preimage_pullbackSnd (k : ConnectedComponents ↥(pullback f h)) :
    Y'.connectedComponentOpens ((pullback.snd f h).continuous.connectedComponentsMap k) ≤
      h ⁻¹ᵁ Y.connectedComponentOpens
        (f.continuous.connectedComponentsMap
          ((pullback.fst f h).continuous.connectedComponentsMap k)) := by
  have := h.connectedComponentOpens_le_preimage
    ((pullback.snd f h).continuous.connectedComponentsMap k)
  rwa [connectedComponentsMap_pullbackSnd_eq] at this

end Components

/-! ### Vanishing on a component is inherited by the restriction -/

section Vanishing

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
  (h : Y' ⟶ Y) [LocallyOfFiniteType h] (p : ℤ)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Y']
  [IsLocallyNoetherian (pullback f h)]

/-- Pushforward along the inverse of an isomorphism is restriction along the isomorphism. -/
theorem chowPushforwardOfIso_inv_eq_chowGroupRestrict {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : B ≅ A)
    (he : e.inv ≫ sB = sA) (he' : e.hom ≫ sA = sB) (k : ℤ) (x : chowGroup C sA k) :
    chowPushforwardOfIso C sA sB e.inv he k x = chowGroupRestrict C sA sB e.hom he' k x := by
  rw [chowGroupRestrict_of_isIso]
  exact chowPushforwardOfIso_congr_apply C sA sB _ _ (IsIso.Iso.inv_hom e).symm _ _ k x

/-- **Stacks 0FDZ and 0F9Z.** Let `X'_k` be a connected component of `X' = X ×_Y Y'`, lying over
the connected component `X_i` of `X`. If a bivariant class `d ∈ A^p(X ⟶ Y)` restricts to zero on
`X_i`, then its restriction `res(d) ∈ A^p(X' ⟶ Y')` restricts to zero on `X'_k`: on a test scheme
`T` over the component of `Y'` below `X'_k`, the cap operation of the latter is that of `d` at
`T ⟶ Y`, restricted along the open immersion `X'_k ×_{Y'_b} T ⟶ X ×_Y T`, which factors through
the open immersion `X_i ×_{Y_a} T ⟶ X ×_Y T` along which the cap operation of the former is
restricted. -/
theorem bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero
    (hgysO : G.IsNaturalUnderOpenImmersion) (hgys : G.IsNaturalUnderBaseChangeIso)
    (d : BivariantClass C G sX sY f hf p) (k : ConnectedComponents ↥(pullback f h))
    (hd : bivariantConnectedComponentRestriction C G sX sY f hf p hgysO d
      ((pullback.fst f h).continuous.connectedComponentsMap k) = 0) :
    bivariantConnectedComponentRestriction C G (pullback.fst f h ≫ sX) (h ≫ sY)
      (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p hgysO
      (bivariantRestriction C G sX sY f hf h p hgys d) k = 0 := by
  refine BivariantClass.ext C G _ _ _ _ p ?_
  intro T g _ n β
  rw [BivariantClass.zero_cap]
  -- the components involved
  have hle := connectedComponentOpens_le_preimage_pullbackSnd f h k
  have hle' := (pullback.fst f h).connectedComponentOpens_le_preimage k
  -- the test morphism `T ⟶ Y_a`
  obtain ⟨g₁, hm⟩ : ∃ g₁ : T ⟶ (Y.connectedComponentOpens (f.continuous.connectedComponentsMap
      ((pullback.fst f h).continuous.connectedComponentsMap k)) : Scheme.{u}),
      g₁ ≫ (Y.connectedComponentOpens (f.continuous.connectedComponentsMap
        ((pullback.fst f h).continuous.connectedComponentsMap k))).ι =
        (g ≫ (Y'.connectedComponentOpens
          ((pullback.snd f h).continuous.connectedComponentsMap k)).ι) ≫ h :=
    ⟨g ≫ h.resLE _ _ hle, by rw [Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]⟩
  have : LocallyOfFiniteType (g₁ ≫ (Y.connectedComponentOpens (f.continuous.connectedComponentsMap
      ((pullback.fst f h).continuous.connectedComponentsMap k))).ι) := by
    rw [hm]; infer_instance
  have : LocallyOfFiniteType g₁ := locallyOfFiniteType_of_comp g₁
    (Y.connectedComponentOpens (f.continuous.connectedComponentsMap
      ((pullback.fst f h).continuous.connectedComponentsMap k))).ι
  have hmY : g₁ ≫ ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap
      ((pullback.fst f h).continuous.connectedComponentsMap k))).ι ≫ sY) =
      ((g ≫ (Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap k)).ι) ≫ h) ≫ sY := by
    rw [← Category.assoc, hm]
  have hβ : g ≫ ((Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap k)).ι ≫ (h ≫ sY)) =
      g₁ ≫ ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap
        ((pullback.fst f h).continuous.connectedComponentsMap k))).ι ≫ sY) := by
    rw [hmY]; simp only [Category.assoc]
  -- the hypothesis, read at the test morphism `g₁`
  have h0 := congrArg (fun e ↦ e.cap g₁ n (chowGroupCongr C hβ n β)) hd
  simp only [BivariantClass.zero_cap] at h0
  change bivariantPieceRestrictionCap C G sX sY f hf p X.connectedComponentOpens
    Y.connectedComponentOpens f.continuous.connectedComponentsMap
    f.connectedComponentOpens_le_preimage ((pullback.fst f h).continuous.connectedComponentsMap k)
    d g₁ n (chowGroupCongr C hβ n β) = 0 at h0
  rw [bivariantPieceRestrictionCap_eq C G sX sY f hf p X.connectedComponentOpens
    Y.connectedComponentOpens f.continuous.connectedComponentsMap
    f.connectedComponentOpens_le_preimage ((pullback.fst f h).continuous.connectedComponentsMap k)
    d g₁ _ hm hmY _ (pieceComparisonCongr_fst _ _ _ _ _ _ _ _ _)
    (pieceComparisonCongr_snd _ _ _ _ _ _ _ _ _) n
    (pieceComparisonCongr_comp_structureMorphism _ _ _ _ _ _ _ _ hm sX),
    chowGroupCongr_chowGroupCongr] at h0
  -- the goal, unfolded
  change bivariantPieceRestrictionCap C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
    (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p
    (pullback f h).connectedComponentOpens Y'.connectedComponentOpens
    (pullback.snd f h).continuous.connectedComponentsMap
    (pullback.snd f h).connectedComponentOpens_le_preimage k
    (bivariantRestriction C G sX sY f hf h p hgys d) g n β = 0
  rw [bivariantPieceRestrictionCap_apply, bivariantRestriction_cap, bivariantRestrictionCap_apply,
    chowGroupCongr_chowGroupCongr,
    chowPushforwardOfIso_inv_eq_chowGroupRestrict C _ _ (pullbackLeftPullbackSndIso f h _) _
      (by simp)]
  -- the inclusion `X'_k ×_{Y'_b} T ⟶ X_i ×_{Y_a} T`
  have hpm' := pieceMap_comp_ι (pullback.snd f h) (pullback f h).connectedComponentOpens
    Y'.connectedComponentOpens (pullback.snd f h).continuous.connectedComponentsMap
    (pullback.snd f h).connectedComponentOpens_le_preimage k
  have hpm := pieceMap_comp_ι f X.connectedComponentOpens Y.connectedComponentOpens
    f.continuous.connectedComponentsMap f.connectedComponentOpens_le_preimage
    ((pullback.fst f h).continuous.connectedComponentsMap k)
  obtain ⟨r, hr₁, hr₂⟩ : ∃ r : pullback (pieceMap (pullback.snd f h)
        (pullback f h).connectedComponentOpens Y'.connectedComponentOpens
        (pullback.snd f h).continuous.connectedComponentsMap
        (pullback.snd f h).connectedComponentOpens_le_preimage k) g ⟶
      pullback (pieceMap f X.connectedComponentOpens Y.connectedComponentOpens
        f.continuous.connectedComponentsMap f.connectedComponentOpens_le_preimage
        ((pullback.fst f h).continuous.connectedComponentsMap k)) g₁,
      r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (pullback.fst f h).resLE _ _ hle' ∧
      r ≫ pullback.snd _ _ = pullback.snd _ _ := by
    refine ⟨pullback.lift (pullback.fst _ _ ≫ (pullback.fst f h).resLE _ _ hle')
      (pullback.snd _ _) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [← cancel_mono (Y.connectedComponentOpens _).ι]
    simp only [Category.assoc]
    rw [hm, hpm, Scheme.Hom.resLE_comp_ι_assoc, pullback.condition]
    simp only [Category.assoc]
    rw [← reassoc_of% hpm', pullback.condition_assoc]
  have hr : r ≫ pieceComparisonCongr f X.connectedComponentOpens Y.connectedComponentOpens
        f.continuous.connectedComponentsMap f.connectedComponentOpens_le_preimage
        ((pullback.fst f h).continuous.connectedComponentsMap k) g₁ _ hm =
      pieceComparison (pullback.snd f h) (pullback f h).connectedComponentOpens
        Y'.connectedComponentOpens (pullback.snd f h).continuous.connectedComponentsMap
        (pullback.snd f h).connectedComponentOpens_le_preimage k g ≫
        (pullbackLeftPullbackSndIso f h _).hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pieceComparisonCongr_fst, reassoc_of% hr₁, Category.assoc,
        pullbackLeftPullbackSndIso_hom_fst, opensPullbackComparison_fst_assoc,
        Scheme.Hom.resLE_comp_ι]
    · rw [Category.assoc, pieceComparisonCongr_snd, hr₂, Category.assoc,
        pullbackLeftPullbackSndIso_hom_snd, opensPullbackComparison_snd]
  have : IsOpenImmersion (r ≫ pieceComparisonCongr f X.connectedComponentOpens
      Y.connectedComponentOpens f.continuous.connectedComponentsMap
      f.connectedComponentOpens_le_preimage
      ((pullback.fst f h).continuous.connectedComponentsMap k) g₁ _ hm) := by
    rw [hr]; infer_instance
  have : IsOpenImmersion r := IsOpenImmersion.of_comp r (pieceComparisonCongr f
    X.connectedComponentOpens Y.connectedComponentOpens f.continuous.connectedComponentsMap
    f.connectedComponentOpens_le_preimage
    ((pullback.fst f h).continuous.connectedComponentsMap k) g₁ _ hm)
  have hrs : r ≫ (pullback.fst _ _ ≫ ((X.connectedComponentOpens
      ((pullback.fst f h).continuous.connectedComponentsMap k)).ι ≫ sX)) =
      pullback.fst _ _ ≫ (((pullback f h).connectedComponentOpens k).ι ≫
        (pullback.fst f h ≫ sX)) := by
    rw [reassoc_of% hr₁, Scheme.Hom.resLE_comp_ι_assoc]
  rw [chowGroupRestrict_comp, chowGroupRestrict_congr C _ _ _ _ _ _ hr.symm (by
      rw [Category.assoc, ← hrs,
        ← pieceComparisonCongr_comp_structureMorphism _ _ _ _ _ _ _ _ hm sX]),
    ← chowGroupRestrict_comp C _ _ _
      (pieceComparisonCongr_comp_structureMorphism _ _ _ _ _ _ _ _ hm sX) _ _ r hrs, h0, map_zero]


end Vanishing

/-! ### The restriction on the completed groups -/

section Completed

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
  (h : Y' ⟶ Y) [LocallyOfFiniteType h]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Y']
  [IsLocallyNoetherian (pullback f h)]
  (hgysO : G.IsNaturalUnderOpenImmersion) (hgysR : G.IsNaturalUnderOpensRestriction)
  (hgysC : G.IsNaturalUnderPullbackComp) (hgys : G.IsNaturalUnderBaseChangeIso)

/-- Degreewise restriction carries almost-vanishing tuples to almost-vanishing tuples: the
support of the restriction to a connected component `X'_k` of `X'` is contained in the support of
the restriction to the connected component of `X` below it. -/
theorem bivariantRestriction_mem_completedBivariantSubgroup
    (c : ∀ p : ℤ, BivariantClass C G sX sY f hf p)
    (hc : c ∈ completedBivariantSubgroup C G sX sY f hf hgysO) :
    (fun p ↦ bivariantRestriction C G sX sY f hf h p hgys (c p)) ∈
      completedBivariantSubgroup C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) hgysO := fun k ↦
  (hc ((pullback.fst f h).continuous.connectedComponentsMap k)).subset fun p hp ↦ by
    by_contra hcon
    exact hp (bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero C G sX sY f hf
      h p hgysO hgys (c p) k (not_not.1 hcon))

/-- **The restriction `res : A^*(X ⟶ Y)^∧ ⟶ A^*(X' ⟶ Y')^∧` on the completed groups** of
Stacks 0FE0, for `X' = X ×_Y Y'`: the class whose degree `p` part is the restriction
`res(c_p) ∈ A^p(X' ⟶ Y')` of Stacks 0F9Z of the degree `p` part of `c`. -/
def completedBivariantRestriction :
    completedBivariantGroup C G sX sY f hf →+
      completedBivariantGroup C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) where
  toFun c := (completedBivariantGroupEquiv C G (pullback.fst f h ≫ sX) (h ≫ sY)
      (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) hgysO hgysR
      hgysC).symm
    ⟨fun p ↦ bivariantRestriction C G sX sY f hf h p hgys
        (completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC c p),
      bivariantRestriction_mem_completedBivariantSubgroup C G sX sY f hf h hgysO hgys _
        (completedBivariantSequence_mem C G sX sY f hf hgysO hgysR hgysC c)⟩
  map_zero' := by
    rw [AddEquiv.symm_apply_eq]
    refine Subtype.ext (funext fun p ↦ ?_)
    simp only [map_zero, Pi.zero_apply, bivariantRestriction_zero, ZeroMemClass.coe_zero]
  map_add' c d := by
    rw [← map_add, AddEquiv.symm_apply_eq, AddEquiv.apply_symm_apply]
    refine Subtype.ext (funext fun p ↦ ?_)
    simp only [map_add, Pi.add_apply, bivariantRestriction_add, AddMemClass.coe_add]

/-- **In degree `p` the restriction on the completed groups is the restriction of Stacks 0F9Z**:
`res(c)_p = res(c_p)`. -/
theorem completedBivariantSequence_completedBivariantRestriction
    (c : completedBivariantGroup C G sX sY f hf) (p : ℤ) :
    completedBivariantSequence C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) hgysO hgysR hgysC
        (completedBivariantRestriction C G sX sY f hf h hgysO hgysR hgysC hgys c) p =
      bivariantRestriction C G sX sY f hf h p hgys
        (completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC c p) :=
  congrFun (congrArg Subtype.val ((completedBivariantGroupEquiv C G (pullback.fst f h ≫ sX)
    (h ≫ sY) (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) hgysO
    hgysR hgysC).apply_symm_apply _)) p

end Completed

/-! ### The restriction on the completed groups with nothing assumed -/

section Invertible

variable (C : ChowSituation.{u}) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
  (h : Y' ⟶ Y) [LocallyOfFiniteType h]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Y']
  [IsLocallyNoetherian (pullback f h)]

/-- **The restriction `res : A^*(X ⟶ Y)^∧ ⟶ A^*(X' ⟶ Y')^∧` on the completed groups** of
Stacks 0FE0, `(c_p)_p ↦ (res(c_p))_p` with `res` the restriction of Stacks 0F9Z, at the Gysin
system of the first Chern class rule, where every compatibility used is a theorem. -/
def completedBivariantRestrictionOfInvertible :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf →+
      completedBivariantGroup C (gysinSystemOfInvertible C) (pullback.fst f h ≫ sX) (h ≫ sY)
        (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) :=
  completedBivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf h
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)

/-- In degree `p` the restriction on the completed groups is the restriction of Stacks 0F9Z:
`res(c)_p = res(c_p)`. -/
theorem completedBivariantSequenceOfInvertible_completedBivariantRestrictionOfInvertible
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) (p : ℤ) :
    completedBivariantSequenceOfInvertible C (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h)
        (completedBivariantRestrictionOfInvertible C sX sY f hf h c) p =
      bivariantRestrictionOfInvertible C sX sY f hf h p
        (completedBivariantSequenceOfInvertible C sX sY f hf c p) :=
  completedBivariantSequence_completedBivariantRestriction C (gysinSystemOfInvertible C) sX sY f
    hf h _ _ _ _ c p

/-- An element of the completed group of `X' ⟶ Y'` is the restriction of `c` as soon as its
degree `p` part is `res(c_p)` for every `p`. -/
theorem eq_completedBivariantRestrictionOfInvertible
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (d : completedBivariantGroup C (gysinSystemOfInvertible C) (pullback.fst f h ≫ sX) (h ≫ sY)
      (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h))
    (hd : ∀ p : ℤ, completedBivariantSequenceOfInvertible C (pullback.fst f h ≫ sX) (h ≫ sY)
        (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) d p =
      bivariantRestrictionOfInvertible C sX sY f hf h p
        (completedBivariantSequenceOfInvertible C sX sY f hf c p)) :
    d = completedBivariantRestrictionOfInvertible C sX sY f hf h c :=
  completedBivariantSequence_injective C (gysinSystemOfInvertible C) _ _ _ _ _ _ _
    (funext fun p ↦ (hd p).trans
      (completedBivariantSequenceOfInvertible_completedBivariantRestrictionOfInvertible C sX sY f
        hf h c p).symm)

end Invertible

end Stacks.Chow

end
