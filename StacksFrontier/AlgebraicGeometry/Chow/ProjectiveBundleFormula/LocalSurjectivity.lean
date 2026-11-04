module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Compat
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerBaseChange

/-!
# Surjectivity of the projective space bundle map, locally on the base

Let `π : P ⟶ X` be a projective tower of fibre dimension `n` locally on `X`
(`Stacks.Chow.IsLocallyProjectiveTower`) with twist `L`, over a base situation of chapter 42.
This file proves that the map of [Stacks, Tag 02TX]

  `⨁_{i = 0}^{n} A_{k + i}(X) ⟶ A_{k + n}(P),  (α_i) ↦ ∑_i c₁(L)^i ∩ π^* α_i`

is surjective for every `X` locally of finite type over the base and every `k`, granted
[Stacks, Tag 02TT]. Over a base on which `π` is a projective tower this is
`Stacks.Chow.IsProjectiveTower.bundleMap_surjective`; the content here is the passage from there
to an arbitrary base, which is the first half of the surjectivity argument of the source.

The source reduces to an irreducible base and then inducts on its delta-dimension, replacing the
base by a nonempty open subscheme by means of the localization sequence [Stacks, Tag 02RX]. The
proof below runs the same induction without passing to irreducible components, and keeps the
degree `k` fixed throughout:

* a class on `P` is the pushforward of a class on the inverse image of a closed subscheme `T` of
  `X` all of whose points have delta-dimension at most `k + n`, namely the image of the support
  of a representing cycle, so one may assume the delta-dimension of `X` bounded;
* if every point of `X` has delta-dimension less than `k + m`, then the points of
  delta-dimension `k + m - 1` are generic points of irreducible components, and each has an open
  neighbourhood inside its own closure over which `π` is a projective tower; these
  neighbourhoods are pairwise disjoint, so the Chow groups of their union are the product of
  theirs, and the complement of their union has smaller delta-dimension.

## Main results

* `Stacks.Chow.IsLocallyProjectiveTower.isProper` — a locally projective tower is proper.
* `Stacks.Chow.IsProjectiveTower.restrict_of_le` — a tower over an open restricts to a tower over
  any smaller open.
* `Stacks.Chow.bundleMap_surjective_of_pieces` — the localization step: surjectivity over each
  member of a pairwise disjoint family of opens and over the complement of its union gives
  surjectivity over `X`.
* `Stacks.Chow.bundleMap_surjective_of_relativeDimension_lt` — surjectivity over a base all of
  whose points have delta-dimension less than `k + m`, by induction on `m`.
* `Stacks.Chow.IsLocallyProjectiveTower.bundleMap_surjective` — surjectivity of the map of
  Stacks 02TX for a locally projective tower over an arbitrary base.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The localization step -/

section Pieces

variable (C : ChowSituation.{u}) {P X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n) (L : P.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]

/-- The inverse images under `π` of a pairwise disjoint family of opens of `Z` present the inverse
image of their union as a decomposition into open and closed subschemes. -/
private theorem isClopenDecomposition_homOfLE_preimage_iSup {P Z : Scheme.{u}} (π : P ⟶ Z)
    {I : Type u} (V : I → Z.Opens) (hdisj : Pairwise fun i j ↦ Disjoint (V i) (V j)) :
    IsClopenDecomposition fun i ↦
      (P.homOfLE (Scheme.Hom.preimage_mono π (le_iSup V i))).opensRange := by
  refine isClopenDecomposition_of_isOpenImmersion_cover _ (fun x ↦ ?_) fun i l hil ↦ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show π.base x.1 ∈ ⨆ i, V i from x.2)
    exact ⟨i, ⟨⟨x.1, hi⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩⟩
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨⟨a, ha⟩, rfl⟩ ⟨⟨b, hb⟩, h⟩
    rw [Scheme.homOfLE_apply', Scheme.homOfLE_apply'] at h
    obtain rfl : b = a := congrArg Subtype.val h
    exact Set.disjoint_left.1 (Opens.coe_disjoint.2 (hdisj hil)) ha hb

/-- A pairwise disjoint family of opens presents a decomposition of their union into open and
closed subschemes, by the inclusions of its members. -/
theorem isClopenDecomposition_homOfLE_iSup {Z : Scheme.{u}} {I : Type u} (V : I → Z.Opens)
    (hdisj : Pairwise fun i j ↦ Disjoint (V i) (V j)) :
    IsClopenDecomposition fun i ↦ (Z.homOfLE (le_iSup V i)).opensRange := by
  exact isClopenDecomposition_homOfLE_preimage_iSup (𝟙 Z) V hdisj

/-- Restricting a class to an open and then to a smaller open is restricting to the smaller
open. -/
private theorem chowGroupRestrict_homOfLE_opensRestrict (C : ChowSituation.{u}) {Z : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] {W W' : Z.Opens} (h : W ≤ W') (k : ℤ)
    (b : chowGroup C sZ k) :
    chowGroupRestrict C (W'.ι ≫ sZ) (W.ι ≫ sZ) (Z.homOfLE h)
      (by rw [← Category.assoc, Scheme.homOfLE_ι]) k
      (chowGroupOpensRestrictOfIsOpenImmersion C sZ W' k b) =
    chowGroupRestrict C sZ (W.ι ≫ sZ) W.ι rfl k b := by
  rw [← chowGroupRestrict_opensι, chowGroupRestrict_comp]
  exact congrFun (congrArg DFunLike.coe (chowGroupRestrict_congr C sZ _ _ _ _ W.ι
    (Scheme.homOfLE_ι _ _) rfl)) b

/-- If the support of a closed subscheme `Y` of `X` is the complement of an open `U`, then the
inverse image of `Y` in `P` has the complement of the inverse image of `U` as underlying set. -/
private theorem range_comap_subschemeι_eq_compl {P X : Scheme.{u}} (π : P ⟶ X)
    (Y : X.IdealSheafData) (U : X.Opens) (hY : (Y.support : Set X) = (U : Set X)ᶜ) :
    Set.range (Y.comap π).subschemeι.base = (Set.range (π ⁻¹ᵁ U).ι.base)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
    Scheme.Opens.range_ι]
  ext x
  simp only [Closeds.coe_preimage, Set.mem_preimage, SetLike.mem_coe, Set.mem_compl_iff,
    Scheme.Hom.mem_preimage, hY]

/-- Every closed subset of a scheme is the support of an ideal sheaf. -/
private theorem exists_idealSheafData_support_eq {X : Scheme.{u}} {T : Set X} (hT : IsClosed T) :
    ∃ Y : X.IdealSheafData, (Y.support : Set X) = T :=
  ⟨.vanishingIdeal ⟨T, hT⟩, by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl⟩

/-- A point of a closed subscheme lies over a point of the support of its ideal sheaf. -/
private theorem subschemeι_base_mem_support {X : Scheme.{u}} (Y : X.IdealSheafData)
    (y : Y.subscheme) : Y.subschemeι.base y ∈ (Y.support : Set X) := by
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨y, rfl⟩

/-- **The localization step of Stacks 02TX.** Let `V_i` be a pairwise disjoint family of opens of
`X` and `Y` a closed subscheme whose support is the complement of their union. If the map of
Stacks 02TX is surjective in degree `k` over every `V_i` and over `Y`, it is surjective in degree
`k` over `X`.

A class `γ` on `P` restricts over each `V_i` to the image of a family `β^i`. The Chow groups of
`⋃ V_i` are the product of those of the `V_i`, so the `β^i` glue to a family over `⋃ V_i`, which
lifts to a family `β` over `X` (Stacks 02RX). The difference `γ - ∑ c₁(L)^j ∩ π^*β_j` then
restricts to zero over every `V_i`, hence over their union, so it is pushed forward from the
inverse image of `Y` (Stacks 02RX again); there it is in the image by hypothesis, and the map of
Stacks 02TX commutes with that pushforward. -/
theorem bundleMap_surjective_of_pieces {I : Type u} (V : I → X.Opens)
    (hdisj : Pairwise fun i j ↦ Disjoint (V i) (V j)) (Y : X.IdealSheafData)
    (hY : (Y.support : Set X) = (⋃ i, (V i : Set X))ᶜ) (k : ℤ)
    (hV : ∀ i, letI := isInvertible_presheaf_modulePullback L (π ⁻¹ᵁ V i).ι
      Function.Surjective (bundleMap C ((V i).ι ≫ sX) ((π ⁻¹ᵁ V i).ι ≫ sP) (π ∣_ V i)
        (morphismRestrict_comp_base C sX sP π hsP (V i)) n
        (relativeDimension_morphismRestrict π n hπ (V i))
        (invCap C _ ((Scheme.Modules.pullback (π ⁻¹ᵁ V i).ι).obj L)) k))
    (hYs : letI := locallyOfFiniteType_comapRestrict Y π
      letI := flat_comapRestrict Y π
      letI := isInvertible_presheaf_modulePullback L (Y.comap π).subschemeι
      Function.Surjective (bundleMap C (Y.subschemeι ≫ sX) ((Y.comap π).subschemeι ≫ sP)
        (comapRestrict Y π) (comapRestrict_comp_base C sP sX π hsP Y) n
        (relativeDimension_comapRestrict Y π hπ)
        (invCap C _ ((Scheme.Modules.pullback (Y.comap π).subschemeι).obj L)) k)) :
    Function.Surjective (bundleMap C sX sP π hsP n hπ (invCap C sP L) k) := by
  intro γ
  -- the pieces over the `V_i`
  choose β hβ using fun i ↦ hV i
    (chowGroupRestrict C sP ((π ⁻¹ᵁ V i).ι ≫ sP) (π ⁻¹ᵁ V i).ι rfl (k + n) γ)
  -- glue the families over `U = ⋃ V_i` and lift them to `X`
  set U : X.Opens := ⨆ i, V i with hUdef
  have hm : ∀ i, X.homOfLE (le_iSup V i) ≫ (U.ι ≫ sX) = (V i).ι ≫ sX := fun i ↦ by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have hdec := isClopenDecomposition_homOfLE_iSup V hdisj
  have hlift : ∀ j : Fin (n + 1), ∃ b : chowGroup C sX (k + (j : ℕ)),
      ∀ i, chowGroupRestrict C sX ((V i).ι ≫ sX) (V i).ι rfl _ b = β i j := by
    intro j
    obtain ⟨b, hb⟩ := surjective_chowGroupOpensRestrictOfIsOpenImmersion C sX U (k + (j : ℕ))
      ((chowGroupClopenRestrictEquiv C (U.ι ≫ sX) (fun i ↦ (V i).ι ≫ sX)
        (fun i ↦ X.homOfLE (le_iSup V i)) hm hdec (k + (j : ℕ))).symm fun i ↦ β i j)
    refine ⟨b, fun i ↦ ?_⟩
    have h := congrFun (congrArg (chowGroupClopenRestrictEquiv C (U.ι ≫ sX)
      (fun i ↦ (V i).ι ≫ sX) (fun i ↦ X.homOfLE (le_iSup V i)) hm hdec (k + (j : ℕ))) hb) i
    rw [AddEquiv.apply_symm_apply, chowGroupClopenRestrictEquiv_apply] at h
    rw [← h]
    exact (chowGroupRestrict_homOfLE_opensRestrict C sX (le_iSup V i) _ b).symm
  choose b hb using hlift
  -- the difference vanishes over `π⁻¹(U)`
  set δ := γ - bundleMap C sX sP π hsP n hπ (invCap C sP L) k b with hδdef
  have hδV : ∀ i, chowGroupRestrict C sP ((π ⁻¹ᵁ V i).ι ≫ sP) (π ⁻¹ᵁ V i).ι rfl (k + n) δ = 0 := by
    intro i
    rw [hδdef, map_sub, chowGroupRestrict_bundleMap]
    simp only [hb]
    exact sub_eq_zero.2 (hβ i).symm
  have hmP : ∀ i, P.homOfLE (Scheme.Hom.preimage_mono π (le_iSup V i)) ≫ ((π ⁻¹ᵁ U).ι ≫ sP) =
      (π ⁻¹ᵁ V i).ι ≫ sP := fun i ↦ by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have hdecP := isClopenDecomposition_homOfLE_preimage_iSup π V hdisj
  have hδU : chowGroupOpensRestrictOfIsOpenImmersion C sP (π ⁻¹ᵁ U) (k + n) δ = 0 := by
    refine eq_zero_of_chowGroupRestrict_eq_zero C ((π ⁻¹ᵁ U).ι ≫ sP)
      (fun i ↦ (π ⁻¹ᵁ V i).ι ≫ sP) (fun i ↦ P.homOfLE (Scheme.Hom.preimage_mono π (le_iSup V i)))
      hmP hdecP (k + n) _ fun i ↦ ?_
    rw [chowGroupRestrict_homOfLE_opensRestrict]
    exact hδV i
  -- so it comes from the inverse image of `Y`
  have hcompl := range_comap_subschemeι_eq_compl π Y U (by rw [hY, hUdef, Opens.iSup_def]; rfl)
  obtain ⟨ε, hε⟩ := (exact_chowPushforward_chowGroupOpensRestrict C sP
    ((Y.comap π).subschemeι ≫ sP) (Y.comap π).subschemeι rfl (π ⁻¹ᵁ U) hcompl (k + n) δ).1 hδU
  let := locallyOfFiniteType_comapRestrict Y π
  let := flat_comapRestrict Y π
  let := isInvertible_presheaf_modulePullback L (Y.comap π).subschemeι
  obtain ⟨βY, rfl⟩ := hYs ε
  refine ⟨b + fun j ↦ properChowPushforward C (Y.subschemeι ≫ sX) sX Y.subschemeι rfl _
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl _) (βY j), ?_⟩
  rw [map_add, ← properChowPushforward_bundleMap_comap C sX sP π hsP n hπ Y L k βY]
  show _ + chowPushforwardOfIsClosedImmersion C _ sP _ rfl (k + n) _ = γ
  rw [hε, hδdef]
  abel

end Pieces

/-! ### Restricting towers to smaller opens -/

/-- A projective tower is proper: in fibre dimension zero it is an isomorphism, and properness is
part of the structure in positive fibre dimension. -/
theorem IsProjectiveTower.isProper {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U} {L : P.Modules}
    (h : IsProjectiveTower n π L) : IsProper π := by
  cases h with
  | zero _ _ hiso _ => infer_instance
  | succ => assumption

/-- A projective tower locally on the base is proper, properness being local on the target. -/
theorem IsLocallyProjectiveTower.isProper {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U}
    {L : P.Modules} (h : IsLocallyProjectiveTower n π L) : IsProper π := by
  choose V hV htower using h
  refine IsZariskiLocalAtTarget.of_iSup_eq_top V (top_unique fun x _ ↦ Opens.mem_iSup.2
    ⟨x, hV x⟩) fun x ↦ (htower x).isProper

/-- **Restriction of a projective tower over an open to a smaller open.** If `π` restricted over
`V` is a projective tower, so is its restriction over any `V' ≤ V`. -/
theorem IsProjectiveTower.restrict_of_le {n : ℕ} {P X : Scheme.{u}} {π : P ⟶ X}
    {L : P.Modules} {V V' : X.Opens} (hle : V' ≤ V)
    (h : IsProjectiveTower n (π ∣_ V) ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)) :
    IsProjectiveTower n (π ∣_ V') ((Scheme.Modules.pullback (π ⁻¹ᵁ V').ι).obj L) := by
  have hle' : π ⁻¹ᵁ V' ≤ π ⁻¹ᵁ V := Scheme.Hom.preimage_mono π hle
  have hsq : IsPullback (P.homOfLE hle') (π ∣_ V') (π ∣_ V) (X.homOfLE hle) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict π V).flip
    · rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
      exact (isPullback_morphismRestrict π V').flip
    · rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
        Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
  exact h.of_isPullback hsq
    (((Scheme.Modules.pullbackCongr (Scheme.homOfLE_ι P hle')).app L).symm ≪≫
      ((Scheme.Modules.pullbackComp (P.homOfLE hle') (π ⁻¹ᵁ V).ι).app L).symm)

/-! ### The induction on the delta-dimension of the base -/

/-- **Surjectivity of the map of Stacks 02TX over a base of bounded delta-dimension**, granted
Stacks 02TT. If every point of `X` has delta-dimension less than `k + m`, the map is surjective in
degree `k`.

By induction on `m`. For `m = 0` no point of `P` has delta-dimension `k + n`, so its Chow group in
that degree vanishes. For the inductive step, each irreducible component of `X` has an open
neighbourhood of its generic point over which `π` is a projective tower; removing the other
components, which form a locally finite family, makes these opens pairwise disjoint, and over
each of them Stacks 02TX holds by `Stacks.Chow.IsProjectiveTower.bundleMap_surjective`. Every
point outside their union is a proper specialization of the generic point of a component, so has
delta-dimension less than `k + m`, and `Stacks.Chow.bundleMap_surjective_of_pieces` concludes. -/
theorem bundleMap_surjective_of_relativeDimension_lt (C : ChowSituation.{u})
    (hTT : AffineBundleSurjectivity C) (n : ℕ) (k : ℤ) (m : ℕ) :
    ∀ {P X : Scheme.{u}} {π : P ⟶ X} {L : P.Modules}, IsLocallyProjectiveTower n π L →
      ∀ (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
        (hsP : π ≫ sX = sP)
        [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
        [LocallyOfFiniteType π] [Flat π] (hπ : AlgebraicGeometry.RelativeDimension π n),
        (∀ x : X, relativeDimension C.dimensionFunction sX x < k + m) →
        Function.Surjective (bundleMap C sX sP π hsP n hπ (invCap C sP L) k) := by
  induction m with
  | zero =>
    intro P X π L _ sX _ sP _ hsP _ _ _ hπ hdim γ
    refine ⟨0, ?_⟩
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ γ
    have hc : c = 0 := by
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun w ↦ ?_)
      by_contra hw
      have h1 := (mem_cyclesOfDimension_iff_forall_point C sP _ c.1).1 c.2 w hw
      have h2 := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sX π w
      have h3 := toNat_residueTrdeg_le_of_relativeDimension π n hπ w
      have h4 := hdim (π.base w)
      rw [hsP] at h2
      push_cast at h4
      omega
    rw [hc, map_zero, map_zero]
  | succ m ih =>
    intro P X π L hL sX _ sP _ hsP _ _ _ hπ hdim
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    -- the irreducible components, their generic points and tower neighbourhoods
    set I := irreducibleComponents X
    have hclosed : ∀ Z : I, IsClosed (Z : Set X) :=
      fun Z ↦ isClosed_of_mem_irreducibleComponents _ Z.2
    set η : I → X := fun Z ↦ Z.2.1.genericPoint with hηdef
    have hη : ∀ Z : I, IsGenericPoint (η Z) (Z : Set X) :=
      fun Z ↦ Z.2.1.isGenericPoint_genericPoint (hclosed Z)
    choose W hηW htower using fun Z : I ↦ hL (η Z)
    have hloc : LocallyFinite fun Z : I ↦ (Z : Set X) := by
      simpa using locallyFinite_irreducibleComponents_image (𝟙 X)
    have hO : ∀ Z : I, IsClosed (⋃ Z' : {Z' : I // Z' ≠ Z}, (Z'.1 : Set X)) := fun Z ↦
      (hloc.comp_injective Subtype.val_injective).isClosed_iUnion fun Z' ↦ hclosed Z'.1
    set V : I → X.Opens := fun Z ↦ W Z ⊓ ⟨_, (hO Z).isOpen_compl⟩ with hVdef
    -- a point avoiding all components but one lies in that one
    have hcomp : ∀ x : X, ∃ Z : I, x ∈ (Z : Set X) := fun x ↦ by
      obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
        isIrreducible_singleton
      exact ⟨⟨Z, hZ⟩, hsub rfl⟩
    have hV_mem : ∀ (Z : I) (x : X), x ∈ V Z → ∀ Z' : I, x ∈ (Z' : Set X) → Z' = Z := by
      intro Z x hx Z' hxZ'
      by_contra hne
      exact hx.2 (Set.mem_iUnion.2 ⟨⟨Z', hne⟩, hxZ'⟩)
    have hηV : ∀ Z : I, η Z ∈ V Z := by
      intro Z
      refine ⟨hηW Z, fun hmem ↦ ?_⟩
      obtain ⟨⟨Z', hne⟩, hZ'⟩ := Set.mem_iUnion.1 hmem
      have hsub : (Z : Set X) ⊆ Z' := by
        rw [← (hη Z).def]
        exact (hclosed Z').closure_subset_iff.2 (Set.singleton_subset_iff.2 hZ')
      exact hne (Subtype.ext (Z.2.eq_of_le Z'.2.1 hsub).symm)
    have hdisj : Pairwise fun Z Z' ↦ Disjoint (V Z) (V Z') := by
      intro Z Z' hne
      refine Opens.coe_disjoint.1 (Set.disjoint_left.2 fun x hx hx' ↦ hne ?_)
      obtain ⟨Z'', hZ''⟩ := hcomp x
      exact (hV_mem Z x hx Z'' hZ'').symm.trans (hV_mem Z' x hx' Z'' hZ'')
    -- the complement of the union
    obtain ⟨Y, hYsupp⟩ := exists_idealSheafData_support_eq
      (isClosed_compl_iff.2 (isOpen_iUnion fun Z ↦ (V Z).isOpen))
    refine bundleMap_surjective_of_pieces C sX sP π hsP n hπ L V hdisj Y hYsupp k (fun Z ↦ ?_) ?_
    · let := isInvertible_presheaf_modulePullback L (π ⁻¹ᵁ V Z).ι
      exact ((htower Z).restrict_of_le inf_le_left).bundleMap_surjective C hTT _ _
        (morphismRestrict_comp_base C sX sP π hsP (V Z)) _ k
    · let := locallyOfFiniteType_comapRestrict Y π
      let := flat_comapRestrict Y π
      let := isInvertible_presheaf_modulePullback L (Y.comap π).subschemeι
      refine ih (hL.comapRestrict Y) _ _ (comapRestrict_comp_base C sP sX π hsP Y) _ fun y ↦ ?_
      rw [relativeDimension_comp_closedImmersion]
      have hy := subschemeι_base_mem_support Y y
      rw [hYsupp] at hy
      obtain ⟨Z, hZ⟩ := hcomp (Y.subschemeι.base y)
      have hne : Y.subschemeι.base y ≠ η Z := fun h ↦
        hy (Set.mem_iUnion.2 ⟨Z, h ▸ hηV Z⟩)
      obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
        C.dimensionFunction sX
      have hlt := d.strictAnti_specializes
        ((hη Z).specializes hZ) (Ne.symm hne)
      rw [hd, hd] at hlt
      have := hdim (η Z)
      push_cast at this ⊢
      omega

/-! ### Surjectivity over an arbitrary base -/

/-- **Surjectivity of the map of Stacks 02TX for a locally projective tower**, granted Stacks
02TT. Let `π : P ⟶ X` be flat, locally of finite type and of relative dimension `n`, and a
projective tower of fibre dimension `n` with twist `L` locally on `X`, over a base situation of
chapter 42. Then for every `k` the map

  `⨁_{i = 0}^{n} A_{k + i}(X) ⟶ A_{k + n}(P),  (α_i) ↦ ∑_i c₁(L)^i ∩ π^* α_i`

is surjective.

A class on `P` is represented by a cycle whose support `S` is locally finite, so its closure is
the union of the closures of its points and has delta-dimension at most `k + n`. Its image `T`
under the proper morphism `π` is closed, and every point of `T` has delta-dimension at most
`k + n` too. The class vanishes off `π⁻¹(T)`, so it is pushed forward from there (Stacks 02RX);
over `T` the map is surjective by `Stacks.Chow.bundleMap_surjective_of_relativeDimension_lt`, and
it commutes with the pushforward. -/
theorem IsLocallyProjectiveTower.bundleMap_surjective (C : ChowSituation.{u})
    (hTT : AffineBundleSurjectivity C) {n : ℕ} {P X : Scheme.{u}} {π : P ⟶ X} {L : P.Modules}
    (h : IsLocallyProjectiveTower n π L) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (hsP : π ≫ sX = sP)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    [LocallyOfFiniteType π] [Flat π] (hπ : AlgebraicGeometry.RelativeDimension π n) (k : ℤ) :
    Function.Surjective (bundleMap C sX sP π hsP n hπ (invCap C sP L) k) := by
  intro γ
  have := h.isProper
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ γ
  -- the support of `c`, its closure and its image
  set S : Set P := Function.support c.1 with hSdef
  have hSloc : LocallyFinite fun w : S ↦ ({w.1} : Set P) :=
    LocallyFiniteSupport.locallyFinite_support _ (Function.locallyFinsupp.locallyFiniteSupport c.1)
  have hclS : closure S = ⋃ w : S, closure {w.1} := by
    rw [← hSloc.closure_iUnion]
    congr 1
    ext w
    simp
  set T : Set X := π.base '' closure S with hTdef
  have hTc : IsClosed T := π.isClosedMap _ isClosed_closure
  obtain ⟨Y, hYsupp⟩ := exists_idealSheafData_support_eq hTc
  -- every point of `T` has delta-dimension at most `k + n`
  have hdimY : ∀ y : Y.subscheme, relativeDimension C.dimensionFunction (Y.subschemeι ≫ sX) y <
      k + ((n + 1 : ℕ) : ℤ) := by
    intro y
    rw [relativeDimension_comp_closedImmersion]
    obtain ⟨w', hw', hw'y⟩ := hYsupp ▸ subschemeι_base_mem_support Y y
    rw [hclS] at hw'
    obtain ⟨⟨w, hwS⟩, hw'w⟩ := Set.mem_iUnion.1 hw'
    have h1 := (mem_cyclesOfDimension_iff_forall_point C sP _ c.1).1 c.2 w hwS
    obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
      C.dimensionFunction sP
    have h2 : relativeDimension C.dimensionFunction sP w' ≤
        relativeDimension C.dimensionFunction sP w := by
      by_cases hww : w' = w
      · rw [hww]
      · have hlt := d.strictAnti_specializes (specializes_iff_mem_closure.2 hw'w) (Ne.symm hww)
        rw [hd, hd] at hlt
        exact hlt.le
    have h3 := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sX π w'
    rw [hsP, hw'y] at h3
    push_cast
    omega
  -- the class vanishes off `π⁻¹(T)`
  set U : X.Opens := ⟨Tᶜ, hTc.isOpen_compl⟩ with hUdef
  have hcompl := range_comap_subschemeι_eq_compl π Y U (hYsupp.trans (compl_compl T).symm)
  have hres : chowGroupOpensRestrictOfIsOpenImmersion C sP (π ⁻¹ᵁ U) (k + n)
      (QuotientAddGroup.mk' _ c) = 0 := by
    have hc0 : cycleGroupOpensRestrict C sP (π ⁻¹ᵁ U) (k + n) c = 0 := by
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
      rw [cycleGroupOpensRestrict_apply]
      by_contra hz
      exact z.2 ⟨_, subset_closure hz, rfl⟩
    rw [chowGroupOpensRestrictOfIsOpenImmersion_mk, hc0, map_zero]
  obtain ⟨ε, hε⟩ := (exact_chowPushforward_chowGroupOpensRestrict C sP
    ((Y.comap π).subschemeι ≫ sP) (Y.comap π).subschemeι rfl (π ⁻¹ᵁ U) hcompl (k + n) _).1 hres
  let := locallyOfFiniteType_comapRestrict Y π
  let := flat_comapRestrict Y π
  let := isInvertible_presheaf_modulePullback L (Y.comap π).subschemeι
  obtain ⟨β, rfl⟩ := bundleMap_surjective_of_relativeDimension_lt C hTT n k (n + 1)
    (h.comapRestrict Y) _ _ (comapRestrict_comp_base C sP sX π hsP Y)
    (relativeDimension_comapRestrict Y π hπ) hdimY ε
  refine ⟨fun j ↦ properChowPushforward C (Y.subschemeι ≫ sX) sX Y.subschemeι rfl _
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl _) (β j), ?_⟩
  rw [← properChowPushforward_bundleMap_comap C sX sP π hsP n hπ Y L k β]
  exact hε

end Stacks.Chow

end
