module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.GysinMap
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CapFundamentalFormula
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ComponentDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionFlatCommute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedCapFundamentalClass
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg

/-!
# The Gysin map of a local complete intersection morphism on fundamental classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and consider a cartesian
square `X' = X ×_Y Y'` of schemes locally of finite type over `S`, with `f : X ⟶ Y` and its base
change `f' : X' ⟶ Y'`. **Stacks 0FF7** asserts that if `f` is a local complete intersection
morphism for which the Gysin map `f^!` exists (Stacks 0FF3), if `X`, `X'`, `Y`, `Y'` satisfy the
equivalent conditions of Stacks 0FE3, if `n_{x'} - n_{y'} = n_x - n_y` for the invariants of that
lemma, and if `𝒪_{Y', f'(ξ)}` is Cohen–Macaulay at the generic points `ξ` of `X'`, then

  `f^![Y'] = [X']`

for the fundamental classes of Stacks 0FE4.

The proof is the source's. For a factorization `f = g ∘ i` with `i : X ⟶ P` an immersion and
`g : P ⟶ Y` smooth, `f^! = i^! ∘ g^*`. On a connected component `X_a` of `X`, lying in the
connected component `P_c` of `P`, the rank `r` of the normal sheaf of `i` and the relative
dimension `t` of `g` are constant, so `f^!` is homogeneous there of degree `r - t`; since `i` is a
regular immersion, `dim 𝒪_{P, i ξ} = r` at a generic point `ξ` of `X_a`, while `P_c` is pure of
`δ`-dimension `n_y + t`, whence `r - t = n_y - n_x`. On `X_a` the class `i^! ∘ g^*` satisfies
`c ∩ [T]_k = [X_a ×_Y T]_{k - r + t}` for every test scheme `T` pure of `δ`-dimension `k` with the
dimension and Cohen–Macaulay conditions of Stacks 0FEA: `g^*[T] = [P ×_Y T]`, the local rings of
`P ×_Y T` are Cohen–Macaulay where those of `T` are, `P ×_Y T ⟶ T` being smooth, and Stacks 0FEA
applies to `i`. For `T` a connected component of `Y'` the hypotheses are hypotheses (2), (3) and
(4) of Stacks 0FF7, and restricting to the connected components of `X'` concludes.

## Main results

* `Stacks.Chow.completedCapFundamentalClass_completedBivariantRestriction_lciGysinMap` —
  **Stacks 0FF7**.
* `Stacks.Chow.SmoothFactorization.completedCapFundamentalClass_restriction_gysinMap`
  — the same for the Gysin map `i^! ∘ g^*` of any factorization.
* `Stacks.Chow.capFundamentalClassAt_completedBivariantSequenceOfInvertible_lciGysinMap` — the case
  in which `X`, `Y`, `X'`, `Y'` are pure of `δ`-dimensions `n`, `m`, `n'`, `m'`, in the single
  degree `m - n`.
* `Stacks.Chow.cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass` — the
  same case at a test scheme `T ⟶ Y` pure of `δ`-dimension `m'`: the degree `m - n` part of `f^!`
  caps `[T]_{m'}` to `[X ×_Y T]_{m' - (m - n)}`.
* `Stacks.Chow.SmoothFactorization.exists_hasCapFundamentalFormula_gysinMap` — the Gysin map of a
  factorization is homogeneous on each connected component, of degree `n_y - n_x`, and caps
  fundamental classes of Cohen–Macaulay test schemes to fundamental classes.
* `Stacks.Chow.completedCapFundamentalClass_restriction_of_hasCapFundamentalFormula`
  — the conclusion of Stacks 0FF7 for any completed class with that property.

## Implementation notes

The invariant `n_x` of Stacks 0FE3 — the common value of `δ` at the generic points of the
irreducible components through `x` — is constant on connected components and is the index of the
piece of the decomposition containing `x`
(`Stacks.Chow.relativeDimension_eq_componentDeltaDimension_of_mem_genericPoints`), so it is
written `Stacks.Chow.componentDeltaDimension` of the connected component of `x`. As `X'` may have
infinitely many connected components, both sides of `f^![Y'] = [X']` are read on the connected
components of `X'` (`Stacks.Chow.completedCapFundamentalClass`,
`Stacks.Chow.componentFundamentalClassDirectSum`); the restriction of the fundamental class of
Stacks 0FE4 to a connected component is `Stacks.Chow.chowGroupRestrict_fundamentalClass`.

The source replaces `P` by a neighbourhood of `i(X)` on which `g` has constant relative dimension
and `i` is closed. Here the corresponding constancy is read on connected components, where the
completed classes of Stacks 0FE0 are homogeneous, and the closed immersion is that of `X_a` into a
neighbourhood in `P_c`, which is how `i^!` is built (Stacks 0FBQ (3)).

## References

* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FEA](https://stacks.math.columbia.edu/tag/0FEA)
* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
* [Stacks Project, Tag 0FE4](https://stacks.math.columbia.edu/tag/0FE4)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The Gysin map of a factorization on a connected component -/

section Degree

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- **The Gysin map of a factorization is homogeneous on each connected component, of the
expected degree.** For a factorization `f = g ∘ i` of a local complete intersection morphism,
with `i : X ⟶ P` an immersion and `g : P ⟶ Y` smooth, the class `f^! = i^! ∘ g^*` of Stacks 0FF3
is, on each connected component `X_a` of `X`, concentrated in a single degree `d_a`, where it
satisfies `Stacks.Chow.BivariantClass.CapFundamentalFormula` in every degree; and
`d_a = n - δ(ξ)` for every generic point `ξ` of `X` in `X_a`, whenever the connected component of
`Y` containing `f(X_a)` is pure of `δ`-dimension `n`.

The degree is `d_a = r_a - t`, for `r_a` the rank of the normal sheaf of `i` on `X_a` and `t` the
relative dimension of `g` on the connected component `P_c` of `P` containing `i(X_a)`. That class
is the composite of Stacks 0FEA for `X_a ⟶ P_c`, read through open immersions, with flat pullback
along `P_c ⟶ Y_e`, so
`Stacks.Chow.BivariantClass.capFundamentalFormula_bivariantCompositeOfInvertible` applies. For
the degree: `P_c` is pure of `δ`-dimension `n + t` (Stacks 02R8), so
`dim 𝒪_{P, i ξ} = n + t - δ(ξ)`; and `dim 𝒪_{P, i ξ} = dim 𝒪_{X, ξ} + r_a = r_a` because `i` is a
regular immersion whose conormal sheaf has rank `r_a` at `ξ`
(`Stacks.AlgebraicGeometry.ringKrullDim_stalk_eq_add_fiberRank_conormalModule`) and `𝒪_{X, ξ}`
has dimension zero. -/
theorem SmoothFactorization.exists_hasCapFundamentalFormula_gysinMap (F : SmoothFactorization f)
    (hlci : IsLocalCompleteIntersectionMorphism f) :
    ∃ d : _root_.ConnectedComponents X → ℤ,
      completedBivariantGroup.HasCapFundamentalFormula C (F.gysinMap C sX sY hf hlci) d ∧
      ∀ ξ : X, ξ ∈ genericPoints X → ∀ nY : ℤ,
        (∀ W : irreducibleComponents (Y.connectedComponentOpens
            (f.continuous.connectedComponentsMap (_root_.ConnectedComponents.mk ξ))),
          deltaDimension C ((Y.connectedComponentOpens
              (f.continuous.connectedComponentsMap (_root_.ConnectedComponents.mk ξ))).ι ≫ sY)
            ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set (Y.connectedComponentOpens
              (f.continuous.connectedComponentsMap (_root_.ConnectedComponents.mk ξ)))) W.2⟩ =
            nY) →
        d (_root_.ConnectedComponents.mk ξ) = nY - relativeDimension C.dimensionFunction sX ξ := by
  have : IsLocallyNoetherian F.ambient := LocallyOfFiniteType.isLocallyNoetherian (F.proj ≫ sY)
  have hreg := F.isRegularImmersion hlci
  set 𝒩 := VirtualNormalBundle.ofIsRegularImmersion F.imm hreg
  refine ⟨fun a ↦ (componentRank (𝒩.toOpenFactor F.imm.liftCoborder_ι).bundle a : ℤ) +
    -(smoothComponentRelativeDimension F.proj (F.imm.continuous.connectedComponentsMap a) : ℤ),
    ?_, ?_⟩
  · rw [SmoothFactorization.gysinMap]
    exact ((hasCapFundamentalFormula_completedVirtualNormalGysinClassOfOpen C sX (F.proj ≫ sY)
      F.imm _ _ _ _ 𝒩).comp_completedFlatPullbackOfSmooth C sX (F.proj ≫ sY) F.imm _ sY
        F.proj rfl).copy C F.imm_proj _ hf
  intro ξ hξ nY hY
  set a := _root_.ConnectedComponents.mk ξ
  set c := F.imm.continuous.connectedComponentsMap a
  set t := smoothComponentRelativeDimension F.proj c
  have he : f.continuous.connectedComponentsMap a = F.proj.continuous.connectedComponentsMap c := by
    rw [← Scheme.Hom.connectedComponentsMap_comp, F.imm_proj]
  rw [he] at hY
  -- the connected component `P_c` is pure of `δ`-dimension `nY + t`
  have hPc : ∀ W : irreducibleComponents (F.ambient.connectedComponentOpens c),
      relativeDimension C.dimensionFunction
        ((F.ambient.connectedComponentOpens c).ι ≫ F.proj ≫ sY) W.2.1.genericPoint = nY + t := by
    intro W
    obtain ⟨V, hV⟩ := exists_irreducibleComponent_map_genericPoint
      (F.proj.resConnectedComponent c) W
    have h := deltaDimension_irreducibleComponent_eq_add C (F.proj.resConnectedComponent c)
      ((Y.connectedComponentOpens (F.proj.continuous.connectedComponentsMap c)).ι ≫ sY) t
      (relativeDimension_smoothComponentRelativeDimension F.proj c) W V hV
    rw [hY V] at h
    simp only [F.proj.resConnectedComponent_comp_ι_comp (sY := sY) rfl c] at h
    rwa [deltaDimension_eq_of_isGenericPoint C _ _ _
      (W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2))] at h
  -- `δ(i ξ) = δ(ξ)`
  have hδ : relativeDimension C.dimensionFunction (F.proj ≫ sY) (F.imm ξ) =
      relativeDimension C.dimensionFunction sX ξ := by
    have hfac := F.imm.liftCoborder_ι
    have h1 := relativeDimension_comp_closedImmersion C.dimensionFunction F.imm.liftCoborder
      (F.imm.coborderRange.ι ≫ F.proj ≫ sY) ξ
    have h2 := relativeDimension_comp_isOpenImmersion C.dimensionFunction F.imm.coborderRange.ι
      (F.proj ≫ sY) (F.imm.liftCoborder ξ)
    rw [← Scheme.Hom.comp_apply, hfac] at h2
    rw [← h2, ← h1, ← Category.assoc, hfac, F.imm_comp_structureMorphism C sX sY hf]
  have hmem : F.imm ξ ∈ F.ambient.connectedComponentOpens c :=
    F.imm.connectedComponentOpens_le_preimage a (mem_connectedComponentOpens_mk ξ)
  set pt : (F.ambient.connectedComponentOpens c : Scheme.{u}) := ⟨F.imm ξ, hmem⟩
  have hpt : relativeDimension C.dimensionFunction
      ((F.ambient.connectedComponentOpens c).ι ≫ F.proj ≫ sY) pt =
        relativeDimension C.dimensionFunction sX ξ := by
    rw [relativeDimension_comp_isOpenImmersion, ← hδ]
    rfl
  have hle := relativeDimension_le_of_forall_genericPoint C _ hPc pt
  rw [hpt] at hle
  -- `dim 𝒪_{P, i ξ} = nY + t - δ(ξ)` and `dim 𝒪_{P, i ξ} = r_a`
  have hdim₁ := ringKrullDim_stalk_eq_toNat_sub_relativeDimension C _ hPc pt
  rw [hpt, ringKrullDim_eq_of_ringEquiv
    (asIso ((F.ambient.connectedComponentOpens c).ι.stalkMap pt)).commRingCatIsoToRingEquiv.symm]
    at hdim₁
  have hdim₂ := Stacks.AlgebraicGeometry.ringKrullDim_stalk_eq_add_fiberRank_conormalModule
    F.imm hreg ξ
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_zero_of_mem_genericPoints X ξ hξ, zero_add] at hdim₂
  have hrank : (componentRank (𝒩.toOpenFactor F.imm.liftCoborder_ι).bundle a : ℤ) =
      Scheme.Modules.fiberRank (conormalModule F.imm) ξ := by
    rw [← fiberRank_eq_componentRank _ a ξ (mem_connectedComponentOpens_mk ξ)]
    exact congrArg _ (Scheme.Modules.fiberRank_dualSheaf (conormalModule F.imm)
      (isFiniteLocallyFree_conormalModule F.imm hreg) ξ)
  have hnat : ((nY + t - relativeDimension C.dimensionFunction sX ξ).toNat : ℤ) =
      Scheme.Modules.fiberRank (conormalModule F.imm) ξ := by
    have h := hdim₁.symm.trans hdim₂
    exact_mod_cast h
  rw [Int.toNat_of_nonneg (by omega)] at hnat
  have key : (componentRank (𝒩.toOpenFactor F.imm.liftCoborder_ι).bundle a : ℤ) + -(t : ℤ) =
      nY - relativeDimension C.dimensionFunction sX ξ := by
    omega
  exact key

end Degree

/-! ### The cap product of a restricted completed class with a fundamental class -/

/-- Restricting the sequence of a completed class to `X_a` gives its component `c a p`. -/
private theorem bivariantConnectedComponentRestriction_completedBivariantSequenceOfInvertible
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) (p : ℤ)
    (a : _root_.ConnectedComponents X) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf p
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (completedBivariantSequenceOfInvertible C sX sY f hf c p) a = c a p :=
  restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c p a

/-- The `δ`-dimension at `ξ` of the base change of `f` along `h ≫ g`, for an open immersion `h`,
is that at the image of `ξ` in the base change along `g`. -/
private theorem relativeDimension_baseChangeMapOfEq_of_isOpenImmersion
    (C : ChowSituation.{u}) {X Y T T' : Scheme.{u}} (sX : X ⟶ C.S) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : T' ⟶ T) [IsOpenImmersion h] (ξ : (pullback f (h ≫ g) : Scheme.{u})) :
    relativeDimension C.dimensionFunction (pullback.fst f (h ≫ g) ≫ sX) ξ =
      relativeDimension C.dimensionFunction (pullback.fst f g ≫ sX)
        (baseChangeMapOfEq f g h (h ≫ g) rfl ξ) := by
  have : IsOpenImmersion (baseChangeMapOfEq f g h (h ≫ g) rfl) :=
    MorphismProperty.of_isPullback (isPullback_baseChangeMapOfEq f g h (h ≫ g) rfl)
      (P := @IsOpenImmersion) inferInstance
  rw [← baseChangeMapOfEq_comp_structure sX f g h (h ≫ g) rfl,
    relativeDimension_comp_isOpenImmersion]

section Restriction

variable (C : ChowSituation.{u}) {X Y Y' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) (g : Y' ⟶ Y) [LocallyOfFiniteType g] [IsLocallyNoetherian X]
  [IsLocallyNoetherian Y] [IsLocallyNoetherian Y'] [IsLocallyNoetherian (pullback f g)]

/-- **The restriction of a completed class, capped with the fundamental class of a connected
component of the base.** Let `c ∈ A^*(X ⟶ Y)^∧` (Stacks 0FE0), let `g : Y' ⟶ Y`, let `X'_w` be a
connected component of `X' = X ×_Y Y'`, lying over the connected components `X_a` of `X` and
`Y'_b` of `Y'`, and assume that the part of `c` of degree `p` on `X_a` satisfies
`Stacks.Chow.BivariantClass.CapFundamentalFormula` in degree `n`. If `Y'_b` is pure of
`δ`-dimension `n`, the points of `X'` over `X_a` and `Y'_b` have `δ`-dimension at most `n - p`, and
`𝒪_{Y'}` is Cohen–Macaulay at the images of those of `δ`-dimension `n - p`, then the part of
degree `p` of `res(c)` (Stacks 0F9Z) on `X'_w` caps `[Y'_b]_n` to `[X'_w]_{n - p}`. -/
theorem cap_fundamentalChowClass_completedBivariantRestriction_apply
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (w : _root_.ConnectedComponents (pullback f g : Scheme.{u})) {p n : ℤ}
    (hc : (c ((pullback.fst f g).continuous.connectedComponentsMap w) p).CapFundamentalFormula C
      _ _ _ (f.resConnectedComponent _) (f.resConnectedComponent_comp_ι_comp hf _) n)
    (hT : ∀ W : irreducibleComponents (Y'.connectedComponentOpens
        ((pullback.snd f g).continuous.connectedComponentsMap w)),
      deltaDimension C ((Y'.connectedComponentOpens
          ((pullback.snd f g).continuous.connectedComponentsMap w)).ι ≫ g ≫ sY)
        ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set (Y'.connectedComponentOpens
          ((pullback.snd f g).continuous.connectedComponentsMap w))) W.2⟩ = n)
    (hdim : ∀ x : (pullback f g : Scheme.{u}),
      pullback.snd f g x ∈ Y'.connectedComponentOpens
        ((pullback.snd f g).continuous.connectedComponentsMap w) →
      pullback.fst f g x ∈ X.connectedComponentOpens
        ((pullback.fst f g).continuous.connectedComponentsMap w) →
      relativeDimension C.dimensionFunction (pullback.fst f g ≫ sX) x ≤ n - p)
    (hCM : ∀ x : (pullback f g : Scheme.{u}),
      pullback.snd f g x ∈ Y'.connectedComponentOpens
        ((pullback.snd f g).continuous.connectedComponentsMap w) →
      pullback.fst f g x ∈ X.connectedComponentOpens
        ((pullback.fst f g).continuous.connectedComponentsMap w) →
      relativeDimension C.dimensionFunction (pullback.fst f g ≫ sX) x = n - p →
      IsCohenMacaulayLocalRing (Y'.presheaf.stalk (pullback.snd f g x))) :
    (completedBivariantRestrictionViaSequence C sX sY f hf g c w p).cap (𝟙 _) n
        (fundamentalChowClass C (𝟙 _ ≫ ((Y'.connectedComponentOpens
          ((pullback.snd f g).continuous.connectedComponentsMap w)).ι ≫ (g ≫ sY))) n) =
      fundamentalChowClass C (pullback.fst ((pullback.snd f g).resConnectedComponent w) (𝟙 _) ≫
        (((pullback f g : Scheme.{u}).connectedComponentOpens w).ι ≫ (pullback.fst f g ≫ sX)))
        (n - p) := by
  set a := (pullback.fst f g).continuous.connectedComponentsMap w
  set b := (pullback.snd f g).continuous.connectedComponentsMap w
  set h := 𝟙 (Y'.connectedComponentOpens b : Scheme.{u}) ≫ (Y'.connectedComponentOpens b).ι
  have hc' : (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf p
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (completedBivariantSequenceOfInvertible C sX sY f hf c p) a).CapFundamentalFormula C _ _ _
        (f.resConnectedComponent a) (f.resConnectedComponent_comp_ι_comp hf a) n := by
    rw [bivariantConnectedComponentRestriction_completedBivariantSequenceOfInvertible]
    exact hc
  set m := baseChangeMapOfEq f g h (h ≫ g) rfl
  have hmrel := relativeDimension_baseChangeMapOfEq_of_isOpenImmersion C sX f g h
  have hmfst : ∀ ξ, pullback.fst f g (m ξ) = pullback.fst f (h ≫ g) ξ := by
    intro ξ
    rw [← Scheme.Hom.comp_apply, baseChangeMapOfEq_fst]
  have hmsnd : ∀ ξ, pullback.snd f g (m ξ) = h (pullback.snd f (h ≫ g) ξ) := by
    intro ξ
    rw [← Scheme.Hom.comp_apply, baseChangeMapOfEq_snd, Scheme.Hom.comp_apply]
  have hmemb : ∀ ξ, pullback.snd f g (m ξ) ∈ Y'.connectedComponentOpens b := by
    intro ξ
    rw [hmsnd]
    exact (pullback.snd f (h ≫ g) ξ).2
  rw [completedBivariantRestriction_apply, bivariantConnectedComponentRestriction_cap,
    bivariantRestriction_cap, bivariantRestrictionCap_apply, chowGroupCongr_fundamentalChowClass,
    chowGroupCongr_fundamentalChowClass]
  have hL : (pullbackLeftPullbackSndIso f g h).hom ≫ (pullback.fst f (h ≫ g) ≫ sX) =
      pullback.fst (pullback.snd f g) h ≫ (pullback.fst f g ≫ sX) := by
    simp
  rw [← chowGroupRestrict_eq_chowPushforwardOfIso_inv C _ _ _ hL, chowGroupRestrict_comp]
  refine chowGroupRestrict_cap_fundamentalChowClass_of_capFundamentalFormula C sX sY f hf
    (completedBivariantSequenceOfInvertible C sX sY f hf c p) a hc' (h ≫ g) ?_ ?_ ?_ _ _ _
    (pullback.fst ((pullback.snd f g).resConnectedComponent w) (𝟙 _) ≫
      (pullback.fst f g).resConnectedComponent w) ?_
  · intro W
    simpa only [h, Category.id_comp, Category.assoc] using hT W
  · intro ξ hξ
    rw [hmrel]
    exact hdim _ (hmemb ξ) (by rw [hmfst]; exact hξ)
  · intro ξ hξ hξd
    have hx := hCM (m ξ) (hmemb ξ) (by rw [hmfst]; exact hξ) (by rw [← hmrel]; exact hξd)
    rw [hmsnd] at hx
    exact (isCohenMacaulayLocalRing_iff_of_ringEquiv
      (asIso (h.stalkMap (pullback.snd f (h ≫ g) ξ))).commRingCatIsoToRingEquiv).mp hx
  · rw [Category.assoc, Scheme.Hom.resConnectedComponent_comp_ι, Category.assoc,
      pullbackLeftPullbackSndIso_hom_fst, ← Category.assoc _ (pullback.fst _ _),
      opensPullbackComparison_fst, Category.assoc]

/-- **The cap product of a restricted completed class with the fundamental class (Stacks 0FE4).**
Let `c ∈ A^*(X ⟶ Y)^∧` be concentrated on each connected component `X_a` of `X` in the degree
`d a = n_{f(X_a)} - n_{X_a}`, where it satisfies `Stacks.Chow.BivariantClass.CapFundamentalFormula`
in every degree, the `n` being the `δ`-dimensions of the connected components (Stacks 0FE3). Let
`g : Y' ⟶ Y` and `X' = X ×_Y Y'`, and assume hypotheses (2), (3) and (4) of Stacks 0FF7. Then
`res(c) ∩ [Y'] = [X']`, componentwise: on a connected component `X'_w`, lying over `X_a` and
`Y'_b`, `res(c)` is concentrated in degree `d a` (Stacks 0FDZ), and its cap with `[Y'_b]_{n_b}` is
`[X'_w]_{n_b - d a}` by `Stacks.Chow.cap_fundamentalChowClass_completedBivariantRestriction_apply`:
the points of `X'` over `X_a` and `Y'_b` lie in connected components of `δ`-dimension
`n_b + n_a - n_{f(X_a)} = n_b - d a` by (3), and those of that `δ`-dimension are generic points of
`X'`, at which (4) applies. -/
theorem completedCapFundamentalClass_restriction_of_hasCapFundamentalFormula
    (hX : HasDimensionDecomposition (relativeDimension C.dimensionFunction sX))
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))
    (hX' : HasDimensionDecomposition
      (relativeDimension C.dimensionFunction (pullback.fst f g ≫ sX)))
    (hY' : HasDimensionDecomposition (relativeDimension C.dimensionFunction (g ≫ sY)))
    (hn : ∀ x : (pullback f g : Scheme.{u}),
      componentDeltaDimension C (pullback.fst f g ≫ sX) hX' (_root_.ConnectedComponents.mk x) -
          componentDeltaDimension C (g ≫ sY) hY'
            (_root_.ConnectedComponents.mk (pullback.snd f g x)) =
        componentDeltaDimension C sX hX (_root_.ConnectedComponents.mk (pullback.fst f g x)) -
          componentDeltaDimension C sY hY
            (_root_.ConnectedComponents.mk (f (pullback.fst f g x))))
    (hCM : ∀ ξ : (pullback f g : Scheme.{u}), ξ ∈ genericPoints (pullback f g : Scheme.{u}) →
      IsCohenMacaulayLocalRing (Y'.presheaf.stalk (pullback.snd f g ξ)))
    {c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf}
    {d : _root_.ConnectedComponents X → ℤ}
    (hc : completedBivariantGroup.HasCapFundamentalFormula C c d)
    (hd : ∀ a, d a = componentDeltaDimension C sY hY (f.continuous.connectedComponentsMap a) -
      componentDeltaDimension C sX hX a) :
    completedCapFundamentalClass C (gysinSystemOfInvertible C) (pullback.fst f g ≫ sX) (g ≫ sY)
        (pullback.snd f g) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) hY'
        (completedBivariantRestrictionViaSequence C sX sY f hf g c) =
      componentFundamentalClassDirectSum C (pullback.fst f g ≫ sX) hX' := by
  classical
  funext w
  set a := (pullback.fst f g).continuous.connectedComponentsMap w
  set b := (pullback.snd f g).continuous.connectedComponentsMap w
  set nb := componentDeltaDimension C (g ≫ sY) hY' b
  -- the `δ`-dimension of the connected components of `X'` over `X_a` and `Y'_b`
  have hpts : ∀ x : (pullback f g : Scheme.{u}), pullback.snd f g x ∈ Y'.connectedComponentOpens b →
      pullback.fst f g x ∈ X.connectedComponentOpens a →
      componentDeltaDimension C (pullback.fst f g ≫ sX) hX' (_root_.ConnectedComponents.mk x) =
        nb - d a := by
    intro x hxb hxa
    have h := hn x
    have hxb' : _root_.ConnectedComponents.mk (pullback.snd f g x) = b := hxb
    have hxa' : _root_.ConnectedComponents.mk (pullback.fst f g x) = a := hxa
    have hfx : _root_.ConnectedComponents.mk (f (pullback.fst f g x)) =
        f.continuous.connectedComponentsMap a := by
      rw [← hxa']
      rfl
    rw [hxb', hxa', hfx] at h
    rw [hd a]
    omega
  obtain ⟨x₀, hx₀⟩ := _root_.ConnectedComponents.surjective_coe w
  have hb₀ : _root_.ConnectedComponents.mk (pullback.snd f g x₀) = b := by
    simp only [b, ← hx₀, Continuous.connectedComponentsMap_mk]
  have ha₀ : _root_.ConnectedComponents.mk (pullback.fst f g x₀) = a := by
    simp only [a, ← hx₀, Continuous.connectedComponentsMap_mk]
  have hw : componentDeltaDimension C (pullback.fst f g ≫ sX) hX' w = nb - d a := by
    rw [← hx₀]
    exact hpts x₀ hb₀ ha₀
  -- `res(c)` is concentrated in degree `d a` on `X'_w`
  have hzero : ∀ q, q ≠ d a →
      completedBivariantRestrictionViaSequence C sX sY f hf g c w q = 0 := by
    intro q hq
    rw [completedBivariantRestriction_apply]
    refine bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero C _ sX sY f hf g q
      _ _ _ w ?_
    rw [bivariantConnectedComponentRestriction_completedBivariantSequenceOfInvertible,
      (hc a).1]
    exact DirectSum.of_eq_of_ne _ _ _ hq
  have hcap := cap_fundamentalChowClass_completedBivariantRestriction_apply C sX sY f hf g c w
    ((hc a).2 nb) (deltaDimension_connectedComponentOpens C (g ≫ sY) hY' b)
    (fun x hxb hxa ↦ by
      rw [← hpts x hxb hxa]
      exact relativeDimension_le_componentDeltaDimension C _ hX' x)
    (fun x hxb hxa hx ↦ hCM x (mem_genericPoints_of_relativeDimension_eq_componentDeltaDimension
      C _ hX' x (by rw [hx, hpts x hxb hxa])))
  rw [completedCapFundamentalClass, Finset.sum_eq_single (d a)
    (fun q _ hq ↦ by rw [hzero q hq, map_zero, map_zero])
    (fun hq ↦ by rw [DFinsupp.notMem_support_iff.mp hq, map_zero, map_zero]),
    capFundamentalClassAt_apply, hcap, componentFundamentalClassDirectSum, hw]
  have hpush : chowGroupPullbackIdEquiv C
        (((pullback f g : Scheme.{u}).connectedComponentOpens w).ι ≫ (pullback.fst f g ≫ sX))
        ((pullback.snd f g).resConnectedComponent w) (nb - d a)
        (fundamentalChowClass C (pullback.fst ((pullback.snd f g).resConnectedComponent w) (𝟙 _) ≫
          (((pullback f g : Scheme.{u}).connectedComponentOpens w).ι ≫ (pullback.fst f g ≫ sX)))
          (nb - d a)) =
      fundamentalChowClass C
        (((pullback f g : Scheme.{u}).connectedComponentOpens w).ι ≫ (pullback.fst f g ≫ sX))
        (nb - d a) :=
    chowPushforwardOfIso_fundamentalChowClass C _ _ _ _ _
  rw [hpush]

end Restriction

/-! ### Stacks 0FF7 -/

section Lci

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX)

/-- The degree of the Gysin map of a factorization on a connected component `X_a` is
`n_{f(X_a)} - n_{X_a}`, the difference of the `δ`-dimensions of Stacks 0FE3 of the connected
components of `Y` and of `X`. -/
theorem SmoothFactorization.exists_hasCapFundamentalFormula_gysinMap_of_hasDimensionDecomposition
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (F : SmoothFactorization f)
    (hlci : IsLocalCompleteIntersectionMorphism f)
    (hX : HasDimensionDecomposition (relativeDimension C.dimensionFunction sX))
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY)) :
    ∃ d : _root_.ConnectedComponents X → ℤ,
      completedBivariantGroup.HasCapFundamentalFormula C (F.gysinMap C sX sY hf hlci) d ∧
      ∀ a, d a = componentDeltaDimension C sY hY (f.continuous.connectedComponentsMap a) -
        componentDeltaDimension C sX hX a := by
  obtain ⟨d, hd, hdeg⟩ := F.exists_hasCapFundamentalFormula_gysinMap C sX sY hf hlci
  refine ⟨d, hd, fun a ↦ ?_⟩
  obtain ⟨ξ, hξ, hξa⟩ := exists_mem_genericPoints_mk_eq a
  have h := hdeg ξ hξ (componentDeltaDimension C sY hY
    (f.continuous.connectedComponentsMap (_root_.ConnectedComponents.mk ξ)))
    (deltaDimension_connectedComponentOpens C sY hY
      (f.continuous.connectedComponentsMap (_root_.ConnectedComponents.mk ξ)))
  have hδ := relativeDimension_eq_componentDeltaDimension_of_mem_genericPoints C sX hX ξ hξ
  rw [hδ, hξa] at h
  exact h

/-- **Stacks 0FF7 for the Gysin map of a factorization.** Let `f = g ∘ i` be a factorization of a
local complete intersection morphism `f : X ⟶ Y` of schemes locally of finite type over the base,
with `i` an immersion and `g` smooth, and let `f^! = i^! ∘ g^*` be the Gysin map of Stacks 0FF3.
For `Y' ⟶ Y` locally of finite type with `X' = X ×_Y Y'`, if `X`, `X'`, `Y`, `Y'` have
decompositions as in Stacks 0FE3, if `n_{x'} - n_{y'} = n_x - n_y` for every `x' ∈ X'` with
images `x`, `y'`, `y`, and if `𝒪_{Y', f'(ξ)}` is Cohen–Macaulay at every generic point `ξ` of
`X'`, then `res(f^!) ∩ [Y'] = [X']` for the fundamental classes of Stacks 0FE4, read on the
connected components. -/
theorem SmoothFactorization.completedCapFundamentalClass_restriction_gysinMap
    (F : SmoothFactorization f) (hlci : IsLocalCompleteIntersectionMorphism f) {Y' : Scheme.{u}}
    (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hX : HasDimensionDecomposition (relativeDimension C.dimensionFunction sX))
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))
    (hX' : HasDimensionDecomposition
      (relativeDimension C.dimensionFunction (pullback.fst f g ≫ sX)))
    (hY' : HasDimensionDecomposition (relativeDimension C.dimensionFunction (g ≫ sY)))
    (hn : ∀ x : (pullback f g : Scheme.{u}),
      componentDeltaDimension C (pullback.fst f g ≫ sX) hX' (_root_.ConnectedComponents.mk x) -
          componentDeltaDimension C (g ≫ sY) hY'
            (_root_.ConnectedComponents.mk (pullback.snd f g x)) =
        componentDeltaDimension C sX hX (_root_.ConnectedComponents.mk (pullback.fst f g x)) -
          componentDeltaDimension C sY hY
            (_root_.ConnectedComponents.mk (f (pullback.fst f g x))))
    (hCM : haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
      ∀ ξ : (pullback f g : Scheme.{u}), ξ ∈ genericPoints (pullback f g : Scheme.{u}) →
        IsCohenMacaulayLocalRing (Y'.presheaf.stalk (pullback.snd f g ξ))) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
    haveI : IsLocallyNoetherian (pullback f g) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ sX)
    completedCapFundamentalClass C (gysinSystemOfInvertible C) (pullback.fst f g ≫ sX) (g ≫ sY)
        (pullback.snd f g) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) hY'
        (completedBivariantRestrictionViaSequence C sX sY f hf g (F.gysinMap C sX sY hf hlci)) =
      componentFundamentalClassDirectSum C (pullback.fst f g ≫ sX) hX' := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
  have : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ sX)
  obtain ⟨d, hd, hdeg⟩ :=
    F.exists_hasCapFundamentalFormula_gysinMap_of_hasDimensionDecomposition C sX sY hf hlci hX hY
  exact completedCapFundamentalClass_restriction_of_hasCapFundamentalFormula C sX
    sY f hf g hX hY hX' hY' hn hCM hd hdeg

/-- **Stacks 0FF7.** Consider a cartesian square `X' = X ×_Y Y'` of schemes locally of finite type
over the base, with `f : X ⟶ Y` and its base change `f' : X' ⟶ Y'`. Assume

1. `f` is a local complete intersection morphism for which the Gysin map `f^!` exists
   (Stacks 0FF3);
2. `X`, `X'`, `Y`, `Y'` satisfy the equivalent conditions of Stacks 0FE3, here as decompositions
   into open and closed pieces of constant `δ`-dimension;
3. `n_{x'} - n_{y'} = n_x - n_y` for every `x' ∈ X'` with images `x ∈ X`, `y' ∈ Y'`, `y ∈ Y`;
4. `𝒪_{Y', f'(ξ)}` is Cohen–Macaulay for every generic point `ξ` of `X'`.

Then `f^![Y'] = [X']`, for the fundamental classes of Stacks 0FE4. Here `n_x` is the common value
of `δ` at the generic points of the irreducible components through `x` (Stacks 0FE3); it is
constant on connected components, and equals the index of the piece of the decomposition
containing the point
(`Stacks.Chow.relativeDimension_eq_componentDeltaDimension_of_mem_genericPoints`), which is why
it is written `Stacks.Chow.componentDeltaDimension` of the connected component of `x`. The cap
product `f^![Y']` is that of the restriction `res(f^!)` of Stacks 0F9Z on the completed groups
of Stacks 0FE0 (`Stacks.Chow.completedCapFundamentalClass`), and both sides are read on the
connected components of `X'`, where `[X']` is `[X'_w]_{n_w}`
(`Stacks.Chow.componentFundamentalClassDirectSum`,
`Stacks.Chow.chowGroupRestrict_fundamentalClass`).

The proof is the source's. For a factorization `f = g ∘ i` with `i : X ⟶ P` an immersion and
`g : P ⟶ Y` smooth, `f^! = i^! ∘ g^*` is, on a connected component `X_a` of `X`, homogeneous of
degree `n_{f(X_a)} - n_{X_a}`, the relative dimension of `g` and the rank of the normal sheaf of
`i` being constant on the connected components
(`Stacks.Chow.SmoothFactorization.exists_hasCapFundamentalFormula_gysinMap`);
there `g^*[T] = [P ×_Y T]`, the local rings of `P ×_Y T` are Cohen–Macaulay where needed, and
Stacks 0FEA applies to `i`
(`Stacks.Chow.BivariantClass.capFundamentalFormula_bivariantCompositeOfInvertible`). Restricting
to `Y'` and to the connected components of `X'` is
`Stacks.Chow.completedCapFundamentalClass_restriction_of_hasCapFundamentalFormula`. -/
@[stacks 0FF7]
theorem completedCapFundamentalClass_completedBivariantRestriction_lciGysinMap
    (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f) {Y' : Scheme.{u}}
    (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hX : HasDimensionDecomposition (relativeDimension C.dimensionFunction sX))
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))
    (hX' : HasDimensionDecomposition
      (relativeDimension C.dimensionFunction (pullback.fst f g ≫ sX)))
    (hY' : HasDimensionDecomposition (relativeDimension C.dimensionFunction (g ≫ sY)))
    (hn : ∀ x : (pullback f g : Scheme.{u}),
      componentDeltaDimension C (pullback.fst f g ≫ sX) hX' (_root_.ConnectedComponents.mk x) -
          componentDeltaDimension C (g ≫ sY) hY'
            (_root_.ConnectedComponents.mk (pullback.snd f g x)) =
        componentDeltaDimension C sX hX (_root_.ConnectedComponents.mk (pullback.fst f g x)) -
          componentDeltaDimension C sY hY
            (_root_.ConnectedComponents.mk (f (pullback.fst f g x))))
    (hCM : haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
      ∀ ξ : (pullback f g : Scheme.{u}), ξ ∈ genericPoints (pullback f g : Scheme.{u}) →
        IsCohenMacaulayLocalRing (Y'.presheaf.stalk (pullback.snd f g ξ))) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
    haveI : IsLocallyNoetherian (pullback f g) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ sX)
    completedCapFundamentalClass C (gysinSystemOfInvertible C) (pullback.fst f g ≫ sX) (g ≫ sY)
        (pullback.snd f g) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) hY'
        (completedBivariantRestrictionViaSequence C sX sY f hf g (lciGysinMap C sX sY hf hlci h)) =
      componentFundamentalClassDirectSum C (pullback.fst f g ≫ sX) hX' :=
  SmoothFactorization.completedCapFundamentalClass_restriction_gysinMap C sX sY
    hf _ hlci g hX hY hX' hY' hn hCM

/-- **Stacks 0FF7 in a single degree, at a test scheme.** In the situation of Stacks 0FF7, assume
`X` and `Y` are pure of `δ`-dimensions `n` and `m` — every irreducible component has that
`δ`-dimension — and let `t : T ⟶ Y` be locally of finite type with `T` pure of `δ`-dimension `m'`.
If every point of `X ×_Y T` has `δ` at most `m' - (m - n)`, and `𝒪_{T, t'(ξ)}` is Cohen–Macaulay at
every point `ξ` of `X ×_Y T` where `δ` equals `m' - (m - n)`, then the term of degree `m - n` of
the tuple attached to the Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` (Stacks 0FE0) caps `[T]_{m'}` to
`[X ×_Y T]_{m' - (m - n)}`.

The Gysin map `f^!` is homogeneous of degree `m - n` on every connected component of `X`
(`Stacks.Chow.SmoothFactorization.exists_hasCapFundamentalFormula_gysinMap`), and the class
`f^! ∩ [T]` on `X ×_Y T` is determined by its restrictions to the preimages of the connected
components of `X`, on each of which it is the fundamental class by
`Stacks.Chow.chowGroupRestrict_cap_fundamentalChowClass_of_capFundamentalFormula`. -/
theorem cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass
    (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f) {T : Scheme.{u}}
    (t : T ⟶ Y) [LocallyOfFiniteType t] {n m m' : ℤ}
    (hXn : ∀ W : irreducibleComponents X,
      deltaDimension C sX ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set X) W.2⟩ = n)
    (hYm : ∀ W : irreducibleComponents Y,
      deltaDimension C sY ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set Y) W.2⟩ = m)
    (hTm' : ∀ W : irreducibleComponents T,
      deltaDimension C (t ≫ sY)
        ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set T) W.2⟩ = m')
    (hdim : ∀ ξ : (pullback f t : Scheme.{u}),
      relativeDimension C.dimensionFunction (pullback.fst f t ≫ sX) ξ ≤ m' - (m - n))
    (hCM : ∀ ξ : (pullback f t : Scheme.{u}),
      relativeDimension C.dimensionFunction (pullback.fst f t ≫ sX) ξ = m' - (m - n) →
      letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (t ≫ sY)
      IsCohenMacaulayLocalRing (T.presheaf.stalk (pullback.snd f t ξ))) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    (completedBivariantSequenceOfInvertible C sX sY f hf (lciGysinMap C sX sY hf hlci h)
        (m - n)).cap t m' (fundamentalChowClass C (t ≫ sY) m') =
      fundamentalChowClass C (pullback.fst f t ≫ sX) (m' - (m - n)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨d, hd, hdeg⟩ := (Classical.choice ((gysinMapExists_iff_nonempty f).1 h) :
    SmoothFactorization f).exists_hasCapFundamentalFormula_gysinMap C sX sY hf hlci
  -- `f^!` has degree `m - n` on every connected component of `X`
  have hda : ∀ a, d a = m - n := by
    intro a
    obtain ⟨ξ, hξ, hξa⟩ := exists_mem_genericPoints_mk_eq a
    have hdξ := hdeg ξ hξ m fun W ↦
      deltaDimension_irreducibleComponents_of_isOpenImmersion C sY hYm _ W
    have hξn : relativeDimension C.dimensionFunction sX ξ = n := by
      rw [← hXn ⟨_, hξ⟩, deltaDimension_eq_of_isGenericPoint C _ _ ξ isGenericPoint_closure]
    rw [← hξa, hdξ, hξn]
  have hdimW : schemeDeltaDimension C (pullback.fst f t ≫ sX) ≤ ((m' - (m - n) : ℤ) : EInt) := by
    simpa using schemeDeltaDimension_le_of_forall_relativeDimension_le C _ (𝟙 _)
      (by simpa using hdim)
  -- `f^! ∩ [T]_{m'} = [X ×_Y T]_{m' - (m - n)}`, component by component of `X`
  refine chowGroup_eq_of_chowGroupRestrict_preimage_connectedComponent_eq (C := C)
    (pullback.fst f t ≫ sX) (pullback.fst f t) _ fun a ↦ ?_
  rw [chowGroupRestrict_fundamentalChowClass C _ _ _ rfl _ hdimW]
  have hca := (hd a).2 m'
  rw [hda a] at hca
  exact chowGroupRestrict_cap_fundamentalChowClass_of_capFundamentalFormula C sX sY f hf _ a
    (by rw [bivariantConnectedComponentRestriction_completedBivariantSequenceOfInvertible]
        exact hca) t hTm' (fun ξ _ ↦ hdim ξ) (fun ξ _ hξ ↦ hCM ξ hξ) _ _ rfl
    ((pullback.fst f t).resLE (X.connectedComponentOpens a)
      (pullback.fst f t ⁻¹ᵁ X.connectedComponentOpens a) le_rfl)
    (Scheme.Hom.resLE_comp_ι _ _)

/-- **Stacks 0FF7 in a single degree.** In the situation of Stacks 0FF7, assume `X`, `Y`, `X'`,
`Y'` are pure of `δ`-dimensions `n`, `m`, `n'`, `m'` — every irreducible component has that
`δ`-dimension — with `n' - m' = n - m`, and that `𝒪_{Y', f'(ξ)}` is Cohen–Macaulay at every
generic point `ξ` of `X'`. Then the term of degree `m - n` of the tuple attached to the restriction
`res(f^!) ∈ A^*(X' ⟶ Y')^∧` (Stacks 0FE0, Stacks 0F9Z) caps `[Y']_{m'}` to `[X']_{n'}`, the cap
being read on `X'` through `X' ×_{Y'} Y' ≅ X'` (`Stacks.Chow.capFundamentalClassAt`).

This is the case of Stacks 0FF7 in which the fundamental classes of Stacks 0FE4 have a single
degree. The cap of `res(f^!)` with `[Y']` is that of `f^!` at the test scheme `Y' ⟶ Y`
(`Stacks.Chow.completedBivariantSequenceOfInvertible_completedBivariantRestriction`), which is
`Stacks.Chow.cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass`: every
point of `X ×_Y Y'` has `δ` at most `n'`, and one where `δ = n'` is a generic point. -/
theorem capFundamentalClassAt_completedBivariantSequenceOfInvertible_lciGysinMap
    (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f) {Y' : Scheme.{u}}
    (g : Y' ⟶ Y) [LocallyOfFiniteType g] {n m n' m' : ℤ}
    (hXn : ∀ W : irreducibleComponents X,
      deltaDimension C sX ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set X) W.2⟩ = n)
    (hYm : ∀ W : irreducibleComponents Y,
      deltaDimension C sY ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set Y) W.2⟩ = m)
    (hX'n' : ∀ W : irreducibleComponents (pullback f g : Scheme.{u}),
      deltaDimension C (pullback.fst f g ≫ sX) ⟨W, W.2.1,
        isClosed_of_mem_irreducibleComponents (W : Set (pullback f g : Scheme.{u})) W.2⟩ = n')
    (hY'm' : ∀ W : irreducibleComponents Y',
      deltaDimension C (g ≫ sY)
        ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set Y') W.2⟩ = m')
    (hdim : n' - m' = n - m)
    (hCM : haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
      ∀ ξ : (pullback f g : Scheme.{u}), ξ ∈ genericPoints (pullback f g : Scheme.{u}) →
        IsCohenMacaulayLocalRing (Y'.presheaf.stalk (pullback.snd f g ξ))) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
    haveI : IsLocallyNoetherian (pullback f g) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ sX)
    capFundamentalClassAt C (gysinSystemOfInvertible C) (pullback.fst f g ≫ sX) (g ≫ sY)
        (pullback.snd f g) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) (m - n) m'
        (completedBivariantSequenceOfInvertible C (pullback.fst f g ≫ sX) (g ≫ sY)
          (pullback.snd f g) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g)
          (completedBivariantRestrictionViaSequence C sX sY f hf g (lciGysinMap C sX sY hf hlci h))
          (m - n)) =
      chowGroupDegreeEquiv C (pullback.fst f g ≫ sX) (by omega : n' = m' - (m - n))
        (fundamentalChowClass C (pullback.fst f g ≫ sX) n') := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
  have : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ sX)
  set t := 𝟙 Y' ≫ g
  set mm := baseChangeMapOfEq f g (𝟙 Y') t rfl
  have hmrel := relativeDimension_baseChangeMapOfEq_of_isOpenImmersion C sX f g (𝟙 Y')
  have hX'gen : ∀ W : irreducibleComponents (pullback f g : Scheme.{u}),
      relativeDimension C.dimensionFunction (pullback.fst f g ≫ sX) W.2.1.genericPoint = n' := by
    intro W
    rw [← hX'n' W, deltaDimension_eq_of_isGenericPoint C _ _ _
      (W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2))]
  have hdimpt : ∀ ξ, relativeDimension C.dimensionFunction (pullback.fst f t ≫ sX) ξ ≤
      m' - (m - n) := by
    intro ξ
    rw [hmrel]
    exact (relativeDimension_le_of_forall_genericPoint C _ hX'gen _).trans (le_of_eq (by omega))
  have hX'dim : schemeDeltaDimension C (pullback.fst f g ≫ sX) ≤ (n' : EInt) :=
    iSup_le fun W ↦ (congrArg (fun z : ℤ ↦ (z : EInt)) (hX'n' W)).le
  have hCMt : ∀ ξ : (pullback f t : Scheme.{u}),
      relativeDimension C.dimensionFunction (pullback.fst f t ≫ sX) ξ = m' - (m - n) →
      IsCohenMacaulayLocalRing (Y'.presheaf.stalk (pullback.snd f t ξ)) := by
    intro ξ hξ
    have hgen : mm ξ ∈ genericPoints (pullback f g : Scheme.{u}) := by
      obtain ⟨W, hW⟩ := isGenericPoint_component_of_relativeDimension_eq C
        (pullback.fst f g ≫ sX) (𝟙 _) (by simpa using hX'dim) (mm ξ)
        (by rw [← Scheme.Hom.comp_apply, Category.comp_id, ← hmrel, hξ]; omega)
      rw [genericPoints, Set.mem_ofPred_eq, hW.def]
      exact W.2
    have hpt : pullback.snd f g (mm ξ) = pullback.snd f t ξ := by
      rw [← Scheme.Hom.comp_apply, baseChangeMapOfEq_snd, Category.comp_id]
    rw [← hpt]
    exact hCM _ hgen
  -- `f^! ∩ [Y']_{m'} = [X ×_Y Y']_{n'}`
  have key := cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass C sX sY
    hf hlci h t hXn hYm (fun W ↦ by simpa only [t, Category.id_comp] using hY'm' W) hdimpt hCMt
  rw [capFundamentalClassAt_apply,
    completedBivariantSequenceOfInvertible_completedBivariantRestriction, bivariantRestriction_cap,
    bivariantRestrictionCap_apply, chowGroupCongr_fundamentalChowClass, key,
    chowPushforwardOfIso_fundamentalChowClass, chowGroupDegreeEquiv_fundamentalChowClass]
  exact chowPushforwardOfIso_fundamentalChowClass C _ _ _ _ _

end Lci

end Stacks.Chow

end
