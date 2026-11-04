module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedClassAtInfinity.Modification
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedPowerSumAtInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernClass
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.IsPerfectComparison
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksCore.Tactic.StacksAttribute

/-!
# The localized classes `P'_p(Q)`, `c'_p(Q)` of Stacks 0F9K and Stacks 0FAU

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let `Z ⊆ X` be
a closed subscheme, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X` (A1), and let
`Q ∈ D(𝒪_W)` be a perfect object whose Chern classes are defined (A0). Let `T ⊆ W_∞` be a closed
subscheme containing every point of `W_∞` over `X \ Z` such that `Q|_T` is zero, resp. isomorphic
to a finite locally free `𝒪_T`-module of rank `< p` in degree `0` (A2). Stacks 0F9K defines

  `P'_p(Q) = (E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C`,   resp.   `c'_p(Q) = (E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C`

in `A^p(Z ⟶ X)`, where `E = W_∞ ×_X Z`, `C ∈ A⁰(W_∞ ⟶ X)` is the class of Stacks 0F9J and
`P'_p(Q|_E)`, resp. `c'_p(Q|_E) ∈ A^p(E ⟶ W_∞)` is the class of Stacks 0F9H for the cover
`W_∞ = T ∪ E`.

**Stacks 0FAU**: the class does not depend on `T`, and for a proper `g : W' ⟶ W` which is an
isomorphism over `𝐀¹_X` the class built from `b ∘ g` and `Q' = g^*Q` is the same.

## Main definitions and comparisons

* `Stacks.Chow.GysinAtInfinity.localizedChernClassAtInfinity_eq`,
  `Stacks.Chow.GysinAtInfinity.localizedPowerSumClassAtInfinity_eq` — the classes `c'_p(Q)`,
  `P'_p(Q)` of Stacks 0F9K, that is
  `Stacks.Chow.GysinAtInfinity.localizedChernClassAtInfinity` and
  `Stacks.Chow.GysinAtInfinity.localizedPowerSumClassAtInfinity`, read in the
  form `Stacks.Chow.GysinAtInfinity.localizedClassAtInfinityOf`.

## Main results

* `Stacks.Chow.GysinAtInfinity.localizedPowerSumAtInfinity_invariance` — **Stacks 0FAU** for
  `P'_p(Q)`.
* `Stacks.Chow.GysinAtInfinity.localizedChernClassAtInfinity_invariance` — **Stacks 0FAU** for
  `c'_p(Q)`.

## Implementation notes

`Q|_E` and `Q|_T` are the derived pullbacks of `Q|_{W_∞}` along `E ⟶ W_∞` and `T ⟶ W_∞`, and
`g^*Q` is the derived pullback along `g`. The class `c_p(Q|_E)`, resp. `P_p(Q|_E)` is
`Stacks.Chow.perfectChernClass`, resp. `Stacks.Chow.perfectPowerSumComponent`, the classes of
Section 42.46 (Stacks 0GUD); that the localized class of Stacks 0F9H is defined, i.e. that these
vanish on `T ∩ E`, is derived from (A2) as in the source.

The second statement contains the source's observation that `T' = g^{-1}(T)` satisfies (A2) for
`b ∘ g` and `Q'` (`Stacks.Chow.GysinAtInfinity.isZero_restrictToInfinity_preimage`,
`Stacks.Chow.GysinAtInfinity.restrictionIsLocallyFreeOfRankLT_preimage`), so that `P'_p(Q')`,
resp. `c'_p(Q')` is defined, and the equality is proved for every closed subscheme
`T' ⊆ W'_∞` satisfying (A2) for `b ∘ g` and `Q'`.

## References

* [Stacks Project, Tag 0FAU](https://stacks.math.columbia.edu/tag/0FAU)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0FAH](https://stacks.math.columbia.edu/tag/0FAH)
* [Stacks Project, Tag 0FAQ](https://stacks.math.columbia.edu/tag/0FAQ)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Restriction of total classes -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- Restrictions along equal morphisms, read with equal structure morphisms, agree. -/
theorem res_apply_heq {s₁ s₂ : Y' ⟶ C.S} [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂]
    {h h' : Y' ⟶ Y} [LocallyOfFiniteType h] [LocallyOfFiniteType h'] (hh : h = h')
    (hs₁ : h ≫ sY = s₁) (hs₂ : h' ≫ sY = s₂) (c : TotalChowClass C sY) (p : ℕ) :
    res h hs₁ c p ≍ res h' hs₂ c p := by
  subst hh hs₁ hs₂
  rfl

end TotalChowClass

/-- The vanishing of a Chow cohomology class on a closed subscheme does not depend on how the
structure morphism is written. -/
theorem chowCohomologyRestriction_eq_zero_of_heq {C : ChowSituation.{u}} {Y Y' : Scheme.{u}}
    {s₁ s₂ : Y ⟶ C.S} [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂] (hs : s₁ = s₂)
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] {p : ℤ}
    {κ₁ : chowCohomologyComponent C (gysinSystemOfInvertible C) s₁ p}
    {κ₂ : chowCohomologyComponent C (gysinSystemOfInvertible C) s₂ p} (hκ : κ₁ ≍ κ₂)
    (h₁ : chowCohomologyRestriction C (gysinSystemOfInvertible C) s₁ h p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ₁ = 0) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) s₂ h p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ₂ = 0 := by
  subst hs
  obtain rfl := eq_of_heq hκ
  exact h₁

/-- The derived pullback of a zero object is zero. -/
theorem isZero_derivedPullback_of_isZero {X Y : Scheme.{u}} (h : Y ⟶ X)
    {E : DerivedCategory X.Modules} (hE : IsZero E) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      h.toLRSHom.toShHom).obj E) :=
  Functor.map_isZero _ hE

/-- Derived pullback along a composite, for a composite presented by an equality. -/
theorem isZero_derivedPullback_comp {X Y Y' : Scheme.{u}} (h : Y ⟶ X) (h₁ : Y' ⟶ Y) (h' : Y' ⟶ X)
    (hh : h₁ ≫ h = h') {E : DerivedCategory X.Modules}
    (hE : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      h.toLRSHom.toShHom).obj E)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      h'.toLRSHom.toShHom).obj E) := by
  subst hh
  refine (isZero_derivedPullback_of_isZero h₁ hE).of_iso ?_
  exact ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
    h₁.toLRSHom.toShHom h.toLRSHom.toShHom).app E).symm

/-- The two transports of a bivariant class along an equality of morphisms and an equality of
degrees used by the constructions of Stacks 0F9K agree. -/
theorem bivariantClassCongr_bivariantClassCongrDeg (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {p q : ℤ} (hpq : p = q) {g g' : X ⟶ Y} [LocallyOfFiniteType g]
    [LocallyOfFiniteType g'] (hgg : g = g') (hg : g ≫ sY = sX) (hg' : g' ≫ sY = sX)
    (c : BivariantClass C G sX sY g hg p) :
    bivariantClassCongr C G sX sY hgg hg hg' q (bivariantClassCongrDeg C G sX sY g hg hpq c) =
      BivariantClass.copy C G sX sY hgg hg hg' rfl
        (BivariantClass.copy C G sX sY rfl hg hg hpq c) := by
  subst hpq hgg
  rfl

namespace GysinAtInfinity

/-! ### The localized classes of Stacks 0F9K -/

section Classes

variable (C : ChowSituation.{u}) {X W Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (iZ : Z ⟶ X) [IsClosedImmersion iZ] (Q : DerivedCategory W.Modules)

/-- The restriction `Q|_T` of `Q` to a closed subscheme `T` of `W_∞`, read through `Q|_{W_∞}`. -/
abbrev restrictToInfinity {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b) :
    DerivedCategory T.Modules :=
  (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback iT.toLRSHom.toShHom).obj
    (restrictionAtInfinity f b Q)

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion iZ] in
/-- `E ⟶ W_∞ ⟶ W ⟶ S` is the structure morphism `E ⟶ W_∞ ⟶ X ⟶ S`. -/
theorem infinityPreimage_structure :
    (preimageInclusion f b iZ ≫ modificationInclusionAtInfinity f b) ≫
        (modificationProjection f b ≫ f) =
      preimageInclusion f b iZ ≫ (modificationProjectionAtInfinity f b ≫ f) := by
  simp only [Category.assoc]

variable {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT]

/-- If a total class on `W` vanishes in degree `p` after restriction to every scheme over `T`,
then its restriction to `E` vanishes in degree `p` on `T ∩ E`. -/
theorem chowCohomologyRestriction_res_eq_zero
    (K : TotalChowClass C (modificationProjection f b ≫ f))
    (p : ℕ)
    (hK : ∀ {Y : Scheme.{u}} (h : Y ⟶ T) [LocallyOfFiniteType h] (sY : Y ⟶ C.S)
      [LocallyOfFiniteType sY]
      (hs : (h ≫ iT ≫ modificationInclusionAtInfinity f b) ≫ (modificationProjection f b ≫ f) = sY),
      TotalChowClass.res (h ≫ iT ≫ modificationInclusionAtInfinity f b) hs K p = 0) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (preimageInclusion f b iZ ≫ (modificationProjectionAtInfinity f b ≫ f))
        (pullback.snd iT (preimageInclusion f b iZ)) (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (TotalChowClass.res (preimageInclusion f b iZ ≫ modificationInclusionAtInfinity f b)
          (infinityPreimage_structure C f b iZ) K p) = 0 := by
  rw [← TotalChowClass.res_rfl_apply, TotalChowClass.res_res,
    TotalChowClass.res_congr (h' := pullback.fst iT (preimageInclusion f b iZ) ≫ iT ≫
      modificationInclusionAtInfinity f b) (by rw [← Category.assoc, ← pullback.condition,
        Category.assoc])]
  · exact hK _ _ _
  · simp only [Category.assoc, modificationProjectionAtInfinity, modificationProjection]
    rw [← pullback.condition_assoc]

/-- **Assumption (A2) for `Q|_T = 0` on every scheme over `T`**: the power sums of `Q` restrict to
zero on every scheme over `T`. -/
theorem res_perfectPowerSumTotal_apply_eq_zero_of_isZero
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hQ : HasDefinedChernClasses Q) (p : ℕ) (hzero : IsZero (restrictToInfinity C f b Q iT))
    {Y : Scheme.{u}} (h : Y ⟶ T) [LocallyOfFiniteType h] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (hs : (h ≫ iT ≫ modificationInclusionAtInfinity f b) ≫ (modificationProjection f b ≫ f) = sY) :
    TotalChowClass.res (h ≫ iT ≫ modificationInclusionAtInfinity f b) hs
      (perfectPowerSumTotal C (modificationProjection f b ≫ f) hQ) p = 0 := by
  subst hs
  rw [TotalChowClass.res_rfl_apply, perfectPowerSumTotal_apply]
  refine chowCohomologyRestriction_perfectPowerSumComponent_eq_zero C _ perfect hQ _
    (isZero_derivedPullback_comp (iT ≫ modificationInclusionAtInfinity f b) h _ rfl ?_) p
  exact hzero.of_iso ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
    iT.toLRSHom.toShHom (modificationInclusionAtInfinity f b).toLRSHom.toShHom).app Q).symm

/-- `W_∞ ⟶ W ⟶ X ⟶ S` is the structure morphism `W_∞ ⟶ X ⟶ S`. -/
private theorem modificationInclusionAtInfinity_comp_structure {X W S : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) :
    modificationInclusionAtInfinity f b ≫ (modificationProjection f b ≫ f) =
      modificationProjectionAtInfinity f b ≫ f := by
  simp only [modificationProjectionAtInfinity, Category.assoc]

/-- Restricting to `E` is restricting to `W_∞` and then to `E`. -/
private theorem res_preimageInclusion_comp_inclusion
    (K : TotalChowClass C (modificationProjection f b ≫ f)) :
    TotalChowClass.res (preimageInclusion f b iZ ≫ modificationInclusionAtInfinity f b)
        (infinityPreimage_structure C f b iZ) K =
      TotalChowClass.res (preimageInclusion f b iZ) rfl
        (TotalChowClass.res (modificationInclusionAtInfinity f b)
          (modificationInclusionAtInfinity_comp_structure f b) K) := by
  rw [TotalChowClass.res_res]

/-- **Assumption (A2) for `Q|_T` locally free of rank `< p`, on every scheme over `T`**: the
`p`-th Chern class of `Q` restricts to zero on every scheme over `T`. -/
theorem res_perfectChernClass_apply_eq_zero_of_small (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hres : RestrictionIsLocallyFreeOfRankLT f b iT Q p)
    {Y : Scheme.{u}} (h : Y ⟶ T) [LocallyOfFiniteType h] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (hs : (h ≫ iT ≫ modificationInclusionAtInfinity f b) ≫ (modificationProjection f b ≫ f) = sY) :
    TotalChowClass.res (h ≫ iT ≫ modificationInclusionAtInfinity f b) hs
      (perfectChernClass C (modificationProjection f b ≫ f) hQ) p = 0 := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hres
  have hInf := modificationInclusionAtInfinity_comp_structure f b
  have hQT := hasDefinedChernClasses_derivedPullback iT
    (hasDefinedChernClasses_restrictionAtInfinity f b hQ)
  have key : TotalChowClass.res (h ≫ iT ≫ modificationInclusionAtInfinity f b) hs
        (perfectChernClass C (modificationProjection f b ≫ f) hQ) =
      TotalChowClass.res h (by rw [← hs, ← hInf]; simp only [Category.assoc])
        (TotalChowClass.res iT rfl (TotalChowClass.res (modificationInclusionAtInfinity f b) hInf
          (perfectChernClass C (modificationProjection f b ≫ f) hQ))) := by
    rw [TotalChowClass.res_res, TotalChowClass.res_res]
    exact TotalChowClass.res_congr (Category.assoc _ _ _).symm _ _ _
  rw [key, res_perfectChernClass_derivedPullback_of_eq C _ _ hInf hQ
      (hasDefinedChernClasses_restrictionAtInfinity f b hQ),
    res_perfectChernClass_derivedPullback C _ iT _ hQT]
  exact TotalChowClass.res_apply_eq_zero C h _ _ p
    (perfectChernClass_apply_eq_zero_of_iso_single C _ hQT M hM e)

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion iZ] in
/-- `W' ⟶ W ⟶ X ⟶ S` is the structure morphism `W' ⟶ X ⟶ S` of `b ∘ g`. -/
theorem modificationProjection_comp_structure {W' : Scheme.{u}} (g : W' ⟶ W) :
    g ≫ (modificationProjection f b ≫ f) = modificationProjection f (g ≫ b) ≫ f := by
  simp only [modificationProjection, Category.assoc]

/-- The morphisms `E' ⟶ W' ⟶ W` and `E' ⟶ E ⟶ W` agree, for `E' = g_∞^{-1}(E)`. -/
private theorem preimageInclusion_modification_comp_eq {X W W' Z S : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) (iZ : Z ⟶ X) (g : W' ⟶ W) :
    (preimageInclusion f (g ≫ b) iZ ≫ modificationInclusionAtInfinity f (g ≫ b)) ≫ g =
      baseChangeWitnessProjection (infinityMap f b g) (preimageInclusion f b iZ)
          (infinityPreimageModificationIso f b iZ g) ≫
        preimageInclusion f b iZ ≫ modificationInclusionAtInfinity f b := by
  rw [← Category.assoc (baseChangeWitnessProjection _ _ _),
    baseChangeWitnessProjection_comp (infinityMap f b g) (preimageInclusion f b iZ)
      (preimageInclusion f (g ≫ b) iZ) (infinityPreimageModificationIso f b iZ g)
      (infinityPreimageModificationIso_hom_ι f b iZ g), Category.assoc, Category.assoc,
    infinityMap_fst]

/-- **(A2) for `T' = g_∞^{-1}(T)`, for a class restricted from `W`.** If a total class on `W`
vanishes in degree `p` on every scheme over `T`, then its restriction to `W'` vanishes in degree
`p` on every scheme over `T' = g_∞^{-1}(T)`. -/
private theorem res_modification_apply_eq_zero_of_preimage
    (K : TotalChowClass C (modificationProjection f b ≫ f)) (p : ℕ)
    (hK : ∀ {Y : Scheme.{u}} (h : Y ⟶ T) [LocallyOfFiniteType h] (sY : Y ⟶ C.S)
      [LocallyOfFiniteType sY]
      (hs : (h ≫ iT ≫ modificationInclusionAtInfinity f b) ≫ (modificationProjection f b ≫ f) = sY),
      TotalChowClass.res (h ≫ iT ≫ modificationInclusionAtInfinity f b) hs K p = 0)
    {W' : Scheme.{u}} (g : W' ⟶ W) [IsProper g] {Y : Scheme.{u}}
    (h : Y ⟶ pullback iT (infinityMap f b g)) [LocallyOfFiniteType h] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY]
    (hs : (h ≫ pullback.snd iT (infinityMap f b g) ≫ modificationInclusionAtInfinity f (g ≫ b)) ≫
      (modificationProjection f (g ≫ b) ≫ f) = sY) :
    TotalChowClass.res (h ≫ pullback.snd iT (infinityMap f b g) ≫
      modificationInclusionAtInfinity f (g ≫ b)) hs
      (TotalChowClass.res g (modificationProjection_comp_structure C f b g) K) p = 0 := by
  have hTT : pullback.snd iT (infinityMap f b g) ≫ modificationInclusionAtInfinity f (g ≫ b) ≫ g =
      pullback.fst iT (infinityMap f b g) ≫ iT ≫ modificationInclusionAtInfinity f b := by
    rw [← infinityMap_fst, ← Category.assoc, ← pullback.condition, Category.assoc]
  rw [TotalChowClass.res_res, TotalChowClass.res_congr (h' := (h ≫
    pullback.fst iT (infinityMap f b g)) ≫ iT ≫ modificationInclusionAtInfinity f b)
    (by rw [Category.assoc, Category.assoc, hTT, Category.assoc])]
  · exact hK _ _ _
  · rw [← hs]
    have h₁ := congrArg (fun m ↦ h ≫ m ≫ (modificationProjection f b ≫ f)) hTT
    simp only [modificationProjection, Category.assoc] at h₁ ⊢
    exact h₁.symm

/-- **Stacks 0FAU for a class restricted from `W`.** Let `K` be a total class on `W` vanishing in
degree `p` on every scheme over `T`, and let `g : W' ⟶ W` be proper and an isomorphism over `𝐀¹_X`.
The class of Stacks 0F9K built from `b ∘ g`, any admissible `T' ⊆ W'_∞` and the restriction of
`K` to `E'` equals the class built from `b`, `T` and the restriction of `K` to `E`. -/
theorem localizedClassAtInfinityOf_res_modification
    (K : TotalChowClass C (modificationProjection f b ≫ f)) (p : ℕ)
    (hK : ∀ {Y : Scheme.{u}} (h : Y ⟶ T) [LocallyOfFiniteType h] (sY : Y ⟶ C.S)
      [LocallyOfFiniteType sY]
      (hs : (h ≫ iT ≫ modificationInclusionAtInfinity f b) ≫ (modificationProjection f b ≫ f) = sY),
      TotalChowClass.res (h ≫ iT ≫ modificationInclusionAtInfinity f b) hs K p = 0)
    (hT : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
    {W' : Scheme.{u}} (g : W' ⟶ W) [IsProper g] (hg : IsIso (pullback.snd g (chartInclusion f b)))
    {T' : Scheme.{u}} (iT' : T' ⟶ modificationFibreAtInfinity f (g ≫ b)) [IsClosedImmersion iT']
    (hT' : ∀ w : modificationFibreAtInfinity f (g ≫ b),
      (modificationProjectionAtInfinity f (g ≫ b)).base w ∉ Set.range iZ.base →
        w ∈ Set.range iT'.base)
    (hKT' : ∀ {Y : Scheme.{u}} (h : Y ⟶ T') [LocallyOfFiniteType h] (sY : Y ⟶ C.S)
      [LocallyOfFiniteType sY]
      (hs : (h ≫ iT' ≫ modificationInclusionAtInfinity f (g ≫ b)) ≫
        (modificationProjection f (g ≫ b) ≫ f) = sY),
      TotalChowClass.res (h ≫ iT' ≫ modificationInclusionAtInfinity f (g ≫ b)) hs
        (TotalChowClass.res g (modificationProjection_comp_structure C f b g) K) p = 0) :
    haveI := hA
    haveI := hg
    localizedClassAtInfinityOf C f (g ≫ b) (isIso_pullbackSnd_comp f b g) iZ
        (modificationProjectionAtInfinity f (g ≫ b) ≫ f) rfl iT' hT'
        (TotalChowClass.res
          (preimageInclusion f (g ≫ b) iZ ≫ modificationInclusionAtInfinity f (g ≫ b))
          (infinityPreimage_structure C f (g ≫ b) iZ)
          (TotalChowClass.res g (modificationProjection_comp_structure C f b g) K) p)
        (chowCohomologyRestriction_res_eq_zero C f (g ≫ b) iZ iT' _ p hKT') =
      localizedClassAtInfinityOf C f b hA iZ (modificationProjectionAtInfinity f b ≫ f) rfl iT hT
        (TotalChowClass.res (preimageInclusion f b iZ ≫ modificationInclusionAtInfinity f b)
          (infinityPreimage_structure C f b iZ) K p)
        (chowCohomologyRestriction_res_eq_zero C f b iZ iT K p hK) := by
  have := hA
  have := hg
  have hsW' := modificationProjectionAtInfinity_comp_eq C f b
    (modificationProjectionAtInfinity f b ≫ f) rfl g
  have hus := baseChangeWitnessProjection_comp_structureMorphism (infinityMap f b g)
    (preimageInclusion f b iZ) (preimageInclusion f (g ≫ b) iZ)
    (infinityPreimageModificationIso f b iZ g) (infinityPreimageModificationIso_hom_ι f b iZ g)
    (modificationProjectionAtInfinity f b ≫ f)
  have hκ''₂ := chowCohomologyRestriction_res_eq_zero C f (g ≫ b) iZ
    (pullback.snd iT (infinityMap f b g))
    (TotalChowClass.res g (modificationProjection_comp_structure C f b g) K) p
    (res_modification_apply_eq_zero_of_preimage C f b iT K p hK g)
  -- the two readings of the class on `E'`
  have hκ : TotalChowClass.res
        (preimageInclusion f (g ≫ b) iZ ≫ modificationInclusionAtInfinity f (g ≫ b))
        (infinityPreimage_structure C f (g ≫ b) iZ)
        (TotalChowClass.res g (modificationProjection_comp_structure C f b g) K) p ≍
      TotalChowClass.res (baseChangeWitnessProjection (infinityMap f b g) (preimageInclusion f b iZ)
      (infinityPreimageModificationIso f b iZ g)) hus (TotalChowClass.res
        (preimageInclusion f b iZ ≫ modificationInclusionAtInfinity f b)
        (infinityPreimage_structure C f b iZ) K) p := by
    rw [TotalChowClass.res_res, TotalChowClass.res_res]
    exact TotalChowClass.res_apply_heq (preimageInclusion_modification_comp_eq f b iZ g) _ _ K p
  have hsE : preimageInclusion f (g ≫ b) iZ ≫ (modificationProjectionAtInfinity f (g ≫ b) ≫ f) =
      preimageInclusion f (g ≫ b) iZ ≫
        (infinityMap f b g ≫ (modificationProjectionAtInfinity f b ≫ f)) := by rw [hsW']
  have hκ' := chowCohomologyRestriction_eq_zero_of_heq hsE _ hκ hκ''₂
  rw [localizedClassAtInfinityOf_eq_of_closed C f (g ≫ b) _ iZ _ rfl _ iT' hT'
      (pullback.snd iT (infinityMap f b g)) (preimage_mem_range f b iZ g iT hT) _ hκ''₂,
    localizedClassAtInfinityOf_congr C f (g ≫ b) _ iZ _ _ rfl hsW' hκ hκ''₂ hκ']
  refine localizedClassAtInfinityOf_modification C f b hA iZ
    (modificationProjectionAtInfinity f b ≫ f) rfl iT hT g hg _ _ _ hκ' ?_
  intro V v _ k α
  rw [ChernCapFamily.restrict_cap]
  refine eq_of_heq ((chowGroupCongr_heq C _ _ _).trans ?_)
  exact (TotalChowClass.op_res_apply _ hus _ v k p α _
    (chowGroupCongr_heq C _ k α).symm).symm

/-! ### The classes `P'_p(Q)` and `c'_p(Q)` -/

/-- **The class `c'_p(Q)` of Stacks 0F9K is `(E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C`** in the form of
`Stacks.Chow.GysinAtInfinity.localizedClassAtInfinityOf`: the two transports of bivariant classes
along `E ⟶ W_∞ ⟶ X = E ⟶ Z ⟶ X` and `p + 0 = p` are the same. -/
theorem localizedChernClassAtInfinity_eq (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hT : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
    (hres : RestrictionIsLocallyFreeOfRankLT f b iT Q p) :
    localizedChernClassAtInfinity C hA iZ hQ hT hres =
      localizedClassAtInfinityOf C f b hA iZ (modificationProjectionAtInfinity f b ≫ f) rfl iT hT
        (chernClassOnPreimage C f b iZ hQ p)
        (chowCohomologyRestriction_chernClassOnPreimage_eq_zero C iZ hQ hres) := by
  unfold localizedChernClassAtInfinity localizedClassAtInfinityOf pushAtInfinity compAtInfinity
  rw [bivariantClassCongr_bivariantClassCongrDeg]
  rfl

/-- `c_p(Q|_E)` is the restriction of `c(Q)` to `E`, in degree `p`. -/
theorem chernClassOnPreimage_eq_res (hQ : HasDefinedChernClasses Q) (p : ℕ) :
    chernClassOnPreimage C f b iZ hQ p =
      TotalChowClass.res (preimageInclusion f b iZ ≫ modificationInclusionAtInfinity f b)
        (infinityPreimage_structure C f b iZ)
        (perfectChernClass C (modificationProjection f b ≫ f) hQ) p := by
  have hInf := modificationInclusionAtInfinity_comp_structure f b
  rw [res_preimageInclusion_comp_inclusion,
    res_perfectChernClass_derivedPullback_of_eq C _ _ hInf hQ
      (hasDefinedChernClasses_restrictionAtInfinity f b hQ),
    res_perfectChernClass_derivedPullback C _ _ _
      (hasDefinedChernClasses_derivedPullback (preimageInclusion f b iZ)
        (hasDefinedChernClasses_restrictionAtInfinity f b hQ))]

/-- `P_p(Q|_E)` is the restriction of `P(Q)` to `E`, in degree `p`. -/
theorem powerSumOnPreimage_eq_res
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hQ : HasDefinedChernClasses Q) (p : ℕ) :
    powerSumOnPreimage C f b iZ hQ p =
      TotalChowClass.res (preimageInclusion f b iZ ≫ modificationInclusionAtInfinity f b)
        (infinityPreimage_structure C f b iZ)
        (perfectPowerSumTotal C (modificationProjection f b ≫ f) hQ) p := by
  have hInf := modificationInclusionAtInfinity_comp_structure f b
  rw [res_preimageInclusion_comp_inclusion,
    res_perfectPowerSumTotal_derivedPullback C _ _ hInf perfect hQ
      (isPerfect_restrictionAtInfinity C f b perfect)
      (hasDefinedChernClasses_restrictionAtInfinity f b hQ)]
  have h1 := chowCohomologyRestriction_powerSumAtInfinity_preimage C f b iZ hQ perfect p
  unfold powerSumAtInfinity at h1
  rw [← perfectPowerSumTotal_apply] at h1
  exact h1.symm

/-- **The class `P'_p(Q)` of Stacks 0F9K is `(E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C`** in the form of
`Stacks.Chow.GysinAtInfinity.localizedClassAtInfinityOf`. -/
theorem localizedPowerSumClassAtInfinity_eq
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hT : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
    (hzero : IsZero (restrictToInfinity C f b Q iT)) :
    localizedPowerSumClassAtInfinity (p := p) C hA iZ hQ perfect hT hzero =
      localizedClassAtInfinityOf C f b hA iZ (modificationProjectionAtInfinity f b ≫ f) rfl iT hT
        (powerSumOnPreimage C f b iZ hQ p)
        (chowCohomologyRestriction_powerSumOnPreimage_eq_zero C f b iZ iT hQ perfect p hzero) := by
  unfold localizedPowerSumClassAtInfinity localizedClassAtInfinityOf pushAtInfinity compAtInfinity
  rw [bivariantClassCongr_bivariantClassCongrDeg]
  rfl

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion iZ] [IsClosedImmersion iT] in
/-- `T' = g_∞^{-1}(T) ⟶ W'_∞ ⟶ W' ⟶ W` is `T' ⟶ T ⟶ W_∞ ⟶ W`. -/
theorem preimage_comp_eq {W' : Scheme.{u}} (g : W' ⟶ W) :
    pullback.fst iT (infinityMap f b g) ≫ iT ≫ modificationInclusionAtInfinity f b =
      pullback.snd iT (infinityMap f b g) ≫ modificationInclusionAtInfinity f (g ≫ b) ≫ g := by
  rw [← infinityMap_fst, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
    Category.assoc]

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion iZ] [IsClosedImmersion iT] in
/-- **Assumption (A2) for `T' = g_∞^{-1}(T)`, zero case.** If `Q|_T = 0`
then `(g^*Q)|_{T'} = 0`. -/
theorem isZero_restrictToInfinity_preimage {W' : Scheme.{u}} (g : W' ⟶ W)
    (hzero : IsZero (restrictToInfinity C f b Q iT)) :
    IsZero (restrictToInfinity C f (g ≫ b)
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj Q)
      (pullback.snd iT (infinityMap f b g))) :=
  (isZero_derivedPullback_of_comp_eq _ _ _ _ (preimage_comp_eq C f b iT g).symm Q
    (hzero.of_iso ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      iT.toLRSHom.toShHom
        (modificationInclusionAtInfinity f b).toLRSHom.toShHom).app Q).symm)).of_iso
    ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd iT (infinityMap f b g)).toLRSHom.toShHom).mapIso
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (modificationInclusionAtInfinity f (g ≫ b)).toLRSHom.toShHom g.toLRSHom.toShHom).app Q))

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion iZ] [IsClosedImmersion iT] in
/-- **Assumption (A2) for `T' = g_∞^{-1}(T)`, locally free case.** If `Q|_T` is isomorphic to a
finite locally free module `M` of rank `< p` in degree `0`, then `(g^*Q)|_{T'}` is isomorphic to
the pullback of `M`, which is finite locally free of rank `< p`, in degree `0`. -/
theorem restrictionIsLocallyFreeOfRankLT_preimage {W' : Scheme.{u}} (g : W' ⟶ W) (p : ℕ)
    (hres : RestrictionIsLocallyFreeOfRankLT f b iT Q p) :
    RestrictionIsLocallyFreeOfRankLT f (g ≫ b) (pullback.snd iT (infinityMap f b g))
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj Q)
      p := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hres
  obtain ⟨M', hM', ⟨e'⟩⟩ := exists_iso_single_derivedPullback_of_comp_eq _ _ _ _
    (preimage_comp_eq C f b iT g).symm Q
    ⟨M, hM, ⟨((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      iT.toLRSHom.toShHom (modificationInclusionAtInfinity f b).toLRSHom.toShHom).app Q).symm ≪≫ e⟩⟩
  exact ⟨M', hM', ⟨(Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd iT (infinityMap f b g)).toLRSHom.toShHom).mapIso
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (modificationInclusionAtInfinity f (g ≫ b)).toLRSHom.toShHom g.toLRSHom.toShHom).app Q) ≪≫
    e'⟩⟩

end Classes

/-! ### Stacks 0FAU -/

section Invariance

variable (C : ChowSituation.{u}) {X W Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (iZ : Z ⟶ X) [IsClosedImmersion iZ] (Q : DerivedCategory W.Modules)

/-- **Stacks 0FAU, independence of `T`, for `c'_p(Q)`.** -/
theorem localizedChernClassAtInfinity_eq_of_closed (hQ : HasDefinedChernClasses Q) (p : ℕ)
    {T₁ : Scheme.{u}} (iT₁ : T₁ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT₁]
    (hT₁ : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT₁.base)
    (hres₁ : RestrictionIsLocallyFreeOfRankLT f b iT₁ Q p)
    {T₂ : Scheme.{u}} (iT₂ : T₂ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT₂]
    (hT₂ : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT₂.base)
    (hres₂ : RestrictionIsLocallyFreeOfRankLT f b iT₂ Q p) :
    localizedChernClassAtInfinity C hA iZ hQ hT₁ hres₁ =
      localizedChernClassAtInfinity C hA iZ hQ hT₂ hres₂ := by
  rw [localizedChernClassAtInfinity_eq C f b hA iZ Q iT₁ hQ p hT₁ hres₁,
    localizedChernClassAtInfinity_eq C f b hA iZ Q iT₂ hQ p hT₂ hres₂]
  exact localizedClassAtInfinityOf_eq_of_closed C f b hA iZ _ rfl _ iT₁ hT₁ iT₂ hT₂ _ _

/-- **Stacks 0FAU, independence of `T`, for `P'_p(Q)`.** -/
theorem localizedPowerSumAtInfinity_eq_of_closed
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    {T₁ : Scheme.{u}} (iT₁ : T₁ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT₁]
    (hT₁ : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT₁.base)
    (hzero₁ : IsZero (restrictToInfinity C f b Q iT₁))
    {T₂ : Scheme.{u}} (iT₂ : T₂ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT₂]
    (hT₂ : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT₂.base)
    (hzero₂ : IsZero (restrictToInfinity C f b Q iT₂)) :
    localizedPowerSumClassAtInfinity (p := p) C hA iZ hQ perfect hT₁ hzero₁ =
      localizedPowerSumClassAtInfinity (p := p) C hA iZ hQ perfect hT₂ hzero₂ := by
  rw [localizedPowerSumClassAtInfinity_eq C f b hA iZ Q iT₁ perfect hQ p hT₁ hzero₁,
    localizedPowerSumClassAtInfinity_eq C f b hA iZ Q iT₂ perfect hQ p hT₂ hzero₂]
  exact localizedClassAtInfinityOf_eq_of_closed C f b hA iZ _ rfl _ iT₁ hT₁ iT₂ hT₂ _ _

/-- **Stacks 0FAU for the classes on `E'` and `E` restricted from a class `K` on `W`.** -/
private theorem localizedClassAtInfinityOf_eq_of_eq_res_modification
    (K : TotalChowClass C (modificationProjection f b ≫ f)) (p : ℕ)
    {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT]
    (hK : ∀ {Y : Scheme.{u}} (h : Y ⟶ T) [LocallyOfFiniteType h] (sY : Y ⟶ C.S)
      [LocallyOfFiniteType sY]
      (hs : (h ≫ iT ≫ modificationInclusionAtInfinity f b) ≫ (modificationProjection f b ≫ f) = sY),
      TotalChowClass.res (h ≫ iT ≫ modificationInclusionAtInfinity f b) hs K p = 0)
    (hT : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
    {W' : Scheme.{u}} (g : W' ⟶ W) [IsProper g] (hg : IsIso (pullback.snd g (chartInclusion f b)))
    {T' : Scheme.{u}} (iT' : T' ⟶ modificationFibreAtInfinity f (g ≫ b)) [IsClosedImmersion iT']
    (hT' : ∀ w : modificationFibreAtInfinity f (g ≫ b),
      (modificationProjectionAtInfinity f (g ≫ b)).base w ∉ Set.range iZ.base →
        w ∈ Set.range iT'.base)
    (hKT' : ∀ {Y : Scheme.{u}} (h : Y ⟶ T') [LocallyOfFiniteType h] (sY : Y ⟶ C.S)
      [LocallyOfFiniteType sY]
      (hs : (h ≫ iT' ≫ modificationInclusionAtInfinity f (g ≫ b)) ≫
        (modificationProjection f (g ≫ b) ≫ f) = sY),
      TotalChowClass.res (h ≫ iT' ≫ modificationInclusionAtInfinity f (g ≫ b)) hs
        (TotalChowClass.res g (modificationProjection_comp_structure C f b g) K) p = 0)
    (c' : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (preimageInclusion f (g ≫ b) iZ ≫ (modificationProjectionAtInfinity f (g ≫ b) ≫ f)) p)
    (hE' : c' = TotalChowClass.res
      (preimageInclusion f (g ≫ b) iZ ≫ modificationInclusionAtInfinity f (g ≫ b))
      (infinityPreimage_structure C f (g ≫ b) iZ)
      (TotalChowClass.res g (modificationProjection_comp_structure C f b g) K) p)
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (preimageInclusion f b iZ ≫ (modificationProjectionAtInfinity f b ≫ f)) p)
    (hE : c = TotalChowClass.res (preimageInclusion f b iZ ≫ modificationInclusionAtInfinity f b)
      (infinityPreimage_structure C f b iZ) K p)
    (hz' : chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (preimageInclusion f (g ≫ b) iZ ≫ (modificationProjectionAtInfinity f (g ≫ b) ≫ f))
      (pullback.snd iT' (preimageInclusion f (g ≫ b) iZ)) (p : ℤ)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c' = 0)
    (hz : chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (preimageInclusion f b iZ ≫ (modificationProjectionAtInfinity f b ≫ f))
      (pullback.snd iT (preimageInclusion f b iZ)) (p : ℤ)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c = 0) :
    haveI := hA
    haveI := hg
    localizedClassAtInfinityOf C f (g ≫ b) (isIso_pullbackSnd_comp f b g) iZ
        (modificationProjectionAtInfinity f (g ≫ b) ≫ f) rfl iT' hT' c' hz' =
      localizedClassAtInfinityOf C f b hA iZ (modificationProjectionAtInfinity f b ≫ f) rfl iT hT
        c hz := by
  subst hE' hE
  exact localizedClassAtInfinityOf_res_modification C f b hA iZ iT _ p hK hT g hg iT' hT' hKT'

/-- **Stacks 0FAU, invariance under a proper modification, for `c'_p(Q)`.** Let `g : W' ⟶ W` be
proper and an isomorphism over `𝐀¹_X`, and `Q' = g^*Q`. For every closed subscheme
`T' ⊆ W'_∞` satisfying (A2) for `b ∘ g` and `Q'`, the class `c'_p(Q')` built from `b ∘ g`, `Q'`
and `T'` is `c'_p(Q)`. -/
theorem localizedChernClassAtInfinity_modification (hQ : HasDefinedChernClasses Q) (p : ℕ)
    {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT]
    (hT : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
    (hres : RestrictionIsLocallyFreeOfRankLT f b iT Q p)
    {W' : Scheme.{u}} (g : W' ⟶ W) [IsProper g] (hg : IsIso (pullback.snd g (chartInclusion f b)))
    {T' : Scheme.{u}} (iT' : T' ⟶ modificationFibreAtInfinity f (g ≫ b)) [IsClosedImmersion iT']
    (hT' : ∀ w : modificationFibreAtInfinity f (g ≫ b),
      (modificationProjectionAtInfinity f (g ≫ b)).base w ∉ Set.range iZ.base →
        w ∈ Set.range iT'.base)
    (hres' : RestrictionIsLocallyFreeOfRankLT f (g ≫ b) iT'
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj Q) p) :
    haveI := hA
    haveI := hg
    localizedChernClassAtInfinity C (isIso_pullbackSnd_comp f b g) iZ
        (hasDefinedChernClasses_derivedPullback g hQ) hT' hres' =
      localizedChernClassAtInfinity C hA iZ hQ hT hres := by
  have := hA
  have := hg
  have hQ' := hasDefinedChernClasses_derivedPullback g hQ
  have hW := res_perfectChernClass_derivedPullback_of_eq C (modificationProjection f b ≫ f) g
    (modificationProjection_comp_structure C f b g) hQ hQ'
  have hK := fun {Y : Scheme.{u}} (h : Y ⟶ T) [LocallyOfFiniteType h] (sY : Y ⟶ C.S)
      [LocallyOfFiniteType sY] hs ↦
    res_perfectChernClass_apply_eq_zero_of_small C f b Q iT hQ p hres h sY hs
  have hKT' : ∀ {Y : Scheme.{u}} (h : Y ⟶ T') [LocallyOfFiniteType h] (sY : Y ⟶ C.S)
      [LocallyOfFiniteType sY]
      (hs : (h ≫ iT' ≫ modificationInclusionAtInfinity f (g ≫ b)) ≫
        (modificationProjection f (g ≫ b) ≫ f) = sY),
      TotalChowClass.res (h ≫ iT' ≫ modificationInclusionAtInfinity f (g ≫ b)) hs
        (TotalChowClass.res g (modificationProjection_comp_structure C f b g)
          (perfectChernClass C (modificationProjection f b ≫ f) hQ)) p = 0 := by
    intro Y h _ sY _ hs
    rw [hW]
    exact res_perfectChernClass_apply_eq_zero_of_small C f (g ≫ b) _ iT' hQ' p hres' h sY hs
  have hE' : chernClassOnPreimage C f (g ≫ b) iZ hQ' p =
      TotalChowClass.res
        (preimageInclusion f (g ≫ b) iZ ≫ modificationInclusionAtInfinity f (g ≫ b))
        (infinityPreimage_structure C f (g ≫ b) iZ)
        (TotalChowClass.res g (modificationProjection_comp_structure C f b g)
          (perfectChernClass C (modificationProjection f b ≫ f) hQ)) p := by
    rw [hW]
    exact chernClassOnPreimage_eq_res C f (g ≫ b) iZ _ hQ' p
  have hE := chernClassOnPreimage_eq_res C f b iZ Q hQ p
  rw [localizedChernClassAtInfinity_eq C f (g ≫ b) _ iZ _ iT' hQ' p hT' hres',
    localizedChernClassAtInfinity_eq C f b hA iZ Q iT hQ p hT hres]
  exact localizedClassAtInfinityOf_eq_of_eq_res_modification C f b hA iZ _ p iT hK hT g hg iT' hT'
    hKT' _ hE' _ hE _ _

/-- **Stacks 0FAU, invariance under a proper modification, for `P'_p(Q)`.** Let `g : W' ⟶ W` be
proper and an isomorphism over `𝐀¹_X`, and `Q' = g^*Q`. For every closed subscheme
`T' ⊆ W'_∞` satisfying (A2) for `b ∘ g` and `Q'`, the class `P'_p(Q')` built from `b ∘ g`, `Q'`
and `T'` is `P'_p(Q)`. -/
theorem localizedPowerSumAtInfinity_modification
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT]
    (hT : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
    (hzero : IsZero (restrictToInfinity C f b Q iT))
    {W' : Scheme.{u}} (g : W' ⟶ W) [IsProper g] (hg : IsIso (pullback.snd g (chartInclusion f b)))
    {T' : Scheme.{u}} (iT' : T' ⟶ modificationFibreAtInfinity f (g ≫ b)) [IsClosedImmersion iT']
    (hT' : ∀ w : modificationFibreAtInfinity f (g ≫ b),
      (modificationProjectionAtInfinity f (g ≫ b)).base w ∉ Set.range iZ.base →
        w ∈ Set.range iT'.base)
    (hzero' : IsZero (restrictToInfinity C f (g ≫ b)
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj Q)
        iT')) :
    haveI := hA
    haveI := hg
    localizedPowerSumClassAtInfinity (p := p) C (isIso_pullbackSnd_comp f b g) iZ
        (hasDefinedChernClasses_derivedPullback g hQ)
        (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback g.toLRSHom.toShHom Q perfect)
        hT' hzero' =
      localizedPowerSumClassAtInfinity (p := p) C hA iZ hQ perfect hT hzero := by
  have := hA
  have := hg
  have hQ' := hasDefinedChernClasses_derivedPullback g hQ
  have perfect' :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback g.toLRSHom.toShHom Q perfect
  have hW := res_perfectPowerSumTotal_derivedPullback C (modificationProjection f b ≫ f) g
    (modificationProjection_comp_structure C f b g) perfect hQ perfect' hQ'
  have hK := fun {Y : Scheme.{u}} (h : Y ⟶ T) [LocallyOfFiniteType h] (sY : Y ⟶ C.S)
      [LocallyOfFiniteType sY] hs ↦
    res_perfectPowerSumTotal_apply_eq_zero_of_isZero C f b Q iT perfect hQ p hzero h sY hs
  have hKT' : ∀ {Y : Scheme.{u}} (h : Y ⟶ T') [LocallyOfFiniteType h] (sY : Y ⟶ C.S)
      [LocallyOfFiniteType sY]
      (hs : (h ≫ iT' ≫ modificationInclusionAtInfinity f (g ≫ b)) ≫
        (modificationProjection f (g ≫ b) ≫ f) = sY),
      TotalChowClass.res (h ≫ iT' ≫ modificationInclusionAtInfinity f (g ≫ b)) hs
        (TotalChowClass.res g (modificationProjection_comp_structure C f b g)
          (perfectPowerSumTotal C (modificationProjection f b ≫ f) hQ)) p = 0 := by
    intro Y h _ sY _ hs
    rw [hW]
    exact res_perfectPowerSumTotal_apply_eq_zero_of_isZero C f (g ≫ b) _ iT' perfect' hQ' p hzero'
      h sY hs
  have hE' : powerSumOnPreimage C f (g ≫ b) iZ hQ' p =
      TotalChowClass.res
        (preimageInclusion f (g ≫ b) iZ ≫ modificationInclusionAtInfinity f (g ≫ b))
        (infinityPreimage_structure C f (g ≫ b) iZ)
        (TotalChowClass.res g (modificationProjection_comp_structure C f b g)
          (perfectPowerSumTotal C (modificationProjection f b ≫ f) hQ)) p := by
    rw [hW]
    exact powerSumOnPreimage_eq_res C f (g ≫ b) iZ _ perfect' hQ' p
  have hE := powerSumOnPreimage_eq_res C f b iZ Q perfect hQ p
  rw [localizedPowerSumClassAtInfinity_eq C f (g ≫ b) _ iZ
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj Q) iT'
      perfect' hQ' p hT' hzero',
    localizedPowerSumClassAtInfinity_eq C f b hA iZ Q iT perfect hQ p hT hzero]
  exact localizedClassAtInfinityOf_eq_of_eq_res_modification C f b hA iZ _ p iT hK hT g hg iT' hT'
    hKT' _ hE' _ hE _ _

/-- **Stacks 0FAU, for `P'_p(Q)`.** In the situation of Stacks 0F9K — `X` locally of finite type
over `S`, `Z ⊆ X` closed, `b : W ⟶ 𝐏¹_X` proper and an isomorphism over `𝐀¹_X` (A1), `Q ∈ D(𝒪_W)`
perfect with Chern classes defined (A0) — the class `P'_p(Q) ∈ A^p(Z ⟶ X)`

1. is independent of the choice of the closed subscheme `T ⊆ W_∞` containing all points of `W_∞`
   lying over `X \ Z` with `Q|_T = 0` (A2);
2. is unchanged when `b` is replaced by `b ∘ g` and `Q` by `Q' = g^*Q`, for `g : W' ⟶ W` proper
   and an isomorphism over `𝐀¹_X`: `T' = g^{-1}(T)` satisfies (A2) for `b ∘ g` and `Q'`, so that
   `P'_p(Q')` is defined, and `P'_p(Q) = P'_p(Q')`, the right side computed with any closed
   subscheme `T' ⊆ W'_∞` satisfying (A2) for `b ∘ g` and `Q'`. -/
@[stacks 0FAU "the P'_p(Q) half: independence of the choice of the closed subscheme T, and \
P'_p(Q) = P'_p(Q') for a proper g : W' ⟶ W which is an isomorphism over 𝐀¹_X and Q' = g^*Q"]
theorem localizedPowerSumAtInfinity_invariance
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hQ : HasDefinedChernClasses Q) (p : ℕ) :
    (∀ {T₁ : Scheme.{u}} (iT₁ : T₁ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT₁]
      (hT₁ : ∀ w : modificationFibreAtInfinity f b,
        (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base →
          w ∈ Set.range iT₁.base)
      (hzero₁ : IsZero (restrictToInfinity C f b Q iT₁))
      {T₂ : Scheme.{u}} (iT₂ : T₂ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT₂]
      (hT₂ : ∀ w : modificationFibreAtInfinity f b,
        (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base →
          w ∈ Set.range iT₂.base)
      (hzero₂ : IsZero (restrictToInfinity C f b Q iT₂)),
      localizedPowerSumClassAtInfinity (p := p) C hA iZ hQ perfect hT₁ hzero₁ =
        localizedPowerSumClassAtInfinity (p := p) C hA iZ hQ perfect hT₂ hzero₂) ∧
    (∀ {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT]
      (hT : ∀ w : modificationFibreAtInfinity f b,
        (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
      (hzero : IsZero (restrictToInfinity C f b Q iT))
      {W' : Scheme.{u}} (g : W' ⟶ W) [IsProper g]
      (hg : IsIso (pullback.snd g (chartInclusion f b))),
      ((∀ w : modificationFibreAtInfinity f (g ≫ b),
          (modificationProjectionAtInfinity f (g ≫ b)).base w ∉ Set.range iZ.base →
            w ∈ Set.range (pullback.snd iT (infinityMap f b g)).base) ∧
        IsZero (restrictToInfinity C f (g ≫ b)
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj Q)
          (pullback.snd iT (infinityMap f b g)))) ∧
      ∀ {T' : Scheme.{u}} (iT' : T' ⟶ modificationFibreAtInfinity f (g ≫ b))
        [IsClosedImmersion iT']
        (hT' : ∀ w : modificationFibreAtInfinity f (g ≫ b),
          (modificationProjectionAtInfinity f (g ≫ b)).base w ∉ Set.range iZ.base →
            w ∈ Set.range iT'.base)
        (hzero' : IsZero (restrictToInfinity C f (g ≫ b)
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj Q)
          iT')),
        haveI := hA
        haveI := hg
        localizedPowerSumClassAtInfinity (p := p) C (isIso_pullbackSnd_comp f b g) iZ
            (hasDefinedChernClasses_derivedPullback g hQ)
            (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback g.toLRSHom.toShHom Q
              perfect)
            hT' hzero' =
          localizedPowerSumClassAtInfinity (p := p) C hA iZ hQ perfect hT hzero) :=
  ⟨fun iT₁ _ hT₁ hzero₁ _ iT₂ _ hT₂ hzero₂ ↦ localizedPowerSumAtInfinity_eq_of_closed C f b hA iZ Q
      perfect hQ p iT₁ hT₁ hzero₁ iT₂ hT₂ hzero₂,
    fun iT _ hT hzero _ g _ hg ↦
      ⟨⟨preimage_mem_range f b iZ g iT hT, isZero_restrictToInfinity_preimage C f b Q iT g hzero⟩,
        fun iT' _ hT' hzero' ↦ localizedPowerSumAtInfinity_modification C f b hA iZ Q perfect hQ p
          iT hT hzero g hg iT' hT' hzero'⟩⟩

/-- **Stacks 0FAU, for `c'_p(Q)`.** In the situation of Stacks 0F9K — `X` locally of finite type
over `S`, `Z ⊆ X` closed, `b : W ⟶ 𝐏¹_X` proper and an isomorphism over `𝐀¹_X` (A1), `Q ∈ D(𝒪_W)`
perfect with Chern classes defined (A0) — the class `c'_p(Q) ∈ A^p(Z ⟶ X)`

1. is independent of the choice of the closed subscheme `T ⊆ W_∞` containing all points of `W_∞`
   lying over `X \ Z` with `Q|_T` isomorphic to a finite locally free `𝒪_T`-module of rank `< p`
   in degree `0` (A2);
2. is unchanged when `b` is replaced by `b ∘ g` and `Q` by `Q' = g^*Q`, for `g : W' ⟶ W` proper
   and an isomorphism over `𝐀¹_X`: `T' = g^{-1}(T)` satisfies (A2) for `b ∘ g` and `Q'`, so that
   `c'_p(Q')` is defined, and `c'_p(Q) = c'_p(Q')`, the right side computed with any closed
   subscheme `T' ⊆ W'_∞` satisfying (A2) for `b ∘ g` and `Q'`.

Perfectness of `Q` is a hypothesis of the source; the construction of `c'_p(Q)` does not use it. -/
@[stacks 0FAU "the c'_p(Q) half: independence of the choice of the closed subscheme T, and \
c'_p(Q) = c'_p(Q') for a proper g : W' ⟶ W which is an isomorphism over 𝐀¹_X and Q' = g^*Q"]
theorem localizedChernClassAtInfinity_invariance
    (_perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hQ : HasDefinedChernClasses Q) (p : ℕ) :
    (∀ {T₁ : Scheme.{u}} (iT₁ : T₁ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT₁]
      (hT₁ : ∀ w : modificationFibreAtInfinity f b,
        (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base →
          w ∈ Set.range iT₁.base)
      (hsmall₁ : RestrictionIsLocallyFreeOfRankLT f b iT₁ Q p)
      {T₂ : Scheme.{u}} (iT₂ : T₂ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT₂]
      (hT₂ : ∀ w : modificationFibreAtInfinity f b,
        (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base →
          w ∈ Set.range iT₂.base)
      (hsmall₂ : RestrictionIsLocallyFreeOfRankLT f b iT₂ Q p),
      localizedChernClassAtInfinity C hA iZ hQ hT₁ hsmall₁ =
        localizedChernClassAtInfinity C hA iZ hQ hT₂ hsmall₂) ∧
    (∀ {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT]
      (hT : ∀ w : modificationFibreAtInfinity f b,
        (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
      (hsmall : RestrictionIsLocallyFreeOfRankLT f b iT Q p)
      {W' : Scheme.{u}} (g : W' ⟶ W) [IsProper g]
      (hg : IsIso (pullback.snd g (chartInclusion f b))),
      ((∀ w : modificationFibreAtInfinity f (g ≫ b),
          (modificationProjectionAtInfinity f (g ≫ b)).base w ∉ Set.range iZ.base →
            w ∈ Set.range (pullback.snd iT (infinityMap f b g)).base) ∧
        RestrictionIsLocallyFreeOfRankLT f (g ≫ b) (pullback.snd iT (infinityMap f b g))
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj Q)
          p) ∧
      ∀ {T' : Scheme.{u}} (iT' : T' ⟶ modificationFibreAtInfinity f (g ≫ b))
        [IsClosedImmersion iT']
        (hT' : ∀ w : modificationFibreAtInfinity f (g ≫ b),
          (modificationProjectionAtInfinity f (g ≫ b)).base w ∉ Set.range iZ.base →
            w ∈ Set.range iT'.base)
        (hsmall' : RestrictionIsLocallyFreeOfRankLT f (g ≫ b) iT'
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj Q)
          p),
        haveI := hA
        haveI := hg
        localizedChernClassAtInfinity C (isIso_pullbackSnd_comp f b g) iZ
            (hasDefinedChernClasses_derivedPullback g hQ) hT' hsmall' =
          localizedChernClassAtInfinity C hA iZ hQ hT hsmall) :=
  ⟨fun iT₁ _ hT₁ hsmall₁ _ iT₂ _ hT₂ hsmall₂ ↦ localizedChernClassAtInfinity_eq_of_closed C f b hA
      iZ Q hQ p iT₁ hT₁ hsmall₁ iT₂ hT₂ hsmall₂,
    fun iT _ hT hsmall _ g _ hg ↦
      ⟨⟨preimage_mem_range f b iZ g iT hT,
          restrictionIsLocallyFreeOfRankLT_preimage C f b Q iT g p hsmall⟩,
        fun iT' _ hT' hsmall' ↦ localizedChernClassAtInfinity_modification C f b hA iZ Q hQ p iT
          hT hsmall g hg iT' hT' hsmall'⟩⟩

end Invariance

end GysinAtInfinity

end Stacks.Chow

end
