module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationLocalization
public import StacksCore.Tactic.StacksAttribute

/-!
# Composites of localized Chern classes of a modification

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, and let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`. For
closed subschemes `Z_i ⊆ X`, closed `T_i ⊆ W_∞`, perfect `Q_i ∈ D(𝒪_W)` and integers `p_i ≥ 0`
satisfying the hypotheses of Stacks 0F9K, such that `Q_i|_{W ∖ W_i}` is zero, resp. finite locally
free of rank `< p_i` in degree `0`, for `W_i = b^{-1}(𝐏¹_{Z_i})`, and such that `Q_i` satisfies
condition (3) of Situation 0GUJ, **Stacks 0FE7** says that

  `P'_{p_n}(Q_n) ∘ ⋯ ∘ P'_{p_1}(Q_1) = (W_{n,∞} ∩ ⋯ ∩ W_{1,∞} ⟶ Z_n ∩ ⋯ ∩ Z_1)_* ∘
    P'_{p_n}(Q_n|_{W_{n,∞}}) ∘ ⋯ ∘ P'_{p_1}(Q_1|_{W_{1,∞}}) ∘ C`

in `A^{p_n + ⋯ + p_1}(Z_n ∩ ⋯ ∩ Z_1 ⟶ X)`, resp. the same for `c'`.

## Main definitions

* `Stacks.Chow.iteratedIntersection` — the intersection `Z_{i_n} ∩ ⋯ ∩ Z_{i_1}`.
* `Stacks.Chow.supportedComposite` — the composite `c_{i_n} ∘ ⋯ ∘ c_{i_1}` of classes supported
  on the `Z_i`.
* `Stacks.Chow.modificationInfinityComposite` — the composite over `W_∞` of classes supported on
  the `W_{i,∞}`.
* `Stacks.Chow.modificationSituationOf` — the situation of Stacks 0GUJ for `W`, `W_i` and `Q_i`.
* `Stacks.Chow.modificationInfinityChernClass`, `Stacks.Chow.modificationInfinityPowerSum` — the
  classes `c'_p(Q|_{W_{Z,∞}})` and `P'_p(Q|_{W_{Z,∞}})` of Stacks 0F9H.

## Main results

* `Stacks.Chow.supportedComposite_eq_modificationLocalization` — the general form of Stacks 0FE7
  for localizations of classes preserving the image of the Gysin map at infinity.
* `Stacks.Chow.preservesInfinityGysinImage_modificationInfinityChernClass`,
  `Stacks.Chow.preservesInfinityGysinImage_modificationInfinityPowerSum` — the classes of
  Stacks 0F9H preserve that image (Stacks 0FB8, 0FB7, 0FB3).
* `Stacks.Chow.supportedComposite_modificationChernClass`,
  `Stacks.Chow.supportedComposite_modificationPowerSum` — **Stacks 0FE7**.

## Implementation notes

The `n` factors are an arbitrary family indexed by a type `ι`, and the composite is formed along
a list of indices `i_1, …, i_n` with `n ≥ 1`, written as a first index `i_1` and the list
`[i_n, …, i_2]`; the hypotheses are required of every member of the family, so a sequence of `n`
factors is the case `ι = Fin n`. The intersection `Z_n ∩ ⋯ ∩ Z_1` is the iterated fibre product
`Z_n ×_X (⋯ ×_X Z_1)`, the composite is the product of Stacks 0FE5 (the composite of
Stacks 0B75 with the restriction of Remark 0F9Z), and `W_{n,∞} ∩ ⋯ ∩ W_{1,∞}` is presented as
`W_∞ ×_X (Z_n ∩ ⋯ ∩ Z_1)`. The scheme `W_i = b^{-1}(𝐏¹_{Z_i})` is `W ×_X Z_i`, and
`Q_i|_{W_{i,∞}}` is the restriction of `Q_i|_{W_∞}`. The Chern classes of `Q_i` being defined
(assumption (A0) of Stacks 0F9K) is a hypothesis, as in the source.

The source restricts `c'_{p_n}(Q_n)` to `Z_{n-1} ∩ ⋯ ∩ Z_1` by Stacks 0GUI, simplifies the
result by Stacks 0GUG, and applies Stacks 0FAR to the class at infinity `C_{n-1}` of the restricted
modification. Here the induction step is proved on every test scheme `V ⟶ X`, where the
restriction to `Z_{n-1} ∩ ⋯ ∩ Z_1` is the operation of `c'_{p_n}(Q_n)` on the test scheme
`(Z_{n-1} ∩ ⋯ ∩ Z_1) ×_X V ⟶ X` and `C_{n-1}` is the operation of `C` there; Stacks 0FAR is
applied in that form, and Stacks 0GUI and 0GUG are not needed as separate statements.

## References

* [Stacks Project, Tag 0FE7](https://stacks.math.columbia.edu/tag/0FE7)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0GUI](https://stacks.math.columbia.edu/tag/0GUI)
* [Stacks Project, Tag 0GUG](https://stacks.math.columbia.edu/tag/0GUG)
* [Stacks Project, Tag 0FAR](https://stacks.math.columbia.edu/tag/0FAR)
* [Stacks Project, Tag 0FB8](https://stacks.math.columbia.edu/tag/0FB8)
* [Stacks Project, Tag 0FB7](https://stacks.math.columbia.edu/tag/0FB7)
* [Stacks Project, Tag 0FB3](https://stacks.math.columbia.edu/tag/0FB3)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Iterated intersections and composites -/

section Iteration

variable {X : Scheme.{u}} {ι : Type*} {Z : ι → Scheme.{u}} (z : ∀ i, Z i ⟶ X)

/-- **The iterated intersection `Z_{i_n} ∩ ⋯ ∩ Z_{i_1}`** of closed subschemes of `X`, for the
list `[i_n, …, i_2]` and the first index `i_1`: `Z_{i_1}` for the empty list, and
`Z_i ×_X (Z_{i_m} ∩ ⋯ ∩ Z_{i_1})` for `i :: [i_m, …, i_2]`, together with its morphism to `X`. -/
def iteratedIntersection (i₁ : ι) : List ι → Σ Y : Scheme.{u}, Y ⟶ X
  | [] => ⟨Z i₁, z i₁⟩
  | i :: L => ⟨pullback (z i) (iteratedIntersection i₁ L).2,
      pullback.fst (z i) (iteratedIntersection i₁ L).2 ≫ z i⟩

/-- The iterated intersection of closed subschemes is a closed subscheme. -/
instance isClosedImmersion_iteratedIntersection [∀ i, IsClosedImmersion (z i)] (i₁ : ι)
    (L : List ι) : IsClosedImmersion (iteratedIntersection z i₁ L).2 := by
  induction L with
  | nil => exact inferInstanceAs (IsClosedImmersion (z i₁))
  | cons i L ih =>
    exact inferInstanceAs
      (IsClosedImmersion (pullback.fst (z i) (iteratedIntersection z i₁ L).2 ≫ z i))

/-- The degree `p_{i_n} + ⋯ + p_{i_1}` of the iterated composite. -/
def iteratedDegree (p : ι → ℤ) (i₁ : ι) : List ι → ℤ
  | [] => p i₁
  | i :: L => p i + iteratedDegree p i₁ L

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
  [∀ i, IsClosedImmersion (z i)] (p : ι → ℤ)

/-- **The iterated composite `c_{i_n} ∘ ⋯ ∘ c_{i_1}`** of classes `c_i ∈ A^{p_i}(Z_i ⟶ X)`
supported on closed subschemes, a class of `A^{p_{i_n} + ⋯ + p_{i_1}}(Z_{i_n} ∩ ⋯ ∩ Z_{i_1} ⟶ X)`:
`c_i ∘ (rest)` is `res(c_i) ∘ (rest)`, the product of Stacks 0FE5
(`Stacks.Chow.supportedIntersectionMul`). -/
def supportedComposite (c : ∀ i, BivariantClass C (gysinSystemOfInvertible C) (z i ≫ f) f (z i)
    rfl (p i)) (i₁ : ι) : (L : List ι) →
    BivariantClass C (gysinSystemOfInvertible C) ((iteratedIntersection z i₁ L).2 ≫ f) f
      (iteratedIntersection z i₁ L).2 rfl (iteratedDegree p i₁ L)
  | [] => c i₁
  | i :: L => supportedIntersectionMul C f (z i) (iteratedIntersection z i₁ L).2
      (IsPullback.of_hasPullback _ _) (pullback.fst (z i) (iteratedIntersection z i₁ L).2 ≫ z i)
      pullback.condition.symm (c i) (supportedComposite c i₁ L)

variable {W : Scheme.{u}} (b : W ⟶ projectiveLineProduct f) [IsProper b]

/-- **The iterated composite `a_{i_n} ∘ ⋯ ∘ a_{i_1}` over `W_∞`** of classes
`a_i ∈ A^{p_i}(W_{i,∞} ⟶ W_∞)`, `W_{i,∞} = W_∞ ×_X Z_i`, a class supported on
`W_{i_n,∞} ∩ ⋯ ∩ W_{i_1,∞}`, presented as `W_∞ ×_X (Z_{i_n} ∩ ⋯ ∩ Z_{i_1})`. -/
def modificationInfinityComposite (a : ∀ i, BivariantClass C (gysinSystemOfInvertible C)
    (pullback.fst (modificationProjectionAtInfinity f b) (z i) ≫
      modificationProjectionAtInfinity f b ≫ f)
    (modificationProjectionAtInfinity f b ≫ f)
    (pullback.fst (modificationProjectionAtInfinity f b) (z i)) rfl (p i)) (i₁ : ι) :
    (L : List ι) → BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) (iteratedIntersection z i₁ L).2 ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) (iteratedIntersection z i₁ L).2) rfl
      (iteratedDegree p i₁ L)
  | [] => a i₁
  | i :: L => modificationInfinityMul C f b (z i) (iteratedIntersection z i₁ L).2 (a i)
      (modificationInfinityComposite a i₁ L)

variable {C f b p} in
/-- An iterated composite over `W_∞` of classes preserving the image of the Gysin map at infinity
preserves it. -/
theorem preservesInfinityGysinImage_modificationInfinityComposite
    {a : ∀ i, BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) (z i) ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) (z i)) rfl (p i)}
    (ha : ∀ i, PreservesInfinityGysinImage C f b (z i) (a i)) (i₁ : ι) (L : List ι) :
    PreservesInfinityGysinImage C f b (iteratedIntersection z i₁ L).2
      (modificationInfinityComposite z C f p b a i₁ L) := by
  induction L with
  | nil => exact @ha i₁
  | cons i L ih => exact PreservesInfinityGysinImage.modificationInfinityMul C f b (@ha i) @ih

variable (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- **The iterated composite of localizations** (the general form of Stacks 0FE7). If every
`c_i ∈ A^{p_i}(Z_i ⟶ X)` is the localization `(W_{i,∞} ⟶ Z_i)_* ∘ a_i ∘ C` of a class
`a_i ∈ A^{p_i}(W_{i,∞} ⟶ W_∞)` preserving the image of the Gysin map at infinity, then
`c_{i_n} ∘ ⋯ ∘ c_{i_1} = (W_{i_n,∞} ∩ ⋯ ∩ W_{i_1,∞} ⟶ Z_{i_n} ∩ ⋯ ∩ Z_{i_1})_* ∘
a_{i_n} ∘ ⋯ ∘ a_{i_1} ∘ C`. -/
theorem supportedComposite_eq_modificationLocalization
    (c : ∀ i, BivariantClass C (gysinSystemOfInvertible C) (z i ≫ f) f (z i) rfl (p i))
    (a : ∀ i, BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) (z i) ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) (z i)) rfl (p i))
    (hc : ∀ i, c i = modificationLocalization C f b hA (z i) (a i))
    (ha : ∀ i, PreservesInfinityGysinImage C f b (z i) (a i)) (i₁ : ι) (L : List ι) :
    supportedComposite z C f p c i₁ L =
      modificationLocalization C f b hA (iteratedIntersection z i₁ L).2
        (modificationInfinityComposite z C f p b a i₁ L) := by
  induction L with
  | nil => exact hc i₁
  | cons i L ih =>
    change supportedIntersectionMul C f (z i) (iteratedIntersection z i₁ L).2
      (IsPullback.of_hasPullback _ _) (pullback.fst (z i) (iteratedIntersection z i₁ L).2 ≫ z i)
      pullback.condition.symm (c i) (supportedComposite z C f p c i₁ L) = _
    rw [hc i, ih]
    exact supportedIntersectionMul_modificationLocalization C f b hA (z i) _ (a i) _
      (preservesInfinityGysinImage_modificationInfinityComposite z ha i₁ L)

end Iteration

section Factor

variable (C : ChowSituation.{u}) {X W Z T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {Q : DerivedCategory W.Modules}

variable {C f} in
/-- The open complement `W ∖ W_Z` of `W_Z = W ×_X Z`. -/
abbrev modificationComplementOpens : W.Opens :=
  ⟨(Set.range (pullback.fst (modificationProjection f b) z).base)ᶜ,
    (pullback.fst (modificationProjection f b) z).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- **The situation of Stacks 0GUJ on the modification**: the scheme `W`, over the base through
`W ⟶ X ⟶ S`, the closed subscheme `W_Z = W ×_X Z = b^{-1}(𝐏¹_Z)`, a perfect object `Q` and a
degree `p`, with condition (2) along `W_Z` and condition (3). -/
abbrev modificationSituationOf (p : ℕ)
    (hperf : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q)
    (hres : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (W.toRingedSpace.ofRestrict (modificationComplementOpens b z).isOpenEmbedding)).obj Q) ∨
      ∃ M : OXMod.{u, u, u} (W.toRingedSpace.restrict
          (modificationComplementOpens b z).isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M p ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (W.toRingedSpace.ofRestrict (modificationComplementOpens b z).isOpenEmbedding)).obj
              Q ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (hfin : LocalizedChernFiniteness C (modificationProjection f b ≫ f) Q) :
    LocalizedSituation.{u} where
  base := C
  X := W
  a := modificationProjection f b ≫ f
  Z := pullback (modificationProjection f b) z
  i := pullback.fst (modificationProjection f b) z
  E := Q
  p := p
  perfect := hperf
  restriction := hres
  finiteness := hfin

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion t] in
variable {t} in
/-- If `Q|_T` is finite locally free of rank `< p` in degree `0`, so is `(Q|_{W_∞})|_T`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_derivedPullback_inclusionAtInfinity {p : ℕ}
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback t.toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q) ≅
          (DerivedCategory.singleFunctor _ 0).obj M) :=
  let ⟨M, hM, ⟨e⟩⟩ := hrank
  ⟨M, hM, ⟨derivedPullbackCompIsoOfScheme t (modificationInclusionAtInfinity f b) Q ≪≫ e⟩⟩

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion t] in
variable {t} in
/-- If `Q|_T` is zero, so is `(Q|_{W_∞})|_T`. -/
theorem isZero_derivedPullback_inclusionAtInfinity
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback t.toLRSHom.toShHom).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) :=
  hzero.of_iso (derivedPullbackCompIsoOfScheme t (modificationInclusionAtInfinity f b) Q)

/-- **The class `c'_p(Q|_{W_{Z,∞}})` of Stacks 0F9H**, for the closed cover
`W_∞ = T ∪ W_{Z,∞}` with `W_{Z,∞} = W_∞ ×_X Z`, `E₂ = Q|_{W_{Z,∞}}` the restriction of
`Q|_{W_∞}`, and `Q|_T` finite locally free of rank `< p` in degree `0`. -/
abbrev modificationInfinityChernClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl p :=
  closedCoverChernClass C (modificationProjectionAtInfinity f b ≫ f) t
    (pullback.fst (modificationProjectionAtInfinity f b) z) _ rfl
    ((hQ.derivedPullback (modificationInclusionAtInfinity f b)).derivedPullback
      (pullback.fst (modificationProjectionAtInfinity f b) z)) p
    (range_union_range_pullbackFst_eq_univ z t hT)
    (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd t _
      (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_inclusionAtInfinity C f b hrank))

/-- A class on `W_∞` equal to the pushforward of the restriction (Remark 0F9Z) of a class `κ` on `W`
preserves the image of the Gysin map at infinity. -/
private theorem preservesInfinityGysinImage_of_eq_pushforward_restriction {m : ℤ}
    (κ : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjection f b) z ≫ modificationProjection f b ≫ f)
      (modificationProjection f b ≫ f) (pullback.fst (modificationProjection f b) z) rfl m)
    {A : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl m}
    (e : A = bivariantProperPushforwardOfInvertible C _ _ _ (modificationInfinityRestrictionMap z)
        (pullback.fst (modificationProjectionAtInfinity f b) z)
        (by rw [← Category.assoc, modificationInfinityRestrictionMap_fst]) rfl m
        ((bivariantClassCongrBase C (gysinSystemOfInvertible C)
          (pullback.snd (pullback.fst (modificationProjection f b) z)
            (modificationInclusionAtInfinity f b))
          (pullbackSnd_comp_structureMorphism_eq C _ _ _ rfl _).symm rfl
          (hv := pullbackSnd_comp_structureMorphism_eq C _ _ _ rfl _) (hv' := rfl) m
          (bivariantRestriction C (gysinSystemOfInvertible C) _ _ _ rfl
            (modificationInclusionAtInfinity f b) m
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ)).congrHom
          (modificationInfinityRestrictionMap_fst z).symm
          (by rw [← Category.assoc, modificationInfinityRestrictionMap_fst, Category.assoc]))) :
    PreservesInfinityGysinImage C f b z A := by
  rw [e]
  exact IsModificationInfinityRestriction.preservesInfinityGysinImage C f b z
    (isModificationInfinityRestriction_bivariantProperPushforward C f b z κ)

/-- **`c'_p(Q|_{W_{Z,∞}})` restricted from `c_p(W_Z ⟶ W, Q)`** (Stacks 0FB8, 0FB7, 0FB3). If
`Q|_{W ∖ W_Z}` is finite locally free of rank `< p` in degree `0` and `Q` satisfies condition (3)
of Situation 0GUJ, then `c'_p(Q|_{W_{Z,∞}})` preserves the image of the Gysin map at
infinity. -/
theorem preservesInfinityGysinImage_modificationInfinityChernClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (hperf : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q)
    (hres : ∃ M : OXMod.{u, u, u} (W.toRingedSpace.restrict
          (modificationComplementOpens b z).isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M p ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (W.toRingedSpace.ofRestrict (modificationComplementOpens b z).isOpenEmbedding)).obj
              Q ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (hfin : LocalizedChernFiniteness C (modificationProjection f b ≫ f) Q) :
    PreservesInfinityGysinImage C f b z
      (modificationInfinityChernClass C f b z t hT hQ p hrank) := by
  set S₀ := modificationSituationOf C f b z p hperf (Or.inr hres) hfin
  have h₀ : S₀.IsFiniteLocallyFreeOfRankLTOnComplement := hres
  set S' := S₀.pullback (modificationInclusionAtInfinity f b)
  set S := S'.withLargerClosed (pullback.fst (modificationProjectionAtInfinity f b) z)
    (modificationInfinityRestrictionMap z) (modificationInfinityRestrictionMap_fst z)
  have : @IsClosedImmersion T S.X t := ‹_›
  have h8 := S.closedCoverChernClass_eq_localizedChern t
    (range_union_range_pullbackFst_eq_univ z t hT)
    (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_inclusionAtInfinity C f b hrank)
  have h7 := LocalizedSituation.localizedChern_withLargerClosed (S := S')
    (i' := pullback.fst (modificationProjectionAtInfinity f b) z)
    (j := modificationInfinityRestrictionMap z) (hj := modificationInfinityRestrictionMap_fst z)
    h₀.pullback
  have h3 := S₀.bivariantRestriction_localizedChern (modificationInclusionAtInfinity f b) h₀
  exact @preservesInfinityGysinImage_of_eq_pushforward_restriction C _ _ _ f _ b _ z _ _
    (S₀.localizedChern h₀) _ ((h8.trans h7).trans (by rw [← h3]))

/-- **The class `P'_p(Q|_{W_{Z,∞}})` of Stacks 0F9H**, for the closed cover
`W_∞ = T ∪ W_{Z,∞}` with `W_{Z,∞} = W_∞ ×_X Z`, `E₂ = Q|_{W_{Z,∞}}` the restriction of
`Q|_{W_∞}`, and `Q|_T` zero. -/
abbrev modificationInfinityPowerSum
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) :
    BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl p :=
  closedCoverPowerSum C (modificationProjectionAtInfinity f b ≫ f) t
    (pullback.fst (modificationProjectionAtInfinity f b) z) _ rfl
    ((hQ.derivedPullback (modificationInclusionAtInfinity f b)).derivedPullback
      (pullback.fst (modificationProjectionAtInfinity f b) z)) p
    (range_union_range_pullbackFst_eq_univ z t hT)
    (isZero_derivedPullback_of_isZero_of_comp_eq pullback.condition
      (isZero_derivedPullback_inclusionAtInfinity C f b hzero))

/-- **`P'_p(Q|_{W_{Z,∞}})` restricted from `P_p(W_Z ⟶ W, Q)`** (Stacks 0FB8, 0FB7, 0FB3). If
`Q|_{W ∖ W_Z}` is zero and `Q` satisfies condition (3) of Situation 0GUJ, then
`P'_p(Q|_{W_{Z,∞}})` preserves the image of the Gysin map at infinity. -/
theorem preservesInfinityGysinImage_modificationInfinityPowerSum
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q))
    (hperf : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q)
    (hres : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (W.toRingedSpace.ofRestrict (modificationComplementOpens b z).isOpenEmbedding)).obj Q))
    (hfin : LocalizedChernFiniteness C (modificationProjection f b ≫ f) Q) :
    PreservesInfinityGysinImage C f b z
      (modificationInfinityPowerSum C f b z t hT hQ p hzero) := by
  set S₀ := modificationSituationOf C f b z p hperf (Or.inl hres) hfin
  have h₀ : S₀.IsZeroOnComplement := hres
  set S' := S₀.pullback (modificationInclusionAtInfinity f b)
  set S := S'.withLargerClosed (pullback.fst (modificationProjectionAtInfinity f b) z)
    (modificationInfinityRestrictionMap z) (modificationInfinityRestrictionMap_fst z)
  have : @IsClosedImmersion T S.X t := ‹_›
  have h8 := S.closedCoverPowerSum_eq_localizedPowerSum t
    (range_union_range_pullbackFst_eq_univ z t hT)
    (isZero_derivedPullback_inclusionAtInfinity C f b hzero) p
  have h7 := LocalizedSituation.localizedPowerSum_withLargerClosed (S := S')
    (i' := pullback.fst (modificationProjectionAtInfinity f b) z)
    (j := modificationInfinityRestrictionMap z) (hj := modificationInfinityRestrictionMap_fst z)
    h₀.pullback p
  have h3 := S₀.bivariantRestriction_localizedPowerSum (modificationInclusionAtInfinity f b) h₀ p
  exact @preservesInfinityGysinImage_of_eq_pushforward_restriction C _ _ _ f _ b _ z _ _
    (S₀.localizedPowerSum h₀ p) _ ((h8.trans h7).trans (by rw [← h3]))

/-- The extension `(c_p(Q)|_{W_{Z,∞}})'` of the construction of Stacks 0F9K is the class
`c'_p(Q|_{W_{Z,∞}})` of Stacks 0F9H: the restriction of `c_p(Q)` to `W_{Z,∞}` is
`c_p(Q|_{W_{Z,∞}})`. -/
theorem modificationExtension_perfectChernClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    modificationExtension z t hT (vanishesOver_perfectChernClass_of_rankLT C
        (modificationProjection f b ≫ f) (t ≫ modificationInclusionAtInfinity f b) hQ p hrank) =
      modificationInfinityChernClass C f b z t hT hQ p hrank := by
  unfold modificationExtension modificationInfinityChernClass closedCoverChernClass
  apply closedCoverExtension_congr
  case ha =>
    exact BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
      (BivariantClass.VanishesOver.chowCohomologyRestriction_modificationInclusionAtInfinity t
        (vanishesOver_perfectChernClass_of_rankLT C _ _ hQ p hrank))
  case ha' =>
    exact vanishesOver_perfectChernClass_of_rankLT C _ _ _ p
      (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd t _
        (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_inclusionAtInfinity C f b hrank))
  rw [← res_perfectChernClass_derivedPullback_of_comp_eq C
      (modificationProjectionAtInfinity f b ≫ f)
      (hQ.derivedPullback (modificationInclusionAtInfinity f b))
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl,
    ← res_perfectChernClass_derivedPullback_of_comp_eq C (modificationProjection f b ≫ f) hQ
      (sX' := modificationProjectionAtInfinity f b ≫ f) (modificationInclusionAtInfinity f b) rfl]
  rfl

/-- The extension `(P_p(Q)|_{W_{Z,∞}})'` of the construction of Stacks 0F9K is the class
`P'_p(Q|_{W_{Z,∞}})` of Stacks 0F9H. -/
theorem modificationExtension_perfectPowerSumClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) :
    modificationExtension z t hT (vanishesOver_perfectPowerSumClass_of_isZero C
        (modificationProjection f b ≫ f) (t ≫ modificationInclusionAtInfinity f b) hQ p hzero) =
      modificationInfinityPowerSum C f b z t hT hQ p hzero := by
  unfold modificationExtension modificationInfinityPowerSum closedCoverPowerSum
  apply closedCoverExtension_congr
  case ha =>
    exact BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
      (BivariantClass.VanishesOver.chowCohomologyRestriction_modificationInclusionAtInfinity t
        (vanishesOver_perfectPowerSumClass_of_isZero C _ _ hQ p hzero))
  case ha' =>
    exact vanishesOver_perfectPowerSumClass_of_isZero C _ _ _ p
      (isZero_derivedPullback_of_isZero_of_comp_eq pullback.condition
        (isZero_derivedPullback_inclusionAtInfinity C f b hzero))
  change _ = perfectPowerSum C _ _ p p
  rw [← res_perfectPowerSum_derivedPullback C (modificationProjectionAtInfinity f b ≫ f)
      (hQ.derivedPullback (modificationInclusionAtInfinity f b))
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl _ p,
    ← res_perfectPowerSum_derivedPullback C (modificationProjection f b ≫ f) hQ
      (sX' := modificationProjectionAtInfinity f b ≫ f) (modificationInclusionAtInfinity f b) rfl _
      p]
  rfl

end Factor

/-! ### Stacks 0FE7 -/

section Composite

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  {ι : Type*} {Z : ι → Scheme.{u}} (z : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (z i)]
  {T : ι → Scheme.{u}} (t : ∀ i, T i ⟶ modificationFibreAtInfinity f b)
  [∀ i, IsClosedImmersion (t i)] {Q : ι → DerivedCategory W.Modules}
  (hQ : ∀ i, HasDefinedChernClasses (Q i)) (p : ι → ℕ)
  (hT : ∀ i w, modificationProjectionAtInfinity f b w ∉ Set.range (z i) → w ∈ Set.range (t i))

/-- **Composites of the classes `c'`.** Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over
`𝐀¹_X`, and for every index `i` let `Z_i ⊆ X` and `T_i ⊆ W_∞` be closed, `Q_i ∈ D(𝒪_W)` perfect
with defined Chern classes and `p_i ≥ 0`, such that the hypotheses of Stacks 0F9K hold for
`b, Z_i, Q_i, T_i, p_i` (`T_i` contains every point of `W_∞` over `X ∖ Z_i` and `Q_i|_{T_i}` is
finite locally free of rank `< p_i` in degree `0`), `Q_i|_{W ∖ W_i}` is finite locally free of rank
`< p_i` in degree `0` for `W_i = b^{-1}(𝐏¹_{Z_i}) = W ×_X Z_i`, and `Q_i` satisfies condition (3)
of Situation 0GUJ. Then for every sequence of indices `i_1, …, i_n` (`n ≥ 1`; the list
`L = [i_n, …, i_2]` and the first index `i_1`)

  `c'_{p_{i_n}}(Q_{i_n}) ∘ ⋯ ∘ c'_{p_{i_1}}(Q_{i_1}) =
    (W_{i_n,∞} ∩ ⋯ ∩ W_{i_1,∞} ⟶ Z_{i_n} ∩ ⋯ ∩ Z_{i_1})_* ∘
      c'_{p_{i_n}}(Q_{i_n}|_{W_{i_n,∞}}) ∘ ⋯ ∘ c'_{p_{i_1}}(Q_{i_1}|_{W_{i_1,∞}}) ∘ C`

in `A^{p_{i_n} + ⋯ + p_{i_1}}(Z_{i_n} ∩ ⋯ ∩ Z_{i_1} ⟶ X)`. Here `c'_p(Q)` is the class of
Stacks 0F9K (`Stacks.Chow.modificationChernClass`), `c'_p(Q|_{W_{i,∞}})` that of Stacks 0F9H
(`Stacks.Chow.modificationInfinityChernClass`), `C` the class of Stacks 0F9J, the composites are
the products of classes supported on closed subschemes of Stacks 0FE5
(`Stacks.Chow.supportedComposite`, `Stacks.Chow.modificationInfinityComposite`), and the right
side is `Stacks.Chow.modificationLocalization`. -/
@[stacks 0FE7 "the statement for c': c'_{p_n}(Q_n) ∘ ⋯ ∘ c'_{p_1}(Q_1) = \
(W_{n,∞} ∩ ⋯ ∩ W_{1,∞} → Z_n ∩ ⋯ ∩ Z_1)_* ∘ c'_{p_n}(Q_n|_{W_{n,∞}}) ∘ ⋯ ∘ \
c'_{p_1}(Q_1|_{W_{1,∞}}) ∘ C, for every sequence of indices i_1, …, i_n"]
theorem supportedComposite_modificationChernClass
    (hrank : ∀ i, ∃ M : (T i).Modules, IsFiniteLocallyFreeOfRankLT M (p i) ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t i ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj (Q i) ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (hperf : ∀ i, Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) (Q i))
    (hres : ∀ i, ∃ M : OXMod.{u, u, u} (W.toRingedSpace.restrict
          (modificationComplementOpens b (z i)).isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M (p i) ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (W.toRingedSpace.ofRestrict (modificationComplementOpens b (z i)).isOpenEmbedding)).obj
              (Q i) ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (hfin : ∀ i, LocalizedChernFiniteness C (modificationProjection f b ≫ f) (Q i)) (i₁ : ι)
    (L : List ι) :
    supportedComposite z C f (fun i ↦ (p i : ℤ))
        (fun i ↦ modificationChernClass C f b hA (z i) (t i) (hQ i) (p i) (hT i) (hrank i)) i₁ L =
      modificationLocalization C f b hA (iteratedIntersection z i₁ L).2
        (modificationInfinityComposite z C f (fun i ↦ (p i : ℤ)) b
          (fun i ↦ modificationInfinityChernClass C f b (z i) (t i) (hT i) (hQ i) (p i) (hrank i))
          i₁ L) :=
  supportedComposite_eq_modificationLocalization z C f _ b hA _ _
    (fun i ↦ (localizedModificationClass_eq_modificationLocalization C f b hA (z i) (t i) (hT i)
      _).trans (by rw [modificationExtension_perfectChernClass]))
    (fun i ↦ preservesInfinityGysinImage_modificationInfinityChernClass C f b (z i) (t i) (hT i)
      (hQ i) (p i) (hrank i) (hperf i) (hres i) (hfin i)) i₁ L

/-- **Composites of the classes `P'`.** In the situation of
`Stacks.Chow.supportedComposite_modificationChernClass`, with `Q_i|_{T_i}` and `Q_i|_{W ∖ W_i}`
zero instead of finite locally free of rank `< p_i`, for every sequence of indices
`i_1, …, i_n` (`n ≥ 1`)

  `P'_{p_{i_n}}(Q_{i_n}) ∘ ⋯ ∘ P'_{p_{i_1}}(Q_{i_1}) =
    (W_{i_n,∞} ∩ ⋯ ∩ W_{i_1,∞} ⟶ Z_{i_n} ∩ ⋯ ∩ Z_{i_1})_* ∘
      P'_{p_{i_n}}(Q_{i_n}|_{W_{i_n,∞}}) ∘ ⋯ ∘ P'_{p_{i_1}}(Q_{i_1}|_{W_{i_1,∞}}) ∘ C`

in `A^{p_{i_n} + ⋯ + p_{i_1}}(Z_{i_n} ∩ ⋯ ∩ Z_{i_1} ⟶ X)`, with `P'_p(Q)` the class of
Stacks 0F9K (`Stacks.Chow.modificationPowerSum`) and `P'_p(Q|_{W_{i,∞}})` that of Stacks 0F9H
(`Stacks.Chow.modificationInfinityPowerSum`). -/
@[stacks 0FE7 "the statement for P': P'_{p_n}(Q_n) ∘ ⋯ ∘ P'_{p_1}(Q_1) = \
(W_{n,∞} ∩ ⋯ ∩ W_{1,∞} → Z_n ∩ ⋯ ∩ Z_1)_* ∘ P'_{p_n}(Q_n|_{W_{n,∞}}) ∘ ⋯ ∘ \
P'_{p_1}(Q_1|_{W_{1,∞}}) ∘ C, for every sequence of indices i_1, …, i_n"]
theorem supportedComposite_modificationPowerSum
    (hzero : ∀ i, IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t i ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj (Q i)))
    (hperf : ∀ i, Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) (Q i))
    (hres : ∀ i, IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (W.toRingedSpace.ofRestrict (modificationComplementOpens b (z i)).isOpenEmbedding)).obj
          (Q i)))
    (hfin : ∀ i, LocalizedChernFiniteness C (modificationProjection f b ≫ f) (Q i)) (i₁ : ι)
    (L : List ι) :
    supportedComposite z C f (fun i ↦ (p i : ℤ))
        (fun i ↦ modificationPowerSum C f b hA (z i) (t i) (hQ i) (p i) (hT i) (hzero i)) i₁ L =
      modificationLocalization C f b hA (iteratedIntersection z i₁ L).2
        (modificationInfinityComposite z C f (fun i ↦ (p i : ℤ)) b
          (fun i ↦ modificationInfinityPowerSum C f b (z i) (t i) (hT i) (hQ i) (p i) (hzero i))
          i₁ L) :=
  supportedComposite_eq_modificationLocalization z C f _ b hA _ _
    (fun i ↦ (localizedModificationClass_eq_modificationLocalization C f b hA (z i) (t i) (hT i)
      _).trans (by rw [modificationExtension_perfectPowerSumClass]))
    (fun i ↦ preservesInfinityGysinImage_modificationInfinityPowerSum C f b (z i) (t i) (hT i)
      (hQ i) (p i) (hzero i) (hperf i) (hres i) (hfin i)) i₁ L

end Composite

end Stacks.Chow

end
