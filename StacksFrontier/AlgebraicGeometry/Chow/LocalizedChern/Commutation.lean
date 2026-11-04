module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseCommute
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedCap

/-!
# Localized Chern classes commute with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be locally of
finite type over `S`. This file proves the three commutation statements of the theory of localized
Chern classes, each of the form

  `a ∘ c = c ∘ a`   in   `A^*(Y ×_X Z ⟶ X)`

for a class `a ∈ A^p(Z ⟶ X)` and every bivariant class `c ∈ A^q(Y ⟶ X)` with `Y ⟶ X` locally of
finite type, where `a ∘ c = res(a) ∘ c` and `c ∘ a = res(c) ∘ a` are the composites of Stacks 0B75
with the restrictions of Stacks 0F9Z, compared on `Y ×_X Z` (Stacks 0FA2).

* **Stacks 0FAS.** For `b : W ⟶ 𝐏¹_X` proper and an isomorphism over `𝐀¹_X`, the class
  `C ∈ A⁰(W_∞ ⟶ X)` of Stacks 0F9J satisfies `C ∘ c = c ∘ C`.
* **Stacks 0FAW.** In the situation of Stacks 0F9K, `P'_p(Q) ∘ c = c ∘ P'_p(Q)`, resp.
  `c'_p(Q) ∘ c = c ∘ c'_p(Q)`. Indeed `P'_p(Q) = (E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C`; the class `C`
  commutes with `c` by Stacks 0FAS, `P'_p(Q|_E)` by Stacks 0FAJ, and a proper pushforward and a
  composite of classes commuting with every class commute with every class.
* **Stacks 0FBB.** In Situation 0GUJ, `P_p(Z ⟶ X, E) ∘ c = c ∘ P_p(Z ⟶ X, E)`, resp.
  `c_p(Z ⟶ X, E) ∘ c = c ∘ c_p(Z ⟶ X, E)`: these classes are `P'_p(Q)`, resp. `c'_p(Q)`, of
  Stacks 0F9K for the graph construction, so this is Stacks 0FAW.

## Main results

* `Stacks.Chow.nonhomogeneousBivariantTransport_compositeOfInvertible_gysinAtInfinityClass` —
  **Stacks 0FAS**, and
  `Stacks.Chow.bivariantTransport_bivariantCompositeOfInvertible_gysinAtInfinityClass`, its case
  of a homogeneous `c`.
* `Stacks.Chow.localizedModificationClass_commutesWithEveryClass` — the class
  `(E ⟶ Z)_* ∘ (q|_E)' ∘ C` of Stacks 0F9K commutes with every bivariant class as soon as
  `q|_E` is bivariant central.
* `Stacks.Chow.modificationPowerSum_commutesWithEveryClass`,
  `Stacks.Chow.modificationChernClass_commutesWithEveryClass` — so do `P'_p(Q)` and `c'_p(Q)`.
* `Stacks.Chow.nonhomogeneousBivariantTransport_compositeOfInvertible_modificationPowerSum`,
  `Stacks.Chow.nonhomogeneousBivariantTransport_compositeOfInvertible_modificationChernClass` —
  **Stacks 0FAW**;
  `Stacks.Chow.bivariantTransport_bivariantCompositeOfInvertible_modificationPowerSum`,
  `Stacks.Chow.bivariantTransport_bivariantCompositeOfInvertible_modificationChernClass` are its
  case of a homogeneous `c`.
* In the namespace `Stacks.Chow.LocalizedSituation`,
  `nonhomogeneousBivariantTransport_compositeOfInvertible_localizedPowerSum`,
  `nonhomogeneousBivariantTransport_compositeOfInvertible_localizedChern` — **Stacks 0FBB**, and
  `LocalizedSituation.bivariantTransport_bivariantCompositeOfInvertible_localizedPowerSum`,
  `LocalizedSituation.bivariantTransport_bivariantCompositeOfInvertible_localizedChern`, its
  case of a homogeneous `c`.

## Implementation notes

The equation `a ∘ c = c ∘ a` is between a class for `Z ×_X Y ⟶ X` and a class for
`Y ×_X Z ⟶ X`; the first is carried to `Y ×_X Z` along the symmetry of the fibre product
(`Stacks.Chow.bivariantTransport`), and the degrees `p + q` and `q + p` differ, whence the
heterogeneous equality. It is the image, under
`Stacks.Chow.BivariantCommute.bivariantTransport_bivariantCompositeOfInvertible_heq`, of the
assertion that `a` and `c` commute in the sense of Stacks 0FA2. For a general
`c ∈ A^*(Y ⟶ X) = ⊕_q A^q(Y ⟶ X)` the composites, restrictions and transport are their additive
extensions to the graded groups (`Stacks.Chow.nonhomogeneousBivariantCompositeOfInvertible`,
`Stacks.Chow.nonhomogeneousBivariantRestriction`, `Stacks.Chow.nonhomogeneousBivariantTransport`),
the degrees `p + q` and `q + p` are then the same summand, and the equation is an equality in
`A^*(Y ×_X Z ⟶ X)`, by
`Stacks.Chow.nonhomogeneousBivariantTransport_compositeOfInvertible_eq_of_bivariantCommute`.

## References

* [Stacks Project, Tag 0FAS](https://stacks.math.columbia.edu/tag/0FAS)
* [Stacks Project, Tag 0FAW](https://stacks.math.columbia.edu/tag/0FAW)
* [Stacks Project, Tag 0FBB](https://stacks.math.columbia.edu/tag/0FBB)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0FAJ](https://stacks.math.columbia.edu/tag/0FAJ)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Stacks 0FAS -/

section AtInfinity

variable (C : ChowSituation.{u}) {X W Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (fY : Y ⟶ X) [LocallyOfFiniteType fY] (p : ℤ)
  (c : BivariantClass C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl p)

/-- **Stacks 0FAS.** Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, let
`C ∈ A⁰(W_∞ ⟶ X)` be the class of Stacks 0F9J, let `fY : Y ⟶ X` be locally of finite type and
let `c ∈ A^p(Y ⟶ X)`. Then

  `C ∘ c = c ∘ C`   in   `A^p(W_∞ ×_X Y ⟶ X)`,

where `C ∘ c = res(C) ∘ c` and `c ∘ C = res(c) ∘ C`, the latter a class for `Y ×_X W_∞ ⟶ X`
carried to `W_∞ ×_X Y` along the symmetry of the fibre product. This is the commutation
`Stacks.Chow.gysinAtInfinityClass_bivariantCommute` of Stacks 0FA2, read on the two composites. -/
theorem bivariantTransport_bivariantCompositeOfInvertible_gysinAtInfinityClass :
    bivariantTransport C (gysinSystemOfInvertible C)
        (pullback.fst fY (modificationProjectionAtInfinity f b) ≫ (fY ≫ f))
        (pullback.fst (modificationProjectionAtInfinity f b) fY ≫
          (modificationProjectionAtInfinity f b ≫ f)) f
        (pullback.snd fY (modificationProjectionAtInfinity f b) ≫
          modificationProjectionAtInfinity f b)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (fY ≫ f) f fY rfl _) rfl)
        (pullback.snd (modificationProjectionAtInfinity f b) fY ≫ fY)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C _ f (modificationProjectionAtInfinity f b) rfl
            fY) rfl)
        (pullbackSymmetry fY (modificationProjectionAtInfinity f b))
        (by simp [pullback.condition]) (p + 0)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantCompositeOfInvertible C
          (pullback.fst fY (modificationProjectionAtInfinity f b) ≫ (fY ≫ f))
          (modificationProjectionAtInfinity f b ≫ f) f
          (pullback.snd fY (modificationProjectionAtInfinity f b))
          (modificationProjectionAtInfinity f b)
          (pullbackSnd_comp_structureMorphism_eq C (fY ≫ f) f fY rfl _) rfl p 0
          (bivariantRestriction C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl
            (modificationProjectionAtInfinity f b) p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
          (gysinAtInfinityClass C f b hA)) ≍
      bivariantCompositeOfInvertible C
        (pullback.fst (modificationProjectionAtInfinity f b) fY ≫
          (modificationProjectionAtInfinity f b ≫ f)) (fY ≫ f) f
        (pullback.snd (modificationProjectionAtInfinity f b) fY) fY
        (pullbackSnd_comp_structureMorphism_eq C _ f (modificationProjectionAtInfinity f b) rfl
          fY) rfl 0 p
        (bivariantRestriction C (gysinSystemOfInvertible C)
          (modificationProjectionAtInfinity f b ≫ f) f (modificationProjectionAtInfinity f b) rfl
          fY 0 (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (gysinAtInfinityClass C f b hA)) c :=
  BivariantCommute.bivariantTransport_bivariantCompositeOfInvertible_heq
    (BivariantCommute.symm _ _ _ _ _ _ _ _ _
      (gysinAtInfinityClass_bivariantCommute C f b hA fY p c))

/-- Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, let `C ∈ A⁰(W_∞ ⟶ X)` be the class
of Stacks 0F9J, let `fY : Y ⟶ X` be locally of finite type and let `c ∈ A^*(Y ⟶ X)`. Then

  `C ∘ c = c ∘ C`   in   `A^*(W_∞ ×_X Y ⟶ X)`,

where `C ∘ c = res(C) ∘ c` and `c ∘ C = res(c) ∘ C`, the latter a class for `Y ×_X W_∞ ⟶ X`
carried to `W_∞ ×_X Y` along the symmetry of the fibre product. -/
@[stacks 0FAS "C ∘ c = c ∘ C in A^*(W_∞ ×_X Y → X), for every c in A^*(Y → X)"]
theorem nonhomogeneousBivariantTransport_compositeOfInvertible_gysinAtInfinityClass
    (c : nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl) :
    nonhomogeneousBivariantTransport C (gysinSystemOfInvertible C)
        (pullback.fst fY (modificationProjectionAtInfinity f b) ≫ (fY ≫ f))
        (pullback.fst (modificationProjectionAtInfinity f b) fY ≫
          (modificationProjectionAtInfinity f b ≫ f)) f
        (pullback.snd fY (modificationProjectionAtInfinity f b) ≫
          modificationProjectionAtInfinity f b)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (fY ≫ f) f fY rfl _) rfl)
        (pullback.snd (modificationProjectionAtInfinity f b) fY ≫ fY)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C _ f (modificationProjectionAtInfinity f b) rfl
            fY) rfl)
        (pullbackSymmetry fY (modificationProjectionAtInfinity f b))
        (by simp [pullback.condition])
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (nonhomogeneousBivariantCompositeOfInvertible C
          (pullback.fst fY (modificationProjectionAtInfinity f b) ≫ (fY ≫ f))
          (modificationProjectionAtInfinity f b ≫ f) f
          (pullback.snd fY (modificationProjectionAtInfinity f b))
          (modificationProjectionAtInfinity f b)
          (pullbackSnd_comp_structureMorphism_eq C (fY ≫ f) f fY rfl _) rfl
          (nonhomogeneousBivariantRestriction C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl
            (modificationProjectionAtInfinity f b)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
          (DirectSum.of _ 0 (gysinAtInfinityClass C f b hA))) =
      nonhomogeneousBivariantCompositeOfInvertible C
        (pullback.fst (modificationProjectionAtInfinity f b) fY ≫
          (modificationProjectionAtInfinity f b ≫ f)) (fY ≫ f) f
        (pullback.snd (modificationProjectionAtInfinity f b) fY) fY
        (pullbackSnd_comp_structureMorphism_eq C _ f (modificationProjectionAtInfinity f b) rfl
          fY) rfl
        (DirectSum.of _ 0 (bivariantRestriction C (gysinSystemOfInvertible C)
          (modificationProjectionAtInfinity f b ≫ f) f (modificationProjectionAtInfinity f b) rfl
          fY 0 (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (gysinAtInfinityClass C f b hA))) c := by
  have h := nonhomogeneousBivariantTransport_compositeOfInvertible_eq_of_bivariantCommute c
    (DirectSum.of _ 0 (gysinAtInfinityClass C f b hA))
    (((BivariantClass.commutesWithEveryClass_iff _).2 fun _ g _ q d ↦
      gysinAtInfinityClass_bivariantCommute C f b hA g q d).bivariantCommute_apply_of c)
  rwa [nonhomogeneousBivariantRestriction_of] at h

end AtInfinity

/-! ### Stacks 0FAW -/

section Modification

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X W Z T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t]

/-- **The class of Stacks 0F9K commutes with every bivariant class.** Let `q ∈ A^p(W)` vanish
over `T`, and let its restriction `q|_E` to `E = W_∞ ×_X Z` be bivariant central. Then
`q' = (E ⟶ Z)_* ∘ (q|_E)' ∘ C ∈ A^p(Z ⟶ X)` commutes with every bivariant class: `C` does by
Stacks 0FAS, `(q|_E)'` by `Stacks.Chow.closedCoverExtension_commutesWithEveryClass`, and the
property passes to composites and proper pushforwards. -/
theorem localizedModificationClass_commutesWithEveryClass {p : ℤ}
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (hcentral : (chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (chowCohomologyRestriction C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f)
        (modificationInclusionAtInfinity f b) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q)).IsBivariantCentral) :
    (localizedModificationClass (gysinAtInfinityData C f b hA) z t hT
      hq).CommutesWithEveryClass := by
  unfold localizedModificationClass
  refine commutesWithEveryClass_bivariantProperPushforward _ _ _ _ _ ?_
  refine (BivariantClass.commutesWithEveryClass_copy _ _ _ _ _).2 ?_
  exact commutesWithEveryClass_bivariantCompositeOfInvertible _ _ _ _ _ _ _
    (closedCoverExtension_commutesWithEveryClass C (modificationProjectionAtInfinity f b ≫ f) t
      (pullback.fst (modificationProjectionAtInfinity f b) z) _ hcentral
      (range_union_range_pullbackFst_eq_univ z t hT)
      (BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
        (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t)))
    (fun _ g _ q d ↦ gysinAtInfinityClass_bivariantCommute C f b hA g q d)

variable {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q) (p : ℕ)

/-- **`P'_p(Q)` commutes with every bivariant class**, in the sense of Stacks 0FA2: the
restriction of `P_p(Q)` to `E` is `P_p(Q|_E)`, which is bivariant central by Stacks 0FAC. -/
theorem modificationPowerSum_commutesWithEveryClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) :
    (modificationPowerSum C f b hA z t hQ p hT hzero).CommutesWithEveryClass := by
  refine localizedModificationClass_commutesWithEveryClass C f b hA z t hT
    (vanishesOver_perfectPowerSumClass_of_isZero C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ p hzero) ?_
  rw [chowCohomologyRestriction_perfectPowerSumClass]
  change BivariantClass.IsBivariantCentral (chowCohomologyRestriction C
    (gysinSystemOfInvertible C)
    (modificationInclusionAtInfinity f b ≫ modificationProjection f b ≫ f)
    (pullback.fst (modificationProjectionAtInfinity f b) z) p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (perfectPowerSumComponent C
      (modificationInclusionAtInfinity f b ≫ modificationProjection f b ≫ f)
      (hQ.derivedPullback (modificationInclusionAtInfinity f b)) p))
  rw [chowCohomologyRestriction_perfectPowerSumClass
    (hQ.derivedPullback (modificationInclusionAtInfinity f b))
    (pullback.fst (modificationProjectionAtInfinity f b) z) p]
  exact isBivariantCentral_perfectPowerSumClass _ p

/-- **`c'_p(Q)` commutes with every bivariant class**, in the sense of Stacks 0FA2: the
restriction of `c_p(Q)` to `E` is `c_p(Q|_E)`, which is bivariant central by Stacks 0FAC. -/
theorem modificationChernClass_commutesWithEveryClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    (modificationChernClass C f b hA z t hQ p hT hrank).CommutesWithEveryClass := by
  refine localizedModificationClass_commutesWithEveryClass C f b hA z t hT
    (vanishesOver_perfectChernClass_of_rankLT C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ p hrank) ?_
  rw [chowCohomologyRestriction_perfectChernClass]
  change BivariantClass.IsBivariantCentral (chowCohomologyRestriction C
    (gysinSystemOfInvertible C)
    (modificationInclusionAtInfinity f b ≫ modificationProjection f b ≫ f)
    (pullback.fst (modificationProjectionAtInfinity f b) z) p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (perfectChernClass C (modificationInclusionAtInfinity f b ≫ modificationProjection f b ≫ f)
      (hQ.derivedPullback (modificationInclusionAtInfinity f b)) p))
  rw [chowCohomologyRestriction_perfectChernClass
    (hQ.derivedPullback (modificationInclusionAtInfinity f b))
    (pullback.fst (modificationProjectionAtInfinity f b) z) p]
  exact isBivariantCentral_perfectChernClass _ p

variable {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] (q : ℤ)
  (c : BivariantClass C (gysinSystemOfInvertible C) (g ≫ f) f g rfl q)

/-- **Stacks 0FAW for `P'_p`.** In the situation of Stacks 0F9K with `Q|_T` zero, let
`g : Y ⟶ X` be locally of finite type and let `c ∈ A^q(Y ⟶ X)`. Then

  `P'_p(Q) ∘ c = c ∘ P'_p(Q)`   in   `A^{p+q}(Y ×_X Z ⟶ X)`,

where `P'_p(Q) ∘ c = res(P'_p(Q)) ∘ c` is a class for `Z ×_X Y ⟶ X`, carried to `Y ×_X Z` along
the symmetry of the fibre product, and `c ∘ P'_p(Q) = res(c) ∘ P'_p(Q)`. -/
theorem bivariantTransport_bivariantCompositeOfInvertible_modificationPowerSum
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) :
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst z g ≫ (z ≫ f))
        (pullback.fst g z ≫ (g ≫ f)) f (pullback.snd z g ≫ g)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl g) rfl)
        (pullback.snd g z ≫ z)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (g ≫ f) f g rfl z) rfl)
        (pullbackSymmetry z g) (by simp [pullback.condition]) (p + q)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantCompositeOfInvertible C (pullback.fst z g ≫ (z ≫ f)) (g ≫ f) f
          (pullback.snd z g) g
          (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl g) rfl p q
          (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl g p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
            (modificationPowerSum C f b hA z t hQ p hT hzero)) c) ≍
      bivariantCompositeOfInvertible C (pullback.fst g z ≫ (g ≫ f)) (z ≫ f) f
        (pullback.snd g z) z
        (pullbackSnd_comp_structureMorphism_eq C (g ≫ f) f g rfl z) rfl q p
        (bivariantRestriction C (gysinSystemOfInvertible C) (g ≫ f) f g rfl z q
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
        (modificationPowerSum C f b hA z t hQ p hT hzero) :=
  BivariantCommute.bivariantTransport_bivariantCompositeOfInvertible_heq
    ((BivariantClass.commutesWithEveryClass_iff _).1
      (modificationPowerSum_commutesWithEveryClass C f b hA z t hQ p hT hzero) g q c)

/-- **Stacks 0FAW for `c'_p`.** In the situation of Stacks 0F9K with `Q|_T` finite locally free
of rank `< p` in degree `0`, let `g : Y ⟶ X` be locally of finite type and let `c ∈ A^q(Y ⟶ X)`.
Then

  `c'_p(Q) ∘ c = c ∘ c'_p(Q)`   in   `A^{p+q}(Y ×_X Z ⟶ X)`,

where `c'_p(Q) ∘ c = res(c'_p(Q)) ∘ c` is a class for `Z ×_X Y ⟶ X`, carried to `Y ×_X Z` along
the symmetry of the fibre product, and `c ∘ c'_p(Q) = res(c) ∘ c'_p(Q)`. -/
theorem bivariantTransport_bivariantCompositeOfInvertible_modificationChernClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst z g ≫ (z ≫ f))
        (pullback.fst g z ≫ (g ≫ f)) f (pullback.snd z g ≫ g)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl g) rfl)
        (pullback.snd g z ≫ z)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (g ≫ f) f g rfl z) rfl)
        (pullbackSymmetry z g) (by simp [pullback.condition]) (p + q)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantCompositeOfInvertible C (pullback.fst z g ≫ (z ≫ f)) (g ≫ f) f
          (pullback.snd z g) g
          (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl g) rfl p q
          (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl g p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
            (modificationChernClass C f b hA z t hQ p hT hrank)) c) ≍
      bivariantCompositeOfInvertible C (pullback.fst g z ≫ (g ≫ f)) (z ≫ f) f
        (pullback.snd g z) z
        (pullbackSnd_comp_structureMorphism_eq C (g ≫ f) f g rfl z) rfl q p
        (bivariantRestriction C (gysinSystemOfInvertible C) (g ≫ f) f g rfl z q
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
        (modificationChernClass C f b hA z t hQ p hT hrank) :=
  BivariantCommute.bivariantTransport_bivariantCompositeOfInvertible_heq
    ((BivariantClass.commutesWithEveryClass_iff _).1
      (modificationChernClass_commutesWithEveryClass C f b hA z t hQ p hT hrank) g q c)

/-- In the situation of Stacks 0F9K with `Q|_T` zero, let `g : Y ⟶ X` be locally of finite type and
let `c ∈ A^*(Y ⟶ X)`. Then

  `P'_p(Q) ∘ c = c ∘ P'_p(Q)`   in   `A^*(Y ×_X Z ⟶ X)`,

where `P'_p(Q) ∘ c = res(P'_p(Q)) ∘ c` is a class for `Z ×_X Y ⟶ X`, carried to `Y ×_X Z` along
the symmetry of the fibre product, and `c ∘ P'_p(Q) = res(c) ∘ P'_p(Q)`. -/
@[stacks 0FAW "for P'_p: P'_p(Q) ∘ c = c ∘ P'_p(Q) in A^*(Y ×_X Z → X), for every c in \
A^*(Y → X)"]
theorem nonhomogeneousBivariantTransport_compositeOfInvertible_modificationPowerSum
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q))
    (c : nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) (g ≫ f) f g rfl) :
    nonhomogeneousBivariantTransport C (gysinSystemOfInvertible C) (pullback.fst z g ≫ (z ≫ f))
        (pullback.fst g z ≫ (g ≫ f)) f (pullback.snd z g ≫ g)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl g) rfl)
        (pullback.snd g z ≫ z)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (g ≫ f) f g rfl z) rfl)
        (pullbackSymmetry z g) (by simp [pullback.condition])
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (nonhomogeneousBivariantCompositeOfInvertible C (pullback.fst z g ≫ (z ≫ f)) (g ≫ f) f
          (pullback.snd z g) g
          (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl g) rfl
          (DirectSum.of _ (p : ℤ)
            (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl g p
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
              (modificationPowerSum C f b hA z t hQ p hT hzero))) c) =
      nonhomogeneousBivariantCompositeOfInvertible C (pullback.fst g z ≫ (g ≫ f)) (z ≫ f) f
        (pullback.snd g z) z
        (pullbackSnd_comp_structureMorphism_eq C (g ≫ f) f g rfl z) rfl
        (nonhomogeneousBivariantRestriction C (gysinSystemOfInvertible C) (g ≫ f) f g rfl z
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
        (DirectSum.of _ (p : ℤ) (modificationPowerSum C f b hA z t hQ p hT hzero)) := by
  have h := nonhomogeneousBivariantTransport_compositeOfInvertible_eq_of_bivariantCommute
    (DirectSum.of _ (p : ℤ) (modificationPowerSum C f b hA z t hQ p hT hzero)) c
    fun i j ↦ BivariantCommute.symm _ _ _ _ _ _ _ _ _
      ((modificationPowerSum_commutesWithEveryClass C f b hA z t hQ p hT
        hzero).bivariantCommute_apply_of c j i)
  rwa [nonhomogeneousBivariantRestriction_of] at h

/-- In the situation of Stacks 0F9K with `Q|_T` finite locally free of rank `< p` in degree `0`,
let `g : Y ⟶ X` be locally of finite type and let `c ∈ A^*(Y ⟶ X)`. Then

  `c'_p(Q) ∘ c = c ∘ c'_p(Q)`   in   `A^*(Y ×_X Z ⟶ X)`,

where `c'_p(Q) ∘ c = res(c'_p(Q)) ∘ c` is a class for `Z ×_X Y ⟶ X`, carried to `Y ×_X Z` along
the symmetry of the fibre product, and `c ∘ c'_p(Q) = res(c) ∘ c'_p(Q)`. -/
@[stacks 0FAW "for c'_p: c'_p(Q) ∘ c = c ∘ c'_p(Q) in A^*(Y ×_X Z → X), for every c in \
A^*(Y → X)"]
theorem nonhomogeneousBivariantTransport_compositeOfInvertible_modificationChernClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (c : nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) (g ≫ f) f g rfl) :
    nonhomogeneousBivariantTransport C (gysinSystemOfInvertible C) (pullback.fst z g ≫ (z ≫ f))
        (pullback.fst g z ≫ (g ≫ f)) f (pullback.snd z g ≫ g)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl g) rfl)
        (pullback.snd g z ≫ z)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (g ≫ f) f g rfl z) rfl)
        (pullbackSymmetry z g) (by simp [pullback.condition])
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (nonhomogeneousBivariantCompositeOfInvertible C (pullback.fst z g ≫ (z ≫ f)) (g ≫ f) f
          (pullback.snd z g) g
          (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl g) rfl
          (DirectSum.of _ (p : ℤ)
            (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl g p
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
              (modificationChernClass C f b hA z t hQ p hT hrank))) c) =
      nonhomogeneousBivariantCompositeOfInvertible C (pullback.fst g z ≫ (g ≫ f)) (z ≫ f) f
        (pullback.snd g z) z
        (pullbackSnd_comp_structureMorphism_eq C (g ≫ f) f g rfl z) rfl
        (nonhomogeneousBivariantRestriction C (gysinSystemOfInvertible C) (g ≫ f) f g rfl z
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
        (DirectSum.of _ (p : ℤ) (modificationChernClass C f b hA z t hQ p hT hrank)) := by
  have h := nonhomogeneousBivariantTransport_compositeOfInvertible_eq_of_bivariantCommute
    (DirectSum.of _ (p : ℤ) (modificationChernClass C f b hA z t hQ p hT hrank)) c
    fun i j ↦ BivariantCommute.symm _ _ _ _ _ _ _ _ _
      ((modificationChernClass_commutesWithEveryClass C f b hA z t hQ p hT
        hrank).bivariantCommute_apply_of c j i)
  rwa [nonhomogeneousBivariantRestriction_of] at h

end Modification

/-! ### Stacks 0FBB -/

namespace LocalizedSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : LocalizedSituation.{u}) {Y : Scheme.{u}} (g : Y ⟶ S.X)
  [LocallyOfFiniteType g] (q : ℤ)
  (c : BivariantClass S.base (gysinSystemOfInvertible S.base) (g ≫ S.a) S.a g rfl q)

/-- **Stacks 0FBB for `P_p(Z ⟶ X, E)`.** In Situation 0GUJ with `E|_{X ∖ Z}` zero, let
`g : Y ⟶ X` be locally of finite type and let `c ∈ A^q(Y ⟶ X)`. Then

  `P_p(Z ⟶ X, E) ∘ c = c ∘ P_p(Z ⟶ X, E)`   in   `A^{p+q}(Y ×_X Z ⟶ X)`,

where `P_p(Z ⟶ X, E) ∘ c = res(P_p(Z ⟶ X, E)) ∘ c` is a class for `Z ×_X Y ⟶ X`, carried to
`Y ×_X Z` along the symmetry of the fibre product, and `c ∘ P_p(Z ⟶ X, E)` is
`res(c) ∘ P_p(Z ⟶ X, E)`. The class is `P'_p(Q)` of Stacks 0F9K for the graph construction, so
this is `Stacks.Chow.bivariantTransport_bivariantCompositeOfInvertible_modificationPowerSum`. -/
theorem bivariantTransport_bivariantCompositeOfInvertible_localizedPowerSum
    (h : S.IsZeroOnComplement) (p : ℕ) :
    bivariantTransport S.base (gysinSystemOfInvertible S.base) (pullback.fst S.i g ≫ (S.i ≫ S.a))
        (pullback.fst g S.i ≫ (g ≫ S.a)) S.a (pullback.snd S.i g ≫ g)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl g) rfl)
        (pullback.snd g S.i ≫ S.i)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq S.base (g ≫ S.a) S.a g rfl S.i) rfl)
        (pullbackSymmetry S.i g) (by simp [pullback.condition]) (p + q)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
        (bivariantCompositeOfInvertible S.base (pullback.fst S.i g ≫ (S.i ≫ S.a)) (g ≫ S.a) S.a
          (pullback.snd S.i g) g
          (pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl g) rfl p q
          (bivariantRestriction S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl g p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
            (S.localizedPowerSum h p)) c) ≍
      bivariantCompositeOfInvertible S.base (pullback.fst g S.i ≫ (g ≫ S.a)) (S.i ≫ S.a) S.a
        (pullback.snd g S.i) S.i
        (pullbackSnd_comp_structureMorphism_eq S.base (g ≫ S.a) S.a g rfl S.i) rfl q p
        (bivariantRestriction S.base (gysinSystemOfInvertible S.base) (g ≫ S.a) S.a g rfl S.i q
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base) c)
        (S.localizedPowerSum h p) :=
  let := isProper_graphBlowupToBase S.a S.E S.perfect
  let := isClosedImmersion_graphZeroLocus_ι S.a S.E S.perfect S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology
  bivariantTransport_bivariantCompositeOfInvertible_modificationPowerSum S.base S.a _ _ S.i _
    S.hasDefinedChernClasses_graphObject p g q c
    (mem_range_graphZeroLocus S.base S.a S.E S.perfect S.i S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology S.mem_range_graphSubschemeι
      (S.finiteLocallyFreeRank_graphSubscheme_eq_zero h))
    (isZero_derivedPullback_graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology)

/-- **Stacks 0FBB for `c_p(Z ⟶ X, E)`.** In Situation 0GUJ with `E|_{X ∖ Z}` finite locally free
of rank `< p` in degree `0`, let `g : Y ⟶ X` be locally of finite type and let `c ∈ A^q(Y ⟶ X)`.
Then

  `c_p(Z ⟶ X, E) ∘ c = c ∘ c_p(Z ⟶ X, E)`   in   `A^{p+q}(Y ×_X Z ⟶ X)`,

where `c_p(Z ⟶ X, E) ∘ c = res(c_p(Z ⟶ X, E)) ∘ c` is a class for `Z ×_X Y ⟶ X`, carried to
`Y ×_X Z` along the symmetry of the fibre product, and `c ∘ c_p(Z ⟶ X, E)` is
`res(c) ∘ c_p(Z ⟶ X, E)`. The class is `c'_p(Q)` of Stacks 0F9K for the graph construction, so
this is `Stacks.Chow.bivariantTransport_bivariantCompositeOfInvertible_modificationChernClass`. -/
theorem bivariantTransport_bivariantCompositeOfInvertible_localizedChern
    (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    bivariantTransport S.base (gysinSystemOfInvertible S.base) (pullback.fst S.i g ≫ (S.i ≫ S.a))
        (pullback.fst g S.i ≫ (g ≫ S.a)) S.a (pullback.snd S.i g ≫ g)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl g) rfl)
        (pullback.snd g S.i ≫ S.i)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq S.base (g ≫ S.a) S.a g rfl S.i) rfl)
        (pullbackSymmetry S.i g) (by simp [pullback.condition]) (S.p + q)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
        (bivariantCompositeOfInvertible S.base (pullback.fst S.i g ≫ (S.i ≫ S.a)) (g ≫ S.a) S.a
          (pullback.snd S.i g) g
          (pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl g) rfl S.p q
          (bivariantRestriction S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl g
            S.p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
            (S.localizedChern h)) c) ≍
      bivariantCompositeOfInvertible S.base (pullback.fst g S.i ≫ (g ≫ S.a)) (S.i ≫ S.a) S.a
        (pullback.snd g S.i) S.i
        (pullbackSnd_comp_structureMorphism_eq S.base (g ≫ S.a) S.a g rfl S.i) rfl q S.p
        (bivariantRestriction S.base (gysinSystemOfInvertible S.base) (g ≫ S.a) S.a g rfl S.i q
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base) c)
        (S.localizedChern h) :=
  let := isProper_graphBlowupToBase S.a S.E S.perfect
  let := isClosedImmersion_graphSmallRankLocus_ι S.a S.E S.perfect S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology S.p
  bivariantTransport_bivariantCompositeOfInvertible_modificationChernClass S.base S.a _ _ S.i _
    S.hasDefinedChernClasses_graphObject S.p g q c
    (mem_range_graphSmallRankLocus S.base S.a S.E S.perfect S.i S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology S.p S.mem_range_graphSubschemeι
      (S.finiteLocallyFreeRank_graphSubscheme_lt h))
    (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_graphSmallRankLocus S.a S.E S.perfect
      S.graphSubschemeι S.isFiniteLocallyFree_graphObjectRestrictHomology S.p)

/-- In Situation 0GUJ with `E|_{X ∖ Z}` zero, let `g : Y ⟶ X` be locally of finite type and let
`c ∈ A^*(Y ⟶ X)`. Then

  `P_p(Z ⟶ X, E) ∘ c = c ∘ P_p(Z ⟶ X, E)`   in   `A^*(Y ×_X Z ⟶ X)`,

where `P_p(Z ⟶ X, E) ∘ c = res(P_p(Z ⟶ X, E)) ∘ c` is a class for `Z ×_X Y ⟶ X`, carried to
`Y ×_X Z` along the symmetry of the fibre product, and `c ∘ P_p(Z ⟶ X, E)` is
`res(c) ∘ P_p(Z ⟶ X, E)`. The class is `P'_p(Q)` of Stacks 0F9K for the graph construction, so
this is `Stacks.Chow.nonhomogeneousBivariantTransport_compositeOfInvertible_modificationPowerSum`.
-/
@[stacks 0FBB "for P_p(Z → X, E), when E|_(X ∖ Z) is zero: P_p(Z → X, E) ∘ c = \
c ∘ P_p(Z → X, E) in A^*(Y ×_X Z → X), for every c in A^*(Y → X)"]
theorem nonhomogeneousBivariantTransport_compositeOfInvertible_localizedPowerSum
    (h : S.IsZeroOnComplement) (p : ℕ)
    (c : nonhomogeneousBivariantGroup S.base (gysinSystemOfInvertible S.base) (g ≫ S.a) S.a g
      rfl) :
    nonhomogeneousBivariantTransport S.base (gysinSystemOfInvertible S.base)
        (pullback.fst S.i g ≫ (S.i ≫ S.a)) (pullback.fst g S.i ≫ (g ≫ S.a)) S.a
        (pullback.snd S.i g ≫ g)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl g) rfl)
        (pullback.snd g S.i ≫ S.i)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq S.base (g ≫ S.a) S.a g rfl S.i) rfl)
        (pullbackSymmetry S.i g) (by simp [pullback.condition])
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
        (nonhomogeneousBivariantCompositeOfInvertible S.base (pullback.fst S.i g ≫ (S.i ≫ S.a))
          (g ≫ S.a) S.a (pullback.snd S.i g) g
          (pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl g) rfl
          (DirectSum.of _ (p : ℤ)
            (bivariantRestriction S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl
              g p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
              (S.localizedPowerSum h p))) c) =
      nonhomogeneousBivariantCompositeOfInvertible S.base (pullback.fst g S.i ≫ (g ≫ S.a))
        (S.i ≫ S.a) S.a (pullback.snd g S.i) S.i
        (pullbackSnd_comp_structureMorphism_eq S.base (g ≫ S.a) S.a g rfl S.i) rfl
        (nonhomogeneousBivariantRestriction S.base (gysinSystemOfInvertible S.base) (g ≫ S.a) S.a
          g rfl S.i (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base) c)
        (DirectSum.of _ (p : ℤ) (S.localizedPowerSum h p)) :=
  let := isProper_graphBlowupToBase S.a S.E S.perfect
  let := isClosedImmersion_graphZeroLocus_ι S.a S.E S.perfect S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology
  nonhomogeneousBivariantTransport_compositeOfInvertible_modificationPowerSum S.base S.a _ _ S.i _
    S.hasDefinedChernClasses_graphObject p g
    (mem_range_graphZeroLocus S.base S.a S.E S.perfect S.i S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology S.mem_range_graphSubschemeι
      (S.finiteLocallyFreeRank_graphSubscheme_eq_zero h))
    (isZero_derivedPullback_graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology) c

/-- In Situation 0GUJ with `E|_{X ∖ Z}` finite locally free of rank `< p` in degree `0`, let
`g : Y ⟶ X` be locally of finite type and let `c ∈ A^*(Y ⟶ X)`. Then

  `c_p(Z ⟶ X, E) ∘ c = c ∘ c_p(Z ⟶ X, E)`   in   `A^*(Y ×_X Z ⟶ X)`,

where `c_p(Z ⟶ X, E) ∘ c = res(c_p(Z ⟶ X, E)) ∘ c` is a class for `Z ×_X Y ⟶ X`, carried to
`Y ×_X Z` along the symmetry of the fibre product, and `c ∘ c_p(Z ⟶ X, E)` is
`res(c) ∘ c_p(Z ⟶ X, E)`. The class is `c'_p(Q)` of Stacks 0F9K for the graph construction, so
this is
`Stacks.Chow.nonhomogeneousBivariantTransport_compositeOfInvertible_modificationChernClass`. -/
@[stacks 0FBB "for c_p(Z → X, E), when E|_(X ∖ Z) is finite locally free of rank < p in \
degree 0: c_p(Z → X, E) ∘ c = c ∘ c_p(Z → X, E) in A^*(Y ×_X Z → X), for every c in \
A^*(Y → X)"]
theorem nonhomogeneousBivariantTransport_compositeOfInvertible_localizedChern
    (h : S.IsFiniteLocallyFreeOfRankLTOnComplement)
    (c : nonhomogeneousBivariantGroup S.base (gysinSystemOfInvertible S.base) (g ≫ S.a) S.a g
      rfl) :
    nonhomogeneousBivariantTransport S.base (gysinSystemOfInvertible S.base)
        (pullback.fst S.i g ≫ (S.i ≫ S.a)) (pullback.fst g S.i ≫ (g ≫ S.a)) S.a
        (pullback.snd S.i g ≫ g)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl g) rfl)
        (pullback.snd g S.i ≫ S.i)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq S.base (g ≫ S.a) S.a g rfl S.i) rfl)
        (pullbackSymmetry S.i g) (by simp [pullback.condition])
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
        (nonhomogeneousBivariantCompositeOfInvertible S.base (pullback.fst S.i g ≫ (S.i ≫ S.a))
          (g ≫ S.a) S.a (pullback.snd S.i g) g
          (pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl g) rfl
          (DirectSum.of _ (S.p : ℤ)
            (bivariantRestriction S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl
              g S.p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
              (S.localizedChern h))) c) =
      nonhomogeneousBivariantCompositeOfInvertible S.base (pullback.fst g S.i ≫ (g ≫ S.a))
        (S.i ≫ S.a) S.a (pullback.snd g S.i) S.i
        (pullbackSnd_comp_structureMorphism_eq S.base (g ≫ S.a) S.a g rfl S.i) rfl
        (nonhomogeneousBivariantRestriction S.base (gysinSystemOfInvertible S.base) (g ≫ S.a) S.a
          g rfl S.i (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base) c)
        (DirectSum.of _ (S.p : ℤ) (S.localizedChern h)) :=
  let := isProper_graphBlowupToBase S.a S.E S.perfect
  let := isClosedImmersion_graphSmallRankLocus_ι S.a S.E S.perfect S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology S.p
  nonhomogeneousBivariantTransport_compositeOfInvertible_modificationChernClass S.base S.a _ _ S.i
    _ S.hasDefinedChernClasses_graphObject S.p g
    (mem_range_graphSmallRankLocus S.base S.a S.E S.perfect S.i S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology S.p S.mem_range_graphSubschemeι
      (S.finiteLocallyFreeRank_graphSubscheme_lt h))
    (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_graphSmallRankLocus S.a S.E S.perfect
      S.graphSubschemeι S.isFiniteLocallyFree_graphObjectRestrictHomology S.p) c

end LocalizedSituation

end Stacks.Chow

end
