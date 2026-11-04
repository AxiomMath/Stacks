module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.DefinedChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationProduct

/-!
# Vanishing of the localized power sums of high degree on a quasi-compact scheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and quasi-compact, let `i : Z ⟶ X` be a closed immersion and let
`E ∈ D(𝒪_X)` be perfect with `E|_{X ∖ Z}` zero. The last sentence of Stacks 0FET asserts that the
localized Chern character `ch(Z ⟶ X, E)` lies in `A^*(Z ⟶ X) ⊗ 𝐐`, that is, the localized power
sums `P_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)` vanish for all large `p`. This file proves it, for the classes
of Stacks 0FB2 in Situation 0GUJ and for the classes of Remark 0GUK, and the same for the
localized Chern classes `c_p(Z ⟶ X, E)` when `E|_{X ∖ Z}` is finite locally free of bounded rank
in degree `0`.

The localized classes are those of Stacks 0F9K for the graph construction `b : W ⟶ 𝐏¹_X`, `Q` of
`E`: they are built from `P_p(Q) ∈ A^p(W)`, resp. `c_p(Q)`, by restriction, extension along a
closed cover and composition, all additive, so the class built from `0` is `0`. As `W` is proper
over `X`, it is quasi-compact, and `P_p(Q)` and `c_p(Q)` vanish for large `p`
(`Stacks.Chow.exists_perfectPowerSumClass_eq_zero`,
`Stacks.Chow.exists_perfectChernClass_eq_zero`). The bound depends only on `Q`, not on the closed
subscheme of `W_∞` used in the construction. In Remark 0GUK the class is that of Stacks 0FB2 for
the situation of the quasi-compact scheme `X`.

## Main results

* `Stacks.Chow.localizedModificationClass_eq_zero` — the localized class of the zero class is zero.
* `Stacks.Chow.exists_modificationPowerSum_eq_zero`,
  `Stacks.Chow.exists_modificationChernClass_eq_zero` — the classes `P'_p(Q)` and `c'_p(Q)` of
  Stacks 0F9K vanish for large `p`.
* `Stacks.Chow.LocalizedSituation.exists_localizedPowerSum_eq_zero`,
  `Stacks.Chow.LocalizedSituation.exists_localizedChernChar_eq_zero`,
  `Stacks.Chow.LocalizedSituation.exists_localizedChern_ofLe_eq_zero` — the last sentence of
  Stacks 0FET for the classes of Stacks 0FB2.
* `Stacks.Chow.LocalizedChernData.exists_localizedPowerSum_eq_zero`,
  `Stacks.Chow.LocalizedChernData.exists_localizedChernChar_eq_zero`,
  `Stacks.Chow.LocalizedChernData.exists_localizedChern_ofLe_eq_zero` — the same for the classes of
  Remark 0GUK.

## Implementation notes

The localized Chern class `c_q(Z ⟶ X, E)` is formed in the situation whose cutoff is the degree
`q`; the vanishing is stated for the situations `Stacks.Chow.LocalizedSituation.ofLe` at the
cutoffs `q ≥ p`, which differ from the given one only in the degree.

## References

* [Stacks Project, Tag 0FET](https://stacks.math.columbia.edu/tag/0FET)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0FB5](https://stacks.math.columbia.edu/tag/0FB5)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The localized class of the zero class -/

section Modification

variable {C : ChowSituation.{u}} {X W Z T : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f]
  {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  (D : GysinAtInfinityData C (gysinSystemOfInvertible C) f b hA)
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {p : ℤ}

/-- **The localized class of the zero class is zero.** -/
theorem localizedModificationClass_eq_zero
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b)) (h : q = 0) :
    localizedModificationClass D z t hT hq = 0 := by
  subst h
  have h2 := localizedModificationClass_add D z t hT hq hq
  rw [localizedModificationClass_congr D z t hT (add_zero 0) (hq.add hq) hq] at h2
  exact left_eq_add.mp h2

end Modification

/-! ### The classes `P'_p(Q)` and `c'_p(Q)` -/

section Preparation

variable (C : ChowSituation.{u}) {X W Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (z : Z ⟶ X) [IsClosedImmersion z] {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q)

/-- The modification `W` of `𝐏¹_X` is quasi-compact if `X` is: it is proper over `X`. -/
theorem compactSpace_of_gysinAtInfinityData [CompactSpace X] {G : GysinSystem C}
    (D : GysinAtInfinityData C G f b hA) : CompactSpace W :=
  have : IsProper (modificationProjection f b) := D.properModification
  QuasiCompact.compactSpace_of_compactSpace (modificationProjection f b)

/-- **The class `P'_p(Q)` of Stacks 0F9K vanishes when `P_p(Q)` does**: the construction takes the
zero class to zero. -/
theorem modificationPowerSum_eq_zero {T : Scheme.{u}} (t : T ⟶ modificationFibreAtInfinity f b)
    [IsClosedImmersion t] (p : ℕ)
    (hp : perfectPowerSumComponent C (modificationProjection f b ≫ f) hQ p = 0) (hT hzero) :
    modificationPowerSum C f b hA z t hQ p hT hzero = 0 :=
  localizedModificationClass_eq_zero (gysinAtInfinityData C f b hA) z t hT
    (vanishesOver_perfectPowerSumClass_of_isZero C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ p hzero) hp

/-- **The class `c'_p(Q)` of Stacks 0F9K vanishes when `c_p(Q)` does**: the construction takes the
zero class to zero. -/
theorem modificationChernClass_eq_zero {T : Scheme.{u}} (t : T ⟶ modificationFibreAtInfinity f b)
    [IsClosedImmersion t] (p : ℕ)
    (hp : perfectChernClass C (modificationProjection f b ≫ f) hQ p = 0) (hT hrank) :
    modificationChernClass C f b hA z t hQ p hT hrank = 0 :=
  localizedModificationClass_eq_zero (gysinAtInfinityData C f b hA) z t hT
    (vanishesOver_perfectChernClass_of_rankLT C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ p hrank) hp

/-- **The class `P'_p(Q)` of Stacks 0F9K vanishes for large `p` when `X` is quasi-compact**: it is
built from `P_p(Q) ∈ A^p(W)`, which vanishes for large `p` since `W` is proper over `X`, hence
quasi-compact (Stacks 0FET), and the construction takes the zero class to zero. The bound does not
depend on the closed subscheme `T ⊆ W_∞`. -/
theorem exists_modificationPowerSum_eq_zero [CompactSpace X] :
    ∃ N, ∀ p ≥ N, ∀ {T : Scheme.{u}} (t : T ⟶ modificationFibreAtInfinity f b)
      [IsClosedImmersion t] (hT hzero), modificationPowerSum C f b hA z t hQ p hT hzero = 0 := by
  have := compactSpace_of_gysinAtInfinityData C f b hA (gysinAtInfinityData C f b hA)
  obtain ⟨N, hN⟩ := exists_perfectPowerSumClass_eq_zero C (modificationProjection f b ≫ f) hQ
  exact ⟨N, fun p hp _ t _ _ _ ↦ modificationPowerSum_eq_zero C f b hA z hQ t p (hN p hp) _ _⟩

/-- **The class `c'_p(Q)` of Stacks 0F9K vanishes for large `p` when `X` is quasi-compact**, as
`Stacks.Chow.exists_modificationPowerSum_eq_zero`, from `c_p(Q) ∈ A^p(W)`. -/
theorem exists_modificationChernClass_eq_zero [CompactSpace X] :
    ∃ N, ∀ p ≥ N, ∀ {T : Scheme.{u}} (t : T ⟶ modificationFibreAtInfinity f b)
      [IsClosedImmersion t] (hT hrank), modificationChernClass C f b hA z t hQ p hT hrank = 0 := by
  have := compactSpace_of_gysinAtInfinityData C f b hA (gysinAtInfinityData C f b hA)
  obtain ⟨N, hN⟩ := exists_perfectChernClass_eq_zero C (modificationProjection f b ≫ f) hQ
  exact ⟨N, fun p hp _ t _ _ _ ↦ modificationChernClass_eq_zero C f b hA z hQ t p (hN p hp) _ _⟩

end Preparation

/-! ### The classes of the graph construction -/

section Graph

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
  (z : Z ⟶ X) [IsClosedImmersion z] (hQ : HasDefinedChernClasses (graphObject f E hE))

/-- **`P_p(Z ⟶ X, E) = 0` for large `p` when `X` is quasi-compact**, for the class of the graph
construction attached to any closed subscheme `T ⊆ W_∞`. -/
theorem exists_graphPowerSumClass_eq_zero [CompactSpace X] :
    ∃ N, ∀ p ≥ N, ∀ {T : Scheme.{u}}
      (t : T ⟶ modificationFibreAtInfinity f (graphBlowupToBase f E hE)) [IsClosedImmersion t]
      (hH hT hrk), graphPowerSumClass C f E hE z t hH hQ p hT hrk = 0 := by
  obtain ⟨N, hN⟩ := exists_modificationPowerSum_eq_zero C f (graphBlowupToBase f E hE)
    (isIso_pullback_snd_graphBlowupToBase f E hE) z hQ
  exact ⟨N, fun p hp _ t _ hH _ _ ↦ hN p hp ((graphZeroLocus f E hE t hH).ι ≫ t) _ _⟩

/-- **`c_p(Z ⟶ X, E) = 0` for large `p` when `X` is quasi-compact**, for the class of the graph
construction attached to any closed subscheme `T ⊆ W_∞`. -/
theorem exists_graphChernClass_eq_zero [CompactSpace X] :
    ∃ N, ∀ p ≥ N, ∀ {T : Scheme.{u}}
      (t : T ⟶ modificationFibreAtInfinity f (graphBlowupToBase f E hE)) [IsClosedImmersion t]
      (hH hT hrk), graphChernClass C f E hE z t hH hQ p hT hrk = 0 := by
  obtain ⟨N, hN⟩ := exists_modificationChernClass_eq_zero C f (graphBlowupToBase f E hE)
    (isIso_pullback_snd_graphBlowupToBase f E hE) z hQ
  exact ⟨N, fun p hp _ t _ hH _ _ ↦ hN p hp ((graphSmallRankLocus f E hE t hH p).ι ≫ t) _ _⟩

end Graph

/-! ### The localized classes of Stacks 0FB2 and of Remark 0GUK -/

namespace LocalizedSituation

variable (S : LocalizedSituation.{u})

/-- **Stacks 0FET, the localized power sums.** In Situation 0GUJ with `X` quasi-compact and
`E|_{X ∖ Z}` zero, `P_p(Z ⟶ X, E) = 0` in `A^p(Z ⟶ X)` for all large `p`. -/
theorem exists_localizedPowerSum_eq_zero [CompactSpace S.X] (h : S.IsZeroOnComplement) :
    ∃ N, ∀ p ≥ N, S.localizedPowerSum h p = 0 := by
  obtain ⟨N, hN⟩ := exists_graphPowerSumClass_eq_zero S.base S.a S.E S.perfect S.i
    S.hasDefinedChernClasses_graphObject
  exact ⟨N, fun p hp ↦ hN p hp S.graphSubschemeι _ _ _⟩

/-- **Stacks 0FET, the localized Chern character.** In Situation 0GUJ with `X` quasi-compact and
`E|_{X ∖ Z}` zero, `ch_p(Z ⟶ X, E) = 0` in `A^p(Z ⟶ X) ⊗ 𝐐` for all large `p`: the localized
Chern character lies in `A^*(Z ⟶ X) ⊗ 𝐐`. -/
theorem exists_localizedChernChar_eq_zero [CompactSpace S.X] (h : S.IsZeroOnComplement) :
    ∃ N, ∀ p ≥ N, S.localizedChernChar h p = 0 := by
  obtain ⟨N, hN⟩ := S.exists_localizedPowerSum_eq_zero h
  exact ⟨N, fun p hp ↦ by rw [localizedChernChar_apply, hN p hp, TensorProduct.tmul_zero]⟩

/-- **Stacks 0FET, the localized Chern classes.** In Situation 0GUJ with `X` quasi-compact and
`E|_{X ∖ Z}` finite locally free of rank `< p` in degree `0`, the localized Chern classes
`c_q(Z ⟶ X, E)` of the situation at the larger cutoffs `q ≥ p`
(`Stacks.Chow.LocalizedSituation.ofLe`) vanish for all large `q`. -/
theorem exists_localizedChern_ofLe_eq_zero [CompactSpace S.X] :
    ∃ N, ∀ (q : ℕ) (hq : S.p ≤ q), N ≤ q →
      ∀ h : (S.ofLe hq).IsFiniteLocallyFreeOfRankLTOnComplement,
        (S.ofLe hq).localizedChern h = 0 := by
  obtain ⟨N, hN⟩ := exists_graphChernClass_eq_zero S.base S.a S.E S.perfect S.i
    S.hasDefinedChernClasses_graphObject
  exact ⟨N, fun q hq hNq _ ↦ @hN q hNq _ (S.ofLe hq).graphSubschemeι
    (S.ofLe hq).isClosedImmersion_graphSubschemeι _ _ _⟩

end LocalizedSituation

namespace LocalizedChernData

variable (D : LocalizedChernData.{u})

/-- On a quasi-compact scheme the data of a localized Chern class form a situation of Stacks 0GUJ,
through the first finiteness alternative. -/
abbrev toSituationOfCompactSpace [CompactSpace D.X] : LocalizedSituation.{u} where
  toLocalizedChernData := D
  finiteness := Or.inl ‹_›

/-- **Stacks 0FET, the localized power sums of Remark 0GUK.** If `X` is quasi-compact, `E|_{X ∖ Z}`
is zero and the Chern classes of `E` are defined, then `P_p(Z ⟶ X, E) = 0` in `A^p(Z ⟶ X)` for all
large `p`: the class is that of Stacks 0FB2 for the situation of the quasi-compact scheme `X`. -/
theorem exists_localizedPowerSum_eq_zero [CompactSpace D.X] (hE : HasDefinedChernClasses D.E)
    (h : D.IsZeroOnComplement) : ∃ N, ∀ p ≥ N, D.localizedPowerSum hE h p = 0 := by
  obtain ⟨N, hN⟩ := D.toSituationOfCompactSpace.exists_localizedPowerSum_eq_zero h
  exact ⟨N, fun p hp ↦
    (D.toSituationOfCompactSpace.localizedPowerSum_toLocalizedChernData h p).trans (hN p hp)⟩

/-- **Stacks 0FET, the localized Chern character of Remark 0GUK.** If `X` is quasi-compact,
`E|_{X ∖ Z}` is zero and the Chern classes of `E` are defined, then `ch_p(Z ⟶ X, E) = 0` in
`A^p(Z ⟶ X) ⊗ 𝐐` for all large `p`. -/
theorem exists_localizedChernChar_eq_zero [CompactSpace D.X] (hE : HasDefinedChernClasses D.E)
    (h : D.IsZeroOnComplement) : ∃ N, ∀ p ≥ N, D.localizedChernChar hE h p = 0 := by
  obtain ⟨N, hN⟩ := D.exists_localizedPowerSum_eq_zero hE h
  exact ⟨N, fun p hp ↦ by rw [localizedChernChar, hN p hp, TensorProduct.tmul_zero]⟩

/-- **Stacks 0FET, the localized Chern classes of Remark 0GUK.** If `X` is quasi-compact, the
Chern classes of `E` are defined and `E|_{X ∖ Z}` is finite locally free of rank `< p` in degree
`0`, then the localized Chern classes `c_q(Z ⟶ X, E)` of the data at the larger cutoffs `q ≥ p`
vanish for all large `q`. -/
theorem exists_localizedChern_ofLe_eq_zero [CompactSpace D.X] (hE : HasDefinedChernClasses D.E) :
    ∃ N, ∀ (q : ℕ) (hq : D.p ≤ q), N ≤ q →
      ∀ h : (D.toSituationOfCompactSpace.ofLe hq).IsFiniteLocallyFreeOfRankLTOnComplement,
        (D.toSituationOfCompactSpace.ofLe hq).toLocalizedChernData.localizedChern hE h = 0 := by
  obtain ⟨N, hN⟩ := D.toSituationOfCompactSpace.exists_localizedChern_ofLe_eq_zero
  exact ⟨N, fun q hq hNq h ↦
    ((D.toSituationOfCompactSpace.ofLe hq).localizedChern_toLocalizedChernData h).trans
      (hN q hq hNq h)⟩

end LocalizedChernData

end Stacks.Chow

end
