module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.PullbackCase

/-!
# Localized Chern classes and the localized Chern character

Let `(S, δ)`, `X`, `i : Z ⟶ X`, `E ∈ D(𝒪_X)` and `p ≥ 0` be as in Situation 0GUJ
(`Stacks.Chow.LocalizedSituation`). Let `b : W ⟶ 𝐏¹_X` and `Q ∈ D(𝒪_W)` be the graph
construction for `E` (More on Flatness, Section 0F8Z), and let `T ⟶ W_∞` be the closed immersion
of Stacks 0F90 (3), (4). Following the proof of Stacks 0FB2, the localized classes are

  `P_p(Z ⟶ X, E) = P'_p(Q) ∈ A^p(Z ⟶ X)`,   resp.   `c_p(Z ⟶ X, E) = c'_p(Q) ∈ A^p(Z ⟶ X)`,

the classes of Stacks 0F9K for `W`, `b`, `Q` and the open and closed `T' ⊆ T` on which `Q` is zero,
resp. finite locally free of rank `< p` in degree `0`, and

  `i_* ∘ P_p(Z ⟶ X, E) = P_p(E)`,   resp.   `i_* ∘ c_p(Z ⟶ X, E) = c_p(E)`.

When `E|_{X ∖ Z}` is zero the localized Chern character of Definition 0FB5 is
`ch(Z ⟶ X, E) = ∑_p P_p(Z ⟶ X, E)/p! ∈ ∏_p A^p(Z ⟶ X) ⊗ 𝐐`.

The construction needs the Chern classes of `Q` to be defined (Stacks 0F9E). The second paragraph
of the proof of Stacks 0FB2 checks this under each of the finiteness alternatives (a)-(d) of
Situation 0GUJ (3): `Stacks.Chow.LocalizedSituation.hasDefinedChernClasses_graphObject`, so the
classes take no further input.

## Main definitions

* `Stacks.Chow.LocalizedChernData.IsZeroOnComplement`,
  `Stacks.Chow.LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement` — the two
  alternatives of condition (2) of Situation 0GUJ, read on the situation through the
  abbreviations `Stacks.Chow.LocalizedSituation.IsZeroOnComplement` and
  `Stacks.Chow.LocalizedSituation.IsFiniteLocallyFreeOfRankLTOnComplement`.
* `Stacks.Chow.LocalizedSituation.graphSubscheme`,
  `Stacks.Chow.LocalizedSituation.graphSubschemeι` — the closed subscheme `T ⊆ W_∞` of
  Stacks 0F90 (3), (4) for the graph construction of `E`.
* `Stacks.Chow.LocalizedSituation.localizedPowerSum` — `P_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)`, when
  `E|_{X ∖ Z}` is zero, for every `p ≥ 0`.
* `Stacks.Chow.LocalizedSituation.localizedChern` — `c_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)`, when
  `E|_{X ∖ Z}` is finite locally free of rank `< p` in degree `0`.
* `Stacks.Chow.LocalizedSituation.localizedChernChar` — `ch(Z ⟶ X, E)`, when `E|_{X ∖ Z}` is
  zero.

## Main results

* `Stacks.Chow.LocalizedSituation.properPushforwardChowCohomology_localizedPowerSum`,
  `Stacks.Chow.LocalizedSituation.properPushforwardChowCohomology_localizedChern` —
  `i_* ∘ P_p(Z ⟶ X, E) = P_p(E)` and `i_* ∘ c_p(Z ⟶ X, E) = c_p(E)`.
* `Stacks.Chow.graphPowerSumClass_eq`, `Stacks.Chow.graphChernClass_eq` and
  `Stacks.Chow.LocalizedSituation.localizedPowerSum_eq_graphPowerSumClass`,
  `Stacks.Chow.LocalizedSituation.localizedChern_eq_graphChernClass` — the classes do
  not depend on the choice of the closed subscheme `T ⊆ W_∞`.

## Implementation notes

The closed subscheme `T` is a choice among those Stacks 0F90 (3), (4) provide. The classes do not
depend on it: by the first assertion of Stacks 0FAU (`Stacks.Chow.localizedModificationClass_eq`),
the class of Stacks 0F9K depends on the closed subscheme of `W_∞` only through the fact that it
contains `W_∞ ×_X (X ∖ Z)`; see `Stacks.Chow.graphPowerSumClass_eq`.

The four finiteness alternatives of Situation 0GUJ (3) enter only through the definedness of the
Chern classes of `Q`, `Stacks.Chow.LocalizedSituation.hasDefinedChernClasses_graphObject`, which
the classes use; the two alternatives of condition (2) are the hypotheses
`Stacks.Chow.LocalizedSituation.IsZeroOnComplement` (for `P_p` and `ch`) and
`Stacks.Chow.LocalizedSituation.IsFiniteLocallyFreeOfRankLTOnComplement` (for `c_p`), the "resp."
of the source.

The class `P_p(Z ⟶ X, E)` is defined for every degree `p`, as in Definition 0FB5 (1): when
`E|_{X ∖ Z}` is zero the construction does not involve the degree of the situation. The class
`c_p(Z ⟶ X, E)` is in the degree `p` of the situation, which is the bound on the rank.

## References

* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0FB5](https://stacks.math.columbia.edu/tag/0FB5)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F90](https://stacks.math.columbia.edu/tag/0F90)
* [Stacks Project, Tag 0FAU](https://stacks.math.columbia.edu/tag/0FAU)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Independence of the closed subscheme of the fibre at infinity -/

section Independence

variable (C : ChowSituation.{u}) {X Z T T' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
  (z : Z ⟶ X) [IsClosedImmersion z]
  (t : T ⟶ modificationFibreAtInfinity f (graphBlowupToBase f E hE)) [IsClosedImmersion t]
  (t' : T' ⟶ modificationFibreAtInfinity f (graphBlowupToBase f E hE)) [IsClosedImmersion t']
  (hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (graphObjectRestrictHomology f E hE t n))
  (hH' : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (graphObjectRestrictHomology f E hE t' n))
  (hQ : HasDefinedChernClasses (graphObject f E hE)) (p : ℕ)
  (hT : ∀ w, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) w ∉ Set.range z →
    w ∈ Set.range t)
  (hT' : ∀ w, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) w ∉ Set.range z →
    w ∈ Set.range t')

/-- **`P_p(Z ⟶ X, E)` does not depend on the closed subscheme `T ⊆ W_∞`.** The classes
`Stacks.Chow.graphPowerSumClass` attached to two closed subschemes of `W_∞` with the properties
the construction uses agree: both are the class of Stacks 0F9K at the class `P_p(Q)`, which by the
first assertion of Stacks 0FAU depends only on `W_∞ ×_X (X ∖ Z)` lying in the closed subscheme. -/
theorem graphPowerSumClass_eq
    (hrk : ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z → ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0)
    (hrk' : ∀ τ : T', modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t' τ) ∉
      Set.range z → ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T' _ (hH' n) τ = 0) :
    graphPowerSumClass C f E hE z t hH hQ p hT hrk =
      graphPowerSumClass C f E hE z t' hH' hQ p hT' hrk' := by
  unfold graphPowerSumClass modificationPowerSum
  apply localizedModificationClass_eq <;>
    exact vanishesOver_perfectPowerSumClass_of_isZero C _ _ hQ p
      (isZero_derivedPullback_graphZeroLocus f E hE _ _)

/-- **`c_p(Z ⟶ X, E)` does not depend on the closed subscheme `T ⊆ W_∞`.** As
`Stacks.Chow.graphPowerSumClass_eq`, for the classes `Stacks.Chow.graphChernClass`. -/
theorem graphChernClass_eq
    (hrk : ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) τ < p)
    (hrk' : ∀ τ : T', modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t' τ) ∉
      Set.range z →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T' _ (hH' n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T' _ (hH' 0) τ < p) :
    graphChernClass C f E hE z t hH hQ p hT hrk =
      graphChernClass C f E hE z t' hH' hQ p hT' hrk' := by
  unfold graphChernClass modificationChernClass
  apply localizedModificationClass_eq <;>
    exact vanishesOver_perfectChernClass_of_rankLT C _ _ hQ p
      (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_graphSmallRankLocus f E hE _ _ p)

end Independence

namespace LocalizedChernData

variable (D : LocalizedChernData.{u})

/-! ### The two alternatives of condition (2) -/

/-- The first alternative of condition (2) of Situation 0GUJ: `E|_{X ∖ Z}` is zero. -/
def IsZeroOnComplement : Prop :=
  IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj D.E)

/-- The second alternative of condition (2) of Situation 0GUJ: `E|_{X ∖ Z}` is a finite locally
free module of rank `< p` placed in degree `0`. -/
def IsFiniteLocallyFreeOfRankLTOnComplement : Prop :=
  ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
    IsFiniteLocallyFreeOfRankLT M D.p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj D.E ≅
          (DerivedCategory.singleFunctor _ 0).obj M)

end LocalizedChernData

namespace LocalizedSituation

variable (S : LocalizedSituation.{u})

/-! ### The two alternatives of condition (2) -/

/-- The first alternative of condition (2) of Situation 0GUJ: `E|_{X ∖ Z}` is zero
(`Stacks.Chow.LocalizedChernData.IsZeroOnComplement` of the data of the situation). -/
abbrev IsZeroOnComplement : Prop :=
  S.toLocalizedChernData.IsZeroOnComplement

/-- The second alternative of condition (2) of Situation 0GUJ: `E|_{X ∖ Z}` is a finite locally
free module of rank `< p` placed in degree `0`
(`Stacks.Chow.LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement` of the data of the
situation). -/
abbrev IsFiniteLocallyFreeOfRankLTOnComplement : Prop :=
  S.toLocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement

/-- Condition (2) of Situation 0GUJ: one of its two alternatives holds. -/
theorem isZeroOnComplement_or :
    S.IsZeroOnComplement ∨ S.IsFiniteLocallyFreeOfRankLTOnComplement :=
  S.restriction

/-- **Near every point of `X ∖ Z` all cohomology sheaves of `E` are finite locally free**, under
either alternative of condition (2) of Situation 0GUJ. -/
theorem exists_isFiniteLocallyFree_pullback_homology :
    ∀ x ∉ Set.range S.i, ∃ V : S.X.Opens, x ∈ V ∧ ∀ n : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj
          ((DerivedCategory.homologyFunctor S.X.Modules n).obj S.E)) := by
  intro x hx
  rcases S.isZeroOnComplement_or with h | h
  · obtain ⟨V, hxV, hV⟩ := S.exists_isZero_pullback_homology h x hx
    refine ⟨V, hxV, fun n => ?_⟩
    exact (isFiniteLocallyFreeOfRank_zero_of_isZero (hV n)).isFiniteLocallyFree
  · obtain ⟨V, hxV, ⟨r, -, hr⟩, hV⟩ :=
      S.exists_isFiniteLocallyFreeOfRank_pullback_homology h x hx
    refine ⟨V, hxV, fun n => ?_⟩
    rcases eq_or_ne n 0 with rfl | hn
    · exact hr.isFiniteLocallyFree
    · exact (isFiniteLocallyFreeOfRank_zero_of_isZero (hV n hn)).isFiniteLocallyFree

/-! ### The closed subscheme of the fibre at infinity -/

/-- The closed subscheme `T ⊆ W_∞` of Stacks 0F90 (3), (4) for the graph construction of `E`,
as a scheme. -/
def graphSubscheme : Scheme.{u} :=
  (exists_closedImmersion_graphObjectRestrict S.a S.E S.perfect).choose

/-- The closed immersion `T ⟶ W_∞` of Stacks 0F90 (3), (4) for the graph construction of `E`. -/
def graphSubschemeι :
    S.graphSubscheme ⟶ modificationFibreAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect) :=
  (exists_closedImmersion_graphObjectRestrict S.a S.E S.perfect).choose_spec.choose

/-- The morphism `T ⟶ W_∞` given by `graphSubschemeι` is a closed immersion. -/
instance isClosedImmersion_graphSubschemeι : IsClosedImmersion S.graphSubschemeι :=
  (exists_closedImmersion_graphObjectRestrict S.a S.E S.perfect).choose_spec.choose_spec.1

/-- The cohomology sheaves of the restriction of `Q` to `T` are finite locally free. -/
theorem isFiniteLocallyFree_graphObjectRestrictHomology (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (graphObjectRestrictHomology S.a S.E S.perfect S.graphSubschemeι n) :=
  (exists_closedImmersion_graphObjectRestrict S.a S.E S.perfect).choose_spec.choose_spec.2.2.choose
    n

/-- **Every point of `W_∞` over `X ∖ Z` lies in `T`**: clause (3) of Stacks 0F90 and condition
(2) of Situation 0GUJ. -/
theorem mem_range_graphSubschemeι :
    ∀ w, modificationProjectionAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect) w ∉
      Set.range S.i → w ∈ Set.range S.graphSubschemeι :=
  mem_range_of_notMem_range_of_isFiniteLocallyFree S.a S.E S.perfect S.i S.graphSubschemeι
    (exists_closedImmersion_graphObjectRestrict S.a S.E
      S.perfect).choose_spec.choose_spec.2.2.choose_spec.1
    S.exists_isFiniteLocallyFree_pullback_homology

/-- **If `E|_{X ∖ Z}` is zero, all cohomology sheaves of `Q|_T` have rank `0` at the points of
`T` over `X ∖ Z`**: clause (4) of Stacks 0F90. -/
theorem finiteLocallyFreeRank_graphSubscheme_eq_zero (h : S.IsZeroOnComplement) :
    ∀ τ : S.graphSubscheme, modificationProjectionAtInfinity S.a
      (graphBlowupToBase S.a S.E S.perfect) (S.graphSubschemeι τ) ∉ Set.range S.i →
      ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank S.graphSubscheme _
        (S.isFiniteLocallyFree_graphObjectRestrictHomology n) τ = 0 :=
  finiteLocallyFreeRank_eq_zero_of_isZero S.a S.E S.perfect S.i S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology
    (exists_closedImmersion_graphObjectRestrict S.a S.E
      S.perfect).choose_spec.choose_spec.2.2.choose_spec.2
    (S.exists_isZero_pullback_homology h)

/-- **If `E|_{X ∖ Z}` is finite locally free of rank `< p` in degree `0`, then at the points of
`T` over `X ∖ Z` the sheaf `H^n(Q|_T)` has rank `0` for `n ≠ 0` and `H^0(Q|_T)` has rank `< p`**:
clause (4) of Stacks 0F90. -/
theorem finiteLocallyFreeRank_graphSubscheme_lt (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    ∀ τ : S.graphSubscheme, modificationProjectionAtInfinity S.a
      (graphBlowupToBase S.a S.E S.perfect) (S.graphSubschemeι τ) ∉ Set.range S.i →
      (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank S.graphSubscheme _
        (S.isFiniteLocallyFree_graphObjectRestrictHomology n) τ = 0) ∧
        @Scheme.Modules.finiteLocallyFreeRank S.graphSubscheme _
          (S.isFiniteLocallyFree_graphObjectRestrictHomology 0) τ < S.p :=
  finiteLocallyFreeRank_lt_of_isFiniteLocallyFreeOfRank S.a S.E S.perfect S.i S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology
    (exists_closedImmersion_graphObjectRestrict S.a S.E
      S.perfect).choose_spec.choose_spec.2.2.choose_spec.2
    (S.exists_isFiniteLocallyFreeOfRank_pullback_homology h)

/-! ### The localized classes -/

/-- **The localized class `P_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)` of Stacks 0FB2 and Definition 0FB5 (1)**,
when `E|_{X ∖ Z}` is zero, for every `p ≥ 0`: the class `P'_p(Q)` of Stacks 0F9K for the graph
construction `b : W ⟶ 𝐏¹_X`, `Q` of `E` and the open and closed `T' ⊆ T ⊆ W_∞` on which `Q` is
zero, where `T ⊆ W_∞` is the closed subscheme of Stacks 0F90 (3), (4). The Chern classes of `Q`
are defined in Situation 0GUJ (`Stacks.Chow.LocalizedSituation.hasDefinedChernClasses_graphObject`,
from condition (3)). -/
@[stacks 0FB2 "P_p(Z → X, E) ∈ A^p(Z → X), when E|_{X ∖ Z} is zero",
  stacks 0FB5 "(1): P_p(Z → X, E) for every p ≥ 0, when E|_{X ∖ Z} is zero"]
abbrev localizedPowerSum (h : S.IsZeroOnComplement) (p : ℕ) :
    BivariantClass S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl p :=
  graphPowerSumClass S.base S.a S.E S.perfect S.i S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology S.hasDefinedChernClasses_graphObject p
    S.mem_range_graphSubschemeι (S.finiteLocallyFreeRank_graphSubscheme_eq_zero h)

/-- **The localized Chern class `c_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)` of Stacks 0FB2 and
Definition 0FB5 (2)**, when `E|_{X ∖ Z}` is finite locally free of rank `< p` in degree `0`: the
class `c'_p(Q)` of Stacks 0F9K for the graph construction `b : W ⟶ 𝐏¹_X`, `Q` of `E` and the open
and closed `T' ⊆ T ⊆ W_∞` on which `Q` is finite locally free of rank `< p` in degree `0`, where
`T ⊆ W_∞` is the closed subscheme of Stacks 0F90 (3), (4). The Chern classes of `Q` are defined in
Situation 0GUJ (`Stacks.Chow.LocalizedSituation.hasDefinedChernClasses_graphObject`, from
condition (3)). -/
@[stacks 0FB2 "c_p(Z → X, E) ∈ A^p(Z → X), when E|_{X ∖ Z} is finite locally free of rank < p \
    in degree 0",
  stacks 0FB5 "(2): the localized pth Chern class c_p(Z → X, E), when E|_{X ∖ Z} is finite \
    locally free of rank < p in degree 0"]
abbrev localizedChern (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    BivariantClass S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl S.p :=
  graphChernClass S.base S.a S.E S.perfect S.i S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology S.hasDefinedChernClasses_graphObject S.p
    S.mem_range_graphSubschemeι (S.finiteLocallyFreeRank_graphSubscheme_lt h)

/-- **The localized Chern character `ch(Z ⟶ X, E) = ∑_p P_p(Z ⟶ X, E)/p!` of
Definition 0FB5 (1)**, when `E|_{X ∖ Z}` is zero, as an element of
`∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐`, built from `Stacks.Chow.LocalizedSituation.localizedPowerSum`. -/
@[stacks 0FB5 "(1): the localized Chern character ch(Z → X, E) = Σ_p P_p(Z → X, E)/p! in \
    Π_{p ≥ 0} A^p(Z → X) ⊗ Q, when E|_{X ∖ Z} is zero"]
abbrev localizedChernChar (h : S.IsZeroOnComplement) (p : ℕ) :
    TensorProduct ℤ ℚ
      (BivariantClass S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl (p : ℤ)) :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] S.localizedPowerSum h p

/-- The `p`th component of `ch(Z ⟶ X, E)` is `P_p(Z ⟶ X, E)/p!`. -/
theorem localizedChernChar_apply (h : S.IsZeroOnComplement) (p : ℕ) :
    S.localizedChernChar h p = ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] S.localizedPowerSum h p :=
  rfl

/-- **`i_* ∘ P_p(Z ⟶ X, E) = P_p(E)`** (Stacks 0FB2, equation 0FB1) as bivariant classes on `X`,
with `∘` the pushforward of Stacks 0EPK, when `E|_{X ∖ Z}` is zero. -/
@[stacks 0FB2 "i_* ∘ P_p(Z → X, E) = P_p(E), when E|_{X ∖ Z} is zero"]
theorem properPushforwardChowCohomology_localizedPowerSum (h : S.IsZeroOnComplement) (p : ℕ) :
    properPushforwardChowCohomology S.base S.a (S.i ≫ S.a) S.i rfl (S.localizedPowerSum h p) =
      perfectPowerSumComponent S.base S.a S.hasDefinedChernClasses_E p :=
  properPushforwardChowCohomology_graphPowerSumClass S.base S.a S.E S.perfect S.i
    S.graphSubschemeι S.isFiniteLocallyFree_graphObjectRestrictHomology
    S.hasDefinedChernClasses_graphObject p S.mem_range_graphSubschemeι
    (S.finiteLocallyFreeRank_graphSubscheme_eq_zero h) _

/-- **`i_* ∘ c_p(Z ⟶ X, E) = c_p(E)`** (Stacks 0FB2, equation 0FB1) as bivariant classes on `X`,
with `∘` the pushforward of Stacks 0EPK, when `E|_{X ∖ Z}` is finite locally free of rank `< p`
in degree `0`. -/
@[stacks 0FB2 "i_* ∘ c_p(Z → X, E) = c_p(E), when E|_{X ∖ Z} is finite locally free of rank < p \
    in degree 0"]
theorem properPushforwardChowCohomology_localizedChern
    (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    properPushforwardChowCohomology S.base S.a (S.i ≫ S.a) S.i rfl (S.localizedChern h) =
      perfectChernClass S.base S.a S.hasDefinedChernClasses_E S.p :=
  properPushforwardChowCohomology_graphChernClass S.base S.a S.E S.perfect S.i
    S.graphSubschemeι S.isFiniteLocallyFree_graphObjectRestrictHomology
    S.hasDefinedChernClasses_graphObject S.p S.mem_range_graphSubschemeι
    (S.finiteLocallyFreeRank_graphSubscheme_lt h) _

/-- **`P_p(Z ⟶ X, E)` is the class attached to any closed subscheme `T ⊆ W_∞`** with the
properties the construction uses, not only to the chosen one. -/
theorem localizedPowerSum_eq_graphPowerSumClass (h : S.IsZeroOnComplement) (p : ℕ)
    {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect))
    [IsClosedImmersion t]
    (hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (graphObjectRestrictHomology S.a S.E S.perfect t n))
    (hT : ∀ w, modificationProjectionAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect) w ∉
      Set.range S.i → w ∈ Set.range t)
    (hrk : ∀ τ : T, modificationProjectionAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect)
      (t τ) ∉ Set.range S.i → ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) :
    S.localizedPowerSum h p =
      graphPowerSumClass S.base S.a S.E S.perfect S.i t hH S.hasDefinedChernClasses_graphObject p
        hT hrk :=
  graphPowerSumClass_eq S.base S.a S.E S.perfect S.i _ t _ hH S.hasDefinedChernClasses_graphObject
    p _ hT _ hrk

/-- **`c_p(Z ⟶ X, E)` is the class attached to any closed subscheme `T ⊆ W_∞`** with the
properties the construction uses, not only to the chosen one. -/
theorem localizedChern_eq_graphChernClass (h : S.IsFiniteLocallyFreeOfRankLTOnComplement)
    {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect))
    [IsClosedImmersion t]
    (hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (graphObjectRestrictHomology S.a S.E S.perfect t n))
    (hT : ∀ w, modificationProjectionAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect) w ∉
      Set.range S.i → w ∈ Set.range t)
    (hrk : ∀ τ : T, modificationProjectionAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect)
      (t τ) ∉ Set.range S.i →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) τ < S.p) :
    S.localizedChern h =
      graphChernClass S.base S.a S.E S.perfect S.i t hH S.hasDefinedChernClasses_graphObject S.p
        hT hrk :=
  graphChernClass_eq S.base S.a S.E S.perfect S.i _ t _ hH S.hasDefinedChernClasses_graphObject
    S.p _ hT _ hrk

end LocalizedSituation

end Stacks.Chow

end
