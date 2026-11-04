module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.DefinedChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseWhitney
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.DefinedChernRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Triangle

/-!
# The total localized Chern class of a perfect object

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : Z ⟶ X` be a closed
immersion of schemes locally of finite type over `S`, and let `E ∈ D(𝒪_X)` be perfect, with
defined Chern classes, whose restriction to `X ∖ Z` is a finite locally free module of rank `< p`
placed in degree `0`. Remark 0FBC writes

  `c⁽ᵖ⁾(Z ⟶ X, E) = 1 + c₁(E) + … + c_{p-1}(E) + c_p(Z ⟶ X, E) + c_{p+1}(Z ⟶ X, E) + …`

in `A⁽ᵖ⁾(Z ⟶ X)`. This file defines that element for the Chern classes of `E` and its localized
Chern classes, the classes of Remark 0GUK (`Stacks.Chow.LocalizedChernData.localizedChern`), which
in Situation 0GUJ are those of Stacks 0FB2. It then computes the pushforward of its components to
`A^*(X)` and its restriction along a morphism `X' ⟶ X`, and proves the two halves of Stacks 0FBD
that do not depend on the deformation argument of its proof: the identity in the degrees
`< p₁ + p₃`, and the reduction of the identity in the degrees `≥ p₁ + p₃` to an envelope.

## Main definitions

* `Stacks.Chow.LocalizedChernData.localizedChernOfLe` — `c_i(Z ⟶ X, E)` in an integer degree
  `i ≥ p`.
* `Stacks.Chow.LocalizedChernData.totalLocalizedChern` — the class `c⁽ᵖ⁾(Z ⟶ X, E)`, the class
  `Stacks.Chow.LocalizedChernData.totalLocalizedChernClass` of Remark 0FBC at these families.
* `Stacks.Chow.LocalizedChernData.withObject` — the data of a localized Chern class with the
  closed immersion of given data and another object.

## Main results

* `Stacks.Chow.LocalizedChernData.totalLocalizedChern_fst`,
  `Stacks.Chow.LocalizedChernData.totalLocalizedChern_snd` — its components.
* `Stacks.Chow.LocalizedChernData.localizedGradingPush_totalLocalizedChern` — its pushed components
  are the Chern classes of `E`.
* `Stacks.Chow.LocalizedChernData.localizedGradingRestriction_totalLocalizedChern` — its
  restriction along `f : X' ⟶ X` is `c⁽ᵖ⁾(Z ×_X X' ⟶ X', Lf^*E)`.
* `Stacks.Chow.LocalizedChernData.totalLocalizedChern_triangle_fst` — the components of degree
  `< p₁ + p₃` of Stacks 0FBD.
* `Stacks.Chow.LocalizedChernData.totalLocalizedChern_snd_eq_of_isEnvelope` — the components of
  degree `≥ p₁ + p₃` of the identity of Stacks 0FBD may be checked after restriction along an
  envelope.

## Implementation notes

Data of a localized Chern class which differ only in the object and the cutoff are written
`Stacks.Chow.LocalizedChernData.withObject`, that is
`{ D with E := _, p := _, perfect := _, restriction := _ }`, so that their classes lie in groups
`A⁽ᵖ⁾(Z ⟶ X)` built from the same closed immersion and can be multiplied.

## References

* [Stacks Project, Tag 0FBC](https://stacks.math.columbia.edu/tag/0FBC)
* [Stacks Project, Tag 0FBD](https://stacks.math.columbia.edu/tag/0FBD)
* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

namespace LocalizedChernData

variable (D : LocalizedChernData.{u})

/-- A rank bound `< p` on `E|_{X ∖ Z}` is a rank bound `< q` for every `q ≥ p`. -/
theorem IsFiniteLocallyFreeOfRankLTOnComplement.ofLe
    {D : LocalizedChernData.{u}} (h : D.IsFiniteLocallyFreeOfRankLTOnComplement) {q : ℕ}
    (hq : D.p ≤ q) : (D.ofLe hq).IsFiniteLocallyFreeOfRankLTOnComplement :=
  h.imp fun _ hM => ⟨hM.1.mono hq, hM.2⟩

variable {D} (hE : HasDefinedChernClasses D.E) (h : D.IsFiniteLocallyFreeOfRankLTOnComplement)

/-- **The localized Chern class `c_i(Z ⟶ X, E)` in an integer degree `i ≥ p`**: the class of
Remark 0GUK for the data at the cutoff `i`. -/
def localizedChernOfLe (i : {i : ℤ // (D.p : ℤ) ≤ i}) :
    BivariantClass D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl i.1 :=
  bivariantClassDegreeCongr D.base _ (D.i ≫ D.a) D.a D.i rfl
    (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg D.p) i.2))
    ((D.ofLe (q := i.1.toNat) (by have := i.2; omega)).localizedChern hE (h.ofLe _))

/-- **Stacks 0FBC for a perfect object: the total localized Chern class**
`c⁽ᵖ⁾(Z ⟶ X, E) ∈ A⁽ᵖ⁾(Z ⟶ X)`. Its component in a degree `0 ≤ i < p` is the Chern class
`c_i(E) ∈ Aⁱ(X)`, in a negative degree it is `0`, and in a degree `i ≥ p` it is the localized Chern
class `c_i(Z ⟶ X, E) ∈ Aⁱ(Z ⟶ X)` of Remark 0GUK (of Stacks 0FB2 in Situation 0GUJ). -/
def totalLocalizedChern :
    localizedBivariantGrading D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl D.p :=
  LocalizedChernData.totalLocalizedChernClass D (gysinSystemOfInvertible D.base)
    (fun i => (perfectChernClass D.base D.a hE).intComponent D.base D.a i.1)
    (localizedChernOfLe hE h)

/-- The components of `c⁽ᵖ⁾(Z ⟶ X, E)` below the cutoff are the Chern classes of `E` (zero in the
negative degrees). -/
theorem totalLocalizedChern_fst (i : {i : ℤ // i < (D.p : ℤ)}) :
    (totalLocalizedChern hE h).1 i =
      (perfectChernClass D.base D.a hE).intComponent D.base D.a i.1 := by
  by_cases h0 : 0 ≤ i.1
  · exact LocalizedChernData.totalLocalizedChernClass_fst_of_nonneg D _ _ _ i.2 h0
  · rw [TotalChowClass.intComponent_of_neg _ (not_le.mp h0)]
    exact LocalizedChernData.totalLocalizedChernClass_fst_of_neg D _ _ _ i.2 (not_le.mp h0)

/-- The components of `c⁽ᵖ⁾(Z ⟶ X, E)` from the cutoff on are the localized Chern classes. -/
theorem totalLocalizedChern_snd (i : {i : ℤ // (D.p : ℤ) ≤ i}) :
    (totalLocalizedChern hE h).2 i = localizedChernOfLe hE h i :=
  rfl

/-- **The pushed components of `c⁽ᵖ⁾(Z ⟶ X, E)` are the Chern classes of `E`**: in a degree
`i < p` the component is `c_i(E)`, and in a degree `i ≥ p` its pushforward `i_* ∘ c_i(Z ⟶ X, E)`
to `Aⁱ(X)` is `c_i(E)` (Stacks 0FB2, equation 0FB1, for the classes of Remark 0GUK,
`Stacks.Chow.LocalizedChernData.properPushforwardChowCohomology_localizedChern`). -/
theorem localizedGradingPush_totalLocalizedChern (n : ℤ) :
    localizedGradingPush D.base (D.i ≫ D.a) D.a D.i rfl (totalLocalizedChern hE h) n =
      (perfectChernClass D.base D.a hE).intComponent D.base D.a n := by
  rcases lt_or_ge n (D.p : ℤ) with hn | hn
  · rw [localizedGradingPush_of_lt _ hn]
    exact totalLocalizedChern_fst hE h ⟨n, hn⟩
  · have hq : D.p ≤ n.toNat := by omega
    have key : properPushforwardChowCohomology D.base D.a (D.i ≫ D.a) D.i rfl
        ((D.ofLe hq).localizedChern hE (h.ofLe hq)) = perfectChernClass D.base D.a hE n.toNat :=
      properPushforwardChowCohomology_localizedChern (D := D.ofLe hq) hE (h.ofLe hq)
    rw [localizedGradingPush_of_le _ hn, totalLocalizedChern_snd, localizedChernOfLe]
    refine (properPushforwardChowCohomology_bivariantClassDegreeCongr _ _).trans ?_
    refine (congrArg _ key).trans ?_
    rw [TotalChowClass.intComponent, dite_eq_left (by omega)]

/-- **The restriction of `c⁽ᵖ⁾(Z ⟶ X, E)` along `f : X' ⟶ X`** (componentwise, Stacks 0B7F and
Stacks 0F9Z, `Stacks.Chow.localizedGradingRestriction`) is `c⁽ᵖ⁾(Z' ⟶ X', Lf^*E)`, for
`Z' = Z ×_X X'`: on the components of degree `< p` by the compatibility of the Chern classes of
`E` with base change, and on those of degree `≥ p` by Stacks 0FB3 for the classes of Remark 0GUK
(`Stacks.Chow.LocalizedChernData.supportedRestriction_localizedChern`). -/
theorem localizedGradingRestriction_totalLocalizedChern {X' : Scheme.{u}} (f : X' ⟶ D.X)
    [LocallyOfFiniteType f] :
    localizedGradingRestriction D.base (D.i ≫ D.a) D.a D.i rfl f (totalLocalizedChern hE h) =
      totalLocalizedChern (D := D.pullback f) (hE.derivedPullback f) h.pullback := by
  refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
  · rw [localizedGradingRestriction_fst, totalLocalizedChern_fst, totalLocalizedChern_fst,
      TotalChowClass.chowCohomologyRestriction_intComponent f,
      res_perfectChernClass_derivedPullback_of_comp_eq D.base D.a hE f rfl (hE.derivedPullback f)]
  · have hq : D.p ≤ n.1.toNat := by have := n.2; omega
    have : LocallyOfFiniteType (X := X') (Y := (D.ofLe hq).X) f := ‹LocallyOfFiniteType f›
    have key : supportedRestriction D.base (D.i ≫ D.a) D.a D.i rfl f
        ((D.ofLe hq).localizedChern hE (h.ofLe hq)) =
          ((D.pullback f).ofLe hq).localizedChern (hE.derivedPullback f) (h.pullback.ofLe hq) :=
      supportedRestriction_localizedChern (D := D.ofLe hq) hE (h.ofLe hq) f
    rw [localizedGradingRestriction_snd, totalLocalizedChern_snd, totalLocalizedChern_snd,
      localizedChernOfLe, localizedChernOfLe]
    exact (supportedRestriction_bivariantClassDegreeCongr _ _ _ _ _ f _ _).trans (congrArg _ key)

/-! ### Data with the same closed immersion and another object -/

/-- **The data of a localized Chern class for another object**, with the closed immersion
`Z ⟶ X` of `D`: a perfect object `E` of `D(𝒪_X)` whose restriction to `X ∖ Z` is a finite locally
free module of rank `< q` placed in degree `0`, at the cutoff `q`. It is
`{ D with E := E, p := q, perfect := hE, restriction := Or.inr h }`; the classes of data of this
form for several objects lie in groups `A⁽ᵖ⁾(Z ⟶ X)` built from the same closed immersion. -/
abbrev withObject (D : LocalizedChernData.{u}) (E : DerivedCategory D.X.Modules) (q : ℕ)
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E)
    (h : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
    IsFiniteLocallyFreeOfRankLT M q ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    LocalizedChernData.{u} :=
  { D with E := E, p := q, perfect := hE, restriction := Or.inr h }

/-- The restriction of the object of `D.withObject E q hE h` to `X ∖ Z` is finite locally free of
rank `< q` in degree `0`. -/
theorem isFiniteLocallyFreeOfRankLTOnComplement_withObject (D : LocalizedChernData.{u})
    {E : DerivedCategory D.X.Modules} {q : ℕ}
    {hE : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E}
    (h : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
    IsFiniteLocallyFreeOfRankLT M q ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    (D.withObject E q hE h).IsFiniteLocallyFreeOfRankLTOnComplement :=
  h

/-! ### Towards Stacks 0FBD -/

section Triangle

variable (D : LocalizedChernData.{u}) {E₁ E₂ E₃ : DerivedCategory D.X.Modules} {p₁ p₃ : ℕ}
  (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₁)
  (h₂ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₂)
  (h₃ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₃)
  (r₁ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
  IsFiniteLocallyFreeOfRankLT M p₁ ∧
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          D.X.Opens).isOpenEmbedding)).obj E₁ ≅
        (DerivedCategory.singleFunctor _ 0).obj M))
  (r₂ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
  IsFiniteLocallyFreeOfRankLT M (p₁ + p₃) ∧
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          D.X.Opens).isOpenEmbedding)).obj E₂ ≅
        (DerivedCategory.singleFunctor _ 0).obj M))
  (r₃ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
  IsFiniteLocallyFreeOfRankLT M p₃ ∧
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          D.X.Opens).isOpenEmbedding)).obj E₃ ≅
        (DerivedCategory.singleFunctor _ 0).obj M))
  (d₁ : HasDefinedChernClasses E₁) (d₂ : HasDefinedChernClasses E₂)
  (d₃ : HasDefinedChernClasses E₃)

/-- **The components of degree `< p₁ + p₃` of Stacks 0FBD.** Let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a
distinguished triangle of perfect objects of `D(𝒪_X)` satisfying a condition of Stacks 0F9F, with
`E₁|_{X ∖ Z}`, `E₂|_{X ∖ Z}`, `E₃|_{X ∖ Z}` finite locally free of rank `< p₁`, `< p₁ + p₃`, `< p₃`
in degree `0`. Then the components of degree `n < p₁ + p₃` of `c^{(p₁+p₃)}(Z ⟶ X, E₂)` and of
`c^{(p₁)}(Z ⟶ X, E₁) c^{(p₃)}(Z ⟶ X, E₃)` agree: the first is `c_n(E₂)`, the second is
`∑_{i + j = n} c_i(E₁) c_j(E₃)` (the pushed components being the Chern classes,
`Stacks.Chow.LocalizedChernData.localizedGradingPush_totalLocalizedChern`), and the two are equal
by Stacks 0F9F. -/
theorem totalLocalizedChern_triangle_fst (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (c : E₃ ⟶ E₁⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a b c ∈ distTriang _) (hc : HasTriangleChernCondition a)
    (n : {n : ℤ // n < ((p₁ + p₃ : ℕ) : ℤ)}) :
    (totalLocalizedChern (D := D.withObject E₂ (p₁ + p₃) h₂ r₂) d₂
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₂)).1 n =
      (localizedGradingMul D.base (D.i ≫ D.a) D.a D.i rfl
        (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
        (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃))).1 n := by
  rw [localizedGradingMul_fst, totalLocalizedChern_fst,
    perfectChernClass_triangle D.base D.a (Triangle.mk a b c) hT h₁ h₂ h₃ hc d₁ d₂ d₃,
    TotalChowClass.intComponent_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [localizedGradingPush_totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁ _,
    localizedGradingPush_totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃ _]

/-- **The envelope reduction of Stacks 0FBD, in the degrees `≥ p₁ + p₃`.** Let `E₁`, `E₂`, `E₃` be
perfect objects of `D(𝒪_X)` with defined Chern classes and with `E₁|_{X ∖ Z}`, `E₂|_{X ∖ Z}`,
`E₃|_{X ∖ Z}` finite locally free of rank `< p₁`, `< p₁ + p₃`, `< p₃` in degree `0`, and let
`f : Y ⟶ X` be an envelope. If in a degree `n ≥ p₁ + p₃` the component of
`c^{(p₁+p₃)}(Z_Y ⟶ Y, Lf^*E₂)` is that of `c^{(p₁)}(Z_Y ⟶ Y, Lf^*E₁) c^{(p₃)}(Z_Y ⟶ Y, Lf^*E₃)`,
`Z_Y = Z ×_X Y`, then the same holds on `X`: restriction along `f` commutes with the
multiplication of Stacks 0FA0 (`Stacks.Chow.localizedGradingRestriction_localizedGradingMul`) and
takes the classes on `X` to those on `Y`
(`Stacks.Chow.LocalizedChernData.localizedGradingRestriction_totalLocalizedChern`), and it is
injective since `f` is an envelope (Stacks 0GUC). -/
theorem totalLocalizedChern_snd_eq_of_isEnvelope {Y : Scheme.{u}} (f : Y ⟶ D.X)
    [LocallyOfFiniteType f] (hf : IsEnvelope f) (n : {n : ℤ // ((p₁ + p₃ : ℕ) : ℤ) ≤ n})
    (hY : (totalLocalizedChern (D := (D.withObject E₂ (p₁ + p₃) h₂ r₂).pullback f)
        (d₂.derivedPullback f)
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₂).pullback).2 n =
      (localizedGradingMul D.base (pullback.snd D.i f ≫ (f ≫ D.a)) (f ≫ D.a) (pullback.snd D.i f)
        rfl
        (totalLocalizedChern (D := (D.withObject E₁ p₁ h₁ r₁).pullback f) (d₁.derivedPullback f)
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁).pullback)
        (totalLocalizedChern (D := (D.withObject E₃ p₃ h₃ r₃).pullback f) (d₃.derivedPullback f)
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃).pullback)).2 n) :
    (totalLocalizedChern (D := D.withObject E₂ (p₁ + p₃) h₂ r₂) d₂
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₂)).2 n =
      (localizedGradingMul D.base (D.i ≫ D.a) D.a D.i rfl
        (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
        (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃))).2 n := by
  refine supportedRestriction_injective_of_isEnvelope (C := D.base) (sZ := D.i ≫ D.a) (sX := D.a)
    (i := D.i) (hi := rfl) (f := f) hf ?_
  have e₂ := congrArg (fun a => a.2 n) (localizedGradingRestriction_totalLocalizedChern
    (D := D.withObject E₂ (p₁ + p₃) h₂ r₂) d₂
    (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₂) f)
  have em := congrArg (fun a => a.2 n) (localizedGradingRestriction_localizedGradingMul
    (C := D.base) (sZ := D.i ≫ D.a) (sX := D.a) (i := D.i) (hi := rfl) (f := f)
    (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁
      (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
    (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃
      (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃)))
  rw [localizedGradingRestriction_totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁ _ f,
    localizedGradingRestriction_totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃ _ f] at em
  exact e₂.trans (hY.trans em.symm)

end Triangle

end LocalizedChernData

end Stacks.Chow

end
