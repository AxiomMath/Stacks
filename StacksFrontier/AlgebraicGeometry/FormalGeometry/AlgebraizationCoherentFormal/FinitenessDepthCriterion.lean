module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.RegularSequence
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FiniteLocallyFreeComplement
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FiniteLocallyFreeComplementAffine
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.DepthDimensionCriterion
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksFrontier.RingTheory.LocalCohomology.CutoffCompletionSerre
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# Finiteness of the low-degree cohomology as a depth–dimension condition

Fix a Noetherian ring `A` with ideals `I ⊆ 𝔞`, and write `X = Spec A`, `Y = V(I)`, `Z = V(𝔞)`
and `U = X ∖ Z`. Let `(F_n)` be a coherent `I`-adic system on `U`, so that `F_1` is a coherent
module on `U ∩ Y`. The algebraization criterion Stacks 0EJS asks that `H⁰(U, F_1)` and
`H¹(U, F_1)` be finite `A`-modules. When `A` has a dualizing complex this finiteness is
equivalent to the pointwise inequality

  `depth(F_{1,y}) + dim(𝒪_{closure{y}, z}) > 2`

for every `y ∈ U ∩ Y` and every `z ∈ Z ∩ closure{y}`, by the depth–dimension criterion for
coherence of the higher direct images (Stacks 0BJY) applied with `n = 2`. The inequality holds
for instance when `F_1` is finite locally free on `𝒪_{U ∩ Y}`, `Y` satisfies `(S₂)`, and
`codim(Z', Y') ≥ 3` for every pair of irreducible components `Y'` of `Y` and `Z'` of `Z` with
`Z' ⊆ Y'`.

## Main definitions

* `Stacks.Algebraization.HasDepthDimensionAt` — the depth–dimension inequality at a value `n`,
  written over pairs of primes of `A` as Stacks 0BJY writes it.
* `Stacks.Algebraization.AffineDepthDimensionCriterion` — the criterion of Stacks 0BJY over the
  affine base, quantified over the module and over the degree.
* `Stacks.Algebraization.HasLocallyFreeCodimensionThreeCondition` — the sufficient condition of
  the remark: finite local freeness on `U ∩ Y`, property `(S₂)` for `Y`, and codimension at
  least `3` between irreducible components.
* `Stacks.Algebraization.localDimY` — the dimension of the local ring of `Y` at a point.
* `Stacks.Algebraization.PointwiseSerreTwoBound`,
  `Stacks.Algebraization.PointwiseCodimensionThreeBound` — the two pointwise bounds that the
  sufficient condition yields.

## Main results

* `Stacks.Algebraization.hasFiniteLowDegreeCohomology_iff_hasDepthDimensionAt_two` — hypothesis
  (2) of Stacks 0EJS is equivalent to the depth–dimension inequality at `2`.
* `Stacks.Algebraization.hasDepthDimensionAt_two_of_pointwiseBounds` — the sufficient condition
  of the remark gives that inequality.
* `Stacks.Algebraization.affineDepthDimensionCriterion` — the criterion of Stacks 0BJY holds
  over the affine base of an algebraization situation.

## Implementation notes

The locus `U ∩ Y` of the source appears here through the two side conditions on a prime `𝔭` of
`A` that `HasDepthDimensionAt` imposes: `¬ 𝔞 ≤ 𝔭` says `y ∈ U`, and nontriviality of `M_𝔭`
says `y ∈ Supp(F_1)`, which forces `I ≤ 𝔭` because `I` annihilates `F_1`. Likewise `z ∈ Z` is
`𝔞 ≤ 𝔮` and `z ∈ closure{y}` is `𝔭 ≤ 𝔮`, and `dim(𝒪_{closure{y}, z})` is the height of the
image of `𝔮` in `A ⧸ 𝔭`, as licensed by `topCodim_closureSingleton_eq_height_map_quotientMk`.
This is the spelling of
`Stacks.LocalCohomologySequence.forall_lt_depth_add_height_iff_forall_isCoherent_rightDerived`,
and `HasDepthDimensionAt` is its left-hand side at `n = 2` with `I := 𝔞`.

The open `U ∩ Y` is the complement in `Y = Spec(A ⧸ I)` of the vanishing locus of the image of
`𝔞`, which is the closed subset `Stacks.Algebraization.AlgebraizationSituation.closedSubsetZ`;
the irreducible components of `Y` and of `Z` are the minimal primes of `I` and of `𝔞`, and
containment of components is reversed inclusion of those primes.

Stacks 0BJY is not a hypothesis: `AffineDepthDimensionCriterion` is proved, in
`Stacks.Algebraization.affineDepthDimensionCriterion`, from
`Stacks.LocalCohomologySequence.forall_lt_depth_add_height_iff_forall_isCoherent_rightDerived`
of
`DepthDimensionCriterion.lean` in
`StacksFrontier/AlgebraicGeometry/LocalCohomology/PushforwardCoherence/`.
Of that result's two standing assumptions, universal
catenarity of `A` is discharged from the dualizing complex by Stacks 0A80, available as
`Dualizing.isUniversallyCatenary_of_isDualizingComplex` in
`StacksFrontier/RingTheory/Dualizing/UniversallyCatenary.lean:137`.

The hypotheses of the equivalence that are carried rather than discharged are these.

* `hformalOfDual`, the implication from a dualizing complex to Serre's condition `(S₂)` on the
  formal fibres of the local rings of `A`. The condition itself is
  `Stacks.LocalCohomology.FormalFibersHavePropertySk` of
  `StacksFrontier/RingTheory/LocalCohomology/CutoffCompletionSerre.lean:165`, and the library's
  only route to it is from Cohen–Macaulay formal fibres through
  `formalFibersHavePropertySk_of_cohenMacaulay` in
  `StacksFrontier/RingTheory/LocalCohomology/FaltingsFiniteness.lean:416`, which is `private`; no
  declaration derives either from a dualizing complex. This is the only place the dualizing
  complex is not able to pay its own way.
* The two comparison hypotheses are a bridge between two spellings of one and the same
  `A`-module `H^p(U, F_1)`, not a mathematical assumption about the situation. They identify
  the finiteness of the two modules named by
  `Stacks.Algebraization.HasFiniteLowDegreeCohomology` with the finiteness of
  `Stacks.LocalCohomologySequence.complementCohomologyBase`, the library's other `A`-module
  model of `H^p(U, M̃)`; each side is the `p`-th derived functor of sections over `U` restricted
  to `A`, reached through a different functor. Degree `0` of that comparison is
  `Stacks.LocalCohomology.isCoherent_pushforward_iff_module_finite_sections` in
  `StacksFrontier/AlgebraicGeometry/LocalCohomology/PushforwardCoherence/SectionsFiniteness.lean`
  `:124`, which is stated only for the ordinary direct image; its own docstring records that the
  clauses in degrees `p ≥ 1` are not proved. No declaration relates
  `Stacks.LocalCohomology.cohomologyOverBase`, which
  `Stacks.Algebraization.HasFiniteLowDegreeCohomology` uses in degree `1`, to
  `complementCohomologyBase`.

The passage from finiteness of `complementCohomologyBase` to coherence of the higher direct
images is *not* a hypothesis: it is clause (3) of Stacks 0BK0, available here as
`Stacks.LocalCohomologySequence.moduleFinite_complementCohomologyBase_iff_isCoherent`.

The implication from `HasLocallyFreeCodimensionThreeCondition` to `HasDepthDimensionAt` at `2`
is proved from the two pointwise bounds it yields, which are hypotheses. The depth notions do
not obstruct this: `ringDepth`, in which `PropertySkRing` is stated, meets the `Module.depth`
of the inequality above through `moduleDepth_eq_depth`, and a module killed by `I` has
the same depth over `A` as over `A ⧸ I` by `Module.depth_eq_depth_map_algebraMap`. What is
missing is a public form of "the depth of a finite free module over a local ring is the depth
of that ring", and, for the codimension bound, the catenarity that `catenary_height_add`
requires and that the source's condition does not state.

## References

* [Stacks Project, Tag 0EJT](https://stacks.math.columbia.edu/tag/0EJT)
* [Stacks Project, Tag 0EJS](https://stacks.math.columbia.edu/tag/0EJS)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.LocalCohomologySequence

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})

/-- The depth–dimension inequality at a value `n`, over pairs of primes `𝔭 ⊆ 𝔮` of `A` with
`𝔭 ∉ Z`, `𝔮 ∈ Z` and `M_𝔭 ≠ 0`: the depth of `M_𝔭` plus the height of the image of `𝔮` in
`A ⧸ 𝔭` exceeds `n`. The remark is the case `n = 2`. -/
public def HasDepthDimensionAt (M : ModuleCat.{u} (CommRingCat.of S.A)) (n : ℕ) : Prop :=
  ∀ p q : PrimeSpectrum S.A, ¬ S.a ≤ p.asIdeal → S.a ≤ q.asIdeal →
    p.asIdeal ≤ q.asIdeal →
    Nontrivial (LocalizedModule p.asIdeal.primeCompl M) →
    (n : ℕ∞) < Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) +
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height

/-- The criterion of Stacks 0BJY over the affine base `X = Spec A` with `Z = V(𝔞)`, quantified
over the finite `A`-module and over the degree: if `A` is universally catenary and the formal
fibres of its local rings satisfy `(Sₙ)`, then the depth–dimension inequality at `n` holds if
and only if the higher direct images of `M̃|_U` along `U ⟶ X` are coherent in all degrees
below `n`. The two standing assumptions are those of the source. -/
public def AffineDepthDimensionCriterion : Prop :=
  ∀ (N : ModuleCat.{u} (CommRingCat.of S.A)) (_ : Module.Finite S.A N) (n : ℕ),
    Ring.IsUniversallyCatenary S.A →
    (∀ q : PrimeSpectrum S.A,
      Stacks.LocalCohomology.FormalFibersHavePropertySk
        (Localization.AtPrime q.asIdeal) n) →
    (HasDepthDimensionAt S N n ↔
      ∀ m : ℕ, m < n →
        (((Scheme.Modules.pushforward
              (zeroLocusCompl (A := CommRingCat.of S.A) S.a).ι).rightDerived m).obj
            ((tilde N).restrict
              (zeroLocusCompl (A := CommRingCat.of S.A) S.a).ι)).IsCoherent)

/-- The criterion of Stacks 0BJY holds over the affine base of an algebraization situation:
this is `forall_lt_depth_add_height_iff_forall_isCoherent_rightDerived` with `I := 𝔞`. -/
public theorem affineDepthDimensionCriterion : AffineDepthDimensionCriterion S := by
  intro N hN n hcat hformal
  have hfin : Module.Finite (ToType (CommRingCat.of S.A)) N := hN
  exact forall_lt_depth_add_height_iff_forall_isCoherent_rightDerived
    (A := CommRingCat.of S.A) S.a N hcat n hformal

/-- **Stacks Project, Tag 0EJT (the equivalence).** Assume `A` has a dualizing complex. Then
hypothesis (2) of Stacks 0EJS, that `H⁰(U, F_1)` and `H¹(U, F_1)` are finite `A`-modules, holds
if and only if `depth(F_{1,y}) + dim(𝒪_{closure{y}, z}) > 2` for every `y ∈ U ∩ Y` and every
`z ∈ Z ∩ closure{y}`.

The right-hand side is `Stacks.Algebraization.HasDepthDimensionAt` at `2` for a finite
`A`-module `M` whose associated sheaf restricts to `F_1` on `U`. The equivalence is the
criterion of Stacks 0BJY at `n = 2`, which is proved here as
`Stacks.Algebraization.affineDepthDimensionCriterion`; the dualizing complex discharges its
catenarity assumption by Stacks 0A80 and enters the proof only through that and through
`hformalOfDual`. The two comparison hypotheses are a bridge between two spellings of the same
`A`-module `H^p(U, F_1)` and assume nothing about the situation, and the passage from
`complementCohomologyBase` to coherence of the higher direct images is clause (3) of
Stacks 0BK0 and is proved. -/
@[stacks 0EJT "the equivalence; only the formal-fibre step and an H^p(U, F₁) bridge are assumed"]
public theorem hasFiniteLowDegreeCohomology_iff_hasDepthDimensionAt_two
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (M : ModuleCat.{u} (CommRingCat.of S.A)) (hM : Module.Finite S.A M)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hformalOfDual :
      (∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K) →
        ∀ q : PrimeSpectrum S.A,
          Stacks.LocalCohomology.FormalFibersHavePropertySk
            (Localization.AtPrime q.asIdeal) 2)
    (hcompare₀ : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)) ↔
      Module.Finite S.A (complementCohomologyBase (A := CommRingCat.of S.A) S.a M 0))
    (hcompare₁ : Module.Finite S.A
        (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι (F.obj.obj (op 0)) 1) ↔
      Module.Finite S.A (complementCohomologyBase (A := CommRingCat.of S.A) S.a M 1)) :
    HasFiniteLowDegreeCohomology S F ↔ HasDepthDimensionAt S M 2 := by
  have c₀ := hcompare₀.trans
    (moduleFinite_complementCohomologyBase_iff_isCoherent (A := CommRingCat.of S.A) S.a M 0)
  have c₁ := hcompare₁.trans
    (moduleFinite_complementCohomologyBase_iff_isCoherent (A := CommRingCat.of S.A) S.a M 1)
  have hcat : Ring.IsUniversallyCatenary S.A := by
    obtain ⟨K, hK⟩ := hdual
    exact Dualizing.isUniversallyCatenary_of_isDualizingComplex hK
  refine Iff.trans ?_
    (affineDepthDimensionCriterion S M hM 2 hcat (hformalOfDual hdual)).symm
  constructor
  · intro h m hm
    obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    exacts [c₀.mp h.1, c₁.mp h.2]
  · exact fun h => ⟨c₀.mpr (h 0 (by omega)), c₁.mpr (h 1 (by omega))⟩

/-- **Stacks Project, Tag 0EJT (the sufficient condition).** The three conditions under which
the remark asserts that the depth–dimension inequality holds: for a finite `A ⧸ I`-module `N`
whose associated sheaf restricts to `F_1`, the restriction of `Ñ` to `U ∩ Y` is finite locally
free, `Y = Spec(A ⧸ I)` satisfies Serre's condition `(S₂)`, and `codim(Z', Y') ≥ 3` for every
pair of irreducible components `Y'` of `Y` and `Z'` of `Z` with `Z' ⊆ Y'`.

The components of `Y` and of `Z` are the minimal primes of `I` and of `𝔞`, and `Z' ⊆ Y'` is
`𝔭 ≤ 𝔮` for the corresponding primes; the codimension of `Z'` in `Y'` is the height of the
image of `𝔮` in `A ⧸ 𝔭`. The bound is the source's `≥ 3`. -/
public def HasLocallyFreeCodimensionThreeCondition
    (N : ModuleCat.{u} (CommRingCat.of (S.A ⧸ S.I))) : Prop :=
  Scheme.Modules.IsFiniteLocallyFree
      ((tilde N).restrict
        (zeroLocusCompl (A := CommRingCat.of (S.A ⧸ S.I))
          (S.a.map (Ideal.Quotient.mk S.I))).ι) ∧
    PropertySkRing (S.A ⧸ S.I) 2 ∧
      ∀ p ∈ S.I.minimalPrimes, ∀ q ∈ S.a.minimalPrimes, p ≤ q →
        3 ≤ (q.map (Ideal.Quotient.mk p)).height

/-- The dimension of the local ring of `Y` at a point `y` of `Y`, namely the height of the
image of `𝔭` in `A ⧸ I`. This is the `dim(𝒪_{Y,y})` of the Serre condition, in the same
`height`-of-a-quotient spelling that Stacks 0BJY uses for `dim(𝒪_{closure{y},z})`. -/
public def localDimY (p : PrimeSpectrum S.A) : ℕ∞ :=
  (p.asIdeal.map (Ideal.Quotient.mk S.I)).height

/-- The pointwise depth bound that finite local freeness on `U ∩ Y` together with `(S₂)` for `Y`
yields: at every `y ∈ U ∩ Y` in the support of `F_1`, the depth of `F_{1,y}` is at least
`min(2, dim(𝒪_{Y,y}))`.

Its antecedent is the sufficient condition of the remark, so this is the implication from that
condition to the bound, not a free-standing assumption. -/
public def PointwiseSerreTwoBound (M : ModuleCat.{u} (CommRingCat.of S.A))
    (N : ModuleCat.{u} (CommRingCat.of (S.A ⧸ S.I))) : Prop :=
  HasLocallyFreeCodimensionThreeCondition S N →
    ∀ p : PrimeSpectrum S.A, ¬ S.a ≤ p.asIdeal →
      Nontrivial (LocalizedModule p.asIdeal.primeCompl M) →
      min (2 : ℕ∞) (localDimY S p) ≤
        Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)

/-- The pointwise codimension bound that `codim(Z', Y') ≥ 3` yields in a catenary ring: at
every `y ∈ U ∩ Y` and `z ∈ Z ∩ closure{y}`, the sum `dim(𝒪_{Y,y}) + dim(𝒪_{closure{y},z})` is
at least `3`.

Its antecedent is the sufficient condition of the remark. The passage from the bound on pairs
of irreducible components to this bound on arbitrary pairs of primes is codimension additivity
along a chain, which is what universal catenarity of `A` provides. -/
public def PointwiseCodimensionThreeBound (M : ModuleCat.{u} (CommRingCat.of S.A))
    (N : ModuleCat.{u} (CommRingCat.of (S.A ⧸ S.I))) : Prop :=
  HasLocallyFreeCodimensionThreeCondition S N →
    ∀ p q : PrimeSpectrum S.A, ¬ S.a ≤ p.asIdeal → S.a ≤ q.asIdeal →
      p.asIdeal ≤ q.asIdeal →
      Nontrivial (LocalizedModule p.asIdeal.primeCompl M) →
      3 ≤ localDimY S p + (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height

/-- A prime strictly above a prime `𝔭` has positive height in `A ⧸ 𝔭`: the quotient is a
domain, and the image of the larger prime is a nonzero ideal of it. -/
private lemma one_le_height_map_quotient {A : Type*} [CommRing A] {p q : Ideal A}
    [p.IsPrime] (hpq : p < q) :
    (1 : ℕ∞) ≤ (q.map (Ideal.Quotient.mk p)).height := by
  have : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  obtain ⟨x, hxq, hxp⟩ := IsConcreteLE.exists_of_lt hpq
  intro hbot
  have hx : Ideal.Quotient.mk p x ∈ q.map (Ideal.Quotient.mk p) :=
    Ideal.mem_map_of_mem _ hxq
  rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact hxp hx

/-- The arithmetic of the sufficient condition: the Serre bound `min(2, d) ≤ depth`, the
codimension bound `3 ≤ d + h` and positivity `1 ≤ h` together force `depth + h > 2`. -/
private lemma lt_two_add_of_serre_codim_bounds {d h depth : ℕ∞}
    (hS : min 2 d ≤ depth) (hc : 3 ≤ d + h) (hh : 1 ≤ h) : 2 < depth + h := by
  rcases le_or_gt 2 d with hd | hd
  · have h2 : (2 : ℕ∞) ≤ depth := by rwa [min_eq_left hd] at hS
    calc (2 : ℕ∞) < 2 + 1 := by decide
      _ ≤ depth + h := add_le_add h2 hh
  · have hdle : d ≤ depth := by rwa [min_eq_right hd.le] at hS
    calc (2 : ℕ∞) < 3 := by decide
      _ ≤ d + h := hc
      _ ≤ depth + h := add_le_add hdle (le_refl h)

/-- **Stacks Project, Tag 0EJT (the sufficient condition).** The depth–dimension inequality at
`2` holds when `F_1` is finite locally free on `𝒪_{U ∩ Y}`, `Y` is `(S₂)`, and
`codim(Z', Y') ≥ 3` for every pair of irreducible components `Y'` of `Y` and `Z'` of `Z` with
`Z' ⊆ Y'`.

The two pointwise bounds that the condition yields are hypotheses, for one reason each.
`PointwiseSerreTwoBound` would follow from `(S₂)` for `Y` by way of the depth of a finite
locally free module over a local ring being the depth of that ring, and that statement has no
public form in this library; the other two steps it needs do, namely
`moduleDepth_eq_depth` and `Module.depth_eq_depth_map_algebraMap`.
`PointwiseCodimensionThreeBound` would follow from the codimension clause by additivity of
codimension along a chain, which is available as `catenary_height_add`, but in the direction
required that needs `A` to be catenary, and catenarity is not part of the condition stated by
the source. What is proved here is that those two bounds, together with the positivity of
`dim(𝒪_{closure{y},z})` for `z` strictly above `y`, give the inequality. -/
@[stacks 0EJT "the trailing sufficient condition, via the two pointwise bounds it yields"]
public theorem hasDepthDimensionAt_two_of_pointwiseBounds
    (M : ModuleCat.{u} (CommRingCat.of S.A))
    (N : ModuleCat.{u} (CommRingCat.of (S.A ⧸ S.I)))
    (hcond : HasLocallyFreeCodimensionThreeCondition S N)
    (hserre : PointwiseSerreTwoBound S M N)
    (hcodim : PointwiseCodimensionThreeBound S M N) :
    HasDepthDimensionAt S M 2 := by
  intro p q hpa hqa hpq hnt
  have hne : p.asIdeal ≠ q.asIdeal := fun heq => hpa (heq ▸ hqa)
  have hlt : p.asIdeal < q.asIdeal := lt_of_le_of_ne hpq hne
  have hh : (1 : ℕ∞) ≤ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height :=
    one_le_height_map_quotient hlt
  have hcast : ((2 : ℕ) : ℕ∞) = (2 : ℕ∞) := by norm_num
  rw [hcast]
  exact lt_two_add_of_serre_codim_bounds (hserre hcond p hpa hnt)
    (hcodim hcond p q hpa hqa hpq hnt) hh

end Stacks.Algebraization

end
