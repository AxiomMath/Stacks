module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceFormsVanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Exactness
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationShortExact
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSumIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreComputation
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The twisted Hodge cohomology of projective space

Let `A` be a commutative ring and `n = m + 1 ≥ 1`. Write `ℙⁿ_A = Proj A[T₀, …, Tₙ]` with its
structure morphism `ℙⁿ_A ⟶ Spec A`, let `𝒪(d)` be the Serre twists, let
`Ω = Ω_{ℙⁿ_A/A}` be the sheaf of relative differentials and `Ωᵖ = ⋀ᵖ Ω` its exterior powers.
The cohomology `H^q(ℙⁿ_A, ℱ)` is read as an `A`-module through the structure morphism, exactly as
`Stacks.ProjectiveSpace.Cohomology.twistCohomology` reads the cohomology of a twist.

This file proves the three clauses of [Stacks, Tag 0FUK]:

1. `H^q(ℙⁿ_A, Ωᵖ) = 0` unless `0 ≤ p = q ≤ n`;
2. for `0 ≤ p ≤ n` the `A`-module `H^p(ℙⁿ_A, Ωᵖ)` is free of rank one;
3. for `q > 0`, `k > 0` and arbitrary `p`, `H^q(ℙⁿ_A, Ωᵖ(k)) = 0`.

It also states the vanishing clause of [Stacks, Tag 0FMI], which repeats clause (1). The basis
clause of [Stacks, Tag 0FMI] — for `0 ≤ p ≤ n` the free rank-one `A`-module `H^p(ℙⁿ_A, Ωᵖ)` has
basis element the `p`-th power `c₁^{Hodge}(𝒪(1))^p` of the Hodge first Chern class of `𝒪(1)` —
is proved in `StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeChernPowers`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.forms`: the sheaf `Ωᵖ` of relative differential
  `p`-forms of `ℙⁿ_A ⟶ Spec A`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.twistedForms`: its Serre twist `Ωᵖ(k)`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.hodgeCohomology` and
  `twistedHodgeCohomology`: the `A`-modules `H^q(ℙⁿ_A, Ωᵖ)` and `H^q(ℙⁿ_A, Ωᵖ(k))`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.eulerWedge`: the middle term
  `⋀ᵖ(𝒪(-1)^{⊕ n+1})(k) ≅ 𝒪(k - p)^{⊕ binom(n+1, p)}` of the filtration the source's proof uses.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.EulerFiltrationData`: the geometric input of the
  source's proof — the two displayed short exact sequences obtained by filtering `⋀ᵖ` of the
  Euler sequence. It is constructed below, in `eulerFiltrationData`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.eulerWedgeMiddleIso`: the identification
  `⋀ᵖ(𝒪(-1)^{⊕ n+1}) ≅ 𝒪(-p)^{⊕ binom(n+1, p)}` of the middle term of the filtration, in the
  spelling `eulerWedge` of this file.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.twistEulerWedgeIso`: the twist of that middle
  term, `(𝒪(-p)^{⊕ binom(n+1, p)})(k) ≅ 𝒪(k - p)^{⊕ binom(n+1, p)}`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.twistingSheafOnePicardClass`: the class of
  `𝒪(1)` in `Pic(ℙⁿ_A)`, whose Hodge first Chern class is the generator of `H¹(ℙⁿ_A, Ω)`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.hodgeCohomologyZeroIso`: the identification
  `H⁰(ℙⁿ_A, Ω⁰) = A`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.wedgeDelta`: the connecting map
  `H^p(ℙⁿ_A, Ωᵖ) ⟶ H^{p+1}(ℙⁿ_A, Ω^{p+1})` of a filtration sequence, an isomorphism by
  `isIso_wedgeDelta`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.eulerFiltrationData`: **the geometric input of
  the source's proof, constructed**, so that the clauses below hold unconditionally. It is
  assembled from `shortExact_wedge_of_euler` and `shortExact_wedge_twist_of_euler`, which
  transport the proved exterior-power filtration of the Euler sequence
  (`Stacks.AlgebraicGeometry.ProjEulerSequence.shortExact_eulerWedgeFiltration`) across the
  closed form of its middle term and across the twist by `𝒪(k)`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isEquivalence_twistFunctor_polyGrading` and
  `shortExact_map_twistFunctor_polyGrading`: twisting by `𝒪(k)` on `ℙⁿ_A` is an equivalence and
  therefore carries short exact sequences to short exact sequences, for every `k : ℤ`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isZero_hodgeCohomology`: **clause (1)**.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.nonempty_hodgeCohomology_diag_iso` and
  `free_hodgeCohomology_diag`: **clause (2)**, as an isomorphism with `A` and as freeness.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isZero_twistedHodgeCohomology`: **clause (3)**.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isZero_cohomologySheaf_twistingSheaf`: the base
  case the source quotes without further mention — `H^q(ℙⁿ_A, 𝒪(d)) = 0` for every `q` when
  `-n ≤ d < 0`, and for every `q > 0` when `-n ≤ d`. It is read off
  `Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology` ([Stacks, Tag 01XU]).
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isZero_hodgeCohomology_of_ne_or_gt`: **the
  vanishing clause of [Stacks, Tag 0FMI]**, in the source's own phrasing.

## Implementation notes

**Clause (4) of the source is the literal text `add more here`.** It is an unfilled placeholder in
`derham.tex`, not an omission in this transcription, so the covering set of [Stacks, Tag 0FUK] is
clauses (1)–(3) and nothing else. Verified against
<https://stacks.math.columbia.edu/tag/0FUK> and against
`https://raw.githubusercontent.com/stacks/stacks-project/master/derham.tex`, Section
`derham-section-projective-space`, Lemma `derham-lemma-twisted-hodge-cohomology-projective-space`.

**The geometric input, and how it is obtained.** The proof of the source rests on one geometric
input: reading the Euler sequence `0 → Ω → 𝒪(-1)^{⊕ n+1} → 𝒪 → 0` of [Stacks, Tag 0FMH] as a
two-step filtration of `𝒪(-1)^{⊕ n+1}`, the induced filtration of `⋀ᵖ(𝒪(-1)^{⊕ n+1})` is a short
exact sequence `0 → Ωᵖ → ⋀ᵖ(𝒪(-1)^{⊕ n+1}) → Ω^{p-1} → 0`, and `⋀ᵖ(𝒪(-1)^{⊕ n+1})` is a direct
sum of `binom(n+1, p)` copies of `𝒪(-p)`. It is packaged as `EulerFiltrationData`, in the two
forms the source displays (untwisted, and twisted by `k > 0`), and it is *proved*: the
exterior-power filtration itself is
`Stacks.AlgebraicGeometry.ProjEulerSequence.shortExact_eulerWedgeFiltration`, the closed form of
its middle term is
`Stacks.AlgebraicGeometry.ProjTwistRank.nonempty_exteriorPower_twistMinusOneSum_isoZeroTwistSum`,
and the twisted form is obtained from the untwisted one because `𝒪(k)` is invertible. The
assembled datum is `eulerFiltrationData`, so the clauses of [Stacks, Tag 0FUK] and of
[Stacks, Tag 0FMI] below take no hypothesis beyond `A` being a commutative ring. (The same input
for an arbitrary short exact sequence of finite locally free modules is recorded as
`AlgebraicGeometry.VectorBundleKZero.ExteriorPowersData` for [Stacks, Tag 0FIC], where it is
still carried as a hypothesis.)

Everything else is proved too: the base case [Stacks, Tag 01XU] is proved and is used through
`isZero_cohomologySheaf_twistingSheaf` and `twistingSheafZeroCohomologyIso`, the dimension
shifting is `Stacks.Cohomology.RightDerivedDelta`, and the two inductions — ascending on `p` for
clauses (1) and (2), descending on `p` for clause (3) — are the source's own. The vanishing
`Ωᵖ = 0` for `p > n`, which the source asserts alongside the filtration, is proved in
`Stacks.AlgebraicGeometry.ProjectiveSpaceForms.isZero_relativeDifferentialForms_of_lt`: the
differentials of the `n` affine coordinates of a standard chart generate the stalk of `Ω`, so the
exterior powers of that stalk vanish above `n`.

`EulerFiltrationData` is a `Prop`-valued structure whose two short-exactness fields are stated
with `∃`, so no morphism is chosen out of it; only its short exactness is ever used, and short
exactness is a proposition.

**The sheaf of rings has several definitionally equal spellings and instance search matches heads
syntactically.** The proved filtration sequence lives over
`Stacks.AlgebraicGeometry.ProjEulerSequence.ringSheafOfComm` of the structure sheaf of `Proj`,
the twist functor over `Stacks.AlgebraicGeometry.ProjTwistFunctor.projRingSheaf`, the closed form
of the middle term over `CategoryTheory.Sheaf.toRingCat` of the scheme's sheaf, and
`EulerFiltrationData` over `AlgebraicGeometry.Scheme.Modules`. The transport is therefore done
*once*, by `shortExact_transportMiddle`, which is stated for an abstract category with zero
morphisms and so mentions no sheaf of rings at all; every bridging unification happens where a
statement of the construction ascribes a type, and no proof there rewrites in a goal whose
morphisms mix two spellings.

**`HasFiniteBiproducts` is supplied as a local instance at the twist functor's spelling**, as it
is in `StacksFrontier/AlgebraicGeometry/ProjEulerSequence/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/ProjTwistRank/ExteriorPowerSumIso.lean`: the universally
quantified instances of the library are stated for `SheafOfModules.{max u v}` and
`max ?u ?v =?= u` is not a constraint the universe unifier solves, so instance search never
applies them in a single universe. For the same reason the twisted family of summands,
`twistEulerWedgeFamily`, is given a name with an ascribed codomain rather than written as a
lambda inside `⨁`.

**The twist of a general module** is `Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor`,
whose value on objects is `ℱ ⊗ 𝒪(k)`. Two of its properties are used: it is additive, which is
what makes the twist of the zero sheaf `Ω^{p}` (`p > n`) zero and what identifies the twist of a
direct sum of twists with the direct sum of their twists, and it is an equivalence
(`isEquivalence_twistFunctor_polyGrading`), which is what carries the untwisted filtration
sequence to the twisted one.

**Why `n` is written `m + 1`.** `Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology` is stated
for `ℙ^{m+1}`, the hypothesis `n ≥ 1` being part of [Stacks, Tag 01XU] — at `n = 0` its first and
last rows would both apply and disagree. The source's standing setup also has `n ≥ 1`.

**Additivity of the derived functors** is not an instance in Mathlib. It is obtained from the
`δ`-functor of [Stacks, Tag 010Q],
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`, whose `additive` field is
exactly it; this is what makes `Functor.mapBiproduct` available and hence what reduces the
acyclicity of `eulerWedge` to the acyclicity of a single twist.

**Restriction of scalars neither creates nor destroys vanishing**, because the carrier of
`(ModuleCat.restrictScalars f).obj Z` is the carrier of `Z`. Both directions are needed — the
induction runs on the `Γ(ℙⁿ_A, 𝒪)`-modules the derived functors produce, while the statements are
about `A`-modules — and they are `isZero_restrictScalars_iff`.

**[Stacks, Tag 0FMI].** Its vanishing is quoted wholesale from [Stacks, Tag 0FUK], and so is it
here. Its own content, the identification of the generator `c₁^{Hodge}(𝒪(1))^p`, needs the cup
product of [Stacks, Section 01FP] and the Čech computation of the boundary of `1` along the Euler
sequence; it is proved in `StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeChernPowers`.

**Freeness of rank one with a named basis element** is spelled as a `Module.Basis (Fin 1) A`
whose unique vector is the given class, which is exactly the source's "free of rank `1` with
basis element".

## References

* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
* [Stacks Project, Tag 0FUK](https://stacks.math.columbia.edu/tag/0FUK)
* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 0FIC](https://stacks.math.columbia.edu/tag/0FIC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v w u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHodge

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjectiveSpace.Cohomology

/-! ### Restriction of scalars and vanishing -/

/-- Restriction of scalars neither creates nor destroys vanishing: the carrier of
`(ModuleCat.restrictScalars f).obj Z` is the carrier of `Z`. -/
theorem isZero_restrictScalars_iff {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (Z : ModuleCat.{u} S) :
    IsZero ((ModuleCat.restrictScalars f).obj Z) ↔ IsZero Z := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact Iff.rfl

/-! ### The setting -/

variable (A : Type u) [CommRing A] (m : ℕ)

/-- `ℙⁿ_A = Proj A[T₀, …, Tₙ]` with `n = m + 1`. -/
abbrev projSpace : Scheme.{u} := AlgebraicGeometry.Proj (polyGrading A (m + 1))

/-- Global sections on `ℙⁿ_A`, the functor whose right derived functors are the cohomology. -/
abbrev globalSections : (projSpace A m).Modules ⥤ ModuleCat.{u} Γ(projSpace A m, ⊤) :=
  Stacks.Cohomology.sectionsFunctor (projSpace A m) ⊤

/-- `H^q(ℙⁿ_A, ℱ)` as a module over the global functions on `ℙⁿ_A`. -/
abbrev cohomologySheaf (F : (projSpace A m).Modules) (q : ℕ) :
    ModuleCat.{u} Γ(projSpace A m, ⊤) :=
  ((globalSections A m).rightDerived q).obj F

/-- `H^q(ℙⁿ_A, ℱ)` as an `A`-module, the coefficients acting through the structure morphism
`ℙⁿ_A ⟶ Spec A`. This is the reading of
`Stacks.ProjectiveSpace.Cohomology.twistCohomology`, extended from the twists to an arbitrary
sheaf of modules. -/
abbrev cohomology (F : (projSpace A m).Modules) (q : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj (cohomologySheaf A m F q)

/-- The `q`-th cohomology of the twist `𝒪(d)` is the one Serre's computation is about. -/
theorem cohomology_twistingSheaf (d : ℤ) (q : ℕ) :
    cohomology A m (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) d) q =
      twistCohomology A (m + 1) d q :=
  rfl

/-- The sheaf `Ωᵖ_{ℙⁿ_A/A}` of relative differential `p`-forms, the `p`-th exterior power of the
sheaf of relative differentials of the structure morphism. -/
abbrev forms (p : ℕ) : (projSpace A m).Modules :=
  Scheme.Hom.relativeDifferentialForms (projToSpecCoeff A (m + 1)) (p : ℤ)

/-- The `k`-th Serre twist `Ωᵖ(k) = Ωᵖ ⊗ 𝒪(k)` of the sheaf of relative `p`-forms. -/
abbrev twistedForms (p : ℕ) (k : ℤ) : (projSpace A m).Modules :=
  (Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor (polyGrading A (m + 1)) k).obj
    (forms A m p)

/-- The `A`-module `H^q(ℙⁿ_A, Ωᵖ)`, the Hodge cohomology of projective space. -/
abbrev hodgeCohomology (p q : ℕ) : ModuleCat.{u} A := cohomology A m (forms A m p) q

/-- The `A`-module `H^q(ℙⁿ_A, Ωᵖ(k))`, the twisted Hodge cohomology of projective space. -/
abbrev twistedHodgeCohomology (p : ℕ) (k : ℤ) (q : ℕ) : ModuleCat.{u} A :=
  cohomology A m (twistedForms A m p k) q

/-- The `binom(n+1, p)` copies of `𝒪(k - p)` that the middle term of the filtration is a direct
sum of. The codomain is ascribed as `(projSpace A m).Modules` rather than left as the unfolded
category of sheaves of modules over the structure sheaf of `Proj`, which is where the biproduct
instances are found. -/
abbrev eulerWedgeFamily (p : ℕ) (k : ℤ) : Fin ((m + 2).choose p) → (projSpace A m).Modules :=
  fun _ => ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) (k - (p : ℤ))

/-- The middle term of the filtration the source's proof uses: the `k`-th twist of
`⋀ᵖ(𝒪(-1)^{⊕ n+1})`, which is a direct sum of `binom(n+1, p)` copies of `𝒪(k - p)`. -/
abbrev eulerWedge (p : ℕ) (k : ℤ) : (projSpace A m).Modules := ⨁ eulerWedgeFamily A m p k

/-! ### The geometric input -/

/-- **The geometric input of the proof of [Stacks, Tag 0FUK], and the only thing in it that the
library does not supply**: reading the Euler sequence `0 → Ω → 𝒪(-1)^{⊕ n+1} → 𝒪 → 0` of
[Stacks, Tag 0FMH] as a two-step filtration of `𝒪(-1)^{⊕ n+1}`, the induced filtration of
`⋀ᵖ(𝒪(-1)^{⊕ n+1})` is short exact with graded pieces `Ωᵖ` and `Ω^{p-1}`, and
`⋀ᵖ(𝒪(-1)^{⊕ n+1})` is a direct sum of `binom(n+1, p)` copies of `𝒪(-p)`.

The same input, for an arbitrary short exact sequence of finite locally free modules, is carried
as a hypothesis for [Stacks, Tag 0FIC] by
`AlgebraicGeometry.VectorBundleKZero.ExteriorPowersData`.

The two fields are the two displayed short exact sequences, untwisted and twisted. The source
also asserts that `Ωᵖ` vanishes above the relative dimension; that is proved, in
`Stacks.AlgebraicGeometry.ProjectiveSpaceForms.isZero_relativeDifferentialForms_of_lt`. -/
structure EulerFiltrationData : Prop where
  /-- `0 → Ω^{p+1} → ⋀^{p+1}(𝒪(-1)^{⊕ n+1}) → Ωᵖ → 0`, the first sequence the source displays. -/
  shortExact_wedge : ∀ p : ℕ, p ≤ m →
    ∃ (a : forms A m (p + 1) ⟶ eulerWedge A m (p + 1) 0)
      (b : eulerWedge A m (p + 1) 0 ⟶ forms A m p) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact
  /-- `0 → Ω^{p+1}(k) → ⋀^{p+1}(𝒪(-1)^{⊕ n+1})(k) → Ωᵖ(k) → 0`, the second sequence the source
  displays, used there for `k > 0`. -/
  shortExact_wedge_twist : ∀ k : ℤ, 0 < k → ∀ p : ℕ, p ≤ m + 1 →
    ∃ (a : twistedForms A m (p + 1) k ⟶ eulerWedge A m (p + 1) k)
      (b : eulerWedge A m (p + 1) k ⟶ twistedForms A m p k) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact

/-! ### Degree one, and the invertibility of the Serre twists -/

/-- **The standard opens `D₊(Tᵢ)` of `ℙⁿ_A` are attached to elements of degree one**, so `ℙⁿ_A`
satisfies the hypothesis of [Stacks, Tag 01MT] under which the Serre twists are invertible. -/
theorem degreeOneCover_polyGrading :
    Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.DegreeOneCover (polyGrading A (m + 1)) := by
  refine top_le_iff.1 ?_
  rw [← iSup_basicOpen_X_eq_top A (m + 1)]
  exact iSup_le fun i => le_iSup_of_le ⟨MvPolynomial.X i, X_mem_one A (m + 1) i⟩ le_rfl

/-! ### Constructing the geometric input

Both sequences of `EulerFiltrationData` come from one proved sequence,
`Stacks.AlgebraicGeometry.ProjEulerSequence.shortExact_eulerWedgeFiltration`, whose middle term
is the exterior power `⋀^{p+1}(𝒪(-1)^{⊕ n+1})` itself. Two things are done to it.

* Its middle term is replaced by the direct sum of twists: the identification
  `⋀^{p+1}(𝒪(-1)^{⊕ n+1}) ≅ 𝒪(-(p+1))^{⊕ binom(n+1, p+1)}` is
  `Stacks.AlgebraicGeometry.ProjTwistRank.nonempty_exteriorPower_twistMinusOneSum_isoZeroTwistSum`,
  and replacing the middle term of a short exact sequence by an isomorphic object keeps it short
  exact (`shortExact_transportMiddle`), the two arrows being composed with the isomorphism and
  its inverse.
* It is twisted by `𝒪(k)`. The twist is an equivalence of categories because `𝒪(k)` is
  invertible on `ℙⁿ_A` — the standard opens `D₊(Tᵢ)` are attached to elements of degree one, so
  [Stacks, Tag 01MT] applies — hence it preserves short exactness; and it is additive, so it
  carries the direct sum of twists to the direct sum of their twists, where `𝒪(-(p+1)) ⊗ 𝒪(k)`
  is `𝒪(k - (p+1))` by Equation 01MO.
-/

section Construction

open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AlgebraicGeometry.ProjTwistRank
open AlgebraicGeometry.ProjectiveSpectrum.Proj

/-! #### Replacing the middle term of a short exact sequence -/

section Transport

variable {C : Type w} [Category.{v} C] [HasZeroMorphisms C]

/-- **Replacing the middle term of a short exact sequence by an isomorphic object gives a short
exact sequence.** The new arrows are the old ones composed with the isomorphism and its inverse,
and the two sequences are isomorphic through the identity on the outer terms. -/
theorem shortExact_transportMiddle {S : ShortComplex C} (hS : S.ShortExact) {X : C}
    (e : S.X₂ ≅ X) :
    ∃ (a : S.X₁ ⟶ X) (b : X ⟶ S.X₃) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact :=
  ⟨S.f ≫ e.hom, e.inv ≫ S.g,
    (Category.assoc _ _ _).trans
      ((congrArg (fun φ => S.f ≫ φ) (e.hom_inv_id_assoc S.g)).trans S.zero),
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (Iso.refl S.X₁) e (Iso.refl S.X₃) (Category.id_comp _)
        ((e.hom_inv_id_assoc S.g).trans (Category.comp_id S.g).symm)) hS⟩

end Transport

/-! #### The closed form of the middle term -/

/-- **The middle term of the filtration in closed form**:
`⋀ᵖ(𝒪(-1)^{⊕ n+1}) ≅ 𝒪(-p)^{⊕ binom(n+1, p)}`, with the target written as the `k = 0` case of
`eulerWedge`, the spelling the Hodge computation uses. -/
def eulerWedgeMiddleIso (p : ℕ) :
    Scheme.Modules.exteriorPower (X := projSpace A m) (twistMinusOneSum A (m + 1))
        ((p : ℕ) : ℤ) ≅ eulerWedge A m p 0 :=
  (nonempty_exteriorPower_twistMinusOneSum_isoZeroTwistSum A (m + 1) p).some

/-! #### The untwisted sequence -/

/-- **The first sequence of `EulerFiltrationData`**:
`0 → Ω^{p+1} → 𝒪(-(p+1))^{⊕ binom(n+1, p+1)} → Ωᵖ → 0`. It is the exterior-power filtration of
the Euler sequence with its middle term replaced by its closed form. -/
@[sga "6 VIII 5.2" "Case p = 0"]
theorem shortExact_wedge_of_euler (p : ℕ) :
    ∃ (a : forms A m (p + 1) ⟶ eulerWedge A m (p + 1) 0)
      (b : eulerWedge A m (p + 1) 0 ⟶ forms A m p) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact :=
  shortExact_transportMiddle (shortExact_eulerWedgeFiltration A (m + 1) p)
    (eulerWedgeMiddleIso A m (p + 1))

/-! #### Twisting by an invertible twisting sheaf -/

/-- The category of sheaves of modules over the structure sheaf of `ℙⁿ_A` has finite biproducts. -/
local instance hasFiniteBiproducts_projRingSheaf :
    HasFiniteBiproducts (SheafOfModules.{u}
      (ProjTwistFunctor.projRingSheaf (polyGrading A (m + 1)))) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **Twisting by `𝒪(k)` is an autoequivalence of `𝒪_{ℙⁿ_A}`-modules**, for every `k : ℤ`: the
standard opens `D₊(Tᵢ)` of `ℙⁿ_A` are attached to elements of degree one, so `𝒪(k)` is
invertible by [Stacks, Tag 01MT]. -/
theorem isEquivalence_twistFunctor_polyGrading (k : ℤ) :
    (ProjTwistFunctor.twistFunctor (polyGrading A (m + 1)) k).IsEquivalence :=
  have : Stacks.SheafOfModules.IsInvertible
      (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A (m + 1))).obj
      (ProjTwistFunctor.projRingSheaf (polyGrading A (m + 1))).property
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) k) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
      (ProjTwistDegreeOneCover.isInvertible_twistingSheaf (polyGrading A (m + 1))
        (degreeOneCover_polyGrading A m) k)
  ProjTwistFunctor.isEquivalence_twistFunctor (polyGrading A (m + 1)) k

/-- **The twist of a short exact sequence of `𝒪_{ℙⁿ_A}`-modules is short exact**, the twist
being an equivalence. -/
theorem shortExact_map_twistFunctor_polyGrading (k : ℤ)
    {T : ShortComplex (SheafOfModules.{u}
      (ProjTwistFunctor.projRingSheaf (polyGrading A (m + 1))))} (hT : T.ShortExact) :
    (T.map (ProjTwistFunctor.twistFunctor (polyGrading A (m + 1)) k)).ShortExact :=
  have := isEquivalence_twistFunctor_polyGrading A m k
  ProjTwistFunctor.shortExact_map_twistFunctor (polyGrading A (m + 1)) k hT

/-! #### The closed form of the twisted middle term -/

/-- **The twist of a Serre twist is a Serre twist**: `𝒪(d) ⊗ 𝒪(k) ≅ 𝒪(d + k)` on `ℙⁿ_A`, which
is Equation 01MO, `A[T₀, …, Tₙ]` being generated in degree one over `A`. -/
def twistTwistingSheafIso (d k : ℤ) :
    (ProjTwistFunctor.twistFunctor (polyGrading A (m + 1)) k).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) d) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) (d + k) :=
  tensorTwistingSheafIso A (m + 1) d k

/-- The family of summands of the twisted middle term, before its degrees are added up: the
`binom(n+1, p)` copies of `𝒪(-p) ⊗ 𝒪(k)`. The codomain is ascribed, so that the direct sum below
is formed in the category where the biproduct instances are found. -/
abbrev twistEulerWedgeFamily (p : ℕ) (k : ℤ) :
    Fin ((m + 2).choose p) → (projSpace A m).Modules :=
  fun i => (ProjTwistFunctor.twistFunctor (polyGrading A (m + 1)) k).obj
    (eulerWedgeFamily A m p 0 i)

/-- The `i`-th summand of the twisted middle term is the `i`-th summand of `eulerWedge … k`:
`𝒪(0 - p) ⊗ 𝒪(k) ≅ 𝒪(k - p)`. -/
def twistEulerWedgeFamilyIso (p : ℕ) (k : ℤ) (i : Fin ((m + 2).choose p)) :
    twistEulerWedgeFamily A m p k i ≅ eulerWedgeFamily A m p k i :=
  twistTwistingSheafIso A m (0 - (p : ℤ)) k ≪≫
    eqToIso (congrArg (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)))
      (by ring : (0 : ℤ) - (p : ℤ) + k = k - (p : ℤ)))

/-- **The twisted middle term in closed form**: the `k`-th twist of
`𝒪(-p)^{⊕ binom(n+1, p)}` is `𝒪(k - p)^{⊕ binom(n+1, p)}`. The twist is additive, hence carries
the direct sum to the direct sum of the twists, and each twisted summand is a Serre twist by
Equation 01MO. -/
def twistEulerWedgeIso (p : ℕ) (k : ℤ) :
    (ProjTwistFunctor.twistFunctor (polyGrading A (m + 1)) k).obj (eulerWedge A m p 0) ≅
      eulerWedge A m p k :=
  (ProjTwistFunctor.twistFunctor (polyGrading A (m + 1)) k).mapBiproduct
      (eulerWedgeFamily A m p 0) ≪≫
    biproduct.mapIso (twistEulerWedgeFamilyIso A m p k)

/-! #### The twisted sequence, and the datum -/

/-- **The second sequence of `EulerFiltrationData`**:
`0 → Ω^{p+1}(k) → 𝒪(k - (p+1))^{⊕ binom(n+1, p+1)} → Ωᵖ(k) → 0`. It is the twist of
`shortExact_wedge_of_euler`, the untwisted sequence, with its middle term put back in closed
form by `twistEulerWedgeIso`.

Two things keep the elaboration bounded, and both are forced.

The *order* of the two steps. Replacing the middle term of the twisted filtration instead —
twisting first and then transporting — asks for `⋀^{p+1}(𝒪(-1)^{⊕ n+1})` to be matched against
`𝒪(-(p+1))^{⊕ binom(n+1, p+1)}` underneath
`Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor`, and the twist is the sheafification of
a tensor product, which the elaborator descends into rather than stopping at the two arguments;
it exhausts the heartbeat budget there. Transporting first makes that match on the bare objects,
where `shortExact_wedge_of_euler` already makes it, and leaves the twist with nothing to compare.

The *identification of the middle term of the twisted sequence*, which is
`CategoryTheory.ShortComplex.map_X₂` and not a definitional unfolding. The middle object of a
`CategoryTheory.ShortComplex.map` is definitionally the twist of the middle object of the
original, but reaching it that way unfolds the `map` and then the twist, which is again over
budget; the `@[simps]` equation says it propositionally, in one step, and `eqToIso` of it is
composed onto `twistEulerWedgeIso`. That is also why the arguments of `map_X₂` are left to
unification: written out, the `CategoryTheory.Functor.PreservesZeroMorphisms` instance for the
twist would be sought at `AlgebraicGeometry.Scheme.Modules` of `ℙⁿ_A`, where instance search does
not match it, instead of at the twist's own
`Stacks.AlgebraicGeometry.ProjTwistFunctor.projRingSheaf`. -/
theorem shortExact_wedge_twist_of_euler (k : ℤ) (p : ℕ) :
    ∃ (a : twistedForms A m (p + 1) k ⟶ eulerWedge A m (p + 1) k)
      (b : eulerWedge A m (p + 1) k ⟶ twistedForms A m p k) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact := by
  obtain ⟨a, b, w, hS⟩ := shortExact_wedge_of_euler A m p
  have hTw := shortExact_map_twistFunctor_polyGrading A m k hS
  exact shortExact_transportMiddle hTw
    (eqToIso (ShortComplex.map_X₂ _ _) ≪≫ twistEulerWedgeIso A m (p + 1) k)

/-- **The geometric input of the proof of [Stacks, Tag 0FUK] is available**: both displayed
short exact sequences hold, so the Hodge computation of `ℙⁿ_A` rests on nothing further. -/
@[sga "6 VIII 5.2" "special case"]
theorem eulerFiltrationData : EulerFiltrationData A m where
  shortExact_wedge p _ := shortExact_wedge_of_euler A m p
  shortExact_wedge_twist k _ p _ := shortExact_wedge_twist_of_euler A m k p

end Construction

/-! ### Additivity of the derived functors -/

/-- The right derived functors of global sections are additive. This is the `additive` field of
the cohomological `δ`-functor of [Stacks, Tag 010Q]; Mathlib does not record it as an instance
for `CategoryTheory.Functor.rightDerived`. -/
instance additive_rightDerived_globalSections (q : ℕ) :
    ((globalSections A m).rightDerived q).Additive :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (globalSections A m)).additive q

/-! ### Serre's computation, in the form the source quotes it -/

section Serre

variable {A m}

/-- The polynomial chart of negative degree is a subsingleton, which is the vanishing that drives
both extreme-degree cases of Serre's computation. -/
private theorem subsingleton_twistChart_empty {d : ℤ} (hd : d < 0) :
    Subsingleton ↥(twistChart A (m + 1) d (∅ : Set (Fin (m + 1 + 1)))) := by
  rw [twistChart_eq_bot_of_neg (R := A) (m + 1) hd]
  infer_instance

/-- `H⁰(ℙⁿ_A, 𝒪(d)) = 0` for `d < 0`. -/
private theorem isZero_twistCohomology_zero {d : ℤ} (hd : d < 0) :
    IsZero (twistCohomology A (m + 1) d 0) :=
  IsZero.of_iso (ModuleCat.isZero_of_iff_subsingleton.2 (subsingleton_twistChart_empty hd))
    (serreTwistCohomology A m d).degreeZero

/-- `Hⁿ(ℙⁿ_A, 𝒪(d)) = 0` for `-n ≤ d`. -/
private theorem isZero_twistCohomology_top {d : ℤ} (hd : -((m : ℤ) + 1) ≤ d) :
    IsZero (twistCohomology A (m + 1) d (m + 1)) := by
  have hneg : -d - (((m + 1 : ℕ) : ℤ) + 1) < 0 := by push_cast; omega
  have hs := subsingleton_twistChart_empty (A := A) (m := m) hneg
  have hhom : Subsingleton (↥(twistChart A (m + 1) (-d - (((m + 1 : ℕ) : ℤ) + 1))
      (∅ : Set (Fin (m + 1 + 1)))) →ₗ[A] A) :=
    ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0]; simp⟩
  exact IsZero.of_iso (ModuleCat.isZero_of_iff_subsingleton.2 hhom)
    (serreTwistCohomology A m d).degreeTop

/-- **`H^q(ℙⁿ_A, 𝒪(d)) = 0` for `q > 0` and `-n ≤ d`.** The case of Serre's computation
([Stacks, Tag 01XU]) that the proof of [Stacks, Tag 0FUK] quotes for the twisted sequences. -/
theorem isZero_twistCohomology_of_pos {d : ℤ} (hd : -((m : ℤ) + 1) ≤ d) {q : ℕ} (hq : 0 < q) :
    IsZero (twistCohomology A (m + 1) d q) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rcases eq_or_ne (r + 1) (m + 1) with h | h
  · rw [h]
    exact isZero_twistCohomology_top hd
  · exact (serreTwistCohomology A m d).vanishing r h

/-- **`H^q(ℙⁿ_A, 𝒪(d)) = 0` in every degree for `-n ≤ d < 0`.** This is the statement the source
uses as "`𝒪(-1)` has vanishing cohomology in all degrees", in the range of twists where it
holds. -/
@[ega "III 2.1.13" "Vanishing of H^i(P^r_A"]
theorem isZero_twistCohomology_of_neg {d : ℤ} (hd : -((m : ℤ) + 1) ≤ d) (hd' : d < 0) (q : ℕ) :
    IsZero (twistCohomology A (m + 1) d q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact isZero_twistCohomology_zero hd'
  · exact isZero_twistCohomology_of_pos hd hq

/-- **The acyclicity of the twists of the structure sheaf on `ℙⁿ_A`**, as a statement about the
sheaf-level cohomology: in every degree for `-n ≤ d < 0`, and in every positive degree for
`-n ≤ d`. -/
theorem isZero_cohomologySheaf_twistingSheaf {d : ℤ} (hd : -((m : ℤ) + 1) ≤ d) (q : ℕ)
    (hq : d < 0 ∨ 0 < q) :
    IsZero (cohomologySheaf A m
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) d) q) := by
  refine (isZero_restrictScalars_iff (coeffScalar A (m + 1)) _).1 ?_
  rcases hq with hq | hq
  · exact isZero_twistCohomology_of_neg hd hq q
  · exact isZero_twistCohomology_of_pos hd hq

/-- The degree-zero part of `A[T₀, …, Tₙ]` is `A`: the constants. -/
def twistChartZeroEquiv : ↥(twistChart A (m + 1) 0 (∅ : Set (Fin (m + 1 + 1)))) ≃ₗ[A] A :=
  (twistChartEmptyLinearEquiv (R := A) (m + 1) (le_refl (0 : ℤ))).trans
    ((LinearEquiv.ofEq _ _ (by
        rw [show ((0 : ℤ)).toNat = 0 from rfl, MvPolynomial.homogeneousSubmodule_zero,
          Submodule.one_eq_range])).trans
      (LinearEquiv.ofInjective (Algebra.linearMap A (MvPolynomial (Fin (m + 1 + 1)) A))
        (fun _ _ hxy => MvPolynomial.C_injective _ _ hxy)).symm)

/-- **`H⁰(ℙⁿ_A, 𝒪) = A`.** The generator the source takes the boundary of is `1`. -/
def twistingSheafZeroCohomologyIso :
    cohomology A m (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 0) 0 ≅
      ModuleCat.of A A :=
  (serreTwistCohomology A m 0).degreeZero ≪≫ (twistChartZeroEquiv (A := A) (m := m)).toModuleIso

/-- `Ω⁰_{ℙⁿ_A/A} = 𝒪 = 𝒪(0)`: the degree-zero exterior power is the structure sheaf, which is the
zeroth twist. -/
def formsZeroIso :
    forms A m 0 ≅ ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 0 :=
  Scheme.Hom.relativeDifferentialFormsZeroIso (projToSpecCoeff A (m + 1)) ≪≫
    (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit
      (polyGrading A (m + 1))).symm

end Serre

/-! ### Acyclicity of the middle terms of the filtration -/

section Middle

variable {A m}

/-- A finite biproduct of sheaves with vanishing `q`-th cohomology has vanishing `q`-th
cohomology: the derived functor is additive, so it commutes with the biproduct. The index type is
`Fin k`, which is the shape the middle terms of the filtration come in. -/
theorem isZero_cohomologySheaf_biproduct {k : ℕ}
    (G : Fin k → (projSpace A m).Modules) (q : ℕ)
    (h : ∀ i, IsZero (cohomologySheaf A m (G i) q)) :
    IsZero (cohomologySheaf A m (⨁ G) q) := by
  refine IsZero.of_iso ?_ (((globalSections A m).rightDerived q).mapBiproduct G)
  rw [IsZero.iff_id_eq_zero]
  refine biproduct.hom_ext' _ _ fun i => ?_
  rw [Category.comp_id, Limits.comp_zero]
  exact (h i).eq_of_src _ _

/-- **The untwisted middle term is acyclic.** For `1 ≤ p ≤ n` the sheaf
`⋀ᵖ(𝒪(-1)^{⊕ n+1}) = 𝒪(-p)^{⊕ binom(n+1, p)}` has vanishing cohomology in every degree, because
`-n ≤ -p < 0`. -/
theorem isZero_cohomologySheaf_eulerWedge {p : ℕ} (hp : 0 < p) (hp' : p ≤ m + 1) (q : ℕ) :
    IsZero (cohomologySheaf A m (eulerWedge A m p 0) q) := by
  refine isZero_cohomologySheaf_biproduct (eulerWedgeFamily A m p 0) q fun _ => ?_
  exact isZero_cohomologySheaf_twistingSheaf (by omega) q (Or.inl (by omega))

/-- **The twisted middle term is acyclic in positive degrees.** For `k > 0` and `1 ≤ p ≤ n + 1`
the sheaf `⋀ᵖ(𝒪(-1)^{⊕ n+1})(k) = 𝒪(k - p)^{⊕ binom(n+1, p)}` has vanishing cohomology in every
positive degree, because `k - p ≥ 1 - (n + 1) = -n`. -/
@[ega "III 2.1.12" "Clause (i)", sga "7 XIX 1.2" "special case"]
theorem isZero_cohomologySheaf_eulerWedge_twist {k : ℤ} (hk : 0 < k) {p : ℕ} (hp : p ≤ m + 2)
    {q : ℕ} (hq : 0 < q) :
    IsZero (cohomologySheaf A m (eulerWedge A m p k) q) := by
  refine isZero_cohomologySheaf_biproduct (eulerWedgeFamily A m p k) q fun _ => ?_
  exact isZero_cohomologySheaf_twistingSheaf (by omega) q (Or.inr hq)

end Middle

/-! ### Clauses (1) and (2): the untwisted Hodge cohomology -/

section Untwisted

variable {A m}

/-- **The ascending induction of the source's proof.** For `p ≤ n` the sheaf-level cohomology
`H^q(ℙⁿ_A, Ωᵖ)` vanishes for `q ≠ p`, and `H^p(ℙⁿ_A, Ωᵖ)` is isomorphic to `H⁰(ℙⁿ_A, 𝒪)`.

The step is the dimension shift along `0 → Ω^{p+1} → ⋀^{p+1}(𝒪(-1)^{⊕ n+1}) → Ωᵖ → 0` whose
middle term is acyclic: that makes `H^r(Ωᵖ) ≅ H^{r+1}(Ω^{p+1})` for every `r`, and makes
`H⁰(Ω^{p+1})` embed in the zero module `H⁰(⋀^{p+1}(𝒪(-1)^{⊕ n+1}))`. -/
private theorem hodge_induction : ∀ p : ℕ, p ≤ m + 1 →
    (∀ q : ℕ, q ≠ p → IsZero (cohomologySheaf A m (forms A m p) q)) ∧
      Nonempty (cohomologySheaf A m (forms A m p) p ≅
        cohomologySheaf A m
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 0) 0) := by
  intro p
  induction p with
  | zero =>
      intro _
      refine ⟨fun q hq => ?_, ⟨Functor.mapIso _ (formsZeroIso (A := A) (m := m))⟩⟩
      refine IsZero.of_iso ?_ (Functor.mapIso _ (formsZeroIso (A := A) (m := m)))
      exact isZero_cohomologySheaf_twistingSheaf (by omega) q
        (Or.inr (Nat.pos_of_ne_zero hq))
  | succ p ih =>
      intro hp
      obtain ⟨hvan, ⟨hiso⟩⟩ := ih (by omega)
      obtain ⟨a, b, w, hS⟩ := (eulerFiltrationData A m).shortExact_wedge p (by omega)
      have hmid : ∀ r : ℕ,
          IsZero (cohomologySheaf A m (eulerWedge A m (p + 1) 0) r) := fun r =>
        isZero_cohomologySheaf_eulerWedge (Nat.succ_pos p) hp r
      -- the dimension shift `H^r(Ωᵖ) ≅ H^{r+1}(Ω^{p+1})`
      have hshift : ∀ r : ℕ, Nonempty (cohomologySheaf A m (forms A m p) r ≅
          cohomologySheaf A m (forms A m (p + 1)) (r + 1)) := fun r =>
        Stacks.Cohomology.RightDerivedDelta.nonempty_iso_rightDerived hS
          (globalSections A m) r (hmid r) (hmid (r + 1))
      -- degree zero vanishes because it embeds in an acyclic module
      have hzero : IsZero (cohomologySheaf A m (forms A m (p + 1)) 0) := by
        have hmono := Stacks.Cohomology.RightDerivedDelta.Horseshoe.mono_rightDerived_zero_map_f
          (Stacks.Cohomology.RightDerivedDelta.horseshoe hS) (globalSections A m)
        rw [IsZero.iff_id_eq_zero, ← cancel_mono (((globalSections A m).rightDerived 0).map a),
          Category.id_comp, Limits.zero_comp]
        exact (hmid 0).eq_of_tgt _ _
      refine ⟨fun q hq => ?_, ?_⟩
      · cases q with
        | zero => exact hzero
        | succ r =>
          obtain ⟨e⟩ := hshift r
          exact IsZero.of_iso (hvan r (by omega)) e.symm
      · obtain ⟨e⟩ := hshift p
        exact ⟨e.symm ≪≫ hiso⟩

/-- **Clause (1) of [Stacks, Tag 0FUK].** `H^q(ℙⁿ_A, Ωᵖ) = 0` unless `0 ≤ p = q ≤ n`. -/
@[stacks 0FUK "clause (1)"]
theorem isZero_hodgeCohomology (p q : ℕ) (hpq : ¬(p = q ∧ p ≤ m + 1)) :
    IsZero (hodgeCohomology A m p q) := by
  refine (isZero_restrictScalars_iff (coeffScalar A (m + 1)) _).2 ?_
  by_cases hp : p ≤ m + 1
  · exact (hodge_induction p hp).1 q fun hq => hpq ⟨hq.symm, hp⟩
  · exact ((globalSections A m).rightDerived q).map_isZero
      (ProjectiveSpaceForms.isZero_relativeDifferentialForms_of_lt m p (by omega))

/-- **Clause (2) of [Stacks, Tag 0FUK].** For `0 ≤ p ≤ n` the `A`-module `H^p(ℙⁿ_A, Ωᵖ)` is
isomorphic to `A`; its generator is, in the source, the `p`-fold boundary of
`1 ∈ H⁰(ℙⁿ_A, 𝒪)`. -/
@[stacks 0FUK "clause (2), as an isomorphism with `A`"]
theorem nonempty_hodgeCohomology_diag_iso (p : ℕ) (hp : p ≤ m + 1) :
    Nonempty (hodgeCohomology A m p p ≅ ModuleCat.of A A) := by
  obtain ⟨e⟩ := (hodge_induction (A := A) (m := m) p hp).2
  exact ⟨Functor.mapIso _ e ≪≫ twistingSheafZeroCohomologyIso⟩

/-- **Clause (2) of [Stacks, Tag 0FUK], as freeness.** For `0 ≤ p ≤ n` the `A`-module
`H^p(ℙⁿ_A, Ωᵖ)` is free, being isomorphic to `A`. -/
@[stacks 0FUK "clause (2), freeness"]
theorem free_hodgeCohomology_diag (p : ℕ) (hp : p ≤ m + 1) :
    Module.Free A ↥(hodgeCohomology A m p p) := by
  obtain ⟨e⟩ := nonempty_hodgeCohomology_diag_iso (A := A) (m := m) p hp
  exact Module.Free.of_equiv e.toLinearEquiv.symm

end Untwisted

/-! ### Clause (3): the twisted Hodge cohomology -/

section Twisted

variable {A m}

/-- `Ωᵖ(k) = 0` for `p > n`, the twist being additive. -/
private theorem isZero_twistedForms_of_lt {p : ℕ} (hp : m + 1 < p) (k : ℤ) :
    IsZero (twistedForms A m p k) :=
  (Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor
    (polyGrading A (m + 1)) k).map_isZero
    (ProjectiveSpaceForms.isZero_relativeDifferentialForms_of_lt m p hp)

/-- **The descending induction of the source's proof.** For `k > 0` the sheaf-level cohomology
`H^q(ℙⁿ_A, Ωᵖ(k))` vanishes in every positive degree, for every `p`.

The induction runs downwards from `p = n + 2`, where `Ωᵖ = 0`. The step reads off the sequence
`0 → Ω^{p+1}(k) → ⋀^{p+1}(𝒪(-1)^{⊕ n+1})(k) → Ωᵖ(k) → 0` that `H^q` of the quotient vanishes as
soon as `H^q` of the acyclic middle term and `H^{q+1}` of the sub do. -/
private theorem twisted_induction {k : ℤ} (hk : 0 < k) :
    ∀ j p : ℕ, p + j = m + 2 → ∀ q : ℕ, 0 < q →
      IsZero (cohomologySheaf A m (twistedForms A m p k) q) := by
  intro j
  induction j with
  | zero =>
      intro p hpj q _
      exact ((globalSections A m).rightDerived q).map_isZero
        (isZero_twistedForms_of_lt (by omega) k)
  | succ j ih =>
      intro p hpj q hq
      obtain ⟨a, b, w, hS⟩ :=
        (eulerFiltrationData A m).shortExact_wedge_twist k hk p (by omega)
      refine Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃ hS
        (globalSections A m) q ?_ ?_
      · exact isZero_cohomologySheaf_eulerWedge_twist (p := p + 1) hk (by omega) hq
      · exact ih (p + 1) (by omega) (q + 1) (by omega)

/-- **Clause (3) of [Stacks, Tag 0FUK].** For `q > 0`, `k > 0` and arbitrary `p` we have
`H^q(ℙⁿ_A, Ωᵖ(k)) = 0`. -/
@[stacks 0FUK "clause (3)"]
theorem isZero_twistedHodgeCohomology (p : ℕ) {k : ℤ} (hk : 0 < k) {q : ℕ} (hq : 0 < q) :
    IsZero (twistedHodgeCohomology A m p k q) := by
  refine (isZero_restrictScalars_iff (coeffScalar A (m + 1)) _).2 ?_
  by_cases hp : p ≤ m + 2
  · exact twisted_induction hk (m + 2 - p) p (by omega) q hq
  · exact ((globalSections A m).rightDerived q).map_isZero
      (isZero_twistedForms_of_lt (by omega) k)

end Twisted

/-! ### The Hodge first Chern class of `𝒪(1)` -/

section ChernClass

/-- **`𝒪(1)` is an invertible sheaf on `ℙⁿ_A`**, by [Stacks, Tag 01MT]: the standard opens
`D₊(Tᵢ)` cover `ℙⁿ_A` and `Tᵢ` trivializes `𝒪(1)` on `D₊(Tᵢ)`. -/
theorem isInvertible_twistingSheafOne :
    Stacks.SheafOfModules.IsInvertible (projSpace A m).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf (projSpace A m).toRingedSpace)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 1) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
    (Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf
      (polyGrading A (m + 1)) (degreeOneCover_polyGrading A m) 1)

/-- **The class of `𝒪(1)` in `Pic(ℙⁿ_A)`.** Its Hodge first Chern class
`c₁^{Hodge}(𝒪(1)) ∈ H¹(ℙⁿ_A, Ω)` is the basis element of [Stacks, Tag 0FMI] in degree one. -/
def twistingSheafOnePicardClass : Stacks.Picard.ofScheme (projSpace A m) :=
  Stacks.SheafOfModules.picardClass (projSpace A m).toRingedSpace.presheaf
    (Stacks.RingedSpace.structureIsSheaf (projSpace A m).toRingedSpace)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 1)
    (isInvertible_twistingSheafOne A m)

/-- **The Hodge first Chern class of `𝒪(1)` on `ℙⁿ_A`**, `c₁^{Hodge}(𝒪(1)) ∈ H¹(ℙⁿ_A, Ω)`, read
in sheaves of abelian groups as [Stacks, Tag 0FMD] forms it. -/
@[sga "7 XI 1.0" "special case", sga "7 XI 1.5" "special case"]
abbrev hodgeFirstChernClassTwistingSheafOne :
    AlgebraicGeometry.Scheme.Hom.hodgeCohomologyOne (projToSpecCoeff A (m + 1)) :=
  AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass (projToSpecCoeff A (m + 1))
    (twistingSheafOnePicardClass A m)

end ChernClass

/-! ### Degree zero, and the connecting map of a chosen filtration sequence -/

section Connecting

/-- **`H⁰(ℙⁿ_A, Ω⁰) = A`.** The zeroth exterior power of `Ω` is the structure sheaf and the
global functions on `ℙⁿ_A` are the constants, so the generator in degree zero is the unit
section `1`. -/
def hodgeCohomologyZeroIso : hodgeCohomology A m 0 0 ≅ ModuleCat.of A A :=
  (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).mapIso
      (Functor.mapIso ((globalSections A m).rightDerived 0) (formsZeroIso (A := A) (m := m))) ≪≫
    twistingSheafZeroCohomologyIso (A := A) (m := m)

/-- `H⁰(ℙⁿ_A, Ω⁰) = A`, as an `A`-linear equivalence. -/
def hodgeCohomologyZeroLinearEquiv : ↥(hodgeCohomology A m 0 0) ≃ₗ[A] A :=
  (hodgeCohomologyZeroIso A m).toLinearEquiv

variable {A m}

/-- **The connecting map `H^p(ℙⁿ_A, Ωᵖ) ⟶ H^{p+1}(ℙⁿ_A, Ω^{p+1})`** of a short exact sequence
`0 → Ω^{p+1} → ⋀^{p+1}(𝒪(-1)^{⊕ n+1}) → Ωᵖ → 0`, read as a map of `A`-modules. It is the
boundary the proof of [Stacks, Tag 0FMI] takes of the `p`-th Chern power. -/
def wedgeDelta {p : ℕ} {a : forms A m (p + 1) ⟶ eulerWedge A m (p + 1) 0}
    {b : eulerWedge A m (p + 1) 0 ⟶ forms A m p} {w : a ≫ b = 0}
    (hS : (ShortComplex.mk a b w).ShortExact) :
    hodgeCohomology A m p p ⟶ hodgeCohomology A m (p + 1) (p + 1) :=
  (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).map
    ((Stacks.Cohomology.RightDerivedDelta.horseshoe hS).delta (globalSections A m) p)

/-- **The connecting map is an isomorphism for `p ≤ n - 1`**, because the middle term
`⋀^{p+1}(𝒪(-1)^{⊕ n+1}) = 𝒪(-p-1)^{⊕ binom(n+1, p+1)}` of the sequence is acyclic in degrees
`p` and `p + 1`. This is the dimension shift of the proof of [Stacks, Tag 0FUK], applied to a
chosen sequence rather than to an existential one. -/
theorem isIso_wedgeDelta {p : ℕ} (hp : p ≤ m)
    {a : forms A m (p + 1) ⟶ eulerWedge A m (p + 1) 0}
    {b : eulerWedge A m (p + 1) 0 ⟶ forms A m p} {w : a ≫ b = 0}
    (hS : (ShortComplex.mk a b w).ShortExact) : IsIso (wedgeDelta hS) :=
  ((ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).mapIso
    (@asIso _ _ _ _ _ ((Stacks.Cohomology.RightDerivedDelta.horseshoe hS).isIso_delta
      (globalSections A m) p
      (isZero_cohomologySheaf_eulerWedge (Nat.succ_pos p) (by omega) p)
      (isZero_cohomologySheaf_eulerWedge (Nat.succ_pos p) (by omega) (p + 1))))).isIso_hom

end Connecting

/-! ### [Stacks, Tag 0FMI], the vanishing -/

section ChernBasis

variable {A m}

/-- **[Stacks, Tag 0FMI], the vanishing.** `H^q(ℙⁿ_A, Ωᵖ) = 0` unless `0 ≤ p = q ≤ n`. The
source quotes this from [Stacks, Tag 0FUK], and so does the proof. The basis assertion of
[Stacks, Tag 0FMI] is `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.exists_basis_chernPow`. -/
@[stacks 0FMI "H^q(ℙⁿ_A, Ω^p) = 0 unless 0 ≤ p = q ≤ n"]
theorem isZero_hodgeCohomology_of_ne_or_gt (p q : ℕ)
    (hpq : p ≠ q ∨ m + 1 < p) : IsZero (hodgeCohomology A m p q) := by
  refine isZero_hodgeCohomology p q fun hc => ?_
  rcases hpq with hne | hgt
  · exact hne hc.1
  · exact absurd hc.2 (by omega)

end ChernBasis

end Stacks.AlgebraicGeometry.ProjectiveSpaceHodge

end
