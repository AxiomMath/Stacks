module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetUnion
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# One closed subset proper over the base carrying the whole cohomological support

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type and let `E` be an object of `D(𝒪_X)`.  The chapter states "the support of `H^i(E)` is proper
over `Y`" in two ways: degreewise, as `AlgebraicGeometry.Space.HasProperSupport` of Stacks 0CZD
for each cohomology module, which is the form Stacks 08GK consumes and the form Stacks 08IS and
Stacks 0D0R hypothesize; and as a *single* closed subset `T ⊆ |X|` proper over `Y` on which `E`
is supported in the sense of Stacks 08GF, which is the form
`AlgebraicGeometry.Space.CohomologySupportedOn` takes and the form in which the chapter's later
sections — Stacks 0DKJ among them — carry the condition.  This file proves that for a
cohomologically bounded `E` the two agree.

The passage from the degreewise form to the single subset is the second paragraph of the source's
proof of Stacks 08IS: "let `T ⊂ |X|` be the union of the supports of `H^i(E)` for all `i`; then
`T` is proper over `Y` by assumptions (1) and (2) and Lemma 0CZH".

## Main results

* `AlgebraicGeometry.Space.exists_isClosed_isProperOver_of_eventually_empty`: a `ℤ`-indexed
  family of subsets of `|X|`, almost all empty and each inside a closed subset proper over `Y`,
  lies inside one closed subset proper over `Y`.
* `AlgebraicGeometry.Space.exists_isClosed_isProperOver_cohomologySupportedOn`: a
  cohomologically bounded object of `D(𝒪_X)` each of whose cohomology modules has support proper
  over `Y` is supported on a single closed subset of `|X|` proper over `Y`.
* `AlgebraicGeometry.Space.hasProperSupport_homology_of_cohomologySupportedOn`: conversely, an
  object supported on a closed subset proper over `Y` has every cohomology module of proper
  support, as soon as those supports are closed.
* `AlgebraicGeometry.Space.hasProperSupport_homology_of_cohomologySupportedOn_of_isCoherent`:
  the same with the closedness supplied by coherence of the cohomology modules, which is the
  form in which Stacks 08IS has it.
* `AlgebraicGeometry.Space.hasProperSupport_homology_iff_exists_isClosed_isProperOver`: the two
  readings, equivalent for an object of `D^b_{Coh}(𝒪_X)`.

## Implementation notes

*Why boundedness is needed in one direction only.*  The union of the supports is a union over all
of `ℤ`, and Stacks 0CZH — `AlgebraicGeometry.Space.isProperOver_iUnion` — covers only a finite
union.  Boundedness confines the nonvanishing cohomology to an interval `[a, b]`, whose integers
form a finite type; outside it the cohomology module is zero, so its support is empty by
`AlgebraicGeometry.Space.supportOfSheaf_eq_empty_iff_isZero` and contributes nothing.  The
converse direction is Stacks 0CZE, `AlgebraicGeometry.Space.isProperOver_of_subset`, applied
degreewise, and needs no bound; what it does need is closedness of each support, which
`AlgebraicGeometry.Space.HasProperSupport` carries as an existential witness and a containment
of supports does not supply.  For a coherent module it is Stacks 07TZ, through the finite type
of Stacks 03DL(8).

*Boundedness is taken as `DerivedCategoryB.IsBounded`*, the conjunction of the two vanishing
bounds, which is the first component of
`DerivedCategoryB.derivedCategoryBBounded (AlgebraicGeometry.Space.isCoherent …)` — so a
hypothesis `E ∈ D^b_{Coh}(𝒪_X)` supplies it as `hE.1` and the coherence of the third statement
as `hE.2`.

*The module universe* is free in the first two statements, as it is in
`AlgebraicGeometry.Space.CohomologySupportedOn` and in
`AlgebraicGeometry.Space.HasProperSupport`; the two sheafification hypotheses under which the
`𝒪_X`-modules at a free universe have an abelian structure and a derived category are the
binders of `CohomologySupportedOn`.  The third statement is at the universe `u` of the structure
rings, where the passage from coherence to finite type,
`AlgebraicGeometry.Space.isFiniteTypeOnSite_of_isCoherentOnSite`, is available.

## What this does *not* reach, and where each obstruction is

The reduction above is the one step of the source's proof of **Stacks 08IS** — for `f` locally of
finite type and quasi-separated with `Y` Noetherian, an object of `D^b_{Coh}(𝒪_X)` whose
cohomological support is proper over `Y` and which has finite Tor dimension over `f^{-1}𝒪_Y` has
perfect `Rf_*E` — that this library proves.  That lemma is registered on no declaration of this
development, and the four remaining steps of its proof are each missing a cited result.  Each
entry below names the nearest available statement and what it still carries.

* `Rf_*E ∈ D^b_{Coh}(𝒪_Y)`, the source's Stacks 08GK.  No declaration of this tree states it;
  only the clause "bounded below", which is left t-exactness of `Rf_*`, is proved, as
  `AlgebraicGeometry.Space.isGE_derivedModulePushforward_obj` in
  `StacksFrontier/AlgebraicGeometry/Spaces/DerivedPushforwardBoundedBelow.lean`, whose own notes
  record the other two clauses as out of reach.  Coherence of the cohomology sheaves is
  Stacks 08GC, carried by
  `AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_hasProperSupport`
  (`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ProperSupportCoherentPushforward.lean`,
  line 206) with the three inputs `h03DW`, `h08AR` and `h0734`; the library's Stacks 08AR,
  `AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_isProper`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ProperHigherDirectImageCoherence.lean`, line 312),
  itself carries Stacks 0720, the dévissage of Stacks 08AN and the integral-subspace witness
  that the source draws from Chow's lemma for algebraic spaces.  Boundedness above is
  Stacks 073G, whose two library forms in
  `StacksFrontier/AlgebraicGeometry/Spaces/UniformHigherDirectImageVanishing.lean` (lines 252 and
  332) both carry `AlgebraicGeometry.Space.SchemeBaseUniformVanishing` and so produce no bound;
  Stacks 08FA has no presence.
* `D^b_{Coh}(𝒪_Y) ⊆ D^-_{Coh}(𝒪_Y)` pseudo-coherent, the source's Stacks 08IK in the direction
  (1) ⇒ (2).  Only (2) ⇒ (1) is in this library, as
  `AlgebraicGeometry.Space.isCoherentOnSite_homology_of_isPseudoCoherentFrom_of_isNoetherian`
  (`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherent/CoherentCohomology.lean`, line 382); the
  missing ingredient, recorded at line 111 of that file, is that a coherent module placed in a
  single degree is pseudo-coherent on a ringed site, which asks for étale-locally arbitrarily
  long finite free resolutions and has no statement anywhere in the development.
* pseudo-coherent together with finite Tor dimension gives perfect, the source's
  Stacks 08G8.  Its library form, `isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension`
  in the namespace `Stacks.SheafOfModules.DerivedTensorProduct`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/PerfectnessCriterion.lean`, line 245), is
  pinned to a `AlgebraicGeometry.RingedSite.{0, 0, 0}` while
  `AlgebraicGeometry.Space.smallEtaleRingedSite` is a `RingedSite.{u + 1, u, u}`; the pin comes
  from Stacks 08G7 and the files it passes through, and the implementation notes of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/PerfectnessCriterion.lean`, line 91,
  name them.  Perfectness being local on the small étale site is an obstruction of the same
  shape and not a way around it: the only locality statement is
  `AlgebraicGeometry.RingedSite.isPerfect_of_locally`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/LocalNature.lean`, line 133), stated at
  `RingedSite.{u, u, 0}` with `SheafOfModules.{0}`, and there is no space-level form.  The
  `u = u` half of that pin is inherited from Stacks 08FR; the `0` half is not — Stacks 08FR
  itself, `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`, is stated at a free
  module universe, as are both halves of Stacks 08G6 (1) in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/LocalModels.lean`.
* `Rf_*(E) ⊗^L_{𝒪_Y} ℱ = Rf_*(E ⊗^L_{f^{-1}𝒪_Y} f^{-1}ℱ)` for quasi-coherent `ℱ`, the source's
  Stacks 08IN with Stacks 08I6, and the test-module reduction Stacks 08IL.  Of the three only
  Stacks 08I6 is proved, as `Stacks.Cohomology.MixedDerivedTensor.derivedMixedTensorIso`.
  Stacks 08IN appears only as the invertibility hypothesis of
  `AlgebraicGeometry.Space.PullbackComparisonData.projectionFormulaMap`
  (`StacksFrontier/AlgebraicGeometry/Spaces/DualityPullbackComparison.lean`, line 221), and of
  Stacks 08IL only (1) ⇒ (2) is proved, as
  `AlgebraicGeometry.Space.hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude`
  (`StacksFrontier/AlgebraicGeometry/Spaces/TorAmplitudeQuasiCoherentTests.lean`, line 165), whose
  documentation lists the five inputs its converse needs.

## References

* [Stacks Project, Lemma 75.22.1 (Tag 08IS)](https://stacks.math.columbia.edu/tag/08IS)
* [Stacks Project, Lemma 75.7.6 (Tag 0CZH)](https://stacks.math.columbia.edu/tag/0CZH)
* [Stacks Project, Definition 75.3.2 (Tag 08GF)](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZE](https://stacks.math.columbia.edu/tag/0CZE)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

section Bookkeeping

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)

/-- **A `ℤ`-indexed family of subsets of `|X|`, almost all empty and each inside a closed subset
proper over `Y`, lies inside one closed subset proper over `Y`.**

Only the members indexed by the interval `[a, b]` can be nonempty, and that interval contains
finitely many integers, so the supremum of the closed subsets attached to them is the finite
union Stacks 0CZH covers; the containments are Stacks 0CZE. -/
theorem exists_isClosed_isProperOver_of_eventually_empty
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (s : ℤ → Set (points B S hS X)) (a b : ℤ)
    (hvanish : ∀ i : ℤ, i ∉ Set.Icc a b → s i = ∅)
    (hmem : ∀ i : ℤ, ∃ (Z : Set (points B S hS X)) (hZ : IsClosed Z),
      IsProperOver B S hS hX hY f hf Z hZ ∧ s i ⊆ Z) :
    ∃ (T : Set (points B S hS X)) (hT : IsClosed T),
      IsProperOver B S hS hX hY f hf T hT ∧ ∀ i : ℤ, s i ⊆ T := by
  classical
  choose Z hZcl hZproper hZsub using hmem
  have hfin : Finite (Set.Icc a b : Set ℤ) := (Set.finite_Icc a b).to_subtype
  refine ⟨⋃ j : (Set.Icc a b : Set ℤ), Z (j : ℤ),
    isClosed_iUnion_of_finite fun j ↦ hZcl (j : ℤ),
    isProperOver_iUnion B S hS hX hY f hf (fun j : (Set.Icc a b : Set ℤ) ↦ Z (j : ℤ))
      (fun j ↦ hZcl (j : ℤ)) (fun j ↦ hZproper (j : ℤ)), fun i ↦ ?_⟩
  by_cases hi : i ∈ Set.Icc a b
  · exact (hZsub i).trans (Set.subset_iUnion (fun j : (Set.Icc a b : Set ℤ) ↦ Z (j : ℤ)) ⟨i, hi⟩)
  · rw [hvanish i hi]
    exact Set.empty_subset _

end Bookkeeping

section FreeUniverse

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    [HasSheafify (smallEtaleRingedSite B S hS X hX).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS X hX).J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **A cohomologically bounded object of `D(𝒪_X)` whose cohomology modules have support proper
over `Y` is supported on one closed subset of `|X|` proper over `Y`.**

This is the step "let `T ⊂ |X|` be the union of the supports of `H^i(E)` for all `i`; then `T` is
proper over `Y`" of the source's proof of Stacks 08IS.  Only finitely many integers lie in the
interval supplied by the boundedness hypothesis, so the union over them is the finite union
Stacks 0CZH covers; outside it the cohomology modules vanish and their supports are empty. -/
theorem exists_isClosed_isProperOver_cohomologySupportedOn
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (E : DerivedCategory (Modules.{u, m} B S hS X hX))
    (hbdd : DerivedCategoryB.IsBounded E)
    (hproper : ∀ i : ℤ, HasProperSupport B S hS hX hY f hf
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, m} B S hS X hX) i).obj E))) :
    ∃ (T : Set (points B S hS X)) (hT : IsClosed T),
      IsProperOver B S hS hX hY f hf T hT ∧ CohomologySupportedOn B S hS X hX T E := by
  obtain ⟨a, ha⟩ := hbdd.1
  obtain ⟨b, hb⟩ := hbdd.2
  refine exists_isClosed_isProperOver_of_eventually_empty B S hS hX hY f hf
    (fun i ↦ supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, m} B S hS X hX) i).obj E))) a b
    (fun i hi ↦ ?_) (fun i ↦ ?_)
  · refine (supportOfSheaf_eq_empty_iff_isZero B S hS ⟨X, hX⟩ _).2 ?_
    rcases lt_or_ge i a with h | h
    · exact ha i h
    · exact hb i (by simp only [Set.mem_Icc, not_and, not_le] at hi; exact hi h)
  · obtain ⟨hclosed, hproperi⟩ := hproper i
    exact ⟨_, hclosed, hproperi, subset_rfl⟩

/-- **An object of `D(𝒪_X)` supported on a closed subset proper over `Y` has every cohomology
module of proper support**, as soon as those supports are closed.  The containment of each
support in the proper closed subset is Stacks 0CZE. -/
theorem hasProperSupport_homology_of_cohomologySupportedOn
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (hTproper : IsProperOver B S hS hX hY f hf T hT)
    (E : DerivedCategory (Modules.{u, m} B S hS X hX))
    (hE : CohomologySupportedOn B S hS X hX T E)
    (hcl : ∀ i : ℤ, IsClosed (supportOfSheaf B S hS X
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, m} B S hS X hX) i).obj E))))
    (i : ℤ) :
    HasProperSupport B S hS hX hY f hf
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, m} B S hS X hX) i).obj E)) :=
  ⟨hcl i, isProperOver_of_subset B S hS hX hY f hf _ T (hcl i) hT (hE i) hTproper⟩

end FreeUniverse

section Coherent

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)

/-- **An object of `D(𝒪_X)` with coherent cohomology supported on a closed subset proper over
`Y` has every cohomology module of proper support.**

This is
`AlgebraicGeometry.Space.hasProperSupport_homology_of_cohomologySupportedOn` with the closedness
of the supports read off coherence: a coherent module is of finite type by Stacks 03DL(8) and the
support of a module of finite type is closed by Stacks 07TZ.  It is the passage from the
single-subset hypothesis — one closed subset proper over the base carrying the whole
cohomological support, which is the form the later sections of the chapter produce — to the
degreewise hypothesis that Stacks 08GK and Stacks 08IS consume. -/
theorem hasProperSupport_homology_of_cohomologySupportedOn_of_isCoherent
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (hTproper : IsProperOver B S hS hX hY f hf T hT)
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hE : CohomologySupportedOn B S hS X hX T E)
    (hcoh : ∀ i : ℤ, IsCoherent B S hS X hX
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj E))
    (i : ℤ) :
    HasProperSupport B S hS hX hY f hf
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj E)) :=
  hasProperSupport_homology_of_cohomologySupportedOn B S hS hX hY f hf hT hTproper E hE
    (fun j ↦
      let := (hcoh j).toIsCoherentOnSite
      let := isFiniteTypeOnSite_of_isCoherentOnSite B S hS ⟨X, hX⟩
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).obj E)
      isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X hX _) i

/-- **For an object of `D^b_{Coh}(𝒪_X)` the chapter's two readings of "the cohomological support
is proper over `Y`" agree:** every cohomology module has support proper over `Y` exactly when
the object is supported, in the sense of Stacks 08GF, on a single closed subset of `|X|` proper
over `Y`.

The first reading is the hypothesis of Stacks 08GK, of Stacks 0D0R and of Stacks 08IS; the second
is `AlgebraicGeometry.Space.CohomologySupportedOn` of Stacks 08GF against a closed subset proper
over `Y` in the sense of Stacks 0CZD, which is the form in which the chapter's later sections
carry the condition.  Boundedness is used only for the forward implication and coherence only
for the backward one. -/
theorem hasProperSupport_homology_iff_exists_isClosed_isProperOver
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hbdd : DerivedCategoryB.IsBounded E)
    (hcoh : ∀ i : ℤ, IsCoherent B S hS X hX
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj E)) :
    (∀ i : ℤ, HasProperSupport B S hS hX hY f hf
        ((SheafOfModules.toSheaf _).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj E))) ↔
      ∃ (T : Set (points B S hS X)) (hT : IsClosed T),
        IsProperOver B S hS hX hY f hf T hT ∧ CohomologySupportedOn B S hS X hX T E :=
  ⟨exists_isClosed_isProperOver_cohomologySupportedOn B S hS hX hY f hf E hbdd,
    fun ⟨_, hT, hTproper, hE⟩ ↦
      hasProperSupport_homology_of_cohomologySupportedOn_of_isCoherent B S hS hX hY f hf hT
        hTproper E hE hcoh⟩

end Coherent

end AlgebraicGeometry.Space

end
