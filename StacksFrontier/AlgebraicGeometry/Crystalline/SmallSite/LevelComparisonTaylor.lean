module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsPAdicComplete
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorCrystal07JG

/-!
# Four of the six fields of the comparison datum of [Stacks, Tag 07JG]

`Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG` is the datum the functor of
[Stacks, Lemma 60.17.3, Tag 07JG] is built from, and **every producer of it in this library
consumes a datum, so no closed term of it exists**.  When this module was written the only
producer was `...SmallSite.levelComparison07JGWholeSpaceOfRemaining` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelSectionsPAdicComplete.lean`, which
consumes five of its six fields, `isPAdicallyComplete` being the one already discharged.  This
module discharges three more, so that two of the six remain; the producers added since — in this
file, in `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelComparisonInterchange.lean` and
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelReductionAssembly.lean` — each consume the remainder in some form.

The three are `hasCoordinateOperators`, `isIntegrable` and `isTopologicallyQuasiNilpotent` —
item (07JD), item (07JE) and the non-vacuity of the two.  They are *not* discharged outright:
`Crystalline.isIntegrable_of_isThetaMonomialFamily` and
`Crystalline.isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CoordinateOperatorsUnique.lean` prove them from the
source's own `D(1)` and `D(2)` computations, and those computations are not in the tree.  What is
discharged is everything *else* those two theorems and `Crystalline.TaylorCrystal` ask for: the
tower of levels with its annihilation, the identification of the module with the limit of the
tower, and the Hausdorffness of item (07JB).  At the system of levels of
[Stacks, Proposition 60.21.1, Tag 07JN] all three come from
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelSectionsPAdicComplete.lean` and none is
a hypothesis.

So the module does two things.

First, it exhibits the module `M = lim_e Γ(T_e, ℱ)` of the tag as a
`Crystalline.TaylorCrystal` — `...SmallSite.LevelScalars07JG.taylorCrystal`.  Six of that
record's twelve data fields are supplied from the site rather than carried, at the system of
[Stacks, Tag 07JN]: `carrier` is `...SmallSite.LevelScalars07JG.sections`, `levels` is
`...LevelScalars07JG.levelSections`, `transition` is `...LevelScalars07JG.levelRestrict`,
`levelEquiv` is `...LevelScalars07JG.sectionsInvLimitEquiv`, and `shift` with `level_annihilate`
are the annihilation of the levels, which for that system is the theorem
`...SmallSite.pow_smul_eq_zero_wholeSpaceLevelSections`.  Before this, every term of
`Crystalline.TaylorCrystal` in the tree was `Crystalline.trivialTaylorCrystal`, the zero module
over the zero divided power ring; `...SmallSite.taylorCrystalWholeSpaceLevelSections` is the
first one whose module is a module of sections of a crystal over a system of levels of
`Cris(X/S)` and whose ring is the completed divided power envelope `D(n)` of [Stacks, Tag 07J8].

Second, it assembles the comparison datum from what remains —
`...SmallSite.levelComparison07JGWholeSpaceOfTaylor` — with **four of the six fields proved**.

## Main definitions

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `LevelScalars07JG.taylorCrystal` — **the module `M = lim_e Γ(T_e, ℱ)` of [Stacks, Tag 07JG] as
  a `Crystalline.TaylorCrystal`**, over a system of levels whose level `e` is annihilated by
  `p^{N + e}`, given a comparison datum on `M` and the coordinate operators of its expansion.
* `taylorCrystalWholeSpaceLevelSections` — the same at the system of
  [Stacks, Proposition 60.21.1, Tag 07JN], where the annihilation is not a hypothesis.
* `levelComparison07JGOfTaylor` and `levelComparison07JGWholeSpaceOfTaylor` — **the datum
  `...SmallSite.LevelComparison07JG` assembled with four of its six fields proved**, over an
  arbitrary system of levels with the annihilation and over the system of [Stacks, Tag 07JN]
  respectively.

## Main results

* `LevelScalars07JG.isHausdorff_sections` and `isHausdorff_wholeSpaceLevelScalars_sections` —
  **the Hausdorff half of item (07JB) for the module of the tag**, which is what the proofs of
  items (07JD) and (07JE) consume.  At the system of [Stacks, Tag 07JN] it is unconditional.

## What is and is not proved

**No `@[stacks]` attribute is placed in this module.**  [Stacks, Tag 07JG],
[Stacks, Proposition 60.17.4, Tag 07JH] and [Stacks, Proposition 60.21.3, Tag 07LG] are
`...SmallSite.crystalPairFunctor`, `...SmallSite.crystalPairFunctor_isEquivalence` and
`...SmallSite.crystalPairDeRhamComplex_computesCohomology`, built directly from the whole-space
system and not through the level datum of this module.
In particular `...SmallSite.levelComparison07JGWholeSpaceOfTaylor` still consumes hypotheses, so
it produces no term of `...SmallSite.LevelReduction07JG` and no term of
`...SmallSite.Reduction07JG`: the remark of the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceLevelScalars.lean` — that nothing
in the library makes any statement of [Stacks, Tag 07JH] or [Stacks, Tag 07LG] non-vacuous —
stands unchanged.

What changes is the list of what is consumed.  Of the six fields of
`...SmallSite.LevelComparison07JG`:

* `isPAdicallyComplete` — item (07JB) — is proved, from
  `...SmallSite.LevelScalars07JG.isPAdicallyComplete_sections` and the annihilation
  `...SmallSite.pow_smul_eq_zero_wholeSpaceLevelSections`, which is the content of
  `...SmallSite.isPAdicallyComplete_wholeSpaceLevelScalars_sections`.
* `hasCoordinateOperators`, `isIntegrable` and `isTopologicallyQuasiNilpotent` — items (07JD),
  (07JE) and the non-vacuity of the two — are proved here, from the hypotheses listed below.
* `comparison` and `comparison_naturality` are consumed, unchanged.

**The three hypotheses the proved statements run on are the source's own, and none of them is one of
the six fields.**

1. *The coordinate operators of the expansion over `D(1)`, and the identity `θ_K = ∏ θ_i^{k_i}`
   over `D(2)`*, as `theta`, `thetaPow`, `Crystalline.IsThetaMonomialFamily`,
   `Crystalline.IsCoordinateExpansion` and the `p`-adic convergence
   `finite_thetaPow_notMem_pSmul`.  These are the five fields of `Crystalline.TaylorCrystal` that
   record the source's two coefficient computations, and the module documentation of
   `StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCrystal07JG.lean` names them as the genuinely
   geometric input that is not derived.  Nothing here derives them either.
2. *A basis of `Ω` on the chosen differentials*, `b` and `hdx`.  This is carried exactly as
   `Crystalline.TaylorCrystal` carries it, and the generality is **finite**: `Ω_D` of
   [Stacks, Tag 07J9] is a *completed* direct sum, so the `d x_i` are a `Module.Basis` of it for
   finitely many coordinates and the library has no statement that they are one in general — only
   `Crystalline.dividedPowerDifferentialsBasis`, for the divided power *polynomial* algebra.  The
   statements below therefore do not apply to `Ω_D` of the source's own situation with infinitely
   many coordinates, and that is not hidden: `b` is an explicit argument.
3. *The comparison datum with its naturality*, which is the small-site form of
   `...GlobalCrystallineSituation.FirstOrderIdealBaseChange` read on the limit module.  At the
   structure sheaf it is available, as `...SmallSite.LevelScalars07JG.comparisonUnit`.  For a
   general crystal two things are missing and they should not be conflated.  At a *single*
   object of the site, the datum is equivalent to bijectivity of one base-change map, by
   `...bijective_firstOrderSectionsMap_iff_bijective_extensionSectionsMap`
   of `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean`, and that
   bijectivity is proved nowhere in the tree.  Beyond it, the field of
   `...SmallSite.LevelComparison07JG` is stated over `firstOrderExtension D Omega` and the
   *limit* module, not over one level, so even a level-by-level datum would have to be passed
   through the limit — and nothing here does that or assumes it can be done.  Both are left
   outside: `comparison` and `comparison_naturality` are taken whole.

**What is not consumed.**  The Hausdorffness that items (07JD) and (07JE)
need is *not* among the hypotheses: it is derived from item (07JB), which at the system of
[Stacks, Tag 07JN] is a theorem.  Nor are the tower of levels, its annihilation and the
identification of `M` with its limit: `Crystalline.TaylorCrystal` carries all five of those as
fields — `levels`, `transition`, `shift`, `level_annihilate` and `levelEquiv` — and
`...SmallSite.taylorCrystalWholeSpaceLevelSections` supplies every one of them from the site.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}

/-! ### The Hausdorff half of item (07JB) for the module of the tag -/

namespace LevelScalars07JG

variable (L : LevelScalars07JG S D)

/-- **The Hausdorff half of item (07JB) for `M = lim_e Γ(T_e, ℱ)`.**  A `p`-adically complete
module has nothing in every `p^n M`, so this follows from
`...SmallSite.LevelScalars07JG.isPAdicallyComplete_sections` under the same hypothesis: the level
`e` is annihilated by `p^{N + e}`.

It is separated out because it, and not completeness, is what the proofs of items (07JD) and
(07JE) consume — `Crystalline.eq_of_isCoordinateExpansion` needs exactly this. -/
theorem isHausdorff_sections (p : ℕ) (F : QuasiCoherentCrystal S) (N : ℕ)
    (hann : ∀ (e : ℕ) (x : L.levelSections F e), ((p : (D : Type u)) ^ (N + e)) • x = 0) :
    IsHausdorff (DividedPowers.pAdicIdeal (A := (D : Type u)) p) (L.sections F) := by
  have : IsAdicComplete (DividedPowers.pAdicIdeal (A := (D : Type u)) p) (L.sections F) :=
    L.isPAdicallyComplete_sections p F N hann
  infer_instance

/-! ### The module of the tag as a `Crystalline.TaylorCrystal` -/

/-- **The module `M = lim_e Γ(T_e, ℱ)` of [Stacks, Lemma 60.17.3, Tag 07JG] as a
`Crystalline.TaylorCrystal`.**

`Crystalline.TaylorCrystal` is the record of the hypotheses from which
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCrystal07JG.lean` proves items (07JB), (07JD) and
(07JE) of the tag.  Four of its twelve data fields are supplied here from the site and are not
hypotheses: `carrier` is the module `...SmallSite.LevelScalars07JG.sections` with its `D`-action,
the tower `levels` is `...LevelScalars07JG.levelSections`, the transition maps are
`...LevelScalars07JG.levelRestrict`, and the identification `levelEquiv` of the module with the
limit of the tower is `...LevelScalars07JG.sectionsInvLimitEquiv` — the whole point of which is
that the module *is* that limit, so no new identification is introduced.  Two more, `shift` and
`level_annihilate`, are the annihilation hypothesis `hann`, which for the system of
[Stacks, Proposition 60.21.1, Tag 07JN] is the theorem
`...SmallSite.pow_smul_eq_zero_wholeSpaceLevelSections` and not a hypothesis at all; see
`...SmallSite.taylorCrystalWholeSpaceLevelSections`.

What is carried is the comparison datum `c` and the four fields recording the source's `D(1)` and
`D(2)` coefficient computations.  **No tag follows from this**: it is a term of a record of
hypotheses, over a system of levels about which nothing is assumed beyond the annihilation, and
no `@[stacks]` attribute is placed. -/
def taylorCrystal (F : QuasiCoherentCrystal S) (N : ℕ)
    (hann : ∀ (e : ℕ) (x : L.levelSections F e), ((p : (D : Type u)) ^ (N + e)) • x = 0)
    (c : FirstOrderComparison A D g Omega d (L.sections F))
    (theta : ι → (L.sections F → L.sections F))
    (thetaPow : (ι →₀ ℕ) → (L.sections F → L.sections F))
    (hfam : IsThetaMonomialFamily (L.sections F) theta thetaPow)
    (hco : IsCoordinateExpansion p (D : Type u) Omega dx (c.completedConnection p) theta)
    (hfin : ∀ m : L.sections F,
      {K : ι →₀ ℕ | thetaPow K m ∉ pSmul p (D : Type u) (L.sections F)}.Finite)
    (b : Module.Basis ι (D : Type u) Omega) (hdx : ∀ i, dx i = b i) :
    TaylorCrystal.{u, u, u, uI, u} A D g Omega d p dx b hdx where
  carrier := L.sections F
  comparison := c
  levels := L.levelSections F
  transition := L.levelRestrict F
  shift := N
  level_annihilate e :=
    (pAdicIdeal_pow_smul_top_eq_bot_iff p (D : Type u) (L.levelSections F) N (n := e)).2 (hann e)
  levelEquiv := L.sectionsInvLimitEquiv F
  theta := theta
  thetaPow := thetaPow
  isThetaMonomialFamily := hfam
  isCoordinateExpansion := hco
  finite_thetaPow_notMem_pSmul := hfin

/-- The carrier of `taylorCrystal` is the module `L.sections F` of sections of `F`. -/
@[simp] theorem taylorCrystal_carrier (F : QuasiCoherentCrystal S) (N : ℕ)
    (hann : ∀ (e : ℕ) (x : L.levelSections F e), ((p : (D : Type u)) ^ (N + e)) • x = 0)
    (c : FirstOrderComparison A D g Omega d (L.sections F))
    (theta : ι → (L.sections F → L.sections F))
    (thetaPow : (ι →₀ ℕ) → (L.sections F → L.sections F))
    (hfam : IsThetaMonomialFamily (L.sections F) theta thetaPow)
    (hco : IsCoordinateExpansion p (D : Type u) Omega dx (c.completedConnection p) theta)
    (hfin : ∀ m : L.sections F,
      {K : ι →₀ ℕ | thetaPow K m ∉ pSmul p (D : Type u) (L.sections F)}.Finite)
    (b : Module.Basis ι (D : Type u) Omega) (hdx : ∀ i, dx i = b i) :
    (L.taylorCrystal F N hann c theta thetaPow hfam hco hfin b hdx).carrier = L.sections F :=
  rfl

/-- The comparison datum of `taylorCrystal` is the given comparison `c`. -/
@[simp] theorem taylorCrystal_comparison (F : QuasiCoherentCrystal S) (N : ℕ)
    (hann : ∀ (e : ℕ) (x : L.levelSections F e), ((p : (D : Type u)) ^ (N + e)) • x = 0)
    (c : FirstOrderComparison A D g Omega d (L.sections F))
    (theta : ι → (L.sections F → L.sections F))
    (thetaPow : (ι →₀ ℕ) → (L.sections F → L.sections F))
    (hfam : IsThetaMonomialFamily (L.sections F) theta thetaPow)
    (hco : IsCoordinateExpansion p (D : Type u) Omega dx (c.completedConnection p) theta)
    (hfin : ∀ m : L.sections F,
      {K : ι →₀ ℕ | thetaPow K m ∉ pSmul p (D : Type u) (L.sections F)}.Finite)
    (b : Module.Basis ι (D : Type u) Omega) (hdx : ∀ i, dx i = b i) :
    (L.taylorCrystal F N hann c theta thetaPow hfam hco hfin b hdx).comparison = c :=
  rfl

end LevelScalars07JG

/-! ### The comparison datum with four of its six fields proved -/

/-- **A term of `Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG` with four
of its six fields proved**, over a system of levels whose level `e` is annihilated by `p^{N + e}`.

* `isPAdicallyComplete` — item (07JB) — is
  `...SmallSite.LevelScalars07JG.isPAdicallyComplete_sections`.
* `hasCoordinateOperators` is `Crystalline.hasCoordinateOperators_of_isCoordinateExpansion`.
* `isIntegrable` — item (07JD) — is `Crystalline.isIntegrable_of_isThetaMonomialFamily`.
* `isTopologicallyQuasiNilpotent` — item (07JE) — is
  `Crystalline.isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily`.

The Hausdorffness those last three consume is *not* a hypothesis: it comes from item (07JB) by
`...SmallSite.LevelScalars07JG.isHausdorff_sections`.

`comparison` and `comparison_naturality` are consumed, and so are the source's two coefficient
computations over `D(1)` and `D(2)` — `theta`, `thetaPow`, `hfam`, `hco` and `hfin` — and a basis
of `Ω` on the differentials.  **No tag follows**: this is not a
`...SmallSite.LevelReduction07JG` and not a `...SmallSite.Reduction07JG`, and no `@[stacks]`
attribute is placed. -/
def levelComparison07JGOfTaylor (L : LevelScalars07JG S D) (N : ℕ)
    (comparison : ∀ F : QuasiCoherentCrystal S,
      FirstOrderComparison A D g Omega d (L.sections F))
    (comparison_naturality : ∀ {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (m : L.sections F),
      comparison G (L.sectionsMap psi m) =
        LinearMap.lTensor (firstOrderExtension D Omega) (L.sectionsMap psi) (comparison F m))
    (theta : ∀ F : QuasiCoherentCrystal S, ι → (L.sections F → L.sections F))
    (thetaPow : ∀ F : QuasiCoherentCrystal S, (ι →₀ ℕ) → (L.sections F → L.sections F))
    (hfam : ∀ F : QuasiCoherentCrystal S,
      IsThetaMonomialFamily (L.sections F) (theta F) (thetaPow F))
    (hco : ∀ F : QuasiCoherentCrystal S, IsCoordinateExpansion p (D : Type u) Omega dx
      ((comparison F).completedConnection p) (theta F))
    (hfin : ∀ (F : QuasiCoherentCrystal S) (m : L.sections F),
      {K : ι →₀ ℕ | thetaPow F K m ∉ pSmul p (D : Type u) (L.sections F)}.Finite)
    (hann : ∀ (F : QuasiCoherentCrystal S) (e : ℕ) (x : L.levelSections F e),
      ((p : (D : Type u)) ^ (N + e)) • x = 0)
    (b : Module.Basis ι (D : Type u) Omega) (hdx : ∀ i, dx i = b i) :
    LevelComparison07JG S A D g Omega d p dx L where
  comparison := comparison
  comparison_naturality := comparison_naturality
  isPAdicallyComplete F := L.isPAdicallyComplete_sections p F N (hann F)
  hasCoordinateOperators F :=
    hasCoordinateOperators_of_isCoordinateExpansion p (D : Type u) Omega (L.sections F) (hco F)
  isIntegrable F :=
    isIntegrable_of_isThetaMonomialFamily p (D : Type u) Omega (L.sections F) (hfam F) (hco F)
      b hdx (L.isHausdorff_sections p F N (hann F))
  isTopologicallyQuasiNilpotent F :=
    isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily p (D : Type u) Omega (L.sections F)
      (hfam F) (hco F) b hdx (L.isHausdorff_sections p F N (hann F)) (hfin F)

/-! ### At the system of levels of [Stacks, Tag 07JN] -/

section WholeSpace

variable (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp] [IsAffine S.X] [IsAffine S.S.scheme]

/-- **The Hausdorff half of item (07JB) at the system of levels of [Stacks, Tag 07JN]**, with no
hypothesis: the level `e` of `...SmallSite.wholeSpaceSystem` has section ring `D(n)/(p)^{N + e}`,
so `p^{N + e}` annihilates its sections by
`...SmallSite.pow_smul_eq_zero_wholeSpaceLevelSections`, and the limit is then `p`-adically
complete, hence separated. -/
theorem isHausdorff_wholeSpaceLevelScalars_sections (n : ℕ) (F : QuasiCoherentCrystal S) :
    IsHausdorff
      (DividedPowers.pAdicIdeal (A := ((wholeSpaceSystemEnvelope hp n).ring : Type u)) S.p)
      ((wholeSpaceLevelScalars hp n).sections F) :=
  (wholeSpaceLevelScalars hp n).isHausdorff_sections S.p F
    (_root_.Crystalline.uniformLevel (affineSituation S hp))
    (pow_smul_eq_zero_wholeSpaceLevelSections hp n · F)

section Comparison

variable {A : Type u} [CommRing A] (n : ℕ)
  {g : A →+* (wholeSpaceSystemEnvelope hp n).ring}
  {Omega : Type u} [AddCommGroup Omega]
  [Module (wholeSpaceSystemEnvelope hp n).ring Omega]
  [Module ((wholeSpaceSystemEnvelope hp n).ring)ᵐᵒᵖ Omega]
  [IsCentralScalar (wholeSpaceSystemEnvelope hp n).ring Omega]
  {d : DividedPowerDerivation A (wholeSpaceSystemEnvelope hp n).ring g Omega}
  {ι : Type uI} {dx : ι → Omega}

/-- **The module `M = lim_e Γ(T(n)_e, ℱ)` of [Stacks, Tag 07JG] as a
`Crystalline.TaylorCrystal`, at the system of levels the source's proof works over and over the
completed divided power envelope `D(n)` of [Stacks, Tag 07J8].**

The annihilation of the levels is not a hypothesis here: it is
`...SmallSite.pow_smul_eq_zero_wholeSpaceLevelSections`, with the shift
`N = Crystalline.uniformLevel (...affineSituation S hp)`.  So six of the twelve data fields of
`Crystalline.TaylorCrystal` are discharged — the module with its action, the tower, its
transition maps, the identification of the module with the limit of the tower, the shift and the
annihilation — and the six that are carried are the comparison datum and the five fields
recording the source's two coefficient computations.

Every term of `Crystalline.TaylorCrystal` in the tree before this one was
`Crystalline.trivialTaylorCrystal`, the zero module over `Crystalline.trivialDividedPowerRing`.
This one is over `D(n)` with the module of sections of an arbitrary crystal in quasi-coherent
`𝒪_{X/S}`-modules — but it is **not** a claim that the category is inhabited, because the
comparison datum and the coefficient computations are still hypotheses. -/
def taylorCrystalWholeSpaceLevelSections (F : QuasiCoherentCrystal S)
    (c : FirstOrderComparison A (wholeSpaceSystemEnvelope hp n).ring g Omega d
      ((wholeSpaceLevelScalars hp n).sections F))
    (theta : ι → ((wholeSpaceLevelScalars hp n).sections F →
      (wholeSpaceLevelScalars hp n).sections F))
    (thetaPow : (ι →₀ ℕ) → ((wholeSpaceLevelScalars hp n).sections F →
      (wholeSpaceLevelScalars hp n).sections F))
    (hfam : IsThetaMonomialFamily ((wholeSpaceLevelScalars hp n).sections F) theta thetaPow)
    (hco : IsCoordinateExpansion S.p ((wholeSpaceSystemEnvelope hp n).ring : Type u) Omega dx
      (c.completedConnection S.p) theta)
    (hfin : ∀ m : (wholeSpaceLevelScalars hp n).sections F,
      {K : ι →₀ ℕ | thetaPow K m ∉ pSmul S.p ((wholeSpaceSystemEnvelope hp n).ring : Type u)
        ((wholeSpaceLevelScalars hp n).sections F)}.Finite)
    (b : Module.Basis ι ((wholeSpaceSystemEnvelope hp n).ring : Type u) Omega)
    (hdx : ∀ i, dx i = b i) :
    TaylorCrystal.{u, u, u, uI, u} A (wholeSpaceSystemEnvelope hp n).ring g Omega d S.p dx b hdx :=
  (wholeSpaceLevelScalars hp n).taylorCrystal F
    (_root_.Crystalline.uniformLevel (affineSituation S hp))
    (pow_smul_eq_zero_wholeSpaceLevelSections hp n · F) c theta thetaPow hfam hco hfin b hdx

/-- **A term of `Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG` over the
scalars of [Stacks, Proposition 60.21.1, Tag 07JN], with four of its six fields proved.**

`...SmallSite.levelComparison07JGWholeSpaceOfRemaining` consumes five of the six, having proved
`isPAdicallyComplete`.  Here `hasCoordinateOperators`, `isIntegrable` and
`isTopologicallyQuasiNilpotent` are proved as well, and **two fields remain**: `comparison` and
`comparison_naturality`.

The three newly proved fields are items (07JD), (07JE) and the non-vacuity of the two, and they
are proved from the source's own two coefficient computations — the expansion
`c(m ⊗ 1) = ∑_K θ_K(m) ⊗ ∏ ξ_i^{[k_i]}` over `D(1)` with its `p`-adic convergence, and the
identity `θ_K = ∏ θ_i^{k_i}` over `D(2)` — together with a `Module.Basis` of `Ω` on the chosen
differentials.  Those are carried, as `theta`, `thetaPow`, `hfam`, `hco`, `hfin`, `b` and `hdx`.
The Hausdorffness of item (07JB) that the proofs consume is *not* carried: it is
`...SmallSite.isHausdorff_wholeSpaceLevelScalars_sections`, unconditional at this system of
levels.

**No term of `...SmallSite.Reduction07JG` follows, and no `@[stacks]` attribute is placed.**  The
two fields that remain are the small-site form of
`...GlobalCrystallineSituation.FirstOrderIdealBaseChange` read on the limit module, which
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` reduces to bijectivity of
`...GlobalCrystallineSituation.extensionSectionsMap`; and the basis `b` restricts the generality
to finitely many coordinates, `Ω_D` of [Stacks, Tag 07J9] being a completed direct sum. -/
def levelComparison07JGWholeSpaceOfTaylor
    (comparison : ∀ Fr : QuasiCoherentCrystal S,
      FirstOrderComparison A (wholeSpaceSystemEnvelope hp n).ring g Omega d
        ((wholeSpaceLevelScalars hp n).sections Fr))
    (comparison_naturality : ∀ {Fr Gr : QuasiCoherentCrystal S} (psi : Fr ⟶ Gr)
      (m : (wholeSpaceLevelScalars hp n).sections Fr),
      comparison Gr ((wholeSpaceLevelScalars hp n).sectionsMap psi m) =
        LinearMap.lTensor
          (firstOrderExtension (wholeSpaceSystemEnvelope hp n).ring Omega)
          ((wholeSpaceLevelScalars hp n).sectionsMap psi) (comparison Fr m))
    (theta : ∀ Fr : QuasiCoherentCrystal S, ι → ((wholeSpaceLevelScalars hp n).sections Fr →
      (wholeSpaceLevelScalars hp n).sections Fr))
    (thetaPow : ∀ Fr : QuasiCoherentCrystal S, (ι →₀ ℕ) →
      ((wholeSpaceLevelScalars hp n).sections Fr → (wholeSpaceLevelScalars hp n).sections Fr))
    (hfam : ∀ Fr : QuasiCoherentCrystal S,
      IsThetaMonomialFamily ((wholeSpaceLevelScalars hp n).sections Fr) (theta Fr) (thetaPow Fr))
    (hco : ∀ Fr : QuasiCoherentCrystal S,
      IsCoordinateExpansion S.p ((wholeSpaceSystemEnvelope hp n).ring : Type u) Omega dx
        ((comparison Fr).completedConnection S.p) (theta Fr))
    (hfin : ∀ (Fr : QuasiCoherentCrystal S) (m : (wholeSpaceLevelScalars hp n).sections Fr),
      {K : ι →₀ ℕ | thetaPow Fr K m ∉ pSmul S.p
        ((wholeSpaceSystemEnvelope hp n).ring : Type u)
        ((wholeSpaceLevelScalars hp n).sections Fr)}.Finite)
    (b : Module.Basis ι ((wholeSpaceSystemEnvelope hp n).ring : Type u) Omega)
    (hdx : ∀ i, dx i = b i) :
    LevelComparison07JG S A (wholeSpaceSystemEnvelope hp n).ring g Omega d S.p dx
      (wholeSpaceLevelScalars hp n) :=
  levelComparison07JGOfTaylor (wholeSpaceLevelScalars hp n)
    (_root_.Crystalline.uniformLevel (affineSituation S hp)) comparison comparison_naturality
    theta thetaPow hfam hco hfin
    (fun Fr e ↦ pow_smul_eq_zero_wholeSpaceLevelSections hp n e Fr) b hdx

end Comparison

end WholeSpace

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
