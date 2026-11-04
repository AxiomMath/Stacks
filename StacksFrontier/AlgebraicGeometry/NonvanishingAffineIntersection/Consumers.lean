module

public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTheory.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.FromAmple

/-!
# What Stacks Tag 01PV discharges downstream

`StacksFrontier/AlgebraicGeometry/NonvanishingAffineIntersection/Basic.lean` proves Stacks Tag
01PV: for `M` an invertible `𝒪_X`-module and `s ∈ Γ(X, M)`, every affine open meets `X_s` in an
affine open. This file spends it on the three consumers that were waiting, each in that consumer's
own vocabulary.

## Main results

* `Stacks.NonvanishingAffineIntersection.isAffineOpen_of_le_affineOpen`: **the form of Tag 01PV
  that the source's own downstream proofs use** — an `X_s` contained in an affine open is itself
  affine.
* `Stacks.NonvanishingAffineIntersection.isAffineOfLeAffine`:
  `Stacks.AmpleTheory.IsAffineOfLeAffine` **as a theorem**. That predicate was introduced in
  `StacksFrontier/AlgebraicGeometry/AmpleTheory/Basic.lean` as a *hypothesis*, with the docstring
  "Tag 01PV asserts more … and is not available; this is the part of it the basis argument needs,
  isolated as a hypothesis". It is available now, with no hypothesis beyond invertibility.
* `Stacks.NonvanishingAffineIntersection.isBasisAffineNonvanishing_of_isBasisNonvanishing`:
  **Stacks Tag 01PX unconditionally** — clause (3) of Stacks Tag 01Q3 implies clause (4). This is
  `Stacks.AmpleTheory.isBasisAffineNonvanishing_of_isBasisNonvanishing` with its
  `IsAffineOfLeAffine` hypothesis discharged. No Stacks attribute is attached here: Tag 01PX's
  covering set has not been checked against this statement.
* `Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nvOpen` and
  `isAffineOpen_nvOpen_of_le_affineOpen`: Tag 01PV in the section-ring vocabulary of
  `StacksFrontier/AlgebraicGeometry/AmpleFiniteAvoidance/`, where `X_s` is `nvOpen L a` for `a` a
  homogeneous element of `Γ_*(X, L)`.
* `Stacks.NonvanishingAffineIntersection.exists_affine_nvOpen_containing_finite_le`:
  **Stacks Tag 09NV reduced, in Lean, to exactly two named inputs.** Given clause (3) of Tag 01Q3
  *and* an affine open `U` with `E ⊆ U ⊆ W`, a finite `E` lies in an affine `X_a` inside `W`.

## What this does not close

Neither Tag 09NV nor part (3) of Tag 01ZY follows from Tag 01PV alone, and the reason is the same
for both.

* **Part (3) of Tag 01ZY** asks for an affine open containing a finite set, for `L` merely ample.
  `Stacks.AmpleFiniteAvoidance.exists_nvLocus_containing_finite` produces one `X_a` containing
  `E`, and Tag 01PV makes `X_a` quasi-compact with affine intersections
  (`Stacks.NonvanishingAffineIntersection.isCompact_nonvanishingLocus`), but `X_a` is not thereby
  affine: `isAffineOpen_of_le_affineOpen` needs `X_a` inside *one* affine open, and ampleness
  supplies only a finite *cover* of `X_a` by affine `X_{a·s_i}` (each of which this file does make
  affine). This obstruction is not a real one, for two reasons. First, nothing
  needs `X_a` affine: *quasi-affine* suffices, and part (1) of Tag 01ZY does the rest — so
  **part (3) of Tag 01ZY is proved**, as
  `Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample`
  (`../AmpleAffineAvoidance/AmpleFiniteSet.lean`), using Tag 01PV twice and no clause of Tag 01Q3
  at all. Second, clause (3) is **not** a `Proj Γ_*(X, L)` construction: it is three lines from
  one premise, by `Stacks.AmplePullback.isBasisNonvanishing_of_isAmple`
  (`../AmplePullback/Basic.lean`), whose own input is the surjectivity half of Tag 01PW — Tags
  01Q1 and 01Q2 are not involved.
* **Tag 09NV** is the source's Lemma 28.30.6, and its proof *calls* part (3) of Tag 01ZY to shrink
  `W` to an affine open `U ⊇ E` before running graded prime avoidance inside `U`; affineness of the
  resulting `X_s` is then exactly `isAffineOpen_of_le_affineOpen`. So Tag 09NV needs part (3) of
  Tag 01ZY as well as clause (3) of Tag 01Q3, and `exists_affine_nvOpen_containing_finite_le`
  below is that reduction with both inputs taken as hypotheses. **Part (3) is proved** (see
  above), so `Stacks.AmpleAffineAvoidance.exists_affine_nvOpen_containing_finite_le_of_ample`
  (`../AmpleAffineAvoidance/AmpleFiniteSet.lean`) improves this to Tag 09NV on the *single*
  remaining hypothesis `Stacks.AmpleTheory.IsBasisNonvanishing`. **That hypothesis is
  discharged too, so Tag 09NV is proved**, as
  `Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite_sections`
  (`../AmpleFiniteAffineNonvanishing/Basic.lean`), with ampleness as its only hypothesis: the
  basis clause comes from `Stacks.SectionExtension.isBasisNonvanishing_of_isAmple` and the
  surjectivity half of Tag 01PW it rests on from
  `Stacks.SectionExtension.isSectionRatio_of_isAmple`. So neither of the two consumers named at
  the head of this section is open any longer; what stays taken as hypotheses below is only what
  this file does not itself apply.

  The hypothesis `∀ n, NonvanishingBasis (pow n)` of `isQuasiAffine_iff_isAmpleForPowers` (in the
  conditional file `../AmplePowers/QuasiAffine.lean`) *is*
  constructed, by `Stacks.Ample.unitTensorPowBasis` (`../AmpleWire/Basic.lean`), and
  unconditional Tag 01QE is proved and tagged as `Stacks.Ample.isQuasiAffine_iff_isAmple`
  (same file).

One tempting route — *`X_a` quasi-compact with affine intersections, hence `𝒪` ample
on `X_a`, hence `X_a` quasi-affine by Tag 01QE* — **does not run directly**, and the
obstruction is not Tag 01PV. `Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers` carries the extra
hypothesis `∀ n : ℤ, Stacks.Ample.NonvanishingBasis (pow n)`, and its own module documentation
records that this is *never constructed, for any module*, because nothing identifies the
abelian-group stalk of the structure sheaf with `𝒪_{X, x}` as a ring and so `X_1 = X` is not
provable. Supplying one `NonvanishingBasis` for the unit module — which by
`Stacks.Ample.NonvanishingBasis.ofIso` suffices in every degree — is a separate named piece of
work; the identification it needs is written out, proof-complete, as `Stacks.Ample.unitStalkEquiv`
and `Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one` (`../AmpleWire/UnitStalk.lean`).

## References

* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PX](https://stacks.math.columbia.edu/tag/01PX)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.GradedSections

universe u

namespace Stacks.NonvanishingAffineIntersection

/-! ### Tag 01PV in the form the source's downstream proofs use -/

/-- **A nonvanishing locus contained in an affine open is affine.** This is how Stacks Tag 01PV is
invoked in the source — in the proof of Tag 01PX and again in the proof of Tag 09NV — and it is
immediate from `isAffineOpen_inf_nonvanishingOpen`, the containment turning `U ⊓ X_s` into
`X_s`. -/
theorem isAffineOpen_of_le_affineOpen {X : Scheme.{u}} (M : X.Modules) [IsInvertibleModule X M]
    (s : Γ(M, ⊤)) {U : X.Opens} (hU : IsAffineOpen U)
    (hsU : Stacks.NonvanishingOpen.nonvanishingOpen X M s ≤ U) :
    IsAffineOpen (Stacks.NonvanishingOpen.nonvanishingOpen X M s) := by
  rw [← inf_eq_right.mpr hsU]
  exact isAffineOpen_inf_nonvanishingOpen M s hU

/-! ### The hypothesis of Stacks Tag 01PX, discharged -/

/-- **`Stacks.AmpleTheory.IsAffineOfLeAffine` is a theorem.** The predicate was isolated as a
hypothesis in `StacksFrontier/AlgebraicGeometry/AmpleTheory/Basic.lean` on the grounds that Stacks
Tag 01PV was not available. It is, so this holds for every invertible `𝒪_X`-module on every
scheme. -/
theorem isAffineOfLeAffine (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L] :
    Stacks.AmpleTheory.IsAffineOfLeAffine X L :=
  fun _ _ s _ hU hsU => isAffineOpen_of_le_affineOpen _ s hU hsU

/-- **Stacks Tag 01PX with no hypothesis beyond invertibility**: if the nonvanishing opens of
global sections of positive tensor powers of `L` form a basis for the topology — clause (3) of
Stacks Tag 01Q3 — then the affine ones among them do, which is clause (4).

This is `Stacks.AmpleTheory.isBasisAffineNonvanishing_of_isBasisNonvanishing` with its
`Stacks.AmpleTheory.IsAffineOfLeAffine` hypothesis discharged by `isAffineOfLeAffine`. No Stacks
attribute is attached: Tag 01PX's covering set has not been checked against this statement. -/
theorem isBasisAffineNonvanishing_of_isBasisNonvanishing (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (h : Stacks.AmpleTheory.IsBasisNonvanishing X L) :
    Stacks.AmpleTheory.IsBasisAffineNonvanishing X L :=
  Stacks.AmpleTheory.isBasisAffineNonvanishing_of_isBasisNonvanishing X L h
    (isAffineOfLeAffine X L)

/-! ### Tag 01PV in the section-ring vocabulary -/

-- The monoidal structure `Stacks.GradedSections.powSections` is stated over, in the exact list of
-- local instances `StacksFrontier/AlgebraicGeometry/AmpleFiniteAvoidance/FromAmple.lean` installs.
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **Stacks Tag 01PV for `Stacks.AmpleFiniteAvoidance.nvOpen`**: an affine open meets the
nonvanishing open of a homogeneous element of `Γ_*(X, L)` in an affine open. The two vocabularies
agree on the nose — `nvOpen L a` *is* the `nonvanishingOpen` of the global section attached to
`a` — so no comparison of tensor-power families is involved. -/
theorem isAffineOpen_inf_nvOpen {d : ℕ} (a : powSections L d) {U : X.Opens}
    (hU : IsAffineOpen U) :
    IsAffineOpen (U ⊓ Stacks.AmpleFiniteAvoidance.nvOpen L a) :=
  isAffineOpen_inf_nonvanishingOpen _ _ hU

/-- `isAffineOpen_of_le_affineOpen` in the section-ring vocabulary. -/
theorem isAffineOpen_nvOpen_of_le_affineOpen {d : ℕ} (a : powSections L d) {U : X.Opens}
    (hU : IsAffineOpen U) (haU : Stacks.AmpleFiniteAvoidance.nvOpen L a ≤ U) :
    IsAffineOpen (Stacks.AmpleFiniteAvoidance.nvOpen L a) :=
  isAffineOpen_of_le_affineOpen _ _ hU haU

/-! ### Stacks Tag 09NV, reduced to two named inputs -/

/-- **Stacks Tag 09NV, reduced in Lean to exactly the two inputs the source uses.** Let `L` be an
invertible `𝒪_X`-module whose nonvanishing opens form a basis for the topology (clause (3) of
Stacks Tag 01Q3), let `E` be a finite set inside an open `W`, and suppose `E` lies in an affine
open `U ⊆ W` — which is what part (3) of Stacks Tag 01ZY provides for an ample `L`. Then there is
a homogeneous `a` of positive degree with `E ⊆ X_a ⊆ W` **and `X_a` affine**.

The affineness clause — the whole of what Tag 09NV asks beyond
`Stacks.AmpleFiniteAvoidance.exists_nvOpen_containing_finite_le` — is Tag 01PV, through
`isAffineOpen_nvOpen_of_le_affineOpen`. Nothing else here is new: the section comes from running
that theorem with the prescribed open taken to be the affine `U`. -/
theorem exists_affine_nvOpen_containing_finite_le
    (hb : Stacks.AmpleTheory.IsBasisNonvanishing X L) {E : Set X} (hE : E.Finite)
    {U W : X.Opens} (hU : IsAffineOpen U) (hEU : E ⊆ (U : Set X)) (hUW : U ≤ W) :
    ∃ (d : ℕ) (a : powSections L d), 1 ≤ d ∧ E ⊆ (Stacks.AmpleFiniteAvoidance.nvOpen L a : Set X) ∧
      Stacks.AmpleFiniteAvoidance.nvOpen L a ≤ W ∧
      IsAffineOpen (Stacks.AmpleFiniteAvoidance.nvOpen L a) := by
  obtain ⟨d, a, hd, hEa, haU⟩ :=
    Stacks.AmpleFiniteAvoidance.exists_nvOpen_containing_finite_le L hb hE U hEU
  exact ⟨d, a, hd, hEa, haU.trans hUW, isAffineOpen_nvOpen_of_le_affineOpen L a hU haU⟩

end Stacks.NonvanishingAffineIntersection

end
