module

public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.QuasiAffine

/-!
# Stacks Tag 0B7K: the remaining implication, reduced to lifting one basic open

Let `i : Z ⟶ X` be a closed immersion of Noetherian schemes inducing a homeomorphism of
underlying topological spaces. [Stacks, Tag 0B7K] asserts that `X` is quasi-affine if and only if
`Z` is. `StacksFrontier/AlgebraicGeometry/AmpleSurjectiveThickening/QuasiAffine.lean` proves the
implication `X` quasi-affine `⟹` `Z` quasi-affine unconditionally, and reduces the other
implication to `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` for `𝒪_X`.

**This file reduces that implication to a statement with no invertible module, no tensor power
and no ampleness predicate in it**: every global section of `𝒪_Z` whose nonvanishing locus is
affine has *some* global section of `𝒪_X` with the same nonvanishing locus on `Z`,

    ∀ s : Γ(Z, ⊤), IsAffineOpen (Z.basicOpen s) → ∃ r : Γ(X, ⊤),
      Z.basicOpen (i.appTop r) = Z.basicOpen s

and proves that hypothesis outright whenever `Γ(X, ⊤) ⟶ Γ(Z, ⊤)` is surjective.

## Main results

* `Stacks.AmpleSurjectiveThickening.exists_isAffineOpen_basicOpen_mem`: a point of a quasi-affine
  scheme lies in an affine basic open of a global section. This is the half of
  [Stacks, Tag 01QE] the argument consumes, in Mathlib's own `Scheme.basicOpen` language.
* `Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_forall_exists_basicOpen`: **the implication
  `Z` quasi-affine `⟹` `X` quasi-affine of [Stacks, Tag 0B7K] from the displayed hypothesis
  alone.**
* `Stacks.AmpleSurjectiveThickening.isQuasiAffine_iff_of_forall_exists_basicOpen`: the
  biconditional of [Stacks, Tag 0B7K] from the same hypothesis alone.
* `Stacks.AmpleSurjectiveThickening.exists_basicOpen_of_surjective_appTop`: **the hypothesis is
  implied by surjectivity of `Γ(X, ⊤) ⟶ Γ(Z, ⊤)`**, with no power taken at all.
* `Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_surjective_appTop` and
  `isQuasiAffine_iff_of_surjective_appTop`: hence [Stacks, Tag 0B7K] for a thickening whose
  global sections are surjective.
* `Stacks.AmpleSurjectiveThickening.surjective_appTop_dualNumberThickening` and
  `isQuasiAffine_iff_dualNumberThickening`: the biconditional with **every hypothesis
  discharged**, at `Spec(ℤ/4 ⧸ (2)) ⟶ Spec(ℤ/4)`, a surjective closed immersion of Noetherian
  schemes that is not an isomorphism.

## The route, and why it is shorter than the one through ampleness

`AlgebraicGeometry.Scheme.IsQuasiAffine` is Mathlib's predicate "quasi-compact, and
`X ⟶ Spec Γ(X, ⊤)` is an immersion", and Mathlib proves both halves of [Stacks, Tag 01QE] for it
directly in terms of basic opens of global sections:
`AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen` for one half and
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen` for the other. So the
argument of the source — `𝒪_Z` ample, hence `𝒪_X` ample, hence `X` quasi-affine — can be run
without the ample predicate: given `x : X`, take a preimage `z`, take an affine `Z.basicOpen s`
around it, lift the *open* (not the section) to `X.basicOpen r`, and note
`i ⁻¹ᵁ X.basicOpen r = Z.basicOpen (i.appTop r)`
(`AlgebraicGeometry.Scheme.preimage_basicOpen_top`), so that
`Stacks.AmpleSurjectiveThickening.isAffineOpen_of_isAffineOpen_preimage` — Chevalley's criterion
[Stacks, Tag 01YQ], already discharged there — makes `X.basicOpen r` affine.

Nothing of the invertible-module development enters: no `Stacks.Ample.IsAmple`, no
`tensorPowModule`, no `powNonvanishingOpen`, no `unitModule`. That matters because the remaining
hypothesis is the one still to be proved, and it is easier to prove about `Γ(X, ⊤)` than
about sections of `𝒪_X^{⊗ m}`: taking a power of `s` is not even needed to *state* it, since
`Z.basicOpen (s ^ e) = Z.basicOpen s`.

## What is not done

**The displayed hypothesis is not proved, and no declaration here carries the tag**; the bare tag
is carried nowhere in the repository and the only attribute site for [Stacks, Tag 0B7K] remains
the one for the opposite implication at
`StacksFrontier/AlgebraicGeometry/AmpleSurjectiveThickening/QuasiAffine.lean:118`.

What the hypothesis costs is unchanged by this file: the class
`ξ ∈ H¹(X, 𝓘)` obstructing the lift of `s` restricts to zero on `Z_s`, so some `s^e ξ` vanishes by
[Stacks, Tag 01XR], and `∂(s^{e+1}) = (e+1) s^e ∂ s` because the boundary map of a square-zero
extension is a derivation ([Stacks, Tag 0B8S],
`StacksFrontier/Topology/Sheaves/Cohomology/SquareZeroExtensionBoundaryDerivation.lean:1083`); the
ideal is made square-zero first using its nilpotence ([Stacks, Tag 01Y9]). Of these
[Stacks, Tag 01XR] is the blocker, and in the shape needed here it is the *untwisted* case — `ℒ`
is `𝒪_X`, so the graded module of [Stacks, Tag 09MR] collapses to `H¹(Z, 𝓘)` and its degree-zero
localization to `H¹(Z, 𝓘)_s`. That untwisted case is still not available: the only bijectivity
proved for the comparison map of [Stacks, Tag 09MR] is for an open `U ⊆ X_s`
(`../TwistedCohomologyLocalization/CanonicalMap.lean:472`), where both sides are cohomology of
`X_s` and a class on the whole of `X` is not in the source at all. In exchange the *graded*
extension the general case of [Stacks, Tag 09MS] needs is not needed here: for `ℒ = 𝒪_X` the
derivation is the ungraded one, which is what Tag 0B8S is attached to.

## References

* [Stacks Project, Tag 0B7K](https://stacks.math.columbia.edu/tag/0B7K)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AmpleSurjectiveThickening

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-! ### Quasi-affineness through basic opens of global sections -/

/-- **A point of a quasi-affine scheme lies in an affine basic open of a global section.** This is
the half of [Stacks, Tag 01QE] the argument of [Stacks, Tag 0B7K] consumes, read off
`AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen` at the open `⊤`. -/
theorem exists_isAffineOpen_basicOpen_mem (hZ : Z.IsQuasiAffine) (z : Z) :
    ∃ s : Γ(Z, ⊤), IsAffineOpen (Z.basicOpen s) ∧ z ∈ Z.basicOpen s := by
  have := hZ
  obtain ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, hzs, -⟩ :=
    (Scheme.IsQuasiAffine.isBasis_basicOpen Z).exists_subset_of_mem_open
      (Set.mem_univ z) isOpen_univ
  exact ⟨s, hs, hzs⟩

/-! ### The implication `Z` quasi-affine ⟹ `X` quasi-affine, from lifting basic opens -/

/-- **The implication `Z` quasi-affine `⟹` `X` quasi-affine of [Stacks, Tag 0B7K], from the
lifting of affine basic opens alone.** Let `i : Z ⟶ X` be a surjective closed immersion onto a
locally Noetherian scheme, and suppose every global section `s` of `𝒪_Z` with `Z_s` affine has a
global section `r` of `𝒪_X` with `Z_{i^# r} = Z_s`. Then `Z` quasi-affine gives `X` quasi-affine.

The source's hypothesis that `X` is Noetherian is weakened to locally Noetherian, exactly as in
`Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_sectionsLiftAfterPower`: quasi-compactness of
`X` comes from quasi-compactness of `Z` along the surjection.

No tag is attached — an implication still carrying a hypothesis the source does not make is not
the source statement. -/
theorem isQuasiAffine_of_forall_exists_basicOpen [IsClosedImmersion i] [Surjective i]
    [IsLocallyNoetherian X]
    (hlift : ∀ s : Γ(Z, ⊤), IsAffineOpen (Z.basicOpen s) →
      ∃ r : Γ(X, ⊤), Z.basicOpen (i.appTop r) = Z.basicOpen s)
    (hZ : Z.IsQuasiAffine) : X.IsQuasiAffine := by
  have := hZ
  have : CompactSpace X :=
    Stacks.AmpleClosedImmersion.compactSpace_of_surjective i inferInstance inferInstance
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x => ?_
  obtain ⟨z, hz⟩ := i.surjective x
  obtain ⟨s, hs, hzs⟩ := exists_isAffineOpen_basicOpen_mem hZ z
  obtain ⟨r, hr⟩ := hlift s hs
  have hpre : i ⁻¹ᵁ X.basicOpen r = Z.basicOpen s := by
    rw [Scheme.preimage_basicOpen_top]; exact hr
  have haff : IsAffineOpen (i ⁻¹ᵁ X.basicOpen r) := by rw [hpre]; exact hs
  have hmem : z ∈ i ⁻¹ᵁ X.basicOpen r := by rw [hpre]; exact hzs
  exact ⟨r, isAffineOpen_of_isAffineOpen_preimage i _ haff, hz ▸ hmem⟩

/-- **[Stacks, Tag 0B7K] from the lifting of affine basic opens alone.** For a closed immersion of
Noetherian schemes inducing a homeomorphism of underlying spaces, `X` is quasi-affine exactly when
`Z` is, granted that every affine `Z_s` is `Z_{i^# r}` for some `r : Γ(X, ⊤)`.

The `mp` direction uses none of that: it is
`Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_isQuasiAffine`, which carries the tag. No tag
is attached here: a biconditional still carrying a hypothesis the source does not make is not the
source statement. -/
theorem isQuasiAffine_iff_of_forall_exists_basicOpen [IsClosedImmersion i] [Surjective i]
    [IsNoetherian X]
    (hlift : ∀ s : Γ(Z, ⊤), IsAffineOpen (Z.basicOpen s) →
      ∃ r : Γ(X, ⊤), Z.basicOpen (i.appTop r) = Z.basicOpen s) :
    X.IsQuasiAffine ↔ Z.IsQuasiAffine :=
  ⟨isQuasiAffine_of_isQuasiAffine i, isQuasiAffine_of_forall_exists_basicOpen i hlift⟩

/-! ### The hypothesis holds when global sections are surjective -/

/-- **Surjective global sections lift every basic open.** If `Γ(X, ⊤) ⟶ Γ(Z, ⊤)` is surjective
then every `s : Γ(Z, ⊤)` is `i^# r` on the nose, so the hypothesis of
`Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_forall_exists_basicOpen` holds with no power
taken and with the affineness premise unused. -/
theorem exists_basicOpen_of_surjective_appTop (hsurj : Function.Surjective i.appTop)
    (s : Γ(Z, ⊤)) (_hs : IsAffineOpen (Z.basicOpen s)) :
    ∃ r : Γ(X, ⊤), Z.basicOpen (i.appTop r) = Z.basicOpen s := by
  obtain ⟨r, hr⟩ := hsurj s
  exact ⟨r, by rw [hr]⟩

/-- **[Stacks, Tag 0B7K], implication `Z` quasi-affine `⟹` `X` quasi-affine, for a thickening
with surjective global sections.** Surjectivity of `Γ(X, ⊤) ⟶ Γ(Z, ⊤)` is what the vanishing of
`H¹(X, 𝓘)` buys from the long exact sequence of `0 → 𝓘 → 𝒪_X → i_* 𝒪_Z → 0`, and it is strictly
weaker than that vanishing; this is the sufficient condition
`Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_forall_exists_basicOpen` is stated to expose.

No tag: surjectivity of global sections is not a hypothesis of the source. -/
theorem isQuasiAffine_of_surjective_appTop [IsClosedImmersion i] [Surjective i]
    [IsLocallyNoetherian X] (hsurj : Function.Surjective i.appTop) (hZ : Z.IsQuasiAffine) :
    X.IsQuasiAffine :=
  isQuasiAffine_of_forall_exists_basicOpen i (exists_basicOpen_of_surjective_appTop i hsurj) hZ

/-- **[Stacks, Tag 0B7K] for a thickening with surjective global sections.** -/
theorem isQuasiAffine_iff_of_surjective_appTop [IsClosedImmersion i] [Surjective i]
    [IsNoetherian X] (hsurj : Function.Surjective i.appTop) :
    X.IsQuasiAffine ↔ Z.IsQuasiAffine :=
  isQuasiAffine_iff_of_forall_exists_basicOpen i (exists_basicOpen_of_surjective_appTop i hsurj)

/-! ### Every hypothesis discharged, at a thickening that is not an isomorphism -/

/-- **Global sections are surjective for the dual-number thickening.** Its target is affine, and a
closed immersion with affine target is surjective on global sections. -/
theorem surjective_appTop_dualNumberThickening :
    Function.Surjective dualNumberThickening.appTop :=
  (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine dualNumberThickening).2

/-- **The affineness premise of the lifting hypothesis is met non-vacuously** at the dual-number
thickening: the basic open of `1` is the whole scheme, which is affine. Recorded because a
hypothesis quantified over a collection is satisfied vacuously by an empty one, and this one is
not empty. -/
theorem exists_isAffineOpen_basicOpen_dualNumberThickening :
    ∃ s : Γ(Spec (CommRingCat.of (ZMod 4 ⧸ squareZeroIdeal)), ⊤),
      IsAffineOpen ((Spec (CommRingCat.of (ZMod 4 ⧸ squareZeroIdeal))).basicOpen s) :=
  ⟨1, by rw [Scheme.basicOpen_one]; exact isAffineOpen_top _⟩

/-- **[Stacks, Tag 0B7K] with every hypothesis discharged**, at the surjective closed immersion
`Spec(ℤ/4 ⧸ (2)) ⟶ Spec(ℤ/4)` of Noetherian schemes, which
`Stacks.AmpleSurjectiveThickening.not_isIso_dualNumberThickening` shows is not an isomorphism. So
`Stacks.AmpleSurjectiveThickening.isQuasiAffine_iff_of_surjective_appTop` is not vacuous, and its
hypothesis is instantiable in this repository from declarations that assume nothing.

The target here is affine, so the conclusion is also available directly; what the instance tests
is that the hypotheses do not collapse onto `i = 𝟙 X`, in which case
`Z = X` and the biconditional would say nothing. -/
theorem isQuasiAffine_iff_dualNumberThickening :
    (Spec (CommRingCat.of (ZMod 4))).IsQuasiAffine ↔
      (Spec (CommRingCat.of (ZMod 4 ⧸ squareZeroIdeal))).IsQuasiAffine :=
  isQuasiAffine_iff_of_surjective_appTop dualNumberThickening
    surjective_appTop_dualNumberThickening

end Stacks.AmpleSurjectiveThickening

end
