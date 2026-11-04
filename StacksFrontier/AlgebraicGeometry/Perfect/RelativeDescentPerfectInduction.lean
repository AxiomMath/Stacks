module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineBase
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectObjects
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionCanonicalCertificate

/-!
# The induction of Stacks 08DR for the essential-surjectivity half of Stacks 0DI8

In the relative descent situation of Stacks 0DI6 — a directed inverse limit `S = lim Sᵢ` of
quasi-compact, quasi-separated schemes with affine transition maps, and a flat morphism of finite
presentation `X₀ ⟶ S₀` with base changes `Xᵢ ⟶ Sᵢ` and `X ⟶ S` — Stacks 0DI8 asserts that the
category of `S`-perfect objects of `D(𝒪_X)` is the colimit of the categories of `Sᵢ`-perfect
objects of `D(𝒪_{Xᵢ})`. Full faithfulness of the comparison is Stacks 0DI7, which the source
cites as known; what remains is essential surjectivity, stated on a situation as
`AlgebraicGeometry.RelativeDescentSituation.PerfectEssentiallySurjective`.

The source proves essential surjectivity by considering, for a quasi-compact open `U₀ ⊆ X₀`, the
property `P U₀` that the comparison out of the colimit is essentially surjective for the
situation restricted to `U₀`; it checks `P` on the affine opens lying over an affine open of
`S₀`, where the statement is the ring-theoretic Stacks 0DHX read through Stacks 0DI2; it checks
that `P` passes from `U₀`, `V₀` and `U₀ ∩ V₀` to `U₀ ∪ V₀` by the glueing of Stacks 08DG; and it
then runs the induction principle of Stacks 08DR.

**This file runs that induction.** The property `P` is
`AlgebraicGeometry.RelativeDescentSituation.RestrictPerfectEssentiallySurjective`, essential
surjectivity for `AlgebraicGeometry.RelativeDescentSituation.restrict`; the two steps the source
checks are the hypotheses; and the conclusion is `P` for every quasi-compact open of `X₀`, hence
for `X₀` itself.

## Main definitions

* `AlgebraicGeometry.RelativeDescentSituation.canonicalLimitCertificates` and
  `canonicalStageCertificates`: the derived-tensoring certificates of Stacks 0DI0 on the
  inverse-image ringed spaces of the structure morphisms, taken to be the canonical derived
  tensor product of Stacks 06YU on every open subspace. These are the two families against which
  relative perfectness is read in the affine case of
  `AlgebraicGeometry.AffinePerfectDescent.exists_isPerfectRelativeTo_stage`, so pinning them here
  is what lets the statement of the induction have no certificate parameters.
* `AlgebraicGeometry.RelativeDescentSituation.PerfectEssentiallySurjectiveCanonical`: the half of
  Stacks 0DI8 of `AlgebraicGeometry.RelativeDescentSituation.PerfectEssentiallySurjective`, read
  at those two families.
* `AlgebraicGeometry.RelativeDescentSituation.RestrictPerfectEssentiallySurjective`: the property
  `P` of the source's proof — that half for the situation restricted to a quasi-compact open of
  `X₀`.

## Main results

* `restrictPerfectEssentiallySurjective_of_isAffineOpen_over_affine_of_sup`:
  **the induction of Stacks 08DR for the essential-surjectivity half of Stacks 0DI8.** From the
  affine case over an affine open of the base and the union step, `P` holds for every
  quasi-compact open of `X₀`.
* `AlgebraicGeometry.RelativeDescentSituation.restrictPerfectEssentiallySurjective_top`: the same
  at `U₀ = X₀`, the quasi-compactness of `X₀` coming from the situation's own fields.

## Implementation notes

**Which induction, and why one suffices.** The source runs the induction principle twice: first
over the quasi-compact quasi-separated opens of `S₀`, to reduce to `S₀` affine, and then over
those of `X₀`, to reduce to `X₀` affine. Here, as in the formalization of Stacks 0DI7, one
induction does both, because the family of opens relative to which Stacks 08DR is run is
`AlgebraicGeometry.RelativeDescentSituation.IsAffineOpenOverAffine`, the affine opens of `X₀`
contained in the preimage of an affine open of `S₀`. That family is downward closed, contains
`⊥` and contains an affine open neighbourhood of every point, which is what
`Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact_of_basis` asks for, and an affine
open lying over an affine open of `S₀` is exactly the situation in which the affine case is the
ring-theoretic Stacks 0DHX.

**Both hypotheses are steps of the source's own proof.** `haffine` is the affine case — the
statement that over an affine open of `X₀` lying over an affine open of `S₀` the comparison is
essentially surjective — and `hsup` is the union step. The first is
`RelativeDescentSituation.restrictPerfectEssentiallySurjective_of_isAffineOpenOverAffine`,
Stacks 0DHX read through the affine dictionary; the second is
`AlgebraicGeometry.RelativeDescentSituation.restrictPerfectEssentiallySurjective_sup`, the glueing
of Stacks 08DG. The passage from `U₀ = X₀` to the situation itself is
`RelativeDescentSituation.perfectEssentiallySurjectiveCanonical_restrict_top_iff`.

**Universes.** The index category is in the same universe as the schemes, because
`AlgebraicGeometry.RelativeDescentSituation.LimitCertificates` reads the certificates at
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}`, which is the level at
which `CategoryTheory.HasDerivedCategory.standard` provides them on a `RingedSpace.{u, u}`; the
universe arguments of `AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`
are given explicitly for that reason.

## References

* [Stacks Project, Lemma 36.35.9 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.35.3 (Tag 0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
* [Stacks Project, Lemma 20.45.1 (Tag 08DG)](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Lemma 30.4.1 (Tag 08DR)](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry StrictlyPerfect

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

attribute [local implicit_reducible] restrict

/-! ### The canonical certificates of a relative descent situation -/

/-- **The canonical derived-tensoring certificates on the inverse-image ringed space of the
structure morphism of the limit.** The Tor-dimension clause of Stacks 0DI0 is stated against a
family of certificates, one on each open subspace, because no canonical derived tensor product is
constructed on an inverse-image ringed space; the canonical derived tensor product of Stacks
06YU, however, is available on each open subspace, and this is the family it gives. -/
def canonicalLimitCertificates : D.LimitCertificates :=
  RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u}
    (RingedSpace.inverseImage D.descent.limitCone.pt.toRingedSpace D.structureMapLimit.base)

/-- **The canonical derived-tensoring certificates on the inverse-image ringed space of the
structure morphism of a stage**, the counterpart at `Xᵢ ⟶ Sᵢ` of
`AlgebraicGeometry.RelativeDescentSituation.canonicalLimitCertificates`. -/
def canonicalStageCertificates (i : D.LaterIndex) : D.StageCertificates i :=
  RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u}
    (RingedSpace.inverseImage (D.descent.system.obj (op i.1)).toRingedSpace
      (D.structureMapAt i).base)

/-! ### The property the induction runs on -/

/-- **One half of Stacks 0DI8, at the canonical certificates.** Every object of `D(𝒪_X)` perfect
relative to the limit base `S` is the derived pullback, from some stage `i`, of an object of
`D(𝒪_{Xᵢ})` perfect relative to `Sᵢ`, relative perfectness being read at the canonical
derived-tensoring certificates on both sides. These are the certificates at which the affine case
`AlgebraicGeometry.AffinePerfectDescent.exists_isPerfectRelativeTo_stage` is proved. -/
def PerfectEssentiallySurjectiveCanonical : Prop :=
  D.PerfectEssentiallySurjective D.canonicalLimitCertificates D.canonicalStageCertificates

/-- **The property `P` of the source's proof of Stacks 0DI8**: the essential-surjectivity half of
the tag, at the canonical certificates, for the situation restricted to a quasi-compact open
`U₀ ⊆ X₀`. Explicitly, every object of `D(𝒪_U)` perfect relative to `S`, where
`U = X ×_{X₀} U₀`, is the derived pullback of an object of `D(𝒪_{Uᵢ})` perfect relative to `Sᵢ`
at some stage, where `Uᵢ = Xᵢ ×_{X₀} U₀`. -/
def RestrictPerfectEssentiallySurjective (U₀ : D.X₀.left.Opens)
    (hU₀ : IsCompact (U₀ : Set D.X₀.left)) : Prop :=
  (D.restrict U₀ hU₀).PerfectEssentiallySurjectiveCanonical

/-! ### The induction -/

/-- **The induction of Stacks 08DR for the essential-surjectivity half of Stacks 0DI8.** Suppose
the half holds for the situation restricted to every affine open of `X₀` lying over an affine
open of `S₀`, and that it passes from a quasi-compact `U₀`, such a `V₀` and `U₀ ∩ V₀` to
`U₀ ∪ V₀`. Then it holds for the situation restricted to every quasi-compact open of `X₀`.

`X₀` is quasi-separated, being of finite presentation over the quasi-separated `S₀`, and the
affine opens lying over an affine open of `S₀` form a downward-closed family containing an
affine open neighbourhood of every point, so
`Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact_of_basis` applies to them. The two
hypotheses are the source's own two steps. -/
theorem restrictPerfectEssentiallySurjective_of_isAffineOpen_over_affine_of_sup
    (haffine : ∀ (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀),
      D.IsAffineOpenOverAffine V₀ → D.RestrictPerfectEssentiallySurjective V₀ hV₀.isCompact)
    (hsup : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsAffineOpen V₀) (_ : D.IsAffineOpenOverAffine V₀)
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      D.RestrictPerfectEssentiallySurjective U₀ hU₀ →
        D.RestrictPerfectEssentiallySurjective V₀ hV₀.isCompact →
          D.RestrictPerfectEssentiallySurjective (U₀ ⊓ V₀) hinf →
            D.RestrictPerfectEssentiallySurjective (U₀ ⊔ V₀) hsupc)
    (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left)) :
    D.RestrictPerfectEssentiallySurjective U₀ hU₀ := by
  have : QuasiSeparated D.X₀.hom := D.finitePresentation.quasiSeparated
  have : QuasiSeparatedSpace (D.descent.system.obj (op D.descent.base)) :=
    D.descent.quasiSeparated D.descent.base
  have : QuasiSeparatedSpace D.X₀.left := quasiSeparatedSpace_of_quasiSeparated D.X₀.hom
  refine _root_.Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact_of_basis
    (P := fun W => ∀ h : IsCompact (W : Set D.X₀.left),
      D.RestrictPerfectEssentiallySurjective W h)
    (Q := fun W => D.IsAffineOpenOverAffine W) D.isAffineOpenOverAffine_bot
    (fun _ _ hle hQ => D.isAffineOpenOverAffine_mono hle hQ)
    D.exists_isAffineOpen_isAffineOpenOverAffine (fun W hW hQ _ => haffine W hW hQ) ?_
    U₀ hU₀ hU₀
  intro W V hW hV hVQ hPW hPV hPinf hsupc
  have hinf : IsCompact ((W ⊓ V : D.X₀.left.Opens) : Set D.X₀.left) :=
    QuasiSeparatedSpace.inter_isCompact (W : Set D.X₀.left) (V : Set D.X₀.left) W.isOpen hW
      V.isOpen hV.isCompact
  exact hsup W V hW hV hVQ hinf hsupc (hPW hW) (hPV hV.isCompact) (hPinf hinf)

/-- **The induction of Stacks 08DR for the essential-surjectivity half of Stacks 0DI8, at
`U₀ = X₀`.** `X₀` is quasi-compact, being quasi-compact over the quasi-compact `S₀`, so the
induction reaches the whole of `X₀`. -/
theorem restrictPerfectEssentiallySurjective_top
    (haffine : ∀ (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀),
      D.IsAffineOpenOverAffine V₀ → D.RestrictPerfectEssentiallySurjective V₀ hV₀.isCompact)
    (hsup : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsAffineOpen V₀) (_ : D.IsAffineOpenOverAffine V₀)
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      D.RestrictPerfectEssentiallySurjective U₀ hU₀ →
        D.RestrictPerfectEssentiallySurjective V₀ hV₀.isCompact →
          D.RestrictPerfectEssentiallySurjective (U₀ ⊓ V₀) hinf →
            D.RestrictPerfectEssentiallySurjective (U₀ ⊔ V₀) hsupc)
    (hT : IsCompact ((⊤ : D.X₀.left.Opens) : Set D.X₀.left)) :
    D.RestrictPerfectEssentiallySurjective ⊤ hT :=
  D.restrictPerfectEssentiallySurjective_of_isAffineOpen_over_affine_of_sup haffine hsup ⊤ hT

/-- `X₀` is a quasi-compact space: it is quasi-compact over `S₀`, which is quasi-compact because
every scheme in the inverse system of Stacks 0DI6 is. -/
theorem isCompact_top_X₀ : IsCompact ((⊤ : D.X₀.left.Opens) : Set D.X₀.left) := by
  have : QuasiCompact D.X₀.hom := D.finitePresentation.quasiCompact
  have : CompactSpace (D.descent.system.obj (op D.descent.base)) :=
    D.descent.quasiCompact D.descent.base
  have : CompactSpace D.X₀.left := QuasiCompact.compactSpace_of_compactSpace D.X₀.hom
  rw [TopologicalSpace.Opens.coe_top]
  exact isCompact_univ

end AlgebraicGeometry.RelativeDescentSituation

end
