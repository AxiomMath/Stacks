module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksFrontier.AlgebraicGeometry.PicardGroup.OpenUFD
public import StacksFrontier.RingTheory.GradedAlgebra.SymmetricAway.DegreeOneChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Picard group of a standard chart of projective space is trivial

Grade `R[Xⱼ : j ∈ σ]` by total degree and let `R` be a unique factorization domain. The standard
open `D₊(Xᵢ)` of `Proj R[Xⱼ]` is the spectrum of the chart ring
`Stacks.SymmetricAway.chartRing R i`, which is a polynomial ring over `R` in the remaining
variables and so again a unique factorization domain. Its Picard group is therefore trivial by
[Stacks, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA).

This is the opening move of [Stacks, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ), which
computes `Pic(ℙⁿ_R)` by a Čech `1`-cocycle argument for the covering of `ℙⁿ_R` by the `n + 1`
standard charts: the cocycle description is available precisely because each chart has trivial
Picard group, so every invertible module is trivial on each of them.

## Main results

* `Stacks.ProjectiveSpace.PicardChart.subsingleton_picardGroup_spectrum`: the Picard group of
  `Spec A` is trivial for `A` a unique factorization domain. This is Tag 0BDA, part (1), at the
  improper open `⊤`.
* `Stacks.ProjectiveSpace.PicardChart.subsingleton_picardGroup_basicOpen_X`: the Picard group of
  the standard chart `D₊(Xᵢ)` of `Proj R[Xⱼ]` is trivial.

## Implementation notes

**Why the chart ring rather than affine space.** `Proj.basicOpenIsoSpec` presents `D₊(Xᵢ)` as
`Spec` of `HomogeneousLocalization.Away (homogeneousSubmodule σ R) (Xᵢ)`, which is by definition
`Stacks.SymmetricAway.chartRing R i`. Triviality of the Picard group only needs that ring to be
a unique factorization domain, and `Stacks.SymmetricAway.chartAlgEquiv` identifies it with
`MvPolynomial {j // j ≠ i} R`, over which Mathlib has the instance. So the argument runs through
the chart ring directly and no scheme-level identification of `D₊(Xᵢ)` with affine space
`𝔸ⁿ_R` is needed — `Stacks.PicardUFD.subsingleton_picardGroup_open_affineSpace`, Tag 0BDA
part (2), is not used here.

The two transported instances `isDomain_chartRing` and `uniqueFactorizationMonoid_chartRing` are
stated as instances because the chart ring is an `abbrev` for a homogeneous localization, so
instance search cannot find them on its own: the unique factorization structure lives on the
polynomial ring on the far side of `chartAlgEquiv`.

**Which Picard group.** `Stacks.SheafOfModules.PicardGroup` of
`StacksFrontier/AlgebraicGeometry/PicardGroup/Basic.lean`, which is the one Tag 0BDA and the
descent toolkit of `StacksFrontier/AlgebraicGeometry/PicardGroup/Descent.lean` are stated over,
and whose scheme-level spelling is `AlgebraicGeometry.Scheme.picardGroup`. The repository carries
a second Picard group, `Stacks.SheafOfModules.PicardGroup` of
`StacksFrontier/AlgebraicGeometry/Picard/Group.lean`; no bridge between them is introduced here.

## References

* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial Stacks.SheafOfModules

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

namespace Stacks.ProjectiveSpace.PicardChart

/-- **The Picard group of the spectrum of a unique factorization domain is trivial.** This is
Tag 0BDA, part (1), at the open `⊤`, transported along `AlgebraicGeometry.Scheme.topIso`. -/
theorem subsingleton_picardGroup_spectrum (A : Type u) [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] :
    Subsingleton (PicardGroup (Spec (.of A)).presheaf (Spec (.of A)).ringCatSheaf.2) :=
  Stacks.PicardGroup.subsingleton_of_iso (Scheme.topIso _)
    (Stacks.PicardUFD.subsingleton_picardGroup_open_spectrum A ⊤)

variable (R : Type u) [CommRing R] {σ : Type v} (i : σ)

/-- The chart ring of a standard chart of projective space over a domain is a domain: it is a
polynomial ring over `R` in the variables other than `Xᵢ`. -/
instance isDomain_chartRing [IsDomain R] : IsDomain (Stacks.SymmetricAway.chartRing R i) :=
  MulEquiv.isDomain _ (Stacks.SymmetricAway.chartAlgEquiv (R := R) i).symm.toMulEquiv

/-- The chart ring of a standard chart of projective space over a unique factorization domain is
again a unique factorization domain, being a polynomial ring over `R`. -/
instance uniqueFactorizationMonoid_chartRing [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid (Stacks.SymmetricAway.chartRing R i) :=
  (Stacks.SymmetricAway.chartAlgEquiv (R := R) i).toMulEquiv.uniqueFactorizationMonoid
    inferInstance

/-- **The Picard group of the standard chart `D₊(Xᵢ)` of `Proj R[Xⱼ]` is trivial**, for `R` a
unique factorization domain. The chart is the spectrum of the chart ring, which is again a unique
factorization domain, so this is Tag 0BDA. It is the opening step of Tag 0BXJ. -/
@[ega "I 2.4.8"]
theorem subsingleton_picardGroup_basicOpen_X [IsDomain R] [UniqueFactorizationMonoid R] :
    Subsingleton (PicardGroup
      (Proj.basicOpen (homogeneousSubmodule σ R) (X i)).toScheme.presheaf
      (Proj.basicOpen (homogeneousSubmodule σ R) (X i)).toScheme.ringCatSheaf.2) :=
  Stacks.PicardGroup.subsingleton_of_iso
    (Proj.basicOpenIsoSpec (homogeneousSubmodule σ R) (X i)
      (Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one i) Nat.one_pos).symm
    (subsingleton_picardGroup_spectrum (Stacks.SymmetricAway.chartRing R i))

end Stacks.ProjectiveSpace.PicardChart

end
