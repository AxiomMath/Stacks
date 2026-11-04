module

public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ChartStalkAlgebra
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.TwistTrivialization

/-!
# Projective space over a field is regular

Every local ring of `Proj k[T₀, …, Tₙ]` is a localization of a standard chart ring
`k[T]_{(Tᵢ)}` at a prime, and that chart ring is a polynomial ring in `n` variables over `k`,
hence a regular ring. So all local rings of projective `n`-space over a field are regular, and
the same holds for the projective space `𝐏(W)` of a nonzero finite-dimensional vector space,
which a basis identifies with the polynomial model.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolyChart.isRegularRing_away`: the standard chart ring of
  `Proj k[T₀, …, Tₙ]` is a regular ring.
* `Stacks.AlgebraicGeometry.ProjPolyChart.isRegularLocalRing_stalk_proj`: the local rings of
  `Proj k[T₀, …, Tₙ]` over a field are regular.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isRegularLocalRing_stalk_projectiveSpaceOfModule`:
  the local rings of the projective space of a nonzero finite-dimensional vector space are
  regular.

## Implementation notes

Regularity of the chart ring is Mathlib's `MvPolynomial.isRegularRing_of_isRegularRing`,
transported along `Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv`; the local ring at a point
of the chart is then one of the localizations at a prime that the definition of a regular ring
speaks about, by `Stacks.AlgebraicGeometry.ProjPolyChart.isLocalization_chartToStalk`. Passing
from the polynomial model to `𝐏(W)` uses
`AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_isOpenImmersion` on the isomorphism attached
to a basis, as `AlgebraicGeometry.ProjectiveSpaceOfModule.isReduced_projectiveSpaceOfModule`
does for reducedness. In particular no algebra structure over the ground field on a stalk is
needed anywhere.

## References

* [Stacks Project, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization

namespace Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- **The standard affine chart of projective space over a field is a regular ring**, being a
polynomial ring in `n` variables over `k`. -/
public theorem isRegularRing_away (i : Fin (n + 1)) :
    IsRegularRing (Away (polyGrading k n) (MvPolynomial.X i)) :=
  IsRegularRing.of_ringEquiv (chartEquiv k n i)

/-- **The local rings of `Proj k[T₀, …, Tₙ]` over a field are regular local rings.** A point
lies in some standard chart `D₊(Tᵢ)`, and its local ring is the localization of the chart ring
at the corresponding prime; the chart ring is a polynomial ring over `k`, hence regular. -/
public theorem isRegularLocalRing_stalk_proj
    (x : AlgebraicGeometry.Proj (polyGrading k n)) :
    IsRegularLocalRing ((AlgebraicGeometry.Proj (polyGrading k n)).presheaf.stalk x) := by
  obtain ⟨i, hx⟩ := ProjStalkGlobalSections.exists_X_notMem_asHomogeneousIdeal k n x
  let _ := algebraChartStalk k n i x hx
  have _ := isLocalization_chartToStalk k n i x hx
  have _ := isRegularRing_away k n i
  have _ : IsRegularLocalRing
      (Localization.AtPrime (chartSpecPoint k n i x hx).asIdeal) :=
    IsRegularRing.isRegularLocalRing_localization _
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (chartPrimeCompl k n i x hx)
      (Localization.AtPrime (chartSpecPoint k n i x hx).asIdeal)
      (projStalk k n x)).toRingEquiv

end Stacks.AlgebraicGeometry.ProjPolyChart

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

variable (k W : Type u) [Field k] [AddCommGroup W] [Module k W]

/-- **The projective space of a nonzero finite-dimensional vector space is a regular scheme**:
all of its local rings are regular. A basis identifies `𝐏(W)` with projective `n`-space over
the ground field, whose local rings are localizations of polynomial rings at primes. -/
public theorem isRegularLocalRing_stalk_projectiveSpaceOfModule [FiniteDimensional k W]
    [Nontrivial W] (y : projectiveSpaceOfModule k W) :
    IsRegularLocalRing ((projectiveSpaceOfModule k W).presheaf.stalk y) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := k) (M := W)).ne'
  rw [isRegularLocalRing_stalk_iff_of_isOpenImmersion
    (projectiveSpaceOfModuleIsoProjMvPolynomial (Module.finBasisOfFinrankEq k W hn)).hom y]
  exact isRegularLocalRing_stalk_proj k n _

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
