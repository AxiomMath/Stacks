module

public import StacksFrontier.AlgebraicGeometry.Spaces.PicardGroupFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleCohomologyInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UnitsShortExactSequence
public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ShortExactLongExactSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Picard group of a first-order thickening of algebraic spaces

Let `X ⊂ X'` be a first-order thickening of algebraic spaces over `S`, with ideal sheaf `𝓘`.
This file constructs the canonical exact sequence

`0 → H⁰(X,𝓘) → H⁰(X',𝒪*_{X'}) → H⁰(X,𝒪*_X) → H¹(X,𝓘) → Pic(X') → Pic(X) → H²(X,𝓘) → ⋯`

of Stacks 0DNM, which continues in every degree.

It is the long exact cohomology sequence of the short exact sequence of sheaves of abelian
groups `0 → 𝓘 → 𝒪*_{X'} → 𝒪*_X → 0` on the common small étale site `X_étale = X'_étale`, with
the first-cohomology terms of the two sheaves of units read as Picard groups.

## Main definitions

* `AlgebraicGeometry.Space.idealToUnitsCohomology`,
  `AlgebraicGeometry.Space.unitsRestrictionCohomology` and
  `AlgebraicGeometry.Space.thickeningBoundary`: the three families of maps of the long exact
  sequence, in every degree.
* `AlgebraicGeometry.Space.picardAmbient` and `AlgebraicGeometry.Space.picardClosed`: the
  readings of the two degree-one unit cohomology groups as the Picard groups of `X'` and of `X`.
* `AlgebraicGeometry.Space.picardOfIdeal`, `AlgebraicGeometry.Space.picardRestriction` and
  `AlgebraicGeometry.Space.picardBoundary`: the three displayed maps
  `H¹(X,𝓘) → Pic(X') → Pic(X) → H²(X,𝓘)`.
* `AlgebraicGeometry.Space.PicardFirstOrderSequence`: the whole sequence, bundled.

## Main results

* `AlgebraicGeometry.Space.injective_idealToUnitsCohomology_zero`,
  `AlgebraicGeometry.Space.exact_idealToUnitsCohomology`,
  `AlgebraicGeometry.Space.exact_unitsRestrictionCohomology` and
  `AlgebraicGeometry.Space.exact_thickeningBoundary`: the long exact sequence, in every degree.
* `AlgebraicGeometry.Space.exact_picardOfIdeal`,
  `AlgebraicGeometry.Space.exact_picardRestriction` and
  `AlgebraicGeometry.Space.exact_picardBoundary`: exactness at `Pic(X')`, at `Pic(X)` and at
  `H²(X,𝓘)`.
* `AlgebraicGeometry.Space.picardFirstOrderSequence`: **Stacks 0DNM**, the canonical exact
  sequence, under the source's own hypotheses.

## Implementation notes

Following the source, every term is carried on the small étale site of the *ambient* space `X'`,
which the source identifies with the small étale site of `X` (Stacks 05ZM); the closed space
enters through the direct image `i_*𝒪_X` of its structure sheaf, which on that common site is
`AlgebraicGeometry.Space.thickeningRestrictRingedSite`, the restriction of the structure sheaf
of `X` along base change of étale charts.

The two readings of degree-one unit cohomology as Picard groups are therefore asymmetric.
`picardAmbient` is Tag 040E on the small étale site of `X'` directly,
`AlgebraicGeometry.Space.h1UnitsAddEquivPicardGroup`. For `picardClosed` the cohomology is
first carried from the common site back to the small étale site of `X` by
`AlgebraicGeometry.Space.thickeningCohomologyAddEquiv`, which is the cohomological half of
Stacks 05ZM, and Tag 040E is applied there; so `Pic(X)` is the intrinsic Picard group of `X`
and not merely the Picard group of `i_*𝒪_X` on the ambient site.

Both Picard groups are the repository's `AlgebraicGeometry.Space.picardGroup`, so the sequence
is the displayed one and not a restatement of it in terms of first cohomology. The
`closedUnitsCohomology` field records the same identification of the third term in every
degree, so `H⁰(X, 𝒪*_X)` is the intrinsic group of global units of `X` and not only a group
carried on the ambient presentation of the common site. The ideal sheaf is a subsheaf of
`𝒪_{X'}` and so lives on the common site natively; `H^i(X, 𝓘)` is its cohomology there.

The `Ext` universe is `u + 1`, where the hypothesis is discharged rather than carried; the
sequence therefore has no instance hypotheses beyond the thickening itself. The middle type of
each `AddEquiv.trans` is written out, because the elaborator otherwise leaves that universe a
metavariable and fails to find the additive structure on the cohomology group.

## References

* [Stacks Project, Tag 0DNM](https://stacks.math.columbia.edu/tag/0DNM)
* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R), the scheme analogue
* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.Torsors.Generators

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}
  (hG : IsFirstOrderThickening B S hS X G)

/-- The closed member of a first-order thickening, as an algebraic space. -/
abbrev firstOrderThickeningSpace : AlgebraicSpaces B S hS :=
  IsThickening.space B S hS hG.1

/-! ### The long exact sequence on the common site -/

/-- The map `H^n(X,𝓘) → H^n(X',𝒪*_{X'})` of the sequence, induced by `f ↦ 1 + f`. -/
def idealToUnitsCohomology (n : ℕ) :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₁ n →+
      Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₂ n :=
  Sheaf.H.map.{u + 1} (thickeningUnitsShortComplex B S hS hG).f n

/-- The map `H^n(X',𝒪*_{X'}) → H^n(X,𝒪*_X)` of the sequence, induced by restriction of units
along the thickening. -/
def unitsRestrictionCohomology (n : ℕ) :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₂ n →+
      Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₃ n :=
  Sheaf.H.map.{u + 1} (thickeningUnitsShortComplex B S hS hG).g n

/-- The connecting map `H^n(X,𝒪*_X) → H^{n+1}(X,𝓘)` of the sequence. -/
def thickeningBoundary (n : ℕ) :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₃ n →+
      Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₁ (n + 1) :=
  Stacks.Cohomology.GlobalLongExactSequence.boundary.{u + 1}
    (thickeningUnitsShortComplex_shortExact B S hS hG) n

/-- **The sequence of Stacks 0DNM starts with a zero**: a global section of the ideal sheaf
whose exponential is the unit `1` is zero. -/
theorem injective_idealToUnitsCohomology_zero :
    Function.Injective (idealToUnitsCohomology B S hS hG 0) :=
  have := (thickeningUnitsShortComplex_shortExact B S hS hG).mono_f
  Stacks.Cohomology.GlobalLongExactSequence.injective_map_zero.{u + 1} _

/-- **Exactness at `H^n(X',𝒪*_{X'})`.** -/
theorem exact_idealToUnitsCohomology (n : ℕ) :
    Function.Exact (idealToUnitsCohomology B S hS hG n) (unitsRestrictionCohomology B S hS hG n) :=
  Stacks.Cohomology.GlobalLongExactSequence.exact_map_map.{u + 1}
    (thickeningUnitsShortComplex_shortExact B S hS hG) n

/-- **Exactness at `H^n(X,𝒪*_X)`.** -/
theorem exact_unitsRestrictionCohomology (n : ℕ) :
    Function.Exact (unitsRestrictionCohomology B S hS hG n) (thickeningBoundary B S hS hG n) :=
  Stacks.Cohomology.GlobalLongExactSequence.exact_map_boundary.{u + 1}
    (thickeningUnitsShortComplex_shortExact B S hS hG) n

/-- **Exactness at `H^{n+1}(X,𝓘)`.** -/
theorem exact_thickeningBoundary (n : ℕ) :
    Function.Exact (thickeningBoundary B S hS hG n)
      (idealToUnitsCohomology B S hS hG (n + 1)) :=
  Stacks.Cohomology.GlobalLongExactSequence.exact_boundary_map.{u + 1}
    (thickeningUnitsShortComplex_shortExact B S hS hG) n

/-! ### The two Picard readings -/

/-- **Degree-one cohomology of the units of `X'` is `Pic(X')`.** -/
def picardAmbient :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₂ 1 ≃+ picardGroup X :=
  h1UnitsAddEquivPicardGroup B S hS X

/-- Cohomology of the units of the closed member, read on the common site, is its intrinsic
cohomology on the small étale site of that member. This is the cohomological half of
Stacks 05ZM. -/
def closedUnitsCohomologyEquiv (n : ℕ) :
    Sheaf.H.{u + 1} (unitsAddSheafEtale B S hS (firstOrderThickeningSpace B S hS hG)) n ≃+
      Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₃ n :=
  thickeningCohomologyAddEquiv B S hS hG.1
    (unitsAddSheafEtale B S hS (firstOrderThickeningSpace B S hS hG)) n

/-- **Degree-one cohomology of the units of `X`, read on the common site, is `Pic(X)`.** -/
def picardClosed :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₃ 1 ≃+
      picardGroup (firstOrderThickeningSpace B S hS hG) :=
  AddEquiv.trans
    (N := Sheaf.H.{u + 1} (unitsAddSheafEtale B S hS (firstOrderThickeningSpace B S hS hG)) 1)
    (closedUnitsCohomologyEquiv B S hS hG 1).symm
    (h1UnitsAddEquivPicardGroup B S hS (firstOrderThickeningSpace B S hS hG))

/-! ### The displayed sequence in Picard form -/

/-- The map `H¹(X,𝓘) → Pic(X')` of the displayed sequence. -/
def picardOfIdeal :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₁ 1 →+ picardGroup X :=
  (picardAmbient B S hS hG).toAddMonoidHom.comp (idealToUnitsCohomology B S hS hG 1)

/-- The restriction map `Pic(X') → Pic(X)` of the displayed sequence. -/
def picardRestriction :
    picardGroup X →+ picardGroup (firstOrderThickeningSpace B S hS hG) :=
  (picardClosed B S hS hG).toAddMonoidHom.comp
    ((unitsRestrictionCohomology B S hS hG 1).comp
      (picardAmbient B S hS hG).symm.toAddMonoidHom)

/-- The connecting map `Pic(X) → H²(X,𝓘)` of the displayed sequence. -/
def picardBoundary :
    picardGroup (firstOrderThickeningSpace B S hS hG) →+
      Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₁ 2 :=
  (thickeningBoundary B S hS hG 1).comp (picardClosed B S hS hG).symm.toAddMonoidHom

/-- **Exactness at `Pic(X')`.** -/
theorem exact_picardOfIdeal :
    Function.Exact (picardOfIdeal B S hS hG) (picardRestriction B S hS hG) :=
  Stacks.Thickenings.exact_addEquiv_transport (idealToUnitsCohomology B S hS hG 1)
    (unitsRestrictionCohomology B S hS hG 1) (exact_idealToUnitsCohomology B S hS hG 1)
    (AddEquiv.refl _) (picardAmbient B S hS hG) (picardClosed B S hS hG)

/-- **Exactness at `Pic(X)`.** -/
theorem exact_picardRestriction :
    Function.Exact (picardRestriction B S hS hG) (picardBoundary B S hS hG) :=
  Stacks.Thickenings.exact_addEquiv_transport (unitsRestrictionCohomology B S hS hG 1)
    (thickeningBoundary B S hS hG 1) (exact_unitsRestrictionCohomology B S hS hG 1)
    (picardAmbient B S hS hG).symm (picardClosed B S hS hG) (AddEquiv.refl _)

/-- **Exactness at `H²(X,𝓘)`.** -/
theorem exact_picardBoundary :
    Function.Exact (picardBoundary B S hS hG) (idealToUnitsCohomology B S hS hG 2) :=
  Stacks.Thickenings.exact_addEquiv_transport (thickeningBoundary B S hS hG 1)
    (idealToUnitsCohomology B S hS hG 2) (exact_thickeningBoundary B S hS hG 1)
    (picardClosed B S hS hG).symm (AddEquiv.refl _) (AddEquiv.refl _)

/-! ### The sequence of Stacks 0DNM -/

/-- **The canonical exact sequence of a first-order thickening of algebraic spaces**, the
content of Stacks 0DNM:

`0 → H⁰(X,𝓘) → H⁰(X',𝒪*_{X'}) → H⁰(X,𝒪*_X) → H¹(X,𝓘) → Pic(X') → Pic(X) → H²(X,𝓘) → ⋯`

The three families of maps and the two Picard readings are data, pinned to the canonical
constructions by the `_eq` fields; the rest is exactness. The sequence continues in every
degree, which is the content of the three degreewise exactness fields. -/
structure PicardFirstOrderSequence where
  /-- The map `H^n(X,𝓘) → H^n(X',𝒪*_{X'})` of the sequence, for every `n`. -/
  idealToUnits (n : ℕ) :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₁ n →+
      Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₂ n
  /-- The map `H^n(X',𝒪*_{X'}) → H^n(X,𝒪*_X)` of the sequence, for every `n`. -/
  unitsRestriction (n : ℕ) :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₂ n →+
      Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₃ n
  /-- The connecting map `H^n(X,𝒪*_X) → H^{n+1}(X,𝓘)` of the sequence, for every `n`. -/
  boundary (n : ℕ) :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₃ n →+
      Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₁ (n + 1)
  /-- The first family is the map induced by the exponential `f ↦ 1 + f` of the square-zero
  ideal, and not chosen data. -/
  idealToUnits_eq (n : ℕ) : idealToUnits n = idealToUnitsCohomology B S hS hG n
  /-- The second family is the map induced by restriction of units along the thickening. -/
  unitsRestriction_eq (n : ℕ) : unitsRestriction n = unitsRestrictionCohomology B S hS hG n
  /-- The boundary is the connecting homomorphism of the short exact sequence of units. -/
  boundary_eq (n : ℕ) : boundary n = thickeningBoundary B S hS hG n
  /-- The sequence starts with a zero. -/
  injective_idealToUnits_zero : Function.Injective (idealToUnits 0)
  /-- Exactness at `H^n(X',𝒪*_{X'})`. -/
  exact_idealToUnits (n : ℕ) : Function.Exact (idealToUnits n) (unitsRestriction n)
  /-- Exactness at `H^n(X,𝒪*_X)`. -/
  exact_unitsRestriction (n : ℕ) : Function.Exact (unitsRestriction n) (boundary n)
  /-- Exactness at `H^{n+1}(X,𝓘)`. -/
  exact_boundary (n : ℕ) : Function.Exact (boundary n) (idealToUnits (n + 1))
  /-- The cohomology of the units of `X` read on the common site is its intrinsic cohomology on
  the small étale site of `X`, in every degree: the third term of the sequence really is
  `H^n(X, 𝒪*_X)`. -/
  closedUnitsCohomology (n : ℕ) :
    Sheaf.H.{u + 1} (unitsAddSheafEtale B S hS (firstOrderThickeningSpace B S hS hG)) n ≃+
      Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₃ n
  /-- That identification is the one induced by base change of étale charts along the
  thickening. -/
  closedUnitsCohomology_eq (n : ℕ) :
    closedUnitsCohomology n = closedUnitsCohomologyEquiv B S hS hG n
  /-- Degree-one cohomology of the units of `X'` is the Picard group of `X'`. -/
  picardAmbientEquiv :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₂ 1 ≃+ picardGroup X
  /-- Degree-one cohomology of the units of `X`, read on the common site, is the Picard group
  of `X`. -/
  picardClosedEquiv :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₃ 1 ≃+
      picardGroup (firstOrderThickeningSpace B S hS hG)
  /-- The reading of degree-one unit cohomology of `X'` as `Pic(X')` is the canonical
  isomorphism of Tag 040E. -/
  picardAmbientEquiv_eq : picardAmbientEquiv = picardAmbient B S hS hG
  /-- The reading of degree-one unit cohomology of `X` as `Pic(X)` is the canonical isomorphism
  of Tag 040E, composed with the identification of the two small étale sites. -/
  picardClosedEquiv_eq : picardClosedEquiv = picardClosed B S hS hG
  /-- The map `H¹(X,𝓘) → Pic(X')` of the displayed sequence. -/
  picardOfIdealHom :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₁ 1 →+ picardGroup X
  /-- The restriction map `Pic(X') → Pic(X)` of the displayed sequence. -/
  picardRestrictionHom :
    picardGroup X →+ picardGroup (firstOrderThickeningSpace B S hS hG)
  /-- The connecting map `Pic(X) → H²(X,𝓘)` of the displayed sequence. -/
  picardBoundaryHom :
    picardGroup (firstOrderThickeningSpace B S hS hG) →+
      Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₁ 2
  /-- The three displayed maps are the degree-one maps of the long exact sequence read through
  the two Picard identifications. -/
  picardOfIdealHom_eq : picardOfIdealHom = picardOfIdeal B S hS hG
  /-- See `picardOfIdealHom_eq`. -/
  picardRestrictionHom_eq : picardRestrictionHom = picardRestriction B S hS hG
  /-- See `picardOfIdealHom_eq`. -/
  picardBoundaryHom_eq : picardBoundaryHom = picardBoundary B S hS hG
  /-- Exactness at `Pic(X')`. -/
  exact_picardOfIdealHom : Function.Exact picardOfIdealHom picardRestrictionHom
  /-- Exactness at `Pic(X)`. -/
  exact_picardRestrictionHom : Function.Exact picardRestrictionHom picardBoundaryHom
  /-- Exactness at `H²(X,𝓘)`. -/
  exact_picardBoundaryHom : Function.Exact picardBoundaryHom (idealToUnits 2)

/-- **Stacks Project, Tag 0DNM.** Let `S` be a scheme and let `X ⊂ X'` be a first-order
thickening of algebraic spaces over `S` with ideal sheaf `𝓘`. Then there is a canonical exact
sequence

`0 → H⁰(X,𝓘) → H⁰(X',𝒪*_{X'}) → H⁰(X,𝒪*_X) → H¹(X,𝓘) → Pic(X') → Pic(X) → H²(X,𝓘) → ⋯`

which continues in every degree.

It is the long exact cohomology sequence of
`0 → 𝓘 → 𝒪*_{X'} → 𝒪*_X → 0` on the common small étale site, with the two degree-one unit
cohomology groups read as Picard groups by Tag 040E. -/
@[stacks 0DNM, ega "IV 21.13.9" "The exact segment H¹(U"]
def picardFirstOrderSequence : PicardFirstOrderSequence B S hS hG where
  idealToUnits := idealToUnitsCohomology B S hS hG
  unitsRestriction := unitsRestrictionCohomology B S hS hG
  boundary := thickeningBoundary B S hS hG
  idealToUnits_eq _ := rfl
  unitsRestriction_eq _ := rfl
  boundary_eq _ := rfl
  injective_idealToUnits_zero := injective_idealToUnitsCohomology_zero B S hS hG
  exact_idealToUnits := exact_idealToUnitsCohomology B S hS hG
  exact_unitsRestriction := exact_unitsRestrictionCohomology B S hS hG
  exact_boundary := exact_thickeningBoundary B S hS hG
  closedUnitsCohomology := closedUnitsCohomologyEquiv B S hS hG
  closedUnitsCohomology_eq _ := rfl
  picardAmbientEquiv := picardAmbient B S hS hG
  picardClosedEquiv := picardClosed B S hS hG
  picardAmbientEquiv_eq := rfl
  picardClosedEquiv_eq := rfl
  picardOfIdealHom := picardOfIdeal B S hS hG
  picardRestrictionHom := picardRestriction B S hS hG
  picardBoundaryHom := picardBoundary B S hS hG
  picardOfIdealHom_eq := rfl
  picardRestrictionHom_eq := rfl
  picardBoundaryHom_eq := rfl
  exact_picardOfIdealHom := exact_picardOfIdeal B S hS hG
  exact_picardRestrictionHom := exact_picardRestriction B S hS hG
  exact_picardBoundaryHom := exact_picardBoundary B S hS hG

end AlgebraicGeometry.Space

end
