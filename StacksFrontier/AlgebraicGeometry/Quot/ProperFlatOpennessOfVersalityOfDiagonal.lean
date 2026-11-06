module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatOpennessOfVersality
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatRimSchlessingerStarUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerConormalIso
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerEffectiveOfConormal
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesDiagonalUnconditional

/-!
# Openness of versality for `Spaces'_{fp, flat, proper}` and for curves, on the diagonal alone

The body of the proof of [Stacks Project, Tag 0D3X] shows that `Spaces'_{fp, flat, proper}`
satisfies hypothesis (4) of Artin's criterion Stacks 0CXU: square-zero systems are effective.
Here that is `AlgebraicGeometry.isSquareZeroEffective_cartesianProperFlat`, assembled from
`AlgebraicGeometry.isSquareZeroEffective_cartesianProperFlat_of_towerConormal` and the
invertibility of the conormal map of a realized solution of the tower problem,
`AlgebraicGeometry.ProperFlatFibre.isIso_towerRealizationConormalMap`.

With (RS\*) from Stacks 0D1J
(`AlgebraicGeometry.satisfiesRSStar_cartesianProperFlat_unconditional`) and limit preservation from
Stacks 0D1I, Artin's criterion leaves only hypothesis (1) of Stacks 0CXU, the representability of
the diagonal (Stacks 0D1F). That is supplied by
`AlgebraicGeometry.Space.properFlatSpacesStack_hasRepresentableDiagonal`, so the last three
declarations below have no hypotheses beyond those of the source.

None of these declarations is registered.

## Main results

* `AlgebraicGeometry.openVersalityOf_cartesianProperFlat`: **Stacks 0D3X**, over any locally
  Noetherian base scheme of the site (both clauses of the source: `Spec ℤ` and any Noetherian `S`).
* `AlgebraicGeometry.curves_openVersalityOf_specZ` and `AlgebraicGeometry.curves_openVersalityOf`:
  the two clauses of **Stacks 0D59**.

* `AlgebraicGeometry.isSquareZeroEffective_cartesianProperFlat`: hypothesis (4) of Stacks 0CXU
  for `Spaces'_{fp, flat, proper}`, over any base scheme of the site.
* `AlgebraicGeometry.openVersalityOf_cartesianProperFlat_of_hasRepresentableDiagonal`: Stacks 0D3X
  over a locally Noetherian base, from the diagonal.
* `AlgebraicGeometry.curves_openVersalityOf_specZ_of_hasRepresentableDiagonal` and
  `AlgebraicGeometry.curves_openVersalityOf_of_hasRepresentableDiagonal`: the two clauses of
  Stacks 0D59, from the diagonal.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D59](https://stacks.math.columbia.edu/tag/0D59)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
-/

@[expose] public section

open CategoryTheory Deformation.Artin

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`Spaces'_{fp, flat, proper}` satisfies hypothesis (4) of Stacks 0CXU**: systems of objects
over the spectra of an inverse system of algebras with surjective square-zero transition maps are
effective. This is the body of the proof of Stacks 0D3X. -/
theorem isSquareZeroEffective_cartesianProperFlat :
    IsSquareZeroEffective B S hS (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS) :=
  isSquareZeroEffective_cartesianProperFlat_of_towerConormal B S hS (by
    intro _ _ _ _ _ _ _ _ _ _ _ _ P' X'
    exact ProperFlatFibre.isIso_towerRealizationConormalMap P' X')

/-- **Stacks 0D3X, from the diagonal.** Over a locally Noetherian base `S`, if the diagonal of
`Spaces'_{fp, flat, proper}` is representable by algebraic spaces (Stacks 0D1F), the stack
satisfies openness of versality. -/
theorem openVersalityOf_cartesianProperFlat_of_hasRepresentableDiagonal [IsLocallyNoetherian S]
    (hΔ : Stack.HasRepresentableDiagonal B S hS (Space.properFlatSpacesStack B S hS)) :
    OpenVersalityOf (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) :=
  openVersalityOf_cartesianProperFlat_of_isSquareZeroEffective B S hS hΔ
    (satisfiesRSStar_cartesianProperFlat_unconditional B S hS)
    (isSquareZeroEffective_cartesianProperFlat B S hS)

variable (hZ : B.Contains integerBase)

/-- **The first clause of Stacks 0D59, from the diagonal**: the stack of curves satisfies
openness of versality over `Spec ℤ`, granted that the diagonal of `Spaces'_{fp, flat, proper}`
over `Spec ℤ` is representable by algebraic spaces (Stacks 0D1F). -/
theorem curves_openVersalityOf_specZ_of_hasRepresentableDiagonal
    (hΔ : Stack.HasRepresentableDiagonal B integerBase hZ
      (Space.properFlatSpacesStack B integerBase hZ)) :
    OpenVersalityOf (curvesProjectionOver B hZ ⋙ Over.post B.inclusion) :=
  curves_openVersalityOf_specZ_of_isSquareZeroEffective B hZ hΔ
    (satisfiesRSStar_cartesianProperFlat_unconditional B integerBase hZ)
    (isSquareZeroEffective_cartesianProperFlat B integerBase hZ)

/-- **The second clause of Stacks 0D59, from the diagonal**: the stack of `S`-curves over a
Noetherian scheme `S` satisfies openness of versality over `S`, granted that the diagonal of
`Spaces'_{fp, flat, proper}` over `S` is representable by algebraic spaces (Stacks 0D1F). -/
theorem curves_openVersalityOf_of_hasRepresentableDiagonal [IsNoetherian S]
    (hΔ : Stack.HasRepresentableDiagonal B S hS (Space.properFlatSpacesStack B S hS)) :
    OpenVersalityOf
      (CostructuredArrow.pre (AlgebraicGeometry.curvesProjection B hZ)
        (𝟭 B.Schemes) (B.obj hS) ⋙ Over.post B.inclusion) :=
  curves_openVersalityOf_of_isSquareZeroEffective B S hS hZ hΔ
    (satisfiesRSStar_cartesianProperFlat_unconditional B S hS)
    (isSquareZeroEffective_cartesianProperFlat B S hS)

/-! ### Without hypotheses -/

/-- **Stacks 0D3X.** The stack `Spaces'_{fp, flat, proper}` of finitely presented, flat and proper
families of algebraic spaces satisfies openness of versality over any locally Noetherian base
scheme `S` of the site; in particular over `Spec ℤ` and over any Noetherian scheme. -/
theorem openVersalityOf_cartesianProperFlat [IsLocallyNoetherian S] :
    OpenVersalityOf (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) :=
  openVersalityOf_cartesianProperFlat_of_hasRepresentableDiagonal B S hS
    (Space.properFlatSpacesStack_hasRepresentableDiagonal B S hS)

/-- **Stacks 0D59, first clause.** The stack of curves satisfies openness of versality over
`Spec ℤ`. -/
theorem curves_openVersalityOf_specZ :
    OpenVersalityOf (curvesProjectionOver B hZ ⋙ Over.post B.inclusion) :=
  curves_openVersalityOf_specZ_of_hasRepresentableDiagonal B hZ
    (Space.properFlatSpacesStack_hasRepresentableDiagonal B integerBase hZ)

/-- **Stacks 0D59, second clause.** For a Noetherian scheme `S` of the site, the stack of
`S`-curves (the base change of Stacks 0D54) satisfies openness of versality over `S`. -/
theorem curves_openVersalityOf [IsNoetherian S] :
    OpenVersalityOf
      (CostructuredArrow.pre (AlgebraicGeometry.curvesProjection B hZ)
        (𝟭 B.Schemes) (B.obj hS) ⋙ Over.post B.inclusion) :=
  curves_openVersalityOf_of_hasRepresentableDiagonal B S hS hZ
    (Space.properFlatSpacesStack_hasRepresentableDiagonal B S hS)

end AlgebraicGeometry

end
