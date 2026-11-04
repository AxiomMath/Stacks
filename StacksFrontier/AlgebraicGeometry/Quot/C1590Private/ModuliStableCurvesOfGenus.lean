module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesPrestableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSemistableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable

/-!
# The moduli stack `𝓜̄_g` of stable curves of genus `g`

Stacks 0E78 decomposes `𝓜̄ = Curves^{stable}` (Stacks 0E77) into open and closed substacks
`𝓜̄_g`, `g ≥ 2`. By part (2) of Stacks 0E78 a point `Spec(k) → Curves` lies in `𝓜̄_g` exactly when
the curve it classifies is stable of genus `g`, so `𝓜̄_g` is the substack of stable families of
curves all of whose fibres have genus `g`. That is the definition recorded here, as a category
fibred in groupoids over the big fppf site of `Spec(ℤ)` through `AlgebraicGeometry.curvesSubstack`.

## Main definitions

* `AlgebraicGeometry.C1590Private.IsStableCurveFamilyOfFibreGenus`: stable, with all fibres of
  genus `g`.
* `AlgebraicGeometry.C1590Private.moduliStableCurvesOfGenus`: the stack `𝓜̄_g`.
* `AlgebraicGeometry.C1590Private.moduliStableCurvesOfGenusInclusion`: its inclusion into
  `Curves`.

## Main results

* `AlgebraicGeometry.C1590Private.isStableCurveFamilyOfFibreGenus_iff`: given the comparison
  `AlgebraicGeometry.C1590Private.PrestableHasGenusIff` of the fibre genus of a prestable family
  with the rank of `R¹f_*𝒪_X`, the objects of `𝓜̄_g` are exactly those of
  `AlgebraicGeometry.CurvesStableOfGenus`, the form of part (1)(b) of Stacks 0E78.

## Implementation notes

The genus is that of the fibres, `AlgebraicGeometry.CurveFamily.HasFibresOfGenus`, matching
`Curves^{prestable}_g` of Stacks 0E6V. Part (1)(b) of Stacks 0E78 phrases the same condition
through `R¹f_*𝒪_X` being locally free of rank `g`; for a prestable family the two agree by
cohomology and base change. The fibre form is stable under every morphism of families
(`AlgebraicGeometry.CurveFamily.HasFibresOfGenus.of_hom`), so the substack exists without that
comparison.

## References

* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E77](https://stacks.math.columbia.edu/tag/0E77)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.C1590Private

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- A family of curves is *stable of genus `g`* when it is stable (Stacks 0E75) and all its fibres
have genus `g`. -/
abbrev IsStableCurveFamilyOfFibreGenus (g : ℕ) (X : CurveFamily B hZ) : Prop :=
  IsStableCurveFamily B hZ X ∧ X.HasFibresOfGenus g

/-- A family of curves mapping to a stable family of genus `g` is stable of genus `g`. -/
theorem isStableCurveFamilyOfFibreGenus_of_hom (g : ℕ) {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsStableCurveFamilyOfFibreGenus B hZ g Y) : IsStableCurveFamilyOfFibreGenus B hZ g X :=
  ⟨CurveFamily.isStableCurveFamily_of_hom φ hY.1, hY.2.of_hom φ⟩

/-- **The two forms of `𝓜̄_g` agree.** Given the comparison of the fibre genus of a prestable
family with the rank of `R¹f_*𝒪_X` (cohomology and base change), a family of curves is stable with
fibres of genus `g` exactly when it is stable with `R¹f_*𝒪_X` locally free of rank `g`
(`AlgebraicGeometry.IsStableCurveFamilyOfGenus`, condition (1)(b) of Stacks 0E78). -/
theorem isStableCurveFamilyOfFibreGenus_iff (hR : PrestableHasGenusIff B hZ) (g : ℕ)
    (X : CurveFamily B hZ) :
    IsStableCurveFamilyOfFibreGenus B hZ g X ↔ IsStableCurveFamilyOfGenus B hZ g X :=
  ⟨fun h => ⟨h.1, (hR X h.1.1 g).2 h.2⟩, fun h => ⟨h.1, (hR X h.1.1 g).1 h.2⟩⟩

/-- The moduli stack `𝓜̄_g` of stable curves of genus `g` of Stacks 0E77 and 0E78, as a category
fibred in groupoids over the big fppf site of `Spec(ℤ)`: the substack of `𝓜̄ = Curves^{stable}`
(`AlgebraicGeometry.moduliStableCurves`) of stable families all of whose fibres have genus `g`, the
characterization of `𝓜̄_g` in part (2) of Stacks 0E78. -/
abbrev moduliStableCurvesOfGenus (g : ℕ) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesSubstack B hZ (IsStableCurveFamilyOfFibreGenus B hZ g)
    (isStableCurveFamilyOfFibreGenus_of_hom B hZ g)

/-- The inclusion `𝓜̄_g ⟶ Curves`. -/
abbrev moduliStableCurvesOfGenusInclusion (g : ℕ) :
    moduliStableCurvesOfGenus B hZ g ⟶ curvesFiberedCategory B hZ :=
  curvesSubstackInclusion B hZ (IsStableCurveFamilyOfFibreGenus B hZ g)
    (isStableCurveFamilyOfFibreGenus_of_hom B hZ g)

end AlgebraicGeometry.C1590Private

end
