module

public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CoherentFiniteness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Additivity of the degree on a proper curve over a field

For a short exact sequence `0 ⟶ ℰ₁ ⟶ ℰ₂ ⟶ ℰ₃ ⟶ 0` of finite locally free `𝒪_X`-modules of
finite constant ranks `r₁`, `r₂`, `r₃` on a scheme `X` proper over a field `k` and of dimension
at most one, `deg(ℰ₂) = deg(ℰ₁) + deg(ℰ₃)`.

## Main results

* `AlgebraicGeometry.cohomologyFiniteDimensionalOverFieldOn`: every coherent module on a scheme
  proper over a field has finite-dimensional cohomology in every degree.
* `AlgebraicGeometry.curveDegree_add_of_shortExact_of_isProper`: the additivity of the degree
  along a short exact sequence of finite locally free modules of finite constant rank on a
  scheme proper over a field and of dimension at most one.

## References

* [Stacks Project, Tag 0AYS](https://stacks.math.columbia.edu/tag/0AYS)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- Every coherent `𝒪_X`-module on a scheme `X` proper over a field `k` along `f` has
finite-dimensional cohomology in every degree ([Stacks, Tag 02O6]), in the form
`AlgebraicGeometry.CohomologyFiniteDimensionalOverFieldOn k f`. -/
@[sga "4½ Fonctions_L 3.7" "more general"]
public theorem cohomologyFiniteDimensionalOverFieldOn (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] : CohomologyFiniteDimensionalOverFieldOn k f :=
  forall_finiteDimensional_cohomologyOverField_of_isProper k f

/-- Let `k` be a field and let `X` be a scheme proper over `k` of dimension at most one. For a
short exact sequence `0 ⟶ ℰ₁ ⟶ ℰ₂ ⟶ ℰ₃ ⟶ 0` of locally free `𝒪_X`-modules of finite constant
ranks `r₁`, `r₂`, `r₃`, `deg(ℰ₂) = deg(ℰ₁) + deg(ℰ₃)`. -/
@[stacks 0AYS "deg(ℰ₂) = deg(ℰ₁) + deg(ℰ₃) for a short exact sequence of locally free modules \
of finite constant rank on a proper scheme of dimension at most one over a field"]
public theorem curveDegree_add_of_shortExact_of_isProper (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r₂]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₃] :
    curveDegree k f hdim S.X₂ r₂ =
      curveDegree k f hdim S.X₁ r₁ + curveDegree k f hdim S.X₃ r₃ :=
  curveDegree_add_of_shortExact_of_cohomologyFiniteDimensional k f
    (cohomologyFiniteDimensionalOverFieldOn k f) hdim S hS r₁ r₂ r₃

end AlgebraicGeometry

end
