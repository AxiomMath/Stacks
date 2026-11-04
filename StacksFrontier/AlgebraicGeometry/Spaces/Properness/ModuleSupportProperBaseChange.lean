module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange

/-!
# Base change of a module whose support is proper over the base

Let

```
X' ⟶ X
↓     ↓
Y' ⟶ Y
```

be a cartesian square of algebraic spaces over a scheme `S` whose right vertical morphism `f` is
locally of finite type, and let `F` be a finite type, quasi-coherent `𝒪_X`-module. If the
support of `F` is proper over `Y`, then the support of the pullback of `F` to `X'` is proper
over `Y'`.

## Main results

* `AlgebraicGeometry.Space.isProperOver_supportOfSheaf_modulePullback`: the support of the
  pullback of a finite type module whose support is proper over the base is proper over the new
  base.

## References

* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZE](https://stacks.math.columbia.edu/tag/0CZE)
* [Stacks Project, Tag 0CZF](https://stacks.math.columbia.edu/tag/0CZF)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- In a cartesian square of algebraic spaces over `S` whose right vertical morphism `f` is
locally of finite type, the support of the pullback along the upper horizontal morphism of a
finite type, quasi-coherent `𝒪_X`-module whose support is proper over `Y` is proper over `Y'`.
It takes the quasi-coherence of `F` (`_hqc`), its finite type (`hft`) and the properness of its
support over `Y` (`hproper`) as hypotheses. -/
@[stacks 0CZJ]
theorem isProperOver_supportOfSheaf_modulePullback {X' X Y' Y : AlgebraicSpaces B S hS}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (_hqc : SheafOfModules.IsQuasicoherentOnSite F)
    (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hproper : IsProperOver B S hS X.property Y.property f.hom hf
      (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))
      (letI := hft; isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.property F)) :
    IsProperOver B S hS X'.property Y'.property f'.hom
      ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq hf)
      (supportOfSheaf B S hS X'.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g').obj F)))
      (isClosed_supportOfSheaf_modulePullback B S hS g' F hft) :=
  isProperOver_of_subset B S hS X'.property Y'.property f'.hom
    ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq hf)
    (supportOfSheaf B S hS X'.1
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g').obj F)))
    (pointsMap B S hS X'.1 g'.hom ⁻¹'
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))
    (isClosed_supportOfSheaf_modulePullback B S hS g' F hft)
    (isClosed_preimage_pointsMap B S hS X'.property X.property g'.hom
      (let := hft; isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.property F))
    (supportOfSheaf_modulePullback_subset B S hS g' F hft)
    (isProperOver_preimage B S hS sq hf
      (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))
      (let := hft; isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.property F)
      hproper)

end AlgebraicGeometry.Space

end
