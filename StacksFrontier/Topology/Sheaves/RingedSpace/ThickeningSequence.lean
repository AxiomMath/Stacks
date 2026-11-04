module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening
import StacksCore.Tactic.StacksAttribute

/-!
# Sequences of first order thickenings of a ringed space (Stacks 08LE)

Fix a ringed space `(X, 𝒪_X)`. A sequence of morphisms of first order thickenings of `X`

    (X₁, 𝒪_{X₁}) ⟶ (X₂, 𝒪_{X₂}) ⟶ (X₃, 𝒪_{X₃})

induces maps `ℐ₃ ⟶ ℐ₂ ⟶ ℐ₁` between the square-zero ideal sheaves, read as `𝒪_X`-modules.
The sequence is a *complex* when that composite vanishes, and *short exact* when

    0 ⟶ ℐ₃ ⟶ ℐ₂ ⟶ ℐ₁ ⟶ 0

is a short exact sequence of `𝒪_X`-modules.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.FirstOrderThickeningSequence`: the three
  thickenings, the two morphisms between them and the two induced maps on ideal modules.
* `FirstOrderThickeningSequence.square₁₂` and `.square₂₃`: each morphism of the sequence read
  as a morphism of thickenings in the sense of **Stacks 08KZ**, with `X ⟶ X` the identity.
* `FirstOrderThickeningSequence.HasInducedIdealMaps`: the two chosen maps on ideal modules are
  the ones induced by those squares.
* `AlgebraicGeometry.RingedSpaceThickening.IsComplex`: **Stacks 08LE**, the complex condition.
* `AlgebraicGeometry.RingedSpaceThickening.IsShortExact`: **Stacks 08LE**, short exactness.

## Implementation notes

The homeomorphic underlying spaces of a thickening are not identified; instead each ideal
`ℐ_k = ker(𝒪_{X_k} ⟶ i_{k*} 𝒪_X)` is read as an `𝒪_X`-module by pulling it back along `i_k`.
The induced maps are therefore constrained rather than constructed: `HasInducedIdealMaps`
says that, after pushforward along `i₁` resp. `i₂`, the chosen map agrees with the canonical
first-order factorization `MorphismOfThickenings.firstOrderIdealMap` of Tag 08KZ followed by
the unit of `i^* ⊣ i_*`. Comparing the two sides needs the pullback along the identity that
`firstOrderIdealMap` of the square produces, which is what `idealComparison₂` and
`idealComparison₃` supply.

`IsComplex` and `IsShortExact` are abbreviations so that consumers can use the
`ShortComplex.ShortExact` API and the two component equations directly.

## References

* [Stacks Project, Tag 08LE](https://stacks.math.columbia.edu/tag/08LE)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- Three first order thickenings of one ringed space `X`, with morphisms between them under
`X` and their induced maps on the square-zero ideal modules, read on `X`. -/
structure FirstOrderThickeningSequence where
  /-- The ringed space being thickened. -/
  X : RingedSpace.{u, u}
  /-- The first thickening. -/
  X₁ : RingedSpace.{u, u}
  /-- The second thickening. -/
  X₂ : RingedSpace.{u, u}
  /-- The third thickening. -/
  X₃ : RingedSpace.{u, u}
  /-- The inclusion of `X` into the first thickening. -/
  i₁ : X ⟶ X₁
  /-- The inclusion of `X` into the second thickening. -/
  i₂ : X ⟶ X₂
  /-- The inclusion of `X` into the third thickening. -/
  i₃ : X ⟶ X₃
  /-- The first inclusion is a first order thickening. -/
  firstOrder₁ : IsFirstOrderThickening i₁
  /-- The second inclusion is a first order thickening. -/
  firstOrder₂ : IsFirstOrderThickening i₂
  /-- The third inclusion is a first order thickening. -/
  firstOrder₃ : IsFirstOrderThickening i₃
  /-- The morphism from the first thickening to the second. -/
  f₁₂ : X₁ ⟶ X₂
  /-- The morphism from the second thickening to the third. -/
  f₂₃ : X₂ ⟶ X₃
  /-- The first morphism is a morphism under `X`. -/
  comm₁₂ : i₁ ≫ f₁₂ = i₂
  /-- The second morphism is a morphism under `X`. -/
  comm₂₃ : i₂ ≫ f₂₃ = i₃
  /-- The induced map `ℐ₂ ⟶ ℐ₁` of `𝒪_X`-modules. -/
  idealMap₂₁ :
    (modulePullback i₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf i₂) ⟶
      (modulePullback i₁).obj (AlgebraicGeometry.SheafOfModules.idealSheaf i₁)
  /-- The induced map `ℐ₃ ⟶ ℐ₂` of `𝒪_X`-modules. -/
  idealMap₃₂ :
    (modulePullback i₃).obj (AlgebraicGeometry.SheafOfModules.idealSheaf i₃) ⟶
      (modulePullback i₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf i₂)

namespace FirstOrderThickeningSequence

variable (S : FirstOrderThickeningSequence.{u})

/-- The first morphism of the sequence, read as a morphism of thickenings over the identity
of `X`. -/
def square₁₂ : MorphismOfThickenings.{u} where
  X := S.X
  X' := S.X₁
  S := S.X
  S' := S.X₂
  i := S.i₁
  t := S.i₂
  f := 𝟙 S.X
  f' := S.f₁₂
  i_isThickening := S.firstOrder₁.1
  t_isThickening := S.firstOrder₂.1
  comm := by simpa using S.comm₁₂

/-- The second morphism of the sequence, read as a morphism of thickenings over the identity
of `X`. -/
def square₂₃ : MorphismOfThickenings.{u} where
  X := S.X
  X' := S.X₂
  S := S.X
  S' := S.X₃
  i := S.i₂
  t := S.i₃
  f := 𝟙 S.X
  f' := S.f₂₃
  i_isThickening := S.firstOrder₂.1
  t_isThickening := S.firstOrder₃.1
  comm := by simpa using S.comm₂₃

/-- The comparison between `ℐ₂` pulled back to `X` and the same module pulled back once more
along the identity of `X`, which is the shape in which `square₁₂` produces it. As in
`MorphismOfThickenings.reducedPullbackComparison`, the comparison isomorphism is spelled with
`modulePullbackCompUniq` rather than the `rfl`-equal `pullbackComp`, so that goals mentioning both
stay type-correct at `implicit` transparency. -/
noncomputable def idealComparison₂ :
    (modulePullback S.i₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₂) ≅
      (modulePullback (𝟙 S.X)).obj
        ((modulePullback S.i₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₂)) :=
  eqToIso (congrArg (fun f => (modulePullback f).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₂)) (Category.id_comp S.i₂).symm) ≪≫
    (modulePullbackCompUniq (𝟙 S.X) S.i₂).app (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₂)

/-- The corresponding comparison for `ℐ₃`. -/
noncomputable def idealComparison₃ :
    (modulePullback S.i₃).obj (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₃) ≅
      (modulePullback (𝟙 S.X)).obj
        ((modulePullback S.i₃).obj (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₃)) :=
  eqToIso (congrArg (fun f => (modulePullback f).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₃)) (Category.id_comp S.i₃).symm) ≪≫
    (modulePullbackCompUniq (𝟙 S.X) S.i₃).app (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₃)

/-- The chosen maps on ideal modules are the maps induced by the two morphisms of first order
thickenings, in the sense of the canonical factorization of **Stacks 08KZ**. -/
noncomputable def HasInducedIdealMaps : Prop :=
  ((modulePushforward S.i₁).map S.idealComparison₂.hom ≫
      (S.square₁₂.firstOrderIdealMap S.firstOrder₁ S.firstOrder₂).1 ≫
      (modulePullbackPushforwardAdjunction S.i₁).unit.app
        (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₁) =
      (modulePushforward S.i₁).map S.idealMap₂₁) ∧
    ((modulePushforward S.i₂).map S.idealComparison₃.hom ≫
      (S.square₂₃.firstOrderIdealMap S.firstOrder₂ S.firstOrder₃).1 ≫
      (modulePullbackPushforwardAdjunction S.i₂).unit.app
        (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₂) =
      (modulePushforward S.i₂).map S.idealMap₃₂)

end FirstOrderThickeningSequence

/-- **Stacks Project, Tag 08LE.** A sequence of first order thickenings of `X` is a *complex*
when its induced maps on ideal modules compose to zero. -/
@[stacks 08LE "complex of first order thickenings"]
noncomputable abbrev IsComplex (S : FirstOrderThickeningSequence.{u}) : Prop :=
  S.HasInducedIdealMaps ∧ S.idealMap₃₂ ≫ S.idealMap₂₁ = 0

/-- **Stacks Project, Tag 08LE.** A sequence of first order thickenings of `X` is a *short
exact sequence* when `0 ⟶ ℐ₃ ⟶ ℐ₂ ⟶ ℐ₁ ⟶ 0` is short exact as a sequence of
`𝒪_X`-modules. -/
@[stacks 08LE "short exact sequence of first order thickenings"]
noncomputable abbrev IsShortExact (S : FirstOrderThickeningSequence.{u}) : Prop :=
  S.HasInducedIdealMaps ∧
    ∃ h : S.idealMap₃₂ ≫ S.idealMap₂₁ = 0,
      (ShortComplex.mk S.idealMap₃₂ S.idealMap₂₁ h).ShortExact

end AlgebraicGeometry.RingedSpaceThickening

end
