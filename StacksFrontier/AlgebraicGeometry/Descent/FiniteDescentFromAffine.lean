module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent of integral and finite morphisms reduces to the affine case

For the integral and for the finite morphisms of schemes, effective descent along the surjective
étale morphisms of the big fppf site of `S`
(`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`) follows from effective
descent for the affine morphisms, since both properties are contained in
`AlgebraicGeometry.IsAffineHom` and both satisfy fppf descent.

## Main results

* `AlgebraicGeometry.isIntegralHom_descendsAlong_fppf` and
  `AlgebraicGeometry.isFinite_descendsAlong_fppf`: integral and finite morphisms of schemes
  satisfy fppf descent.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isIntegralHom_of_isAffineHom`
  and `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isFinite_of_isAffineHom`:
  effective descent along the surjective étale morphisms of the big fppf site of `S` for the
  affine morphisms implies it for the integral, respectively the finite, morphisms.

## References

* [Stacks Project, Tag 02L9](https://stacks.math.columbia.edu/tag/02L9)
* [Stacks Project, Tag 02LA](https://stacks.math.columbia.edu/tag/02LA)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty

universe u

namespace AlgebraicGeometry

/-! ### fppf descent of integral and of finite morphisms -/

/-- A property of morphisms of schemes which is Zariski-local at the target and descends along the
surjective flat quasi-compact morphisms descends along the surjective flat morphisms locally of
finite presentation. -/
alias descendsAlong_fppf_of := Space.descendsAlong_fppf

/-- Integral morphisms of schemes descend along the surjective flat quasi-compact morphisms. -/
private theorem isIntegralHom_descendsAlong_qc :
    MorphismProperty.DescendsAlong (@IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have haff : MorphismProperty.DescendsAlong (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    Stacks.Descent.isAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact
  rw [IsIntegralHom.eq_universallyClosed_inf_isAffineHom]
  exact .inf

/-- Integral morphisms of schemes satisfy fppf descent: if the base change of a morphism along a
surjective flat morphism locally of finite presentation is integral, then so is the morphism. -/
@[ega "IV 2.7.1" "(xvii), special case", sga "1 VIII 5.7" "special case"]
theorem isIntegralHom_descendsAlong_fppf :
    MorphismProperty.DescendsAlong (@IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  @descendsAlong_fppf_of _ isIntegralHom_descendsAlong_qc.{u}
    Space.isZariskiLocalAtTarget_isIntegralHom.{u}

/-- Finite morphisms of schemes satisfy fppf descent: if the base change of a morphism along a
surjective flat morphism locally of finite presentation is finite, then so is the morphism. -/
theorem isFinite_descendsAlong_fppf :
    MorphismProperty.DescendsAlong (@IsFinite.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  have hint := isIntegralHom_descendsAlong_qc.{u}
  have hqc : MorphismProperty.DescendsAlong (@IsFinite.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
    rw [IsFinite.eq_inf]
    exact .inf
  exact @descendsAlong_fppf_of _ hqc Space.isZariskiLocalAtTarget_isFinite.{u}

/-! ### The two reductions to the affine case -/

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An integral morphism of schemes is affine. -/
@[ega "II 6.1.2"]
theorem isIntegralHom_le_isAffineHom :
    (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u}) ≤
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
  fun _ _ _ _ ↦ inferInstance

/-- A finite morphism of schemes is affine. -/
theorem isFinite_le_isAffineHom :
    (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) ≤
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
  fun _ _ _ _ ↦ inferInstance

/-- If affine morphisms of schemes descend effectively along the surjective étale morphisms of the
big fppf site of `S`, then so do integral morphisms. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isIntegralHom_of_isAffineHom
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u}) :=
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.DescendsAlong
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    isIntegralHom_descendsAlong_fppf.{u}
  isEffectiveDescentAlongSurjectiveEtale_of_le hdesc isIntegralHom_le_isAffineHom.{u}

/-- If affine morphisms of schemes descend effectively along the surjective étale morphisms of the
big fppf site of `S`, then so do finite morphisms. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isFinite_of_isAffineHom
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.DescendsAlong
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    isFinite_descendsAlong_fppf.{u}
  isEffectiveDescentAlongSurjectiveEtale_of_le hdesc isFinite_le_isAffineHom.{u}

end Space

end AlgebraicGeometry

end
