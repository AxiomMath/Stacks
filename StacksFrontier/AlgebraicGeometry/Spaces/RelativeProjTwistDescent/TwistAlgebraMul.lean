module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedC3TensorCompatAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistMul

/-!
# The multiplication of the twists of a relative Proj

In Situation 0849 the multiplication `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` of the twists of
`P = Proj_X(𝒜)` is descended along the presentation `P = P_U/P_R` from the multiplication of the
twists on the scheme of `P_U`
(`AlgebraicGeometry.Space.RelativeProjSituation.twistModuleMul`).  The descent uses the
compatibility of the tensor identification of Stacks 03DX (2) with inverse images along morphisms
of the site, which is `AlgebraicGeometry.Space.representedC3TensorCompat`; this file records the
multiplication, its characterization along the atlas, and its existence and uniqueness with that
compatibility supplied.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul`: **the multiplication
  `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` of the twists of the relative Proj** (Stacks 084D).

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.existsUnique_twistAlgebraMul`: the
  multiplication exists and is unique, characterized by its inverse image along the atlas.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul_spec`: the inverse image of the
  multiplication along the atlas is the multiplication of the twists of Stacks 01NR on the scheme
  of `P_U`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u m

namespace AlgebraicGeometry.Space

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

attribute [local instance] modulesMonoidalCategory

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The multiplication of the twists of the relative Proj exists and is unique** (Stacks
084D): there is exactly one morphism `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` whose inverse image along the
atlas of the presentation `P = P_U/P_R` is the multiplication of the twists of Stacks 01NR on the
scheme of `P_U`, through Stacks 03EL, the chart identifications of the twists and the tensor
identification of Stacks 03DX (2). -/
theorem existsUnique_twistAlgebraMul (i j : ℤ) :
    type_of% (s.existsUnique_twistModuleMul Px
      (fun g M N => representedC3TensorCompat s.site s.base s.containsBase g M N) i j) :=
  s.existsUnique_twistModuleMul Px
    (fun g M N => representedC3TensorCompat s.site s.base s.containsBase g M N) i j

/-- **The multiplication of the twists of the relative Proj** (Stacks 084D):
`𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)`, the descent along the presentation `P = P_U/P_R` of the
multiplication of the twists of Stacks 01NR on the scheme of `P_U`. -/
def twistAlgebraMul (i j : ℤ) :
    (s.twistModule Px i).obj ⊗ (s.twistModule Px j).obj ⟶ (s.twistModule Px (i + j)).obj :=
  s.twistModuleMul Px (fun g M N => representedC3TensorCompat s.site s.base s.containsBase g M N)
    i j

/-- **The inverse image along the atlas of the multiplication of the twists is the
multiplication of the twists of Stacks 01NR on the scheme of `P_U`**, through Stacks 03EL, the
chart identifications of the twists and the tensor identification of Stacks 03DX (2). -/
theorem twistAlgebraMul_spec (i j : ℤ) :
    type_of% (s.twistModuleMul_spec Px
      (fun g M N => representedC3TensorCompat s.site s.base s.containsBase g M N) i j) :=
  s.twistModuleMul_spec Px
    (fun g M N => representedC3TensorCompat s.site s.base s.containsBase g M N) i j

end RelativeProjSituation

end AlgebraicGeometry.Space

end
