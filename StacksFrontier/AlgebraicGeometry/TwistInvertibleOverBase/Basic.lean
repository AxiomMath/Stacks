module

public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Basic
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Polynomial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `𝒪(1)` on `ℙⁿ_S` is invertible, over an arbitrary base scheme

The hyperplane sheaf `𝒪(1)` of [Stacks, Tag 01MN] on relative projective space `ℙⁿ_S` is an
invertible `𝒪_{ℙⁿ_S}`-module, with no hypothesis on `S` or on `n`.

The integral model `AlgebraicGeometry.projectiveSpaceAtUniverse n` is `Proj` of a polynomial ring
graded by total degree, which is generated in degree one over its degree-zero part, so every
`𝒪(d)` on it is invertible by
`Stacks.AlgebraicGeometry.TwistFlatness.isInvertible_twistingSheaf_of_adjoin_degree_one`. The
relative sheaf `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf` is defined as the
pullback of the integral model's `𝒪(1)` along `ℙⁿ_S ⟶ ℙⁿ_ℤ`, and invertibility is preserved by
pullback ([Stacks, Tag 0B8L], `Stacks.InvertiblePullback.isInvertibleModule_pullback`). For
`S = Spec R` and the `Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistingSheaf` spelling
the same statement is
`Stacks.AlgebraicGeometry.TwistFlatness.isInvertible_projectiveTwistingSheaf`.

Since an epimorphism between invertible sheaves of modules on a scheme is an isomorphism
(`Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible`), it follows that for an
invertible `M` on `X` and any `i : X ⟶ ℙⁿ_S`, an epimorphism between `M` and `i^* 𝒪(1)`, in
either direction, gives an isomorphism `M ≅ i^* 𝒪(1)`: the shape of the conclusion of the twist
half of [Stacks, Tag 01NE] (`Stacks.AmpleImmersionReduction.TwistPullback`).

## Main results

* `Stacks.TwistInvertibleOverBase.isInvertible_twistingSheafAtUniverse` and
  `Stacks.TwistInvertibleOverBase.isInvertibleModule_twistingSheafAtUniverse`: `𝒪(1)` on the
  integral model `ℙⁿ_ℤ` is invertible.
* `Stacks.TwistInvertibleOverBase.isInvertibleModule_projectiveSpaceTwistingSheaf`: **`𝒪(1)` on
  `ℙⁿ_S` is invertible**, for every scheme `S`. An instance.
* `Stacks.TwistInvertibleOverBase.isInvertibleModule_pullback_projectiveSpaceTwistingSheaf`:
  `i^* 𝒪(1)` is invertible for every `i : X ⟶ ℙⁿ_S`.
* `Stacks.TwistInvertibleOverBase.nonempty_iso_of_epi_pullback_twistingSheaf` and
  `Stacks.TwistInvertibleOverBase.nonempty_iso_of_epi_to_pullback_twistingSheaf`: an epimorphism
  between an invertible `M` and `i^* 𝒪(1)`, in either direction, gives `M ≅ i^* 𝒪(1)`.

## Implementation notes

No Stacks tag attribute is attached: nothing below is one of the assertions of Tag 01NE, which is
a representability statement, and Tag 01MN is the definition of the twisting sheaf.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.TwistInvertibleOverBase

/-! ### The absolute case -/

/-- **`𝒪(1)` on the integral model `ℙⁿ_ℤ` is invertible**, in the sense of
`Stacks.SheafOfModules.IsInvertible`.

`AlgebraicGeometry.projectiveSpaceAtUniverse n` is `Proj` of the polynomial ring in `n + 1`
variables graded by total degree, which is generated in degree one over its degree-zero part. -/
@[ega "II 2.6.1" "special case", ega "II 3.2.5" "special case"]
theorem isInvertible_twistingSheafAtUniverse (n : ℕ) :
    Stacks.SheafOfModules.IsInvertible (projectiveSpaceAtUniverse.{u} n).presheaf
      (projectiveSpaceAtUniverse.{u} n).ringCatSheaf.2 (twistingSheafAtUniverse.{u} n) := by
  let : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  exact Stacks.AlgebraicGeometry.TwistFlatness.isInvertible_twistingSheaf_of_adjoin_degree_one _
    (Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule
      (Fin (n + 1)) (ULift.{u} ℤ)) 1

/-- **`𝒪(1)` on `ℙⁿ_ℤ` is invertible**, in the sense of `Stacks.Ample.IsInvertibleModule`. -/
instance isInvertibleModule_twistingSheafAtUniverse (n : ℕ) :
    Stacks.Ample.IsInvertibleModule (projectiveSpaceAtUniverse.{u} n)
      (twistingSheafAtUniverse.{u} n) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
    (isInvertible_twistingSheafAtUniverse n)

/-! ### The relative case -/

/-- **`𝒪(1)` on `ℙⁿ_S` is invertible**, for every scheme `S` and every `n`.

The relative hyperplane sheaf is by definition the pullback of the integral model's along
`ℙⁿ_S ⟶ ℙⁿ_ℤ`, so this is the absolute case together with [Stacks, Tag 0B8L]. -/
instance isInvertibleModule_projectiveSpaceTwistingSheaf (n : ℕ) (S : Scheme.{u}) :
    Stacks.Ample.IsInvertibleModule (projectiveSpaceOver n S)
      (projectiveSpaceTwistingSheaf n S) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback
    (projectiveSpaceOver.toIntegralAtUniverse n S) (twistingSheafAtUniverse.{u} n)

/-- **`i^* 𝒪(1)` is invertible, for every morphism `i : X ⟶ ℙⁿ_S`.** -/
instance isInvertibleModule_pullback_projectiveSpaceTwistingSheaf {X S : Scheme.{u}} (n : ℕ)
    (i : X ⟶ projectiveSpaceOver n S) :
    Stacks.Ample.IsInvertibleModule X
      ((Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback i (projectiveSpaceTwistingSheaf n S)

/-! ### The consequence for the twist half of Tag 01NE -/

section Reduction

variable {X S : Scheme.{u}} (n : ℕ) (i : X ⟶ projectiveSpaceOver n S) (M : X.Modules)
  [Stacks.Ample.IsInvertibleModule X M]

/-- **An epimorphism `M ⟶ i^* 𝒪(1)` out of an invertible module `M` gives an isomorphism
`M ≅ i^* 𝒪(1)`.** Both modules are invertible, and an epimorphism between invertible sheaves of
modules on a scheme is an isomorphism. -/
theorem nonempty_iso_of_epi_pullback_twistingSheaf
    (φ : M ⟶ (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) (hφ : Epi φ) :
    Nonempty (M ≅ (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :=
  let : IsIso φ := Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible φ hφ
  ⟨asIso φ⟩

/-- **An epimorphism `i^* 𝒪(1) ⟶ M` onto an invertible module `M` gives an isomorphism
`M ≅ i^* 𝒪(1)`.** -/
theorem nonempty_iso_of_epi_to_pullback_twistingSheaf
    (φ : (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S) ⟶ M) (hφ : Epi φ) :
    Nonempty (M ≅ (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :=
  let : IsIso φ := Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible φ hφ
  ⟨(asIso φ).symm⟩

end Reduction

end Stacks.TwistInvertibleOverBase

end
