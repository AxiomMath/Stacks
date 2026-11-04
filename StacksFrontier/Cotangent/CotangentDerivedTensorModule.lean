module

public import StacksFrontier.Cotangent.DerivedBaseChange
public import StacksFrontier.Homology.Tor.DerivedTensorKFlatModel
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product of the cotangent complex with a module

Let `A → B` be a ring map and let `M` be a `B`-module. The first term of the Atiyah-class
triangle of [Stacks, Tag 09DD] is `L_{B/A} ⊗^𝐋_B M`. The source computes it as the *ordinary*
tensor product: "`L\pi_!(\Omega_{\mathcal O/\underline A} \otimes_{\mathcal O} \underline M) =
L_{B/A} \otimes_B M = L_{B/A} \otimes_B^{\mathbf L} M` by Lemma 92.4.2 and the flatness of the
terms of `L_{B/A}`". This file proves that last equality.

The terms of `L_{B/A}` are free `B`-modules
(`CommAlgCat.free_cotangentComplex_X`) and the complex vanishes in positive cohomological
degrees, so it is K-flat by [Stacks, Tag 064K]; tensoring with a K-flat complex computes the
derived tensor product against an arbitrary complex, in particular against `M` placed in degree
zero.

## Main results

* `CommAlgCat.kFlat_cotangentComplex`: the cotangent complex is K-flat.
* `CommAlgCat.nonempty_cotangentComplexDerivedTensorModule_iso`: **`L_{B/A} ⊗^𝐋_B M` is the
  ordinary total tensor product** of `L_{B/A}` with `M[0]`, as an object of `D(B)`.

## Implementation notes

The derived tensor product used is
`CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor` of [Stacks, Tag 0BYI], the only
one available on the unbounded derived category of modules; its characterizing property is a
comparison with ordinary total tensor products of K-flat representatives, and
`Stacks.DerivedTensor.nonempty_derivedTensor_iso_tensor_of_kFlat_right` relaxes that to a K-flat
right factor and an arbitrary left one. The cotangent complex is therefore placed on the right and
the symmetry `CochainComplex.DerivedTensor.derivedTensorProductCommIso` moves it back to the left,
which is the side the source displays it on.

The isomorphisms are produced as `Nonempty`, not as data: the comparison of the chosen K-flat
resolution with the complex is not canonical, exactly as in
`Stacks.DerivedTensor.nonempty_derivedTensor_iso_tensor_of_kFlat_right`.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- Every term of the cotangent complex is a flat `B`-module: in a nonpositive degree it is free
and in a positive degree it is zero, and in both cases it is projective. -/
instance flat_cotangentComplex_X (i : ℤ) :
    Module.Flat (B : Type u) ((cotangentComplex.{u, u} A B).X i) :=
  have : Projective ((cotangentComplex.{u, u} A B).X i) :=
    projective_cotangentComplex_X'.{u, u} A B i
  inferInstance

/-- **The cotangent complex is K-flat.** It is bounded above by cohomological degree zero and its
terms are flat, which is [Stacks, Tag 064K]. -/
theorem kFlat_cotangentComplex : (cotangentComplex.{u, u} A B).KFlat :=
  CochainComplex.KFlat.kFlat_of_flat (cotangentComplex.{u, u} A B) 0

variable (M : ModuleCat.{u} (B : Type u))

/-- `M` placed in cohomological degree zero. -/
abbrev moduleSingleComplex : CochainComplex (ModuleCat.{u} (B : Type u)) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} (B : Type u)) (ComplexShape.up ℤ) 0).obj M

/-- **`M ⊗^𝐋_B L_{B/A}` is the ordinary total tensor product `M[0] ⊗ L_{B/A}`**, the cotangent
complex being K-flat. -/
theorem nonempty_moduleDerivedTensorCotangentComplex_iso :
    Nonempty (((canonicalDerivedTensorProductFunctor (B : Type u)).obj
          (DerivedCategory.Q.obj (moduleSingleComplex A B M))).obj
        (DerivedCategory.Q.obj (cotangentComplex.{u, u} A B)) ≅
      DerivedCategory.Q.obj
        (tensorObj (moduleSingleComplex A B M) (cotangentComplex.{u, u} A B))) :=
  Stacks.DerivedTensor.nonempty_derivedTensor_iso_tensor_of_kFlat_right (B : Type u)
    (moduleSingleComplex A B M) (cotangentComplex.{u, u} A B) (kFlat_cotangentComplex A B)

/-- **`L_{B/A} ⊗^𝐋_B M` is an ordinary total tensor product.** This is the step the source calls
"the flatness of the terms of `L_{B/A}`": the first vertex of the Atiyah-class triangle of
[Stacks, Tag 09DD] is the complex `L_{B/A} ⊗_B M`, not merely its derived version. -/
theorem nonempty_cotangentComplexDerivedTensorModule_iso :
    Nonempty (((canonicalDerivedTensorProductFunctor (B : Type u)).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u} A B))).obj
        (DerivedCategory.Q.obj (moduleSingleComplex A B M)) ≅
      DerivedCategory.Q.obj
        (tensorObj (moduleSingleComplex A B M) (cotangentComplex.{u, u} A B))) :=
  (nonempty_moduleDerivedTensorCotangentComplex_iso A B M).map fun e =>
    derivedTensorProductCommIso _ _ ≪≫ e

end CommAlgCat

end
