module

public import StacksFrontier.AlgebraicGeometry.Conormal.FirstOrderThickening
public import StacksFrontier.RingTheory.Ideal.SquareZeroCotangent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sheaf of a first-order thickening on an affine open is its defining ideal

Let `i : Z ⟶ X` be a closed immersion whose defining ideal sheaf has vanishing square — a
first-order thickening — and let `U` be an affine open of `X`. The sections of `i_* 𝒞_{Z/X}` over
`U` are `I/I²` for the ideal `I` cutting out `Z ∩ U`, by [Stacks Project, Tag 01R3] part (2) in
the form `Stacks.Conormal.affineConormalIsoCotangent`; and `I² = 0`, so `I/I²` is `I`. This file
composes the two.

The point is that the right-hand side is the component of `AlgebraicGeometry.Scheme.Hom.ker` over
`U`, which is what the chart-wise torsor structure of the infinitesimal lifting arguments speaks
of, rather than the ideal of an affine model produced by an existential.

## Main results

* `Stacks.Conormal.nonempty_conormalSectionsEquivCotangentKer`: the sections of `i_* 𝒞_{Z/X}`
  over an affine open `U` are linearly equivalent to the cotangent module of
  `(Scheme.Hom.ker i).ideal U`, which by `Ideal.toCotangentEquivOfSqZero` is that ideal itself.
* `Stacks.Conormal.sqZero_ker_ideal`: the component of the defining ideal over an affine open has
  vanishing square, which is the input that collapse takes.

## Implementation notes

The affine model `(I, e, he)` comes from `Stacks.Conormal.exists_affineModel`, the identification
of `I` with the component of the kernel from `Stacks.Conormal.ker_appLE_eq_of_affineModel`, and
the square-zero collapse from `Ideal.toCotangentEquivOfSqZero`. This is the composition recipe
already run inside `Stacks.Conormal.ker_eq_bot_of_isZero_immersionConormalSheaf`, stated as a
result in its own right.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open scoped AlgebraicGeometry

universe u

namespace Stacks.Conormal

/-- **The conormal sheaf of a first-order thickening on an affine open is its defining ideal.**
For a closed immersion `i : Z ⟶ X` with `(Scheme.Hom.ker i)² = ⊥` and `U` an affine open of `X`,
the sections of `i_* 𝒞_{Z/X}` over `U` are the cotangent module of the component of the defining
ideal over `U`. With `Stacks.Conormal.sqZero_ker_ideal` and `Ideal.toCotangentEquivOfSqZero` that
cotangent module is the ideal itself.

The sections are `I/I²` by [Stacks Project, Tag 01R3] part (2),
`Stacks.Conormal.affineConormalIsoCotangent`, for the ideal `I` of an affine model of `i` over
`U`; that ideal is the component of `AlgebraicGeometry.Scheme.Hom.ker` by
`Stacks.Conormal.ker_appLE_eq_of_affineModel`, so its square vanishes and
`Ideal.toCotangentEquivOfSqZero` collapses `I/I²` to `I`. -/
@[ega "IV 16.1.2" "special case",
  sga "5 III 6.8" "N_{Y/X} = I/I²",
  sga "6 0 2.1" "partial",
  sga "6 VII 1.6" "partial",
  sga "7 VI 4.7" "special case"]
theorem nonempty_conormalSectionsEquivCotangentKer {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.affineOpens) :
    Nonempty (((modulePushforward i.toLRSHom.toShHom).obj
        (Stacks.Thickenings.immersionConormalSheaf i)).val.obj (op U.1)
      ≃ₗ[Γ(X, U.1)] (i.ker.ideal U).Cotangent) := by
  obtain ⟨I, e, he⟩ := exists_affineModel i U.1 U.2
  have hI : i.ker.ideal U = I := by
    rw [i.ker_apply U, ← Scheme.Hom.appLE_preimage_self i U.1]
    exact ker_appLE_eq_of_affineModel i U.1 U.2 I e he
  rw [hI]
  exact ⟨(affineConormalIsoCotangent i U.1 U.2 I e he).toLinearEquiv⟩

/-- **The defining ideal of a first-order thickening has vanishing square on every affine open.**
This is the hypothesis `Ideal.toCotangentEquivOfSqZero` takes, and with it
`Stacks.Conormal.nonempty_conormalSectionsEquivCotangentKer` says the sections of `i_* 𝒞_{Z/X}`
over an affine open are the defining ideal there. -/
theorem sqZero_ker_ideal {Z X : Scheme.{u}} (i : Z ⟶ X) (hsq : i.ker ^ 2 = ⊥)
    (U : X.affineOpens) : (i.ker.ideal U) ^ 2 = ⊥ := by
  have h' := congrArg (fun J : X.IdealSheafData => J.ideal U) hsq
  simpa using h'

end Stacks.Conormal

end
