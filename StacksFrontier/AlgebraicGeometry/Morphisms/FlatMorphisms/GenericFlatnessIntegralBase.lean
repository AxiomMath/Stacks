module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness
public import StacksCore.Tactic.StacksAttribute

/-!
# Generic flatness over an integral base

A morphism of finite type to an integral scheme, together with a finite type quasi-coherent
module on its source, becomes flat and of finite presentation over a dense open part of the base.

An integral scheme is reduced, so this is the integral-base case of generic flatness over a
reduced base, whose conclusion is word for word the same.

## Main results

* `AlgebraicGeometry.exists_dense_open_flat_finitePresentation_of_isIntegral`: the dense open of
  an integral base over which the morphism and the module are both flat and of finite
  presentation.

## Implementation notes

The base change to an open `U` of the base is expressed, as over a reduced base, by the
restricted morphism from `f ⁻¹ᵁ U` to `U`, and the module on it by the restriction along the
canonical open immersion. All four conclusions hold on one and the same open and are therefore
stated together under its existential quantifier.

## References

* [Stacks Project, Tag 01ON](https://stacks.math.columbia.edu/tag/01ON)
* [Stacks Project, Tag 052A](https://stacks.math.columbia.edu/tag/052A)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 052A.** For a finite type morphism `f : X ⟶ S` to an integral scheme and a finite
type quasi-coherent module `F` on `X`, there is a dense open `U ⊆ S` such that `X_U → U` is flat
and of finite presentation and `F|_{X_U}` is flat over `U` and of finite presentation over
`𝒪_{X_U}`. An integral scheme is reduced, so this is a case of generic flatness over a reduced
base. -/
@[stacks 052A "Deduced from the reduced-base Proposition 052B, which the Stacks Project notes
supersedes this one, using that an integral scheme is reduced (01ON).",
  ega "IV 8.9.4" "more general",
  ega "IV 6.9.1" "more general"]
public theorem exists_dense_open_flat_finitePresentation_of_isIntegral
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegral S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ U : S.Opens,
      Dense (U : Set S) ∧
        Flat (f.resLE U (f ⁻¹ᵁ U) le_rfl) ∧
        AlgebraicGeometry.FinitePresentation (f.resLE U (f ⁻¹ᵁ U) le_rfl) ∧
        AlgebraicGeometry.IsFlatOver
          (f.resLE U (f ⁻¹ᵁ U) le_rfl).toLRSHom.toShHom
          (F.restrict (f ⁻¹ᵁ U).ι) ∧
        (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation :=
  exists_dense_open_flat_finitePresentation f F

end AlgebraicGeometry

end
