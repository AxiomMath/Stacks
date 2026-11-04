module

public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionMap.FreeDifferentialLift
public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionMap.Curvature
public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionMap.DerivedMorphism

/-!
# The canonical obstruction map of a square-zero extension

Let `f : R' → R` be a surjection of commutative rings whose kernel `I` satisfies `I² = 0`, and
let `K` be a bounded-above object of `D(R)`. There is a canonical morphism
`ω : K ⟶ (K ⊗ᴸ_R I)[2]` in the derived category, obtained by lifting a bounded-above complex of
free `R`-modules representing `K` to free `R'`-modules, choosing differentials `d'` on the lift,
and reading off the squares `d' ∘ d'`, which land in `I ⊗ K` because they reduce to `d ∘ d = 0`.

The construction is the one in the source. A free lift is recorded by `FreeDifferentialLift`;
the square of its differential, factored through the kernel tensor complex, by
`LiftedDifferentialCurvature`; and `IsCanonicalObstructionMap` is the predicate asserting that a
morphism of `D(R)` is represented by such a square on *every* bounded-above free
representative, with *every* lift and *every* comparison datum. The content of the result is
that such a morphism exists and is unique.

## Main definitions

* `Deformation.Obstruction.squareZeroKernelModule`: the kernel of the surjection, as an
  `R`-module.
* `Deformation.Obstruction.squareZeroKernelObject`: that module in degree zero of `D(R)`.
* `Deformation.Obstruction.FreeDifferentialLift`: a lift of a complex of `R`-modules to free
  `R'`-modules with lifted differentials.
* `Deformation.Obstruction.kernelComplex`, `.kernelTensorInclusion`: the kernel in degree zero
  and the inclusion of a tensor summand of the tensor product with it.
* `Deformation.Obstruction.LiftedDifferentialCurvature`: the square of a lifted differential,
  factored through the kernel tensor complex, with the data computing its target in `D(R)`.
* `Deformation.Obstruction.LiftedDifferentialCurvature.tensorComparison`, `.toDerived`: the
  comparison of the kernel tensor complex with the derived tensor product, and the morphism of
  `D(R)` the square represents.
* `Deformation.Obstruction.IsCanonicalObstructionMap`: the lifted-differential characterization
  of the canonical obstruction morphism.
* `Deformation.Obstruction.canonicalObstructionMap`: the canonical obstruction morphism together
  with its specification.

## Main results

* `Deformation.Obstruction.existsUnique_isCanonicalObstructionMap`: the squares of any lifted
  differentials on any bounded-above free representative determine one and the same morphism of
  `D(R)`, and it is the unique morphism they determine.

## Implementation notes

The kernel module is represented by its conormal module `I / I²`. Under the square-zero
hypothesis this is canonically `I`; using the conormal model supplies its canonical module
structure over `R' / I ≃ R` without choosing lifts of scalars.

The kernel inclusion of `LiftedDifferentialCurvature` is normalized on pure tensors by
multiplication in the lifted module; an arbitrary embedding would not characterize the
obstruction. The comparison with the derived tensor product is the canonical K-flat comparison,
computed using a resolution of the kernel, which need not be flat.

`canonicalObstructionMap` is a specified morphism: its underlying arrow is `.val`, and
`.property` asserts existence of a free presentation, existence of curvature for every lift, and
agreement with every curvature presentation. In particular the specification includes
independence of both the free representative and the lifted differentials. The tensor product is
the canonical derived tensor bifunctor, whose comparison API uses a common universe for the
rings and modules. All auxiliary constructions are exposed so that their projections compute in
dependent types. The kernel is an implicit-reducible bundled module: its underlying conormal
type computes while instance search retains its transported `R`-module structure.

## References

* [Stacks Project, Tag 0DYR](https://stacks.math.columbia.edu/tag/0DYR)
-/
