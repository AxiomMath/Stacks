module

public import Mathlib.RingTheory.Kaehler.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sequence of a surjection of commutative rings

Let `R` be a commutative ring, let `A` and `B` be commutative `R`-algebras and let
`φ = algebraMap A B` be a surjective `R`-algebra map, with `I = Ker φ`. The sequence of
`B`-modules

```
          g                        h
I/I²  ─────────►  B ⊗[A] Ω[A⁄R]  ─────────►  Ω[B⁄R]  ─────────►  0
```

is exact, where `g` sends the class of `f ∈ I` to `1 ⊗ d f` and `h` is the base change of the
functorial map on relative differentials.

## Main results

* `Stacks.KaehlerDifferential.Conormal.conormalSequence_exact`: the sequence is exact at
  `B ⊗[A] Ω[A⁄R]`.
* `Stacks.KaehlerDifferential.Conormal.conormalSequence_surjective`: the sequence is exact at
  `Ω[B⁄R]`, that is the right-hand map is surjective.
* `Stacks.KaehlerDifferential.Conormal.kerCotangentToTensor_class`: the left-hand map carries
  the class of a section `f` of `I` to `1 ⊗ d f`.

## Implementation notes

The source writes the middle term as `Ω[A⁄R] ⊗_A B` and the left-hand map as `f̄ ↦ d f ⊗ 1`;
Mathlib writes the tensor product with the scalars on the left, so the same element is
`1 ⊗ₜ d f`.

## References

* [Stacks Project, Tag 00RU](https://stacks.math.columbia.edu/tag/00RU)
-/

@[expose] public section

open KaehlerDifferential TensorProduct

namespace Stacks.KaehlerDifferential.Conormal

/-- **Exactness at `B ⊗[A] Ω[A⁄R]`.** The kernel of the base-change map `mapBaseChange` is the
range of the conormal map `kerCotangentToTensor`. -/
@[stacks 00RU "exactness at the middle",
  sga "3 III 4.25" "exactness at middle",
  ega "0 20.5.12" "(i)",
  ega "0 20.6.23" "partial",
  ega "0 20.6.9" "partial",
  ega "0 22.4.4.2" "partial"]
theorem conormalSequence_exact (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hφ : Function.Surjective (algebraMap A B)) :
    Function.Exact (kerCotangentToTensor R A B) (mapBaseChange R A B) :=
  exact_kerCotangentToTensor_mapBaseChange R A B hφ

/-- **Exactness at `Ω[B⁄R]`.** The base-change map `mapBaseChange` is surjective. -/
@[stacks 00RU "surjectivity on the right",
  sga "3 III 4.25" "surjectivity in (+)",
  ega "0 20.5.12" "(i)",
  ega "0 20.6.23" "partial",
  ega "0 20.6.9" "partial",
  ega "0 22.4.4.2" "partial"]
theorem conormalSequence_surjective (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hφ : Function.Surjective (algebraMap A B)) :
    Function.Surjective (mapBaseChange R A B) :=
  -- The bare name `mapBaseChange_surjective` is ambiguous under `import Stacks` together with
  -- `import StacksDraft`, so it is spelled out in full.
  _root_.KaehlerDifferential.mapBaseChange_surjective R A B hφ

/-- **The left-hand map of the conormal sequence on classes of sections of the ideal.** The
class of `f ∈ I` in `I/I²` maps to `1 ⊗ₜ d f`, which is the source's `d f ⊗ 1`. -/
@[stacks 00RU "the formula for the left-hand map",
  ega "0 20.5.11" "formula on classes",
  ega "0 22.6.4" "partial",
  sga "1 II 5.9" "partial",
  sga "3 III 4.8" "special case",
  sga "6 VIII 2.1" "special case"]
theorem kerCotangentToTensor_class (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (x : RingHom.ker (algebraMap A B)) :
    kerCotangentToTensor R A B ((RingHom.ker (algebraMap A B)).toCotangent x)
      = 1 ⊗ₜ[A] (D R A) x :=
  kerCotangentToTensor_toCotangent R A B x

end Stacks.KaehlerDifferential.Conormal

end
