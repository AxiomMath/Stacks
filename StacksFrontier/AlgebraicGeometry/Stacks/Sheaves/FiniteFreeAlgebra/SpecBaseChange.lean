module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.CarrierMapPushout
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Spectrum

/-!
# The spectrum of a free algebra structure is compatible with base change

Let `m` be a free `d`-dimensional algebra structure over a commutative ring `R` and let `S'` be
an `R`-algebra. Extending the scalars of `m` along `R → S'` and then taking the spectrum gives
the same scheme over `Spec S'` as taking the spectrum of `m` and then pulling back along
`Spec S' → Spec R`: the square

```
Spec (Carrier (map (algebraMap R S') m)) ---> Spec (Carrier m)
            |                                       |
            v                                       v
         Spec S'                       --->       Spec R
```

is cartesian. This is the affine form of the compatibility used in the proof of Stacks 05YQ to
recognise the cover attached to a family of free `d`-dimensional structures as the spectrum of
that family.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.Carrier.isPullback_specCover_baseChange`: the square above
  is cartesian.

## Implementation notes

The content is `AlgebraicGeometry.FiniteFreeAlgebra.isPullback_specCover_map`, which says the
same thing for an arbitrary ring homomorphism out of `R`; this module only transposes it and
specialises the homomorphism to the structure map of the algebra, which is the form the proof of
Stacks 05YQ applies it in.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra.Carrier

variable {R S' : Type u} [CommRing R] [CommRing S'] [Algebra R S'] {d : ℕ} [NeZero d]

/-- **The spectrum of a free `d`-dimensional structure is compatible with base change.** The
spectrum of the structure obtained by extending the scalars of `m` along `R → S'` is the fibre
product of the spectrum of `m` with `Spec S'` over `Spec R`. -/
theorem isPullback_specCover_baseChange (m : FiniteFreeAlgebra R d) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap S' (Carrier (map (algebraMap R S') m)))))
      (Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap R S') m)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S')))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Carrier m)))) :=
  (isPullback_specCover_map (algebraMap R S') m).flip

end AlgebraicGeometry.FiniteFreeAlgebra.Carrier

end
