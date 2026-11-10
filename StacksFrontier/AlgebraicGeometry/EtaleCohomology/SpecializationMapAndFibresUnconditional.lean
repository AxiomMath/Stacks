module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleUnboundedDerivations
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationMapAndFibres

/-!
# The specialization map and the maps to the strict henselization, with nothing assumed

Let `f : X ⟶ S` be a morphism of schemes, let `K` be an object of the unbounded derived category
`D(X_étale)`, let `s` be a geometric point of `S` and let `t` be a geometric point of the strict
henselization `Spec(𝒪^{sh}_{S,s})`, with `c` the specialization morphism of strict henselizations
of Stacks 0GJ4. [Stacks, Tag 0GJ9] says that the square

```
(Rf_*K)_s -----> RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), K)
   | sp                        | (id_X × c)⁻¹
   v                           v
(Rf_*K)_{t ≫ p} -> RΓ(X ×_S Spec(𝒪^{sh}_{S,t ≫ p}), K)
```

commutes, its horizontal arrows being the maps of Stacks 0GIX; the source's third column, the
cohomology of `K` on the two geometric fibres, carries no vertical map, as the source says.

The unbounded `Rf_*` and the two unbounded `RΓ`s on the base changes to the strict henselizations
are the derived functors given by K-injective resolutions of unbounded complexes of abelian sheaves
on the small étale sites (Stacks 079P, 070K), so the square holds with nothing assumed about `f`,
`K`, `s` or `t`.

## Main results

* `derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization_unconditional`:
  the square of Stacks 0GJ9 commutes, for an arbitrary morphism of schemes, an arbitrary object of
  `D(X_étale)` and an arbitrary pair of geometric points.

## References

* [Stacks Project, Tag 0GJ9](https://stacks.math.columbia.edu/tag/0GJ9)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S` and `t` a geometric
point of the strict henselization of `S` at `s`. For `K` in the unbounded derived category
`D(X_étale)`, the maps of Stacks 0GIX from the stalks of `Rf_*K` at `s` and at the specialized
point `t ≫ p` to the derived global sections over the base changes of `X` to the two strict
henselizations form a commutative square with the specialization map `sp` on the left and pullback
along `id_X × c` on the right. -/
@[stacks 0GJ9 "the left square for an arbitrary morphism of schemes and an arbitrary object of \
the unbounded `D(X_etale)`: its verticals are `sp` and pullback along `id_X × c`, its horizontals \
the maps of Stacks 0GIX, and the unbounded `Rf_*` and `RΓ` are built from K-injective \
resolutions; the source states that no vertical map exists in general between the cohomologies \
of `K` on the two fibres, so the right-hand column carries no square"]
theorem
    derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization_unconditional
    (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
    (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s)) :
    derivedPushforwardStalkToStrictHenselizationSections B hS f s ≫
        strictHenselizationSectionsSpecializationAt B hS f s t =
      Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f)
          (smallEtaleDerivedSpecializationStalkAbAt B S hS s t) ≫
        derivedPushforwardStalkToStrictHenselizationSections B hS f
          (specializedGeometricPoint B S hS s t) :=
  derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization B hS f s t

end AlgebraicGeometry

end
