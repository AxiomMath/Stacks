module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.CospecializationSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.ProperLocallyAcyclicSpecialization

/-!
# The cospecialization map is a section of the specialization map (Stacks 0GJV)

Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S`, `t` a geometric point of
`Spec 𝒪^{sh}_{S,s}`, and `K` an object of `D(X_étale)` which is bounded below and relative to
which `f` is locally acyclic. By Stacks 0GJU
(`AlgebraicGeometry.isIso_pullback_cospecializationUnit_of_isGE`) the inverse image
`i⁻¹β_{K,s,t}` on the closed geometric fibre of the comparison `β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})`
is an isomorphism, so the cospecialization map `cosp : RΓ(X_t, K) ⟶ RΓ(X_s, K)` of Section 0GJT
is defined (`AlgebraicGeometry.cospecializationMapGeometricFibre`). This file states Stacks 0GJV:
if moreover `f` is quasi-compact and quasi-separated, the square

```
(Rf_*K)_s ----------> RΓ(X_s, K)
   | sp                    ^ cosp
   v                       |
(Rf_*K)_t ----------> RΓ(X_t, K)
```

commutes, the horizontal arrows being the base change maps of Stacks 0GIX.

## Main results

* `AlgebraicGeometry.specializationStalk_comp_baseChange_comp_cospecializationMap_of_isGE` —
  **[Stacks, Tag 0GJV]**.

## Implementation notes

The square is proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.CospecializationSquare` for every
proof that `i⁻¹β_{K,s,t}` is invertible
(`AlgebraicGeometry.specializationStalk_comp_baseChange_comp_cospecializationMapGeometricFibre`);
that argument routes the specialization map through Stacks 0GJ9 and so does not use the
quasi-compactness and quasi-separatedness of `f`, which the source uses only to identify
`(Rf_*K)_s` with `RΓ(X ×_S Spec 𝒪^{sh}_{S,s}, K)` by Theorem 03Q9. The statement here carries the
source's hypotheses exactly, and the invertibility of `i⁻¹β_{K,s,t}` is supplied by Stacks 0GJU.

The unbounded derived categories of the small étale sites are those of the model
`HasDerivedCategory.standard`, forced by the base declaration
`Stacks.EtaleCohomology.smallEtaleDerivedCategory`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedEtale.lean:184`, under the local instance
of line 177).

## References

* [Stacks Project, Tag 0GJT](https://stacks.math.columbia.edu/tag/0GJT)
* [Stacks Project, Tag 0GJU](https://stacks.math.columbia.edu/tag/0GJU)
* [Stacks Project, Tag 0GJV](https://stacks.math.columbia.edu/tag/0GJV)
* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

-- `Stacks.EtaleCohomology.smallEtaleDerivedCategory` (DerivedEtale.lean:184) is the standard
-- model.
attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-- **[Stacks, Tag 0GJV].** Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of
schemes, `s` a geometric point of `S`, `t` a geometric point of `Spec 𝒪^{sh}_{S,s}`, and `K` an
object of `D(X_étale)` which is bounded below and relative to which `f` is locally acyclic, so
that the cospecialization map `cosp : RΓ(X_t, K) ⟶ RΓ(X_s, K)` is defined (Stacks 0GJU,
`AlgebraicGeometry.isIso_pullback_cospecializationUnit_of_isGE`). Then the square

```
(Rf_*K)_s ----------> RΓ(X_s, K)
   | sp                    ^ cosp
   v                       |
(Rf_*K)_t ----------> RΓ(X_t, K)
```

commutes: `sp` followed by the base change map of Stacks 0GIX at `t` and by `cosp` is the base
change map of Stacks 0GIX at `s`. Here `X_s` and `X_t` are the geometric fibres of `f` at `s` and
at the image of `t` in `S`, and the stalk of `Rf_*K` at `t` is taken at that image. -/
@[stacks 0GJV]
theorem specializationStalk_comp_baseChange_comp_cospecializationMap_of_isGE
    [QuasiCompact f] [QuasiSeparated f] (K : smallEtaleDerivedCategory X) (m : ℤ)
    (hK : K.IsGE m) (hla : IsLocallyAcyclicRelative B hX hS f K) :
    haveI := isIso_pullback_cospecializationUnit_of_isGE B hX hS f s t K m hK hla
    (smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
          ((smallEtaleDerivedPushforwardAb f).obj K) ≫
        (derivedPushforwardStalkToStrictHenselizationSections B hS f
          (t.map (strictHenselizationToBase B S hS s))).app K ≫
        (strictHenselizationSectionsToFibreSections B hS f
          (t.map (strictHenselizationToBase B S hS s))).app K ≫
        cospecializationMapGeometricFibre B hS f s t K =
      (derivedPushforwardStalkToStrictHenselizationSections B hS f s).app K ≫
        (strictHenselizationSectionsToFibreSections B hS f s).app K :=
  have := isIso_pullback_cospecializationUnit_of_isGE B hX hS f s t K m hK hla
  specializationStalk_comp_baseChange_comp_cospecializationMapGeometricFibre B hS f s t K

end AlgebraicGeometry

end
