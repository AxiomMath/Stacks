module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapExistence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.StrictlyHenselianClosedGeometricFibre
public import StacksCore.Tactic.StacksAttribute

/-!
# The specialization map

Let `f : X ⟶ S` be a proper morphism with geometrically connected fibres, let `s' ⇝ s` be a
specialization of points of `S` and let `s̄'` and `s̄` be geometric points over `s'` and `s`. Then
there is a specialization map `sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})` (Stacks 0BUP).

The construction is `AlgebraicGeometry.exists_isSpecializationMap`: with `A` the strict
henselization of `𝒪_{S,s}` and a factorization of `s̄'` through `Spec A`, the map is the
composite `π₁(X_{s̄'}) → π₁(X_A) = π₁(X_{s̄})`. The equality is base change along the closed
geometric fibre `X_{s̄} ⟶ X_A`, which is an equivalence on finite étale covers by
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap`: Stacks 0A48
for `X_A` over the henselian local ring `A`, then Stacks 0BTW and 0A49 to pass from the
separably closed residue field `κ(s)^{sep}` of `A` to the algebraically closed `κ(s̄)`.

## Main results

* `AlgebraicGeometry.exists_continuousMonoidHom_isSpecializationMap` — Stacks 0BUP.

## References

* [Stacks Project, Tag 0BUP](https://stacks.math.columbia.edu/tag/0BUP)
* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0A49](https://stacks.math.columbia.edu/tag/0A49)
* [Stacks Project, Tag 0BTW](https://stacks.math.columbia.edu/tag/0BTW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Stacks Project, Tag 0BUP.** Let `f : X ⟶ S` be a proper morphism with geometrically
connected fibres, let `s' ⇝ s` be a specialization of points of `S`, let `s̄'` and `s̄` be
geometric points over `s'` and `s`, and choose geometric base points of the two geometric fibres
`X_{s̄'}` and `X_{s̄}`. Then there is a specialization map `π₁(X_{s̄'}) ⟶ π₁(X_{s̄})`, that is, a
continuous homomorphism satisfying `AlgebraicGeometry.IsSpecializationMap`: it is the composite
`π₁(X_{s̄'}) → π₁(X_A) ≅ π₁(X_{s̄})` for `A` the strict henselization of `𝒪_{S,s}` and a chosen
factorization of `s̄'` through `Spec A`.

The closed-fibre equivalence `π₁(X_A) ≅ π₁(X_{s̄})` is
`isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap` (Stacks 0A48, 0BTW, 0A49). -/
@[stacks 0BUP "the construction of the specialization map: for `f` proper with geometrically \
connected fibres, a specialization `s' ⇝ s` and geometric points `s̄'`, `s̄` over them, a \
continuous homomorphism `π₁(X_{s̄'}) → π₁(X_{s̄})` which is the composite \
`π₁(X_{s̄'}) → π₁(X_A) = π₁(X_{κ(s)^{sep}}) = π₁(X_{s̄})` of the source, recorded by \
`AlgebraicGeometry.IsSpecializationMap`. As in the source the map depends on the choice of \
the factorization `φ : s̄' → Spec A`, so this is stated as existence. The equality \
`π₁(X_A) = π₁(X_{s̄})` is proved from Stacks 0A48, 0BTW and 0A49 by \
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap`."]
theorem exists_continuousMonoidHom_isSpecializationMap (f : X ⟶ S) [IsProper f]
    [GeometricallyConnected f] (s' s : GeometricPoint S)
    (hspec : s'.hom (closedPoint s'.residueField) ⤳ s.hom (closedPoint s.residueField))
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s)) :
    ∃ sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
        EtaleFundamentalGroup (fiberOverGeometricPoint f s) x,
      IsSpecializationMap f s' s x' x sp :=
  exists_isSpecializationMap f s' s hspec x' x fun C _ _ _ r q hq hqclosed ↦
    isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap f s C r q hq hqclosed

end AlgebraicGeometry

end
