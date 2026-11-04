module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationInjective.NoetherianReduction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationSurjective
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# The specialization map in residue characteristic zero

Let `f : X ⟶ S` be a smooth proper morphism with geometrically connected fibres and let
`sp : π₁(X_{s̄'}) → π₁(X_{s̄})` be a specialization map whose special point has residue
characteristic zero. This file assembles the two halves of [Stacks, Tag 0C0Q]:

* surjectivity is [Stacks, Tag 0C0P]
  (`AlgebraicGeometry.surjective_isSpecializationMap_of_isProper_of_flat`); the geometric
  reducedness of the special fibre which that result asks for is automatic here, because a smooth
  morphism has geometrically reduced fibres;
* injectivity is reduced by
  `AlgebraicGeometry.injective_isSpecializationMap_of_forall_isDiscreteValuationRing` to the single
  remaining statement, injectivity of the specialization map from the generic to the closed point
  over a strictly henselian discrete valuation ring with algebraically closed residue field of
  characteristic zero.

That statement is carried here as the hypothesis `H`.

## Main results

* `bijective_isSpecializationMap_of_ringChar_zero_of_forall_isDiscreteValuationRing`: given `H`,
  the specialization map `sp` is bijective.

## References

* [Stacks Project, Tag 0C0Q](https://stacks.math.columbia.edu/tag/0C0Q)
* [Stacks Project, Tag 0C0P](https://stacks.math.columbia.edu/tag/0C0P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The specialization map in residue characteristic zero is bijective, granted injectivity
over a strictly henselian discrete valuation ring (`H`).** Let `f : X ⟶ S` be a smooth proper
morphism with geometrically connected fibres, let `s' ⇝ s` be a specialization of points of `S`
realized by a specialization map `sp : π₁(X_{s̄'}) → π₁(X_{s̄})`, and suppose the characteristic
of `κ(s)` is zero. If the specialization map from the generic to the closed point of a smooth
proper morphism with geometrically connected fibres over a strictly henselian discrete valuation
ring with algebraically closed residue field of characteristic zero is always injective, then
`sp` is bijective.

Surjectivity is [Stacks, Tag 0C0P] and needs nothing of the characteristic: the geometric
reducedness of `X_s` which it requires holds because `f` is smooth. Injectivity is the three
reductions of
`AlgebraicGeometry.injective_isSpecializationMap_of_forall_isDiscreteValuationRing` applied to
`H`. -/
theorem bijective_isSpecializationMap_of_ringChar_zero_of_forall_isDiscreteValuationRing
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = 0)
    (H : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        [StrictlyHenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
        (Y : Scheme.{u}) (h : Y ⟶ Spec (.of R)) [IsProper h] [Smooth h]
        [GeometricallyConnected h] (η o : GeometricPoint (Spec (.of R)))
        (yη : GeometricPoint (fiberOverGeometricPoint h η))
        (yo : GeometricPoint (fiberOverGeometricPoint h o))
        (spR : EtaleFundamentalGroup (fiberOverGeometricPoint h η) yη →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint h o) yo),
        η.hom default = genericPoint (Spec (.of R)) →
          o.hom default = IsLocalRing.closedPoint R →
            ringChar ((Spec (.of R)).residueField (o.hom default)) = 0 →
              IsSpecializationMap h η o yη yo spR → Function.Injective spR) :
    Function.Bijective sp := by
  have hred : GeometricallyReduced
      (f.fiberToSpecResidueField (s.hom (IsLocalRing.closedPoint s.residueField))) :=
    (GeometricallyReduced.iff_geometricallyReduced_fiber f).mp
      (geometricallyReduced_of_smooth f) _
  exact ⟨injective_isSpecializationMap_of_forall_isDiscreteValuationRing f s' s x' x sp hsp
      hchar H,
    surjective_isSpecializationMap_of_isProper_of_flat f s' s hred x' x sp hsp⟩

end AlgebraicGeometry

end
