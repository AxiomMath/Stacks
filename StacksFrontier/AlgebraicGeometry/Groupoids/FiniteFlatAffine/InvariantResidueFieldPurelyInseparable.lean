module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.IntegralInvariants
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldOverLocalRing
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian

/-!
# Pure inseparability of the residue field extension over a strictly henselian invariant ring

Let `G` be a groupoid scheme with affine object and arrow schemes and finite locally free source
and target maps, write `C` for its ring of invariant functions and `q : U ⟶ M = Spec C` for the
quotient morphism, and assume `C` is **strictly henselian**. Then for every point `u` of `U`
lying over the closed point `p` of `M`, the residue field extension `κ(u)/κ(p)` is **purely
inseparable**.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isPurelyInseparable_residueField_objectsToInvariantSpectrum`:
  **`κ(u)/κ(p)` is purely inseparable** at a point `u` over the closed point of `Spec C`.

## References

* [Stacks Project, Tag 03BJ](https://stacks.math.columbia.edu/tag/03BJ)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- **The residue field extension `κ(u)/κ(p)` of the quotient morphism `U ⟶ Spec C` is purely
inseparable at a point `u` lying over the closed point `p` of `Spec C`**, when the invariant ring
`C` is strictly henselian. -/
theorem isPurelyInseparable_residueField_objectsToInvariantSpectrum {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [StrictlyHenselianLocalRing (invariantRing G)] (u : G.objects.left)
    (hu : (objectsToInvariantSpectrum G).base u =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G))))
    [Algebra ((Spec (.of (invariantRing G))).residueField
        ((objectsToInvariantSpectrum G).base u)) (G.objects.left.residueField u)]
    (hcompat : algebraMap ((Spec (.of (invariantRing G))).residueField
          ((objectsToInvariantSpectrum G).base u)) (G.objects.left.residueField u) =
      ((objectsToInvariantSpectrum G).residueFieldMap u).hom) :
    IsPurelyInseparable ((Spec (.of (invariantRing G))).residueField
      ((objectsToInvariantSpectrum G).base u)) (G.objects.left.residueField u) := by
  have hp : ((objectsToInvariantSpectrum G).base u).asIdeal =
      IsLocalRing.maximalIdeal (invariantRing G) := by rw [hu]; rfl
  have : IsSepClosed ((Spec (.of (invariantRing G))).residueField
      ((objectsToInvariantSpectrum G).base u)) :=
    isSepClosed_residueField_spec_of_asIdeal_eq_maximalIdeal _ _ hp
  have hprime : (G.objects.left.toSpecΓ.base u).asIdeal.IsPrime :=
    (G.objects.left.toSpecΓ.base u).isPrime
  have hmax : (G.objects.left.toSpecΓ.base u).asIdeal.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (CommRingCat.ofHom (invariantRing G).subtype).hom (isIntegral_invariantRing G) _ ?_
    change ((objectsToInvariantSpectrum G).base u).asIdeal.IsMaximal
    exact hp ▸ IsLocalRing.maximalIdeal.isMaximal _
  refine isPurelyInseparable_residueField_of_isIntegral (objectsToInvariantSpectrum G) u
    ?_ hcompat
  change RingHom.IsIntegral (Spec.preimage (G.objects.left.fromSpecResidueField u ≫
    G.objects.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (invariantRing G).subtype))).hom
  exact isIntegral_preimage_fromSpecResidueField_comp_toSpecΓ_comp
    (CommRingCat.ofHom (invariantRing G).subtype) u (isIntegral_invariantRing G) hmax

end AlgebraicGeometry.GroupoidScheme

end

end
