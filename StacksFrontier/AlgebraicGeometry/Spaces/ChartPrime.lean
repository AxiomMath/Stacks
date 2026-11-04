module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections

/-!
# The prime ideal of an étale chart at a point of its scheme

Let `X` be an algebraic space and `W` an étale chart of `X`. A point `u` of the scheme of `W`
cuts out a prime ideal of the ring `Γ(W, 𝒪)` of the chart: the functions whose germ at `u` lies
in the maximal ideal of the local ring. When the scheme of `W` is affine this is the prime of
`Spec Γ(W, 𝒪)` corresponding to `u`.

## Main definitions

* `AlgebraicGeometry.Space.chartPrimeAt`: the prime ideal of the ring of an étale chart cut out by
  a point of its scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The prime ideal of the ring of an étale chart `W` cut out by a point `u` of its scheme: the
preimage of the maximal ideal of the local ring at `u` under the germ map. -/
noncomputable def chartPrimeAt {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (W : SmallEtale B S hS X) (u : chartScheme W) :
    Ideal (chartRing B S hS X hX W) :=
  Ideal.comap ((chartScheme W).presheaf.germ ⊤ u trivial).hom
    (IsLocalRing.maximalIdeal ((chartScheme W).presheaf.stalk u))

/-- The ideal cut out by a point of the chart is prime. -/
instance chartPrimeAt_isPrime {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (W : SmallEtale B S hS X) (u : chartScheme W) :
    (chartPrimeAt B S hS hX W u).IsPrime := by
  unfold chartPrimeAt
  exact Ideal.comap_isPrime _ _

end AlgebraicGeometry.Space

end
