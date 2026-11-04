module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.StrictHenselizationStalkIdeal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale charts with strict normal crossings and the local equation

A closed subscheme of a locally Noetherian scheme which acquires strict normal crossings on an
étale neighbourhood of each of its points has strict normal crossings at every strict
henselization of a local ring at a point of it, and is therefore an effective Cartier divisor.

This isolates the part of the definition of a normal crossings divisor that is responsible for
the Cartier condition: only the étale-chart clause is used, so the conclusion is available
before that definition's own effective Cartier conjunct has been established.

## Main results

* `Stacks.Divisors.isStrictNormalCrossingsAtStrictHenselizations_of_forall_etaleChart`: the
  étale-chart clause gives strict normal crossings at the strict henselizations.
* `Stacks.Divisors.isEffectiveCartierDivisor_of_forall_etaleChart`: hence the closed subscheme
  is an effective Cartier divisor.
* `Stacks.Divisors.isNormalCrossingsDivisor_of_forall_etaleChart`: hence it is a normal
  crossings divisor.

## Implementation notes

The first proof is the argument of
`Stacks.Divisors.isStrictNormalCrossingsDivisor_comap_fromSpecStalk_of_isNormalCrossingsDivisor`
with the étale chart taken from the hypothesis rather than from the definition of a normal
crossings divisor: a strict henselization of `𝒪_{X, x}` is also one of `𝒪_{U, q}` for a lift
`q` of `x` along the chart, so its spectrum maps weakly étale-ly to `U`, and weakly étale
pullback preserves strict normal crossings.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
* [Stacks Project, Tag 0CBS](https://stacks.math.columbia.edu/tag/0CBS)
* [Stacks Project, Tag 0CBP](https://stacks.math.columbia.edu/tag/0CBP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.Divisors

/-- The étale-chart clause in the definition of a normal crossings divisor, named on its own:
every point of the closed subscheme has an étale neighbourhood of its image on which the
pullback of the subscheme has strict normal crossings. -/
@[sga "5 I 3.1.5"]
def HasStrictNormalCrossingsEtaleCharts {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) : Prop :=
  ∀ y : D.subscheme, ∃ (U : Scheme.{u}) (g : U ⟶ X) (hU : IsLocallyNoetherian U), Etale g ∧
    (∃ q : U, g q = D.subschemeι y) ∧ @IsStrictNormalCrossingsDivisor U hU (D.comap g)

/-- A closed subscheme with strict normal crossings on an étale chart through each of its points
has strict normal crossings at every strict henselization. -/
theorem isStrictNormalCrossingsAtStrictHenselizations_of_forall_etaleChart {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hchart : HasStrictNormalCrossingsEtaleCharts D) :
    IsStrictNormalCrossingsAtStrictHenselizations D := by
  intro x hx L _ _ _ Ash _ _ _ _
  have : IsNoetherianRing Ash :=
    IsLocalRing.isNoetherianRing_of_isHenselization (A := X.presheaf.stalk x) L
  obtain ⟨y, hy⟩ := hx
  obtain ⟨U, g, hU, hg, ⟨q, hq⟩, hE⟩ := hchart y
  have hgx : g q = x := hq.trans hy
  subst hgx
  let := hU
  have := hg
  let : Algebra (X.presheaf.stalk (g q)) (U.presheaf.stalk q) := (g.stalkMap q).hom.toAlgebra
  obtain ⟨algB, algκ, htower, hlocal, hsc, hH⟩ :=
    AlgebraicGeometry.exists_isHenselization_stalk_of_etale g q L Ash
  let := algB
  let := algκ
  have := htower
  have := hlocal
  have := hH
  have hwe : Algebra.WeaklyEtale (U.presheaf.stalk q) Ash :=
    Algebra.weaklyEtale_of_ind_etale
      (IsLocalRing.IsHenselization.ind_etale (R := U.presheaf.stalk q) (L := L) (Rh := Ash))
  have : WeaklyEtale
      (Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk q) Ash))) := by
    refine weaklyEtale_specMap _ ?_
    have he : (CommRingCat.ofHom (algebraMap (U.presheaf.stalk q) Ash)).hom.toAlgebra = algB :=
      Algebra.algebra_ext _ _ fun _ => rfl
    exact he ▸ hwe
  have := weaklyEtale_fromSpecStalk U q
  have hglue : Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk q) Ash)) ≫
      U.fromSpecStalk q ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (g q)) Ash)) ≫
        X.fromSpecStalk (g q) := by
    refine spec_map_comp_fromSpecStalk_comp_eq g q _ _
      (CommRingCat.hom_ext (RingHom.ext fun z => ?_))
    exact (IsScalarTower.algebraMap_apply (X.presheaf.stalk (g q)) (U.presheaf.stalk q) Ash z).symm
  have key := isStrictNormalCrossingsDivisor_comap_comp_of_weaklyEtale g
    (Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk q) Ash)) ≫ U.fromSpecStalk q) D hE
  rw [Category.assoc, hglue] at key
  exact key

/-- A closed subscheme with strict normal crossings on an étale chart through each of its points
is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_of_forall_etaleChart {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hchart : HasStrictNormalCrossingsEtaleCharts D) :
    IsEffectiveCartierDivisor D :=
  isEffectiveCartierDivisor_of_isStrictNormalCrossingsAtStrictHenselizations D
    (isStrictNormalCrossingsAtStrictHenselizations_of_forall_etaleChart D hchart)

/-- A closed subscheme with strict normal crossings on an étale chart through each of its points
is a normal crossings divisor: the effective Cartier condition is automatic. -/
theorem isNormalCrossingsDivisor_of_forall_etaleChart {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hchart : HasStrictNormalCrossingsEtaleCharts D) :
    IsNormalCrossingsDivisor D :=
  ⟨isEffectiveCartierDivisor_of_forall_etaleChart D hchart, hchart⟩

end Stacks.Divisors

end
