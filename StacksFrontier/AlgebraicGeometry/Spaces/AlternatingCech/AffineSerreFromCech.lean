module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.ColumnVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleAffineCechCriterion

/-!
# The affine Serre vanishing from Čech vanishing

`AlgebraicGeometry.Space.SpacesEtale.AffineSerreVanishing` — the positive-degree vanishing of the
cohomology of a quasi-coherent module on the spaces-étale site of an affine algebraic space — is
the one input of the alternating Čech recursion of [Stacks, Tag 072C] that the recursion itself
cannot supply.  This file reduces it to the Čech vanishing on the finite affine coverings of the
affine objects of the *small* étale site, which is the shape
`AlgebraicGeometry.Space.subsingleton_sheafH_spacesEtale_of_isZero_cechCohomology` consumes:
the affine objects of the small étale site, read into the spaces-étale site by the comparison of
[Stacks, Tag 03G1], are cofinal, and the Čech-to-derived criterion of [Stacks, Tag 03F9] then
computes the global cohomology at the terminal object.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.affineSerreVanishing_of_isZero_cechCohomology`: the
  positive-degree vanishing on an affine algebraic space, from the Čech vanishing of the
  coefficients along the finite affine coverings of the small étale site.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The slice of the small étale site at a chart has finite limits: the chart is terminal in its
own slice and the site has pullbacks.  Local to this file, as it is in
`StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleAffineCechCriterion`, whose statement of the
Čech hypothesis needs it to elaborate. -/
local instance hasFiniteLimits_overSmallEtaleChart (Y : AlgebraicSpaces B S hS)
    (W : SmallEtale B S hS Y.obj) : HasFiniteLimits (Over W) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- **The affine Serre vanishing from Čech vanishing.**  If the Čech cohomology of the underlying
abelian sheaf of a quasi-coherent module vanishes in positive degrees along every finite covering
of an affine object of the small étale site by affine objects, then the global cohomology of that
module on the spaces-étale site of an affine algebraic space vanishes in positive degrees.

This is `AlgebraicGeometry.Space.subsingleton_sheafH_spacesEtale_of_isZero_cechCohomology`, read
off at the underlying abelian sheaf of the module. -/
theorem affineSerreVanishing_of_isZero_cechCohomology
    (hCech : ∀ (Y : AlgebraicSpaces B S hS), IsAffineSpace B S hS Y.obj →
      ∀ M : SheafOfModules.{u + 1} (spacesEtaleRing B S hS Y), M.IsQuasicoherentOnSite →
        ∀ {W : SmallEtale B S hS Y.obj}, IsAffine (chartScheme W) →
          ∀ E : PreZeroHypercover.{u + 1} W, Finite E.I₀ →
            (∀ i, IsAffine (chartScheme (E.X i))) →
            E.sieve₀ ∈ SmallEtale.topology B S hS Y.obj W →
            ∀ p : ℕ, 0 < p →
              IsZero (Stacks.CechSite.cechCohomology E
                ((comparisonFunctor B S hS Y).op ⋙
                  ((SheafOfModules.toSheaf.{u + 1} (spacesEtaleRing B S hS Y)).obj M).obj) p)) :
    AffineSerreVanishing B S hS := fun Y hY M hM q hq =>
  subsingleton_sheafH_spacesEtale_of_isZero_cechCohomology hY
    ((SheafOfModules.toSheaf.{u + 1} (spacesEtaleRing B S hS Y)).obj M)
    (fun hW E hfin haff hcov p hp => hCech Y hY M hM hW E hfin haff hcov p hp) q hq

end AlgebraicGeometry.Space.SpacesEtale

end
