module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullbackEquations
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalizationDerivation

/-!
# The chart-square comparison carries `d_{Y/Bb}` to the Zariski `d^a`

For a commuting square `w ≫ q = k ≫ v` of étale charts of `q : Y ⟶ Bb` by objects of the big
fppf site, `AlgebraicGeometry.Space.chartSquareDifferentialsAssociatedIso` identifies
`w^*Ω_{Y/Bb}` with the associated module `(Ω_{W/V})ᵃ` of the Zariski sheaf of differentials of
the chart square.  This file shows that the identification is the *canonical* comparison and not
merely some isomorphism: read as a derivation through the étale-pullback bijection
`AlgebraicGeometry.Space.derivationEtalePullbackEquiv`, it returns the associated derivation
`d^a` of [Stacks Project, Tag 04CS] on every local section of `𝒪_W`.

This is the composite of the two factors' own compatibilities,
`AlgebraicGeometry.Space.universalDerivation_sheafOfDifferentialsEtaleLocalizationIso` for
[Stacks Project, Tag 04CU] and
`AlgebraicGeometry.Space.postcomp_representedAssociatedDifferentialsIso` for
[Stacks Project, Tag 04CS].

## Why this is stated on a local section and not between derivations

`AlgebraicGeometry.Space.derivationEtalePullbackEquiv` at `a` and `f` lands in the derivations
over the base morphism `a ≫ f`, while `AlgebraicGeometry.Space.universalDerivation` of the
square's lower edge `ψ` is a derivation over `ψ`.  Those two base morphisms are equal only after
the square `a ≫ f = ψ ≫ b` is used, so the two derivations do **not** have the same type and no
equation between them can be written down; what is shared is the module their values lie in.
Hence the statement is at a section, as [Stacks Project, Tag 04CU]'s own is, and the two factors
are composed through the definitional unfolding of
`PresheafOfModules.Derivation'.postcomp` on a value.

## Main results

* `AlgebraicGeometry.Space.universalDerivation_chartSquareDifferentialsAssociatedIso`: **the
  chart-square comparison carries the universal differential to `d^a`.**

No `@[stacks]` attribute is claimed: Tags 04CS and 04CU are registered where their
isomorphisms are built.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {Bb Y : AlgebraicSpaces B S hS} {W V : BigFppfOver B S hS}

/-- **The chart-square comparison carries the universal differential `d_{Y/Bb}` to the associated
Zariski differential `d^a` of `Ω_{W/V}`.**  Reading
`AlgebraicGeometry.Space.chartSquareDifferentialsAssociatedIso` as a derivation of `𝒪_W` through
the étale-pullback bijection of [Stacks Project, Tag 04CU] returns
`AlgebraicGeometry.Space.transportedAssociatedDerivation` on every local section of `𝒪_W`.

So the identification of `w^*Ω_{Y/Bb}` with `(Ω_{W/V})ᵃ` is the canonical comparison.  The proof
is the two factors' compatibilities composed: [Stacks Project, Tag 04CU]'s on the value, and
[Stacks Project, Tag 04CS]'s read on the value by
`PresheafOfModules.Derivation.congr_d`. -/
theorem universalDerivation_chartSquareDifferentialsAssociatedIso (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    {E : (SmallEtale B S hS (schemeSpace W).1)ᵒᵖ}
    (x : (structureRingSheaf B S hS (schemeSpace W)).obj.obj E) :
    (derivationEtalePullbackEquiv B S hS w hw q
        ((representedAssociatedModule B S hS W (schemeSpace W).property).obj
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)))
        (chartSquareDifferentialsAssociatedIso B S hS q w v k hw hv hsq).hom).d x =
      (transportedAssociatedDerivation B S hS k).d x :=
  (congrArg
      (fun m => (derivationEtalePullbackEquiv B S hS w hw q
        ((representedAssociatedModule B S hS W (schemeSpace W).property).obj
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))) m).d x)
      (chartSquareDifferentialsAssociatedIso_hom B S hS q w v k hw hv hsq)).trans
    ((congrArg (fun D => D.d x)
        (derivationEtalePullbackEquiv_comp B S hS w hw q
          (representedAssociatedDifferentialsIso B S hS k).hom
          (sheafOfDifferentialsEtaleLocalizationIso B S hS q w (schemeSpaceMap k) v hw hv
            hsq).hom)).trans
      ((congrArg
          (fun y => (ModuleCat.Hom.hom
            ((representedAssociatedDifferentialsIso B S hS k).hom.val.app E)) y)
          (universalDerivation_sheafOfDifferentialsEtaleLocalizationIso B S hS q w
            (schemeSpaceMap k) v hw hv hsq x)).trans
        (PresheafOfModulesOfCommRing.Derivation.congr_d
          (postcomp_representedAssociatedDifferentialsIso B S hS k) x)))

end AlgebraicGeometry.Space

end
