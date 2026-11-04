module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom

/-!
# Quasi-coherence of the sheaf acting on the lifts

`AlgebraicGeometry.Space.liftActionSheaf` is the `𝒪_X`-module
`SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` of Stacks 061D which acts on the sheaf of lifts of
`a : X ⟶ Y` along a subspace `X ⊆ X'`.  Step (II) of the proof of Stacks 04AM — the vanishing
`H¹(X_étale, SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})) = 0` of Stacks 061J — is a statement about a
*quasi-coherent* module on the small étale site.  This file supplies that quasi-coherence.

The two arguments of the internal Hom are quasi-coherent with nothing carried: `Ω_{Y/B}` by
Stacks 04CV (`AlgebraicGeometry.Space.isQuasicoherentOnSite_sheafOfDifferentials`), its inverse
image by Stacks 03GA
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`), and
the conormal module by Stacks 04CN
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModule`).  What the internal Hom needs in
addition is a finiteness hypothesis on its *first* argument, and the one used here is finite local
freeness rather than the finite presentation of Stacks 03M1(6); see the implementation notes.

## Main results

* `isQuasicoherentOnSite_smallEtaleInternalHom_of_isFiniteLocallyFreeOnSite`:
  **the internal Hom of two quasi-coherent `𝒪_F`-modules whose first argument is finite locally
  free is quasi-coherent, unconditionally**, at the module universe of the schemes.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_liftActionSheaf_of_isFiniteLocallyFreeOnSite`:
  **the sheaf acting on the lifts is quasi-coherent** as soon as `a^*Ω_{Y/B}` is finite locally
  free.

## Implementation notes

The finiteness hypothesis is finite local freeness, Stacks 03DL(2), and not the finite
presentation of Stacks 03DL(7) which clause (6) of Stacks 03M1 asks for.  This is the hypothesis
under which quasi-coherence of the internal Hom is available in this development **without any
carried input**: Stacks 0GNC on a ringed site,
`AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`.  It is enough for the intended
consumer, Stacks 04AM, where the first argument is the inverse image of the sheaf of differentials
of a *smooth* morphism, and `Ω` of a smooth morphism is finite locally free by Stacks 0CK5,
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials_of_isSmooth`, proved
unconditionally in this tree.

The route of `StacksFrontier.AlgebraicGeometry.Spaces.InternalHomQuasicoherentFree` and
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartLocal` towards clause (6) is not
the one taken here, and the reason is a module universe.  Those files work at the module universe
`max (u + 1) m`, where `AlgebraicGeometry.Space.smallEtaleInternalHom` is stable — the internal
Hom of two `𝒪_F`-modules in module universe `m` lands in `max (u + 1) m` — and they reach
quasi-coherence only through the hypothesis `h03DX`, Descent, Proposition 03DX(2), which this
development proves at `AlgebraicGeometry.Space.Modules.{u, u}` only
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`) and so cannot
discharge there.  `AlgebraicGeometry.Space.liftActionSheaf` is formed from arguments in module
universe `u`, so Stacks 0GNC applies to it directly: its statement is at the module universe of
the coefficient rings, which for the small étale ringed site of an algebraic space over
`Scheme.{u}` is `u`, and the two sheafification hypotheses it carries on the slices of the
topology are the instances
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_over`.

The bridge between the two spellings of finite local freeness — the covering-family form of
Stacks 03DL(2), which is how this development states it, and the local-generators form of
Stacks 01C6(2), which Stacks 0GNC consumes — is
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite`.

The identification of `AlgebraicGeometry.Space.smallEtaleInternalHom` with the internal Hom of
the ringed site `AlgebraicGeometry.Space.smallEtaleRingedSite` is the `rfl` comparison
`AlgebraicGeometry.Space.smallEtaleInternalHom_eq_internalHomSheaf` of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionInternalHom`, used here at the algebraic
space `⟨F, hF⟩`.

**No `@[stacks]` attribute is carried.**  The two statements below are instantiations of
Stacks 0GNC, whose tag sits on the general
statement in `StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentInternalHom`; neither is a
clause of Stacks 03M1, whose finiteness hypothesis is weaker, and neither is a step of Stacks
061D beyond the module it already names.

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC), the internal Hom out of
  a finite locally free module on a ringed site.
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1), clause (6), the same for
  a first argument of finite presentation.
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D), the acting sheaf.
* [Stacks Project, Tag 061J](https://stacks.math.columbia.edu/tag/061J), the vanishing which
  consumes this quasi-coherence.
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM).
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL) and
  [Tag 01C6](https://stacks.math.columbia.edu/tag/01C6), the two forms of finite local freeness.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

section InternalHom

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The internal Hom of two quasi-coherent `𝒪_F`-modules whose first argument is finite locally
free is quasi-coherent**, for an algebraic space `F` over a scheme `S`, at the module universe of
the schemes.

This is Stacks 0GNC, `AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`, at the small
étale ringed site of `F`.  Nothing is carried: the two hypotheses that tag places on the slices of
the topology are the instances
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_over`, and its
local-generators form of finite local freeness comes from the covering-family form by
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite`.

The finiteness hypothesis is finite local freeness, Stacks 03DL(2), rather than the finite
presentation of Stacks 03M1(6); see the implementation notes of this file. -/
@[sga "3 III 0.6" "special case"]
theorem isQuasicoherentOnSite_smallEtaleInternalHom_of_isFiniteLocallyFreeOnSite
    (M N : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite)
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    (smallEtaleInternalHom B S hS F hF M N).IsQuasicoherentOnSite := by
  rw [smallEtaleInternalHom_eq_internalHomSheaf B S hS ⟨F, hF⟩ M N]
  let := hM
  let := hN
  let := SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite M hfree
  exact RingedSite.internalHomSheaf_isQuasicoherent (smallEtaleRingedSite B S hS F hF) M N

end InternalHom

section LiftActionSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T X' Y : AlgebraicSpaces B S hS}

/-- **The sheaf acting on the lifts is quasi-coherent** as soon as the inverse image
`a^*Ω_{Y/T}` of the sheaf of differentials is finite locally free.

The second argument of the internal Hom, the conormal module `𝒞_{X/X'}`, is quasi-coherent by
Stacks 04CN and the first is quasi-coherent by Stacks 04CV and Stacks 03GA, all three
unconditionally in this tree; the finiteness hypothesis is the only input.  For the intended
consumer, Stacks 04AM, it is Stacks 0CK5 at the smooth morphism `q`:
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials_of_isSmooth`, followed
by the stability of Stacks 03DL(2) under the inverse image of Stacks 03LU.  Both are proved,
so for a smooth `q` this statement carries no hypothesis at all; that form is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_liftActionSheaf_of_isSmooth`. -/
theorem isQuasicoherentOnSite_liftActionSheaf_of_isFiniteLocallyFreeOnSite
    (Z : ClosedSubspaces B S hS X'.1) (q : Y ⟶ T)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS q))) :
    (liftActionSheaf B S hS Z q a).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_smallEtaleInternalHom_of_isFiniteLocallyFreeOnSite B S hS _ _ _ _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a _
      (isQuasicoherentOnSite_sheafOfDifferentials B S hS q))
    (isQuasicoherentOnSite_conormalModule B S hS X' Z) hfree

end LiftActionSheaf

end AlgebraicGeometry.Space

end
