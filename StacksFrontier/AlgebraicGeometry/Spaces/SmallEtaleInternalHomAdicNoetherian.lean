module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicSectionsAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAdicChartComparison

/-!
# The chartwise hypothesis of Stacks 08B6, discharged

Let `X` be a Noetherian algebraic space over a scheme `S` of a big fppf site `B`, let `𝓘 ⊆ 𝒪_X`
be a quasi-coherent sheaf of ideals and let `M`, `N` be coherent `𝒪_X`-modules.  Writing
`𝓗 = 𝓗om_{𝒪_X}(M, N)`, the comparison
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicComparisonApp` is bijective on the inverse
limits of the sections over *every* étale chart,

`lim_n (𝓗 / 𝓘 ^ n 𝓗)(U) ≃ lim_n 𝓗om(M, N / 𝓘 ^ n N)(U)`,

which is the chartwise hypothesis `h0882` of
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv`.  Feeding it in gives the identity of
Stacks 08B6 from the source's own hypotheses and nothing else.

Two inputs meet here.  Over an affine chart whose ring is Noetherian the bijection is the
commutative algebra of Stacks 09BB, which is
`AlgebraicGeometry.Space.bijective_adicSectionsMapAt_smallEtaleInternalHomAdicComparison`; and
every affine chart of a Noetherian algebraic space has Noetherian ring, by
`AlgebraicGeometry.Space.isNoetherianAffineChart_of_isAffineChart`, which is Stacks 03E8 at the
chart.  The passage from the affine charts to all of them is
`AlgebraicGeometry.Space.bijective_adicSectionsMapAt_of_isAffine`, which is the sheaf condition
for the two systems.

## Main results

* `AlgebraicGeometry.Space.bijective_adicSectionsMapAt_smallEtaleInternalHomAdic_of_isNoetherian`
  — **the chartwise hypothesis `h0882`**, over every chart, from the hypotheses of
  Stacks 08B6.
* `AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquivOfNoetherian` — **the identity of
  Stacks 08B6 with no assumed input.**

## Implementation notes

Stacks 08B6 is registered, bare, on
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquivOfNoetherian`, which proves the identity
under the source's hypotheses alone.  `AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv`
stays unregistered, since `h0882` is an assumed input there.

The cokernels the ideal-power quotients are formed with, in `Modules.{u, u}` for `N` and in
`Modules.{u, u + 1}` for `𝓗`, are the instances `AlgebraicGeometry.Space.hasCokernels_modules`
and `AlgebraicGeometry.Space.hasCokernels_modules_succ`, made local instances here.  They are not
hypotheses.

## References

* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
* [Stacks Project, Tag 09BB](https://stacks.math.columbia.edu/tag/09BB)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasCokernels_modules hasCokernels_modules_succ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
    (M N : Modules.{u, u} B S hS X.1 X.2)

/-- **The chartwise hypothesis `h0882` of Stacks 08B6, over every étale chart**, from the
hypotheses of Stacks 08B6 and nothing else:

`lim_n (𝓗 / 𝓘 ^ n 𝓗)(U) ≃ lim_n 𝓗om(M, N / 𝓘 ^ n N)(U)`

for a Noetherian algebraic space `X`, a quasi-coherent sheaf of ideals `𝓘` and coherent `M`,
`N`.

Over an affine chart this is
`AlgebraicGeometry.Space.bijective_adicSectionsMapAt_smallEtaleInternalHomAdicComparison`, whose
Noetherian ring comes from `AlgebraicGeometry.Space.isNoetherianAffineChart_of_isAffineChart`;
over an arbitrary chart it is that statement plus the sheaf condition, which is
`AlgebraicGeometry.Space.bijective_adicSectionsMapAt_of_isAffine`. -/
theorem bijective_adicSectionsMapAt_smallEtaleInternalHomAdic_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hFN : IsNoetherian B S hS hZ X.1)
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hM : IsCoherent B S hS X.1 X.2 M) (hN : IsCoherent B S hS X.1 X.2 N)
    (U : ((smallEtaleRingedSite B S hS X.1 X.2).C)ᵒᵖ) :
    Function.Bijective (adicSectionsMapAt B S hS X.1 X.2
      (fun n => smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1)
        (smallEtaleInternalHom B S hS X.1 X.2 M N))
      (fun n => smallEtaleInternalHom B S hS X.1 X.2 M
        (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1) N))
      (fun n => smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 (n + 1)
        (smallEtaleInternalHom B S hS X.1 X.2 M N))
      (fun n => smallEtaleInternalHomMapRight B S hS X.1 X.2 M
        (smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 (n + 1) N))
      (smallEtaleInternalHomAdicComparisonApp B S hS X.1 X.2 𝓘 M N)
      (smallEtaleInternalHomAdicComparison_compat B S hS X.1 X.2 𝓘 M N) U) :=
  bijective_adicSectionsMapAt_of_isAffine B S hS X.1 X.2
    (fun n => smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1)
      (smallEtaleInternalHom B S hS X.1 X.2 M N))
    (fun n => smallEtaleInternalHom B S hS X.1 X.2 M
      (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1) N))
    (fun n => smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 (n + 1)
      (smallEtaleInternalHom B S hS X.1 X.2 M N))
    (fun n => smallEtaleInternalHomMapRight B S hS X.1 X.2 M
      (smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 (n + 1) N))
    (smallEtaleInternalHomAdicComparisonApp B S hS X.1 X.2 𝓘 M N)
    (smallEtaleInternalHomAdicComparison_compat B S hS X.1 X.2 𝓘 M N)
    (fun W hW => bijective_adicSectionsMapAt_smallEtaleInternalHomAdicComparison B S hS X 𝓘 M N
      hI hM hN hW
      (isNoetherianAffineChart_of_isAffineChart B S hS X hZ hFN W hW).2) U

/-- **Stacks 08B6.**  Let `X` be a Noetherian algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_X` be
a quasi-coherent sheaf of ideals and let `M`, `N` be coherent `𝒪_X`-modules.  Put
`𝓗 = 𝓗om_{𝒪_X}(M, N)`.  Then

`lim_n H⁰(X, 𝓗 / 𝓘 ^ n 𝓗) = Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))`,

the inverse limit of the global sections of the ideal-power quotients of `𝓗` being the morphisms
of inverse systems of `𝒪_X`-modules from the completion of `M` to the completion of `N`.

This is `AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv` with its assumed chartwise input
`h0882` discharged, so the hypotheses are exactly the source's: Noetherianness of `X`,
quasi-coherence of `𝓘`, coherence of `M` and of `N`.

The tag is registered here, bare, because this is where the source's identity is proved outright
under the source's own hypotheses and nothing else.  The two step registrations in
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentAdicInternalHomProIso.lean` carry clause strings
naming the pro-isomorphism step and the morphism step.  No registration is placed on
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv` itself, which takes `h0882` as a
hypothesis; this declaration is that one with `h0882` proved. -/
@[stacks 08B6]
def smallEtaleInternalHomAdicEquivOfNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hFN : IsNoetherian B S hS hZ X.1)
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hM : IsCoherent B S hS X.1 X.2 M) (hN : IsCoherent B S hS X.1 X.2 N) :
    adicSections B S hS X.1 X.2
        (fun n => smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1)
          (smallEtaleInternalHom B S hS X.1 X.2 M N))
        (fun n => smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 (n + 1)
          (smallEtaleInternalHom B S hS X.1 X.2 M N)) ≃
      (smallEtaleAdicQuotientSystem B S hS X.1 X.2 𝓘 M ⟶
        smallEtaleAdicQuotientSystem B S hS X.1 X.2 𝓘 N) :=
  smallEtaleInternalHomAdicEquiv B S hS X.1 X.2 𝓘 M N
    (bijective_adicSectionsMapAt_smallEtaleInternalHomAdic_of_isNoetherian
      B S hS X 𝓘 M N hZ hFN hI hM hN)

end AlgebraicGeometry.Space

end
