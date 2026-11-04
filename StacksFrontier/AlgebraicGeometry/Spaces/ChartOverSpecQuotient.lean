module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecQuotientOverAffineBase

/-!
# The ideal of a closed subscheme of the base kills the functions of a chart above it

Let `S` be an affine scheme in a big fppf site `B`, let `I` be an ideal of `Γ(S, ⊤)` and let
`Z = \Spec(Γ(S, ⊤)/I)` be the closed subscheme it cuts out
(`AlgebraicGeometry.Space.specQuotientOver`).  Every object of the big fppf category over `S`
which maps to `Z` has `I` in the kernel of its structure morphism on global functions; in
particular every étale scheme chart of a base-change space `X ×_S Z` does, because such a chart
maps to `Z` through the second projection.

## Main definitions

* `AlgebraicGeometry.Space.chartToTest`: the morphism of the big fppf category over `S` from the
  object underlying an étale scheme chart of a base-change space to the test scheme.

## Main results

* `AlgebraicGeometry.Space.le_ker_appTop_of_hom_specQuotientOver`: an object of the category
  mapping to `Z` has `I` in the kernel of its structure morphism on global functions.
* `AlgebraicGeometry.Space.le_ker_appTop_chartToBase_baseChangeSpace`: consequently `I` is in
  the kernel of the structure morphism to the base of every étale scheme chart of `X ×_S Z`.
* `AlgebraicGeometry.Space.smul_chartRing_baseChangeSpace_eq_zero`: the same, read as the ideal
  acting by zero on the ring of functions of the chart, with the scalars acting through the
  structure morphism of the chart.
* `AlgebraicGeometry.Space.chartRing_eq_gammaTop`: the ring of sections of the structure sheaf
  of the small étale site over a chart is the ring of global functions of the chart's scheme.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The ring of sections of the structure sheaf of the small étale site over a chart is the ring
of global functions of the chart's scheme. -/
theorem chartRing_eq_gammaTop (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (U : SmallEtale B S hS F) :
    chartRing B S hS F hF U = (Γ(chartScheme U, ⊤) : Type u) := rfl

/-- An object of the big fppf category over `S` mapping to the closed subscheme cut out by `I`
has `I` in the kernel of its structure morphism on global functions. -/
theorem le_ker_appTop_of_hom_specQuotientOver [IsAffine S] (I : Ideal Γ(S, ⊤))
    {W : BigFppfOver B S hS} (ψ : W ⟶ specQuotientOver B S hS I) :
    I ≤ RingHom.ker (B.inclusion.map W.hom).appTop.hom := by
  intro a ha
  have hzero : (B.inclusion.map (specQuotientOver B S hS I).hom).appTop.hom a = 0 :=
    (ker_appTop_specQuotientToBase S I).ge ha
  rw [RingHom.mem_ker, ← Over.w ψ, Functor.map_comp, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply, hzero, map_zero]

/-- The object of the big fppf category over `S` underlying an étale scheme chart of the
base-change space `X ×_Y T` maps to the test scheme `T`. -/
def chartToTest (D : ModuleMapSituation.{u, u} B S hS) (T : D.SchemesOver)
    (U : SmallEtale B S hS (D.baseChangeSpace T).1) :
    chartFppfObject B S hS (D.baseChangeSpace T) U ⟶ T.left :=
  yoneda.preimage (U.1.hom ≫ (D.baseChangeInclusion T).hom)

/-- The ideal cutting out a closed subscheme of the affine base lies in the kernel of the
structure morphism to the base of every étale scheme chart of `X ×_S Z`. -/
theorem le_ker_appTop_chartToBase_baseChangeSpace [IsAffine S]
    (D : ModuleMapFlatTargetSituation B S hS) (I : Ideal Γ(S, ⊤))
    (U : SmallEtale B S hS ((D.toModuleMapSituation B S hS).baseChangeSpace
      (D.specQuotientTest B S hS I)).1) :
    I ≤ RingHom.ker (chartToBase B S hS
      ((D.toModuleMapSituation B S hS).baseChangeSpace (D.specQuotientTest B S hS I))
        U).appTop.hom :=
  le_of_le_of_eq
    (le_ker_appTop_of_hom_specQuotientOver B S hS I
      (chartToTest B S hS (D.toModuleMapSituation B S hS) (D.specQuotientTest B S hS I) U))
    (congrArg (fun m : chartScheme U ⟶ S => RingHom.ker m.appTop.hom)
      (chartToBase_eq B S hS
        ((D.toModuleMapSituation B S hS).baseChangeSpace (D.specQuotientTest B S hS I))
          U)).symm

/-- The ideal cutting out a closed subscheme of the affine base acts by zero on the ring of
functions of every étale scheme chart of `X ×_S Z`, the scalars acting through the structure
morphism of the chart on global functions. -/
theorem smul_chartRing_baseChangeSpace_eq_zero [IsAffine S]
    (D : ModuleMapFlatTargetSituation B S hS) (I : Ideal Γ(S, ⊤))
    (U : SmallEtale B S hS ((D.toModuleMapSituation B S hS).baseChangeSpace
      (D.specQuotientTest B S hS I)).1) :
    letI : Module Γ(S, ⊤) (Γ(chartScheme U, ⊤) : Type u) :=
      Module.compHom _ (chartToBase B S hS
        ((D.toModuleMapSituation B S hS).baseChangeSpace (D.specQuotientTest B S hS I))
          U).appTop.hom
    ∀ a ∈ I, ∀ c : (Γ(chartScheme U, ⊤) : Type u), a • c = 0 := fun _ ha c =>
  (congrArg (· * c)
    (RingHom.mem_ker.mp (le_ker_appTop_chartToBase_baseChangeSpace B S hS D I U ha))).trans
    (zero_mul c)

end AlgebraicGeometry.Space

end
