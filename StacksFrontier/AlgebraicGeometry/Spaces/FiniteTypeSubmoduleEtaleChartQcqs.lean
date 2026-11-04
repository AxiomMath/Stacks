module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeSubmoduleEtaleChartStep

/-!
# Dominating a finite type submodule over an étale chart of a qcqs algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, let `ℱ` be a
quasi-coherent `𝒪_X`-module, and let `g : Y ⟶ X` be an étale morphism with `Y` quasi-compact.
A submodule of finite type `𝒢 ⊆ ℱ|_Y` is then contained in the restriction of a quasi-coherent
submodule of finite type of `ℱ` itself.

The proof is the induction principle for quasi-compact quasi-separated algebraic spaces,
Stacks 08GP, applied to `AlgebraicGeometry.Space.DominationProperty`: the affine case is
`AlgebraicGeometry.Space.dominationProperty_of_isAffineSpace` and the step is
`AlgebraicGeometry.Space.dominationProperty_of_isElementaryDistinguishedSquare`.

## Main results

* `AlgebraicGeometry.Space.dominationProperty_of_isQuasiCompactSpace`: every quasi-compact and
  quasi-separated algebraic space has the domination property.
* `AlgebraicGeometry.Space.exists_isFiniteType_le_etaleSubmoduleRestrict`: the domination.

## Implementation notes

No Stacks tag is registered here.  The statement is neither Stacks 0829 — the directedness and
colimit assertions for a quasi-compact quasi-separated algebraic space — nor Stacks 0853, which
extends a finite type quasi-coherent submodule along an *open immersion* and with equality rather
than containment.  It is the containment form along an arbitrary quasi-compact étale morphism,
and it is what the proof of Stacks 0GUT uses Stacks 0829 for.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Every quasi-compact and quasi-separated algebraic space has the domination property**, by
the induction principle of Stacks 08GP. -/
theorem dominationProperty_of_isQuasiCompactSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    DominationProperty B S hS X := by
  have h := qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (fun Y _ => ∀ hY : IsAlgebraicSpace B S hS Y, DominationProperty B S hS ⟨Y, hY⟩)
    (fun V hVa hY => dominationProperty_of_isAffineSpace B S hS ⟨V.1.left.1, hY⟩ hVa)
    (fun _ _ _ _ _ hsq hWqc hWqs hUqc hVa hPU hPV _ hY =>
      dominationProperty_of_isElementaryDistinguishedSquare B S hS hZ (W := ⟨_, hY⟩)
        hsq hWqc hWqs hUqc hVa (hPU _) (hPV _))
  exact h X.2

/-- **A finite type submodule over a quasi-compact étale chart is dominated by one on the
space.**  For `ℱ` a quasi-coherent module on a quasi-compact quasi-separated algebraic space `X`,
an étale `g : Y ⟶ X` with `Y` quasi-compact and a submodule of finite type `𝒢` of `ℱ|_Y`, there
is a quasi-coherent submodule of finite type `𝒦` of `ℱ` with `𝒢 ≤ 𝒦|_Y`. -/
theorem exists_isFiniteType_le_etaleSubmoduleRestrict (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {F : Modules.{u, u} B S hS X.1 X.2} (hF : F.IsQuasicoherentOnSite)
    {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (G : ((etaleModulePullback.{u, u} B S hS g hg).obj F).Submodule)
    (hG : G.toSheafOfModules.IsFiniteType) :
    ∃ K : F.Submodule,
      (K.toSheafOfModules.IsQuasicoherentOnSite ∧ K.toSheafOfModules.IsFiniteType) ∧
        G ≤ etaleSubmoduleRestrict B S hS g hg K :=
  dominationProperty_of_isQuasiCompactSpace B S hS hZ X hXqc hXqs F hF Y g hg hYqc G hG

end AlgebraicGeometry.Space

end
