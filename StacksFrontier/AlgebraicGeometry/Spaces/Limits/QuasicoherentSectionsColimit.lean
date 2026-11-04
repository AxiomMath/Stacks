module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSectionsColimitQuasicoherent

/-!
# Global sections of a quasi-coherent module on a limit of algebraic spaces

Let `X = lim Xᵢ` be the limit of a limit situation of algebraic spaces
(`AlgebraicGeometry.Space.LimitSituation`), let `ℱ₀` be a quasi-coherent module on `X₀`, and set
`ℱᵢ = f_{0i}^*ℱ₀` and `ℱ = f_0^*ℱ₀`. Then `Γ(X, ℱ) = colim_{i ≥ 0} Γ(Xᵢ, ℱᵢ)`, in the form
`AlgebraicGeometry.Space.LimitSituation.IsSectionsColimit`.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.isAlgebraicSpace_of_mk_lt`: the limit of a limit
  situation is an algebraic space.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit`: global sections of the pullback of
  a quasi-coherent module to the limit are the colimit of its global sections on the stages.

## Implementation notes

Besides the data of `AlgebraicGeometry.Space.LimitSituation`, both results take the hypothesis
`#A.I < B.cutoff.ord.cof`: on the bounded big fppf site, the limit of a directed system of
algebraic spaces exists in the site only for an index set below the site's size cutoff. Over an
index set one universe up the scheme-level statement is false
(`Stacks.LimitSectionsIdentification.not_card_01Z0`). Quasi-coherence of `ℱ₀` is
`SheafOfModules.IsQuasicoherentOnSite` on the small étale site of `X₀`.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)

/-- The limit of a limit situation is an algebraic space, for an index set below the cofinality
of the site's size cutoff. -/
theorem isAlgebraicSpace_of_mk_lt (hI : #A.I < B.cutoff.ord.cof) :
    IsAlgebraicSpace B S hS X := by
  have := A.hasLimit
  have hSize' : #A.Iᵒᵖ < B.cutoff.ord.cof := A.mk_op ▸ hI
  have hHomSize : ∀ i j : A.Iᵒᵖ, #(i ⟶ j) < B.cutoff.ord.cof := fun i j =>
    (A.mk_hom_lt_aleph0 i j).trans B.aleph0_lt_cutoff_cof
  exact isAlgebraicSpace_of_iso B S hS (limit.isoLimitCone ⟨A.cone, A.isLimitCone⟩)
    (isAlgebraicSpace_limit B S hS A.system hSize' hHomSize (fun i => A.isAlgebraicSpace i.unop)
      fun {_ _} f => A.transition_affine f)

/-- Let `ℱ₀` be a quasi-coherent module on `X₀`, and set `ℱᵢ = f_{0i}^*ℱ₀` and `ℱ = f_0^*ℱ₀`.
Then `Γ(X, ℱ) = colim_{i ≥ 0} Γ(Xᵢ, ℱᵢ)`, in the elementwise form
`AlgebraicGeometry.Space.LimitSituation.IsSectionsColimit`, for an index set below the
cofinality of the site's size cutoff. -/
@[stacks 07SI]
theorem isSectionsColimit (hI : #A.I < B.cutoff.ord.cof)
    (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)
    (hF₀ : F₀.IsQuasicoherentOnSite) :
    A.IsSectionsColimit F₀ (A.isAlgebraicSpace_of_mk_lt hI) :=
  A.isSectionsColimit_of_isQuasicoherent F₀ (A.isAlgebraicSpace_of_mk_lt hI) hI hF₀

end AlgebraicGeometry.Space.LimitSituation

end
