module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeGluing

/-!
# Tag 02NC's isomorphism is the comparison at every trivializing section

The canonical isomorphism `Proj_S(ℬ) ≅ Proj_S(𝒜)` of Tag 02NC is glued from the comparisons
`Proj ℬ(V) ⟶ Proj 𝒜(V)` attached to sections chosen over the members of the basis of trivializing
affine opens. This file removes the choice from its characterization: over **every** affine open
`V` of the base and **every** section `x` of `ℒ` over `V` whose powers trivialize the powers of
`ℒ`, the isomorphism restricts to the comparison attached to `x`. It is the unique isomorphism
over `S` with this property.

## Main results

* `RelativeInvertibleTwist.chart_comp_relativeTwistIso_hom_of_trivializesPower`: the isomorphism
  is the comparison at every trivializing pair `(V, x)`.
* `RelativeInvertibleTwist.existsUnique_relativeTwistIso_trivializesPower`: it is the unique
  isomorphism over `S` which is the comparison at every trivializing pair.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-- An affine open carrying a section whose powers trivialize the powers of `ℒ` is a member of
the trivializing basis. -/
theorem mem_trivializingOpens_of_trivializesPower {V : S.Opens} (hV : IsAffineOpen V)
    {x : (tp L 1).val.obj (op V)} (hx : ∀ d : ℕ, 0 < d → TrivializesPower L V x d) :
    V ∈ trivializingOpens L :=
  ⟨hV, x, hx 1 Nat.one_pos⟩

/-- **Tag 02NC's isomorphism is the comparison at every trivializing pair**: over every affine
open `V` of the base and every section `x` of `ℒ` over `V` whose powers trivialize the powers of
`ℒ`, the chart of `Proj_S(ℬ)` over `V` followed by the isomorphism is the comparison
`Proj ℬ(V) ⟶ Proj 𝒜(V)` attached to `x` followed by the chart of `Proj_S(𝒜)`. No choice of
section enters: the comparison does not depend on it. -/
theorem chart_comp_relativeTwistIso_hom_of_trivializesPower {V : S.Opens} (hV : IsAffineOpen V)
    {x : (tp L 1).val.obj (op V)} (hx : ∀ d : ℕ, 0 < d → TrivializesPower L V x d) :
    (relativeProj (twist 𝒜 L)).chart V hV ≫ (relativeTwistIso L 𝒜).hom =
      projMap_psiSectionAt L 𝒜 hx ≫ (relativeProj 𝒜).chart V hV := by
  have hV' := mem_trivializingOpens_of_trivializesPower L hV hx
  exact (chart_comp_relativeTwistIso_hom L 𝒜 ⟨V, hV'⟩).trans
    (congrArg (· ≫ _)
      (projMap_psiSectionAt_eq_of_trivializesPower L 𝒜 hx
        (basisSection_trivializesPower L ⟨V, hV'⟩)))

/-- **Tag 02NC's isomorphism is the unique isomorphism `Proj_S(ℬ) ≅ Proj_S(𝒜)` over `S` which is
the comparison at every trivializing pair `(V, x)`.** -/
theorem existsUnique_relativeTwistIso_trivializesPower :
    ∃! e : (relativeProj (twist 𝒜 L)).scheme ≅ (relativeProj 𝒜).scheme,
      (∀ (V : S.Opens) (hV : IsAffineOpen V) (x : (tp L 1).val.obj (op V))
          (hx : ∀ d : ℕ, 0 < d → TrivializesPower L V x d),
          (relativeProj (twist 𝒜 L)).chart V hV ≫ e.hom =
            projMap_psiSectionAt L 𝒜 hx ≫ (relativeProj 𝒜).chart V hV) ∧
        e.hom ≫ (relativeProj 𝒜).toBase = (relativeProj (twist 𝒜 L)).toBase := by
  refine ⟨relativeTwistIso L 𝒜, ⟨fun V hV x hx =>
    chart_comp_relativeTwistIso_hom_of_trivializesPower L 𝒜 hV hx,
    relativeTwistIso_hom_comp_toBase L 𝒜⟩, fun e he => ?_⟩
  refine (existsUnique_relativeTwistIsoOver L 𝒜).unique
    ⟨fun V => he.1 V V.2.1 (basisSection L V) (basisSection_trivializesPower L V), he.2⟩
    ⟨fun V => chart_comp_relativeTwistIso_hom L 𝒜 V, relativeTwistIso_hom_comp_toBase L 𝒜⟩

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
