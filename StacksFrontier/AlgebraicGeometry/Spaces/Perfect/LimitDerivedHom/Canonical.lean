module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom
public import StacksFrontier.CategoryTheory.PullbackData.LimitHomSystem

/-!
# The stages of Situation 09RH as a system over the chosen stage

In Situation 09RH the stages `X_i`, `i ≥ 0`, with the morphisms `f_{i0} : X_i ⟶ X₀`, the
transition morphisms `f_{ji}` and the limit `X` with its projections form a system of algebraic
spaces over `X₀` in the sense of `CategoryTheory.PullbackData.LimitSystem`.  For the derived
pullback of modules `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` — the derived pullback
`Lf^*` of Stacks 06YY along every morphism of algebraic spaces, with the canonical comparisons
of Stacks 0D6D — the colimit statement
`CategoryTheory.PullbackData.LimitSystem.IsColim` for this system at `E₀`, `K₀` is the
conclusion of Stacks 09RI:

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀) ⟶ Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)`

is bijective, the transition maps being `Lf_{ji}^*` read through the canonical comparisons
`Lf_{ji}^*Lf_{i0}^* ≅ Lf_{j0}^*` and the maps to the limit `Lf_i^*` read through
`Lf_i^*Lf_{i0}^* ≅ Lf_0^*`.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.limitSystem`: the stages `i ≥ 0` of Situation 09RH
  as a system of algebraic spaces over `X₀`.

## Implementation notes

The system is read with the canonical comparisons of the coherent pseudofunctor
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, not with the comparisons of an
`AlgebraicGeometry.Space.DescentSituation.DerivedPullbackSystem`: the latter are unconstrained
isomorphisms, and for them the maps to the limit need not form a cocone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace DescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **The stages `i ≥ 0` of Situation 09RH as a system of algebraic spaces over `X₀`**: the
stages `X_i` with the morphisms `f_{i0}`, the transition morphisms `f_{ji}`, and the limit `X`
with its projections. -/
def limitSystem :
    PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) (D.stage D.base) D.Stages where
  stage i := D.stage i.1
  toBase i := D.transition i.2
  transition h := D.transition (show _ ≤ _ from h)
  transition_toBase {i _} h := D.transition_comp i.2 h _
  transition_comp h h' := D.transition_comp h h' _
  limit := D.limitSpace
  limitToBase := D.projection D.base
  proj i := D.projection i.1
  proj_toBase i := D.projection_comp_transition i.2
  proj_transition h := D.projection_comp_transition h

end DescentSituation

end AlgebraicGeometry.Space

end
