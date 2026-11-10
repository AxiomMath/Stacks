module

public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.AmbientFibreDifference

/-!
# The graph of a rational function in a Chow situation

Let `(S, δ)` be a Chow situation, let `X` be integral and locally of finite type over `S` with
`n = dim_δ(X)`, let `f ∈ R(X)^*` and let `U ⊆ X` be a nonempty open on which `f` is an invertible
section `g`. Let `Y ⊆ X ×_S ℙ¹_S` be the closure of the graph of the morphism `U ⟶ ℙ¹_S`
attached to `g`, with projections `p : Y ⟶ X` and `q : Y ⟶ ℙ¹_S`. This file states the six parts
of Tag 02RQ in that situation:

1. `p` is proper (`Stacks.Chow.graphProjection_isProper`, which needs no hypothesis);
2. `p⁻¹(U) ⟶ U` is an isomorphism;
3. the pullbacks `Y₀ = q⁻¹D₀` and `Y_∞ = q⁻¹D_∞` are defined;
4. `div_Y(f) = [Y₀]_{n-1} - [Y_∞]_{n-1}`;
5. `div_X(f) = p_*div_Y(f)`;
6. `div_X(f) = [Y₀]_{n-1} - [Y_∞]_{n-1}`, with `Y₀` and `Y_∞` viewed as closed subschemes of `X`.

The geometry behind these statements is proved in
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor` and the files under
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles` for an open whose inclusion
is
quasi-compact. Here that is automatic: `X` is locally of finite type over the locally Noetherian
base, hence locally Noetherian, so every open immersion into `X` is quasi-compact (Tag 01OX). From
it and the nonemptiness of `U` follow the remaining facts the statements use: `Y` is integral and
locally of finite type over `S`, `p⁻¹(U)` is dense in `Y`, `dim_δ(Y) = n`, and `Y₀ ⟶ X`,
`Y_∞ ⟶ X` are closed immersions.

## Main results

* `Stacks.Chow.isIso_graphProjection_morphismRestrict`: part (2).
* `Stacks.Chow.isPullbackDefined_graphFibres`: part (3).
* `Stacks.Chow.principalDivisorCycle_graphClosure_eq_fibreCycles_sub`: part (4).
* `Stacks.Chow.principalDivisorCycle_eq_properPushforward_graphClosure`: part (5).
* `Stacks.Chow.principalDivisorCycle_eq_imageFibreCycles_sub`: part (6).

## References

* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 01OX](https://stacks.math.columbia.edu/tag/01OX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- A nonempty open of an integral scheme is dense. -/
theorem dense_opens_of_nonempty {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    [Nonempty U.toScheme] : Dense (U : Set X) :=
  U.2.dense (Set.nonempty_coe_sort.mp ‹_›)

attribute [instance] locallyOfFiniteType_graphBaseMorphism isClosedImmersion_graphZeroFiber_comp
  isClosedImmersion_graphInfinityFiber_comp

section ChowSituation

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

include sX in
/-- Every open of a scheme locally of finite type over the base of a Chow situation has
quasi-compact inclusion, the scheme being locally Noetherian. -/
theorem quasiCompact_opens_ι_of_chowSituation (U : X.Opens) : QuasiCompact U.ι :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  inferInstance

/-- The closure `Y` of the graph of a section on a nonempty open of an integral scheme locally of
finite type over the base of a Chow situation is integral. -/
instance isIntegral_graphClosure_of_chowSituation [IsIntegral X] (U : X.Opens)
    [Nonempty U.toScheme] (s : Γ(X, U)) : IsIntegral (graphClosure sX U s) :=
  have := quasiCompact_opens_ι_of_chowSituation C sX U
  isIntegral_graphClosure sX U s (dense_opens_of_nonempty U)

/-- `p⁻¹(U)` is dense in the closure `Y` of the graph. -/
theorem graphPreimageDense_of_chowSituation (U : X.Opens) (s : Γ(X, U)) :
    GraphPreimageDense sX U s :=
  have := quasiCompact_opens_ι_of_chowSituation C sX U
  dense_graphPreimage sX U s

/-- The closure `Y` of the graph has the delta-dimension of `X`. -/
theorem schemeDeltaDimension_graphClosure_of_chowSituation [IsIntegral X] (n : ℤ)
    (dimX : schemeDeltaDimension C sX = (n : EInt)) (U : X.Opens) [Nonempty U.toScheme]
    (g : (Γ(X, U))ˣ) : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (n : EInt) :=
  have := quasiCompact_opens_ι_of_chowSituation C sX U
  schemeDeltaDimension_graphClosure C sX U g n dimX (dense_opens_of_nonempty U)
    (locallyOfFiniteType_graphBaseMorphism sX U ↑g)

/-- **Part (2) of Stacks Project, Tag 02RQ.** The restriction `p|_{p⁻¹(U)} : p⁻¹(U) ⟶ U` of the
projection `p : Y ⟶ X` is an isomorphism. -/
@[stacks 02RQ "part (2)"]
theorem isIso_graphProjection_morphismRestrict (U : X.Opens) (s : Γ(X, U)) :
    IsIso (graphProjection sX U s ∣_ U) := by
  have := quasiCompact_opens_ι_of_chowSituation C sX U
  have := isIso_graphProjection_restrict sX U s
  exact inferInstanceAs
    (IsIso ((pullbackRestrictIsoRestrict (graphProjection sX U s) U).inv ≫ pullback.snd _ _))

/-- **Part (3) of Stacks Project, Tag 02RQ.** The pullbacks `Y₀ = q⁻¹D₀` and `Y_∞ = q⁻¹D_∞` of
the zero and infinity divisors of `ℙ¹_S` along `q : Y ⟶ ℙ¹_S` are defined. -/
@[stacks 02RQ "part (3)"]
theorem isPullbackDefined_graphFibres [IsIntegral X] (U : X.Opens) [Nonempty U.toScheme]
    (g : (Γ(X, U))ˣ) :
    Stacks.Divisors.IsPullbackDefined (graphLineProjection sX U ↑g) (lineZeroDivisor C.S) ∧
      Stacks.Divisors.IsPullbackDefined (graphLineProjection sX U ↑g)
        (lineInfinityDivisor C.S) :=
  have := quasiCompact_opens_ι_of_chowSituation C sX U
  ⟨isPullbackDefined_zeroDivisor sX U g (dense_opens_of_nonempty U),
    isPullbackDefined_infinityDivisor sX U g (dense_opens_of_nonempty U)⟩

/-- **Part (4) of Stacks Project, Tag 02RQ.** On `Y`, the principal divisor of the rational
function `f` is the difference `[Y₀]_{n-1} - [Y_∞]_{n-1}` of the cycles of the two fibres.

Here `f` on `Y` is the pullback of the invertible section `g` to the dense open `p⁻¹(U)`, carried
to the function field by `Stacks.Chow.rationalFunctionsEquivFunctionField`. -/
@[stacks 02RQ "part (4)"]
theorem principalDivisorCycle_graphClosure_eq_fibreCycles_sub [IsIntegral X] (n : ℤ)
    (dimX : schemeDeltaDimension C sX = (n : EInt)) (U : X.Opens) [Nonempty U.toScheme]
    (g : (Γ(X, U))ˣ) :
    principalDivisorCycle C (graphBaseMorphism sX U ↑g)
        (schemeDeltaDimension_graphClosure_of_chowSituation C sX n dimX U g)
        ((rationalFunctionsEquivFunctionField (graphClosure sX U ↑g)).1
          ↑(graphRationalFunction sX U g (graphPreimageDense_of_chowSituation C sX U ↑g))) =
      cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
          (graphZeroFiber sX U ↑g).subschemeι (n - 1) -
        cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
          (graphInfinityFiber sX U ↑g).subschemeι (n - 1) :=
  have := quasiCompact_opens_ι_of_chowSituation C sX U
  principalDivisorCycle_graphClosure_eq_sub C sX U g n _ _ _ _

/-- **Part (5) of Stacks Project, Tag 02RQ.** The principal divisor of `f` on `X` is the proper
pushforward along `p : Y ⟶ X` of the principal divisor of `f` on `Y`. -/
@[stacks 02RQ "part (5)"]
theorem principalDivisorCycle_eq_properPushforward_graphClosure [IsIntegral X] (n : ℤ)
    (dimX : schemeDeltaDimension C sX = (n : EInt)) (f : (rationalFunctions X)ˣ) (U : X.Opens)
    [Nonempty U.toScheme] (g : (Γ(X, U))ˣ)
    (f_eq : ofSection X ⟨U, dense_opens_of_nonempty U⟩ ↑g = (f : rationalFunctions X)) :
    principalDivisorCycle C sX dimX ((rationalFunctionsEquivFunctionField X).1 ↑f) =
      properPushforward C (graphBaseMorphism sX U ↑g) sX (graphProjection sX U ↑g) rfl (n - 1)
        (principalDivisorCycle C (graphBaseMorphism sX U ↑g)
          (schemeDeltaDimension_graphClosure_of_chowSituation C sX n dimX U g)
          ((rationalFunctionsEquivFunctionField (graphClosure sX U ↑g)).1
            ↑(graphRationalFunction sX U g (graphPreimageDense_of_chowSituation C sX U ↑g)))) :=
  have := quasiCompact_opens_ι_of_chowSituation C sX U
  principalDivisorCycle_eq_properPushforward C sX U g n dimX f _ f_eq _ _ _ _ _

/-- **Part (6) of Stacks Project, Tag 02RQ.** Viewing `Y₀` and `Y_∞` as closed subschemes of `X`
through `p : Y ⟶ X`, the principal divisor of `f` on `X` is `[Y₀]_{n-1} - [Y_∞]_{n-1}`. -/
@[stacks 02RQ "part (6)"]
theorem principalDivisorCycle_eq_imageFibreCycles_sub [IsIntegral X] (n : ℤ)
    (dimX : schemeDeltaDimension C sX = (n : EInt)) (f : (rationalFunctions X)ˣ) (U : X.Opens)
    [Nonempty U.toScheme] (g : (Γ(X, U))ˣ)
    (f_eq : ofSection X ⟨U, dense_opens_of_nonempty U⟩ ↑g = (f : rationalFunctions X)) :
    principalDivisorCycle C sX dimX ((rationalFunctionsEquivFunctionField X).1 ↑f) =
      cycleAssociatedToClosedSubscheme C sX
          ((graphZeroFiber sX U ↑g).subschemeι ≫ graphProjection sX U ↑g) (n - 1) -
        cycleAssociatedToClosedSubscheme C sX
          ((graphInfinityFiber sX U ↑g).subschemeι ≫ graphProjection sX U ↑g) (n - 1) :=
  have := quasiCompact_opens_ι_of_chowSituation C sX U
  principalDivisorCycle_eq_sub_imageCycles C sX U g n dimX f _ f_eq _ _

end ChowSituation

end Stacks.Chow

end
