module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMRelativePresentation

/-!
# Quasi-DM 1-morphisms and locally quasi-finite flat covers

For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are equivalent
(**Stacks 06UE**):

1. `f` is quasi-DM (**Stacks 04YW**);
2. every base change of `f` along an algebraic space over `𝒴` has a surjective, flat, locally
   finitely presented and locally quasi-finite cover by an algebraic space;
3. some algebraic space surjective, flat and locally of finite presentation over `𝒴` carries a
   base change of `f` with such a cover.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.hasQuasiFiniteFlatSpaceCoverOnEveryBaseChange_of_isQuasiDM_unconditional`: (1) ⟹ (2).
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isQuasiDM_tfae_hasQuasiFiniteFlatSpaceCover_unconditional`: the equivalence of (1), (2)
  and (3).

## References

* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06UE](https://stacks.math.columbia.edu/tag/06UE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- If `f : 𝒳 ⟶ 𝒴` is quasi-DM then every base change of `f` along an algebraic space over `𝒴`
has a locally quasi-finite flat cover by an algebraic space. -/
theorem hasQuasiFiniteFlatSpaceCoverOnEveryBaseChange_of_isQuasiDM_unconditional
    (f : 𝒳 ⟶ 𝒴) (hf : IsQuasiDM B S hS f) :
    HasQuasiFiniteFlatSpaceCoverOnEveryBaseChange B S hS f := by
  intro 𝒱 h𝒱 g
  have hover : Stack.IsQuasiDMOver B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt := by
    have hcomp := isQuasiDM_comp B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd
      (Stack.structureMorphism B S hS 𝒱) (isQuasiDM_baseChange B S hS f g hf)
      (isQuasiDMOver_of_isRepresentableByAlgebraicSpace B S hS 𝒱 h𝒱)
    rwa [Stack.comp_structureMorphism] at hcomp
  obtain ⟨W, p, hpS, hpF, hpL, hpQ⟩ :=
    Stack.hasQuasiDMPresentation_of_isAbsolutelyQuasiDM.{u, w} B S hS
      (BigFppfSite.contains_terminal B) _
      (isAbsolutelyQuasiDM_of_isQuasiDMOver B S hS (BigFppfSite.contains_terminal B) _ hover)
  exact ⟨Stack.schemeStack.{u, w} B S hS W,
    Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W, p,
    hpS, hpF, hpL, hpQ⟩

/-- For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are equivalent: `f`
is quasi-DM; every base change of `f` along an algebraic space over `𝒴` has a surjective, flat,
locally finitely presented, locally quasi-finite cover by an algebraic space; and some algebraic
space surjective, flat and locally of finite presentation over `𝒴` carries a base change of `f`
with such a cover. -/
@[stacks 06UE "All three conditions, with no hypothesis beyond the source's. The implication
  (1) implies (2) uses Tag 06MF through hasQuasiDMPresentation_of_isAbsolutelyQuasiDM, and the
  terminal scheme that Tag 050D part (6) needs lies in the site by
  AlgebraicGeometry.BigFppfSite.contains_terminal"]
theorem isQuasiDM_tfae_hasQuasiFiniteFlatSpaceCover_unconditional (f : 𝒳 ⟶ 𝒴) :
    [IsQuasiDM B S hS f,
      HasQuasiFiniteFlatSpaceCoverOnEveryBaseChange B S hS f,
      HasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange B S hS f].TFAE := by
  tfae_have 1 → 2 :=
    hasQuasiFiniteFlatSpaceCoverOnEveryBaseChange_of_isQuasiDM_unconditional B S hS f
  tfae_have 2 → 3 :=
    hasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange_of_onEveryBaseChange B S hS f
  tfae_have 3 → 1 :=
    isQuasiDM_of_hasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange B S hS
      (BigFppfSite.contains_terminal B) f
  tfae_finish

end AlgebraicGeometry.Stack.AlgebraicStacks

end
