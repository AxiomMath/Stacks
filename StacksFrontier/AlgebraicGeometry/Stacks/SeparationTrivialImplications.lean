module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

/-!
# The trivial implications between the separation axioms (Stacks 050E)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` in a big fppf site `B`.
Stacks 050E records three implications between the separation axioms of Stacks 04YW. Two of them
are proved here:

1. if `f` is separated then `f` is quasi-separated, and
2. if `f` is DM then `f` is quasi-DM.

Both are implications between conditions of Stacks 04XB imposed on the *same* 1-morphism, the
relative diagonal `Δ_f`, so each reduces to the corresponding implication between properties of
a morphism of algebraic spaces: a proper morphism is separated and of finite type, hence
quasi-separated and quasi-compact (**Stacks 03KK**), and an unramified morphism is locally
quasi-finite.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isUnramified`: an unramified morphism of
  algebraic spaces is locally quasi-finite.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_isSeparated`: **Stacks 050E**,
  part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_isDM`: **Stacks 050E**, part (2).

## Implementation notes

Part (3) of Stacks 050E — a 1-morphism representable by algebraic spaces is DM — is not proved
here but in `StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified`, as
`AlgebraicGeometry.Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`,
beside the parts of Stacks 04YQ its proof consumes: monomorphy of the relative diagonal, part
(3), and its local finite type, part (2).

The space-level implication from unramified to locally quasi-finite is new. Both predicates are
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` (**Stacks 03MJ**, condition (1)) at a property
of scheme morphisms, and that condition is a universally quantified statement whose conclusion
is the property applied to one scheme morphism, so it is monotone in the property; the
scheme-level inclusion is `AlgebraicGeometry.locallyQuasiFinite_of_unramified` together with the
locally-of-finite-type half of
`AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_formallyUnramified`. Monotonicity is
stated separately because it is about Stacks 03MJ and not about unramifiedness.

Properness of a morphism of algebraic spaces is *separated, of finite type and universally
closed* and being of finite type is *locally of finite type and quasi-compact*
(`AlgebraicGeometry.Space.IsProper`, `AlgebraicGeometry.Space.IsFiniteType`), so part (1) is two
projections and one application of `AlgebraicGeometry.Space.isQuasiSeparated_of_isSeparated`,
taken pointwise in the data the Stacks 04XB conditions are quantified over.

Part (2) uses the existential representability witness carried by
`AlgebraicGeometry.Stack.IsDM` only to discard it: quasi-DM-ness, like the other three axioms of
Stacks 04YW formalized in `StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms`, is stated by the
Stacks 04XB quantifier over all algebraic spaces representing a base change and so needs no
witness. In particular neither implication needs the stability and locality instances of
Chapter 67 that `AlgebraicGeometry.Stack.HasRelativeProperty` would ask for; that is the reason
both `AlgebraicGeometry.Stack.IsDM` and the predicates of
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms` are written longhand.

## References

* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 050E, part (1).** A separated 1-morphism of algebraic stacks over `S` is
quasi-separated: its relative diagonal is proper, hence separated and of finite type, hence
quasi-separated and quasi-compact. -/
@[stacks 050E "part (1): separated implies quasi-separated"]
theorem isQuasiSeparated_of_isSeparated {f : 𝒳 ⟶ 𝒴} (hf : IsSeparated B S hS f) :
    IsQuasiSeparated B S hS f :=
  ⟨fun U y hy F hF hrep => (hf U y hy F hF hrep).2.1.2,
    fun U y hy F hF hrep =>
      Space.isQuasiSeparated_of_isSeparated B S hS (hf U y hy F hF hrep).1⟩

/-- **Stacks 050E, part (2).** A Deligne–Mumford 1-morphism of algebraic stacks over `S` is
quasi-DM: its relative diagonal is unramified, hence locally quasi-finite. -/
@[stacks 050E "part (2): DM implies quasi-DM"]
theorem isQuasiDM_of_isDM {f : 𝒳 ⟶ 𝒴} (hf : Stack.IsDM B S hS f) :
    IsQuasiDM B S hS f := by
  obtain ⟨-, hrel⟩ := hf
  intro U y hy F hF hrep
  exact Space.isLocallyQuasiFinite_of_isUnramified B S hS _ (hrel U y hy F hF hrep)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
