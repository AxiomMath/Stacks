module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlas

/-!
# Noetherian algebraic stacks (Stacks 0510)

**Stacks 0510** reads, verbatim: *"Let `𝒳` be an algebraic stack. We say `𝒳` is Noetherian if
`𝒳` is quasi-compact, quasi-separated and locally Noetherian."*

The three conjuncts are the library's:

* quasi-compact — `AlgebraicGeometry.Stack.IsQuasiCompactStack`, **Stacks 04YB**;
* quasi-separated — `AlgebraicGeometry.Stack.IsQuasiSeparatedAbs`, **Stacks 050D** part (8), the
  *absolute* axiom, i.e. quasi-separatedness over `Spec(ℤ)`;
* locally Noetherian — `AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` of **Stacks 04YG**
  taken at `AlgebraicGeometry.IsLocallyNoetherian`.

## Main definitions

* `AlgebraicGeometry.Stack.IsNoetherianStack`: **Stacks 0510**.

## Implementation notes

The source's remark after the definition stresses that quasi-separatedness here is the
*absolute* condition — the one read over `Spec(ℤ)` — and not quasi-separatedness over the base
`S`: "a Noetherian algebraic stack `𝒳` is not just quasi-compact and locally Noetherian, but
also quasi-separated", with the displayed equivalence stated for the absolute structure
morphism `p : 𝒳 ⟶ Spec(ℤ)`. So the middle conjunct is `IsQuasiSeparatedAbs` of Stacks 050D
part (8) and not `IsQuasiSeparatedOver` of part (4).

That predicate needs no hypothesis that the site contain the terminal scheme:
`AlgebraicGeometry.Stack.contains_specULiftZ` is a theorem of every big fppf site. Hence this
definition quantifies over exactly the data `IsQuasiCompactStack` already quantifies over.

The universe `w'` is the descent universe at which the stack viewed over `Spec(ℤ)` is taken, and
is the one `AlgebraicGeometry.Stack.IsQuasiSeparatedAbs` already carries; it is independent of
the descent universe `w` of `𝒳` itself.

This is a definition, so its covering set is the single declaration below.

## References

* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 0510](https://stacks.math.columbia.edu/tag/0510)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0510**, verbatim: *"Let `𝒳` be an algebraic stack. We say `𝒳` is Noetherian if `𝒳`
is quasi-compact, quasi-separated and locally Noetherian."*

Quasi-compactness is `AlgebraicGeometry.Stack.IsQuasiCompactStack` (**Stacks 04YB**),
quasi-separatedness is the absolute axiom `AlgebraicGeometry.Stack.IsQuasiSeparatedAbs`
(**Stacks 050D**, part (8)) and local Noetherianity is the smooth-scheme-atlas criterion
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` of **Stacks 04YG** at
`AlgebraicGeometry.IsLocallyNoetherian`. -/
@[stacks 0510]
noncomputable abbrev IsNoetherianStack (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property ∧
    IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳 ∧
      HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳

end AlgebraicGeometry.Stack

end
