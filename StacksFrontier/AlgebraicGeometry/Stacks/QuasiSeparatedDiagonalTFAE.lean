module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal

/-!
# Stacks 04YT: quasi-separatedness and the relative diagonal

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` contained in a big fppf
site `B`, representable by algebraic spaces. Stacks 04YT asserts the equivalence of

1. `f` is quasi-separated,
2. the relative diagonal `Δ_f` is quasi-compact, and
3. `Δ_f` is of finite type,

all three in the sense of Properties of Stacks, Section 04XB. In particular condition (1) is
`AlgebraicGeometry.Stack.IsQuasiSeparated B S hS f.hom` — every algebraic space representing the
base change of `f` along a scheme-valued point of `𝒴` is quasi-separated over it — and not
Definition 04YW, which Stacks justifies by this lemma.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_relativeDiagonal_tfae`:
  **Stacks 04YT**.

## Implementation notes

The equivalence of (1) and (2) is
`AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated`. Its proof does not
pass through a smooth atlas `V ⟶ 𝒴` as the source's (1) ⇒ (2) does: it tests both conditions at an
arbitrary scheme-valued point `T ⟶ 𝒴`, where the relative diagonal of `𝒳 ×_𝒴 T ⟶ T` is a base
change of `Δ_f` along the square of Stacks 04YR, and conversely every scheme-valued point of
`𝒳 ×_𝒴 𝒳` lifts through the right-hand leg of that square. That is the argument the source gives
for (2) ⇒ (1), used in both directions. The equivalence of (2) and (3) is the source's: `Δ_f` is
locally of finite type, part (2) of Stacks 04YQ.

## References

* [Stacks Project, Tag 04YT](https://stacks.math.columbia.edu/tag/04YT)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
-/

@[expose] public section

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒵 𝒯 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04YT.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is
representable by algebraic spaces and write `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` for its relative
diagonal. The following are equivalent, each in the sense of Properties of Stacks, Section 04XB:

1. `f` is quasi-separated: every algebraic space representing the base change of `f` along a
   scheme-valued point of `𝒴` is quasi-separated over it;
2. `Δ_f` is quasi-compact;
3. `Δ_f` is of finite type.

Condition (1) is `AlgebraicGeometry.Stack.IsQuasiSeparated`, not Definition 04YW. -/
@[stacks 04YT]
theorem isQuasiSeparated_relativeDiagonal_tfae (f : 𝒵 ⟶ 𝒯)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    List.TFAE
      [Stack.IsQuasiSeparated B S hS f.hom,
       Stack.IsQuasiCompact.{u, u, u + 1} B S hS
         (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val f.hom),
       Stack.IsFiniteType.{u, u, u + 1} B S hS
         (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val f.hom)] := by
  tfae_have 1 ↔ 2 := (Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS f hf).symm
  tfae_have 2 → 3 := isFiniteType_relativeDiagonal_of_isQuasiCompact B S hS f hf
  tfae_have 3 → 2 := isQuasiCompact_relativeDiagonal_of_isFiniteType B S hS f
  tfae_finish

end AlgebraicGeometry.Stack.AlgebraicStacks

end
