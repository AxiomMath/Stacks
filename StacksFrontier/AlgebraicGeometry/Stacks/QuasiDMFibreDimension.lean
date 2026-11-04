module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionQuasiDM
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMFieldFibre

/-!
# The fibres of a quasi-DM 1-morphism are quasi-DM of non-negative dimension, and `dim 𝒵 ≤ dim 𝒯`

Remark **Stacks 0DS5** asserts, of a quasi-DM 1-morphism `f : 𝒯 ⟶ 𝒳` locally of finite type of
algebraic stacks, that *the fibres of `f` over points of the target are quasi-DM algebraic stacks,
and hence are of non-negative dimension*, and that in this case the lemma (Stacks 0DS4)
*implies that indeed `dim 𝒯 ≥ dim 𝒵`*. This file states these two assertions.

## Main results

* `isQuasiDMAbs_and_zero_le_dimensionAtPoint_fieldFibreStackSquare`: the fibre `𝒯 ×_𝒳 Spec k`
  of `f` over a field-valued point `Spec k ⟶ 𝒳` is a quasi-DM algebraic stack, of non-negative
  dimension at each of its points, and so of non-negative dimension when it is nonempty.
* `zero_le_relativeStackDimensionAt_and_closedSubstackDimension_le_dimension`: under the
  hypotheses of Stacks 0DS4 and for `f` quasi-DM, the fibre dimension `dim_t(𝒯_{f(t)})` is
  non-negative everywhere and `dim 𝒵 ≤ dim 𝒯`.

## Implementation notes

A point of `|𝒳|` is represented by a field-valued point `Spec k ⟶ 𝒳` (Stacks 04XE), and the fibre
over it is the 2-fibre product `AlgebraicGeometry.Stack.fieldFibreStackSquare`, as in the
definition of the relative dimension of Stacks 0DRL. "Quasi-DM algebraic stack" is the absolute
notion of Stacks 050D, part (6), `AlgebraicGeometry.Stack.IsQuasiDMAbs`, proved for the fibre in
`AlgebraicGeometry.Stack.isQuasiDMAbs_fieldFibreStackSquare`. "Of non-negative dimension" is read
pointwise — the dimension of Stacks 0AFN of the fibre is non-negative at every point of it, which
is `AlgebraicGeometry.Stack.zero_le_dimensionAtPoint_fieldFibreStackSquare`, since a fibre with
no points has dimension `-∞` by the convention of Stacks Remark 0AFQ.

The inequality `dim 𝒵 ≤ dim 𝒯` follows from the inequality `dim 𝒯 ≤ dim 𝒵 + dim_t(𝒯_{f(t)})` of
Stacks 0DS4, with equality on a nonempty open subset of `|𝒯|`, together with the non-negativity of
the fibre dimension; this is
`AlgebraicGeometry.Stack.closedSubstackDimension_le_dimension_of_isQuasiCompactMorphism`. The
hypotheses are those of Stacks 0DS4 — `f` quasi-compact and locally of finite type, `𝒯` and `𝒳`
Jacobson, pseudo-catenary and locally Noetherian, `|𝒯|` irreducible, `𝒳` quasi-separated, `P`
cutting out the scheme theoretic image `𝒵` of `f` — together with `f` quasi-DM.
## References

* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
* [Stacks Project, Tag 0DS5](https://stacks.math.columbia.edu/tag/0DS5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `f : 𝒯 ⟶ 𝒳` be a quasi-DM 1-morphism of algebraic stacks over `S`, locally of finite type,
and let `p` be a field-valued point of `𝒳` with field spectrum `Spec k`. Then the fibre
`𝒯 ×_𝒳 Spec k` of `f` over `p` is a quasi-DM algebraic stack (Stacks 050D, part (6)), and hence has
non-negative dimension at every one of its points; so, when it is nonempty, its dimension of Stacks
0AFP is non-negative. -/
@[stacks 0DS5 "the fibres of a quasi-DM 1-morphism are quasi-DM algebraic stacks, hence of \
non-negative dimension"]
theorem isQuasiDMAbs_and_zero_le_dimensionAtPoint_fieldFibreStackSquare
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hqdm : AlgebraicStacks.IsQuasiDM B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    IsQuasiDMAbs.{u, w, w} B S hS (fieldFibreStackSquare B S hS f p).pt ∧
      (∀ x : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
          (fieldFibreStackSquare B S hS f p).pt.val.property,
        0 ≤ dimensionAtPoint B S hS (fieldFibreStackSquare B S hS f p).pt
          (isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS f hf p) x) ∧
      (Nonempty (points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
          (fieldFibreStackSquare B S hS f p).pt.val.property) →
        0 ≤ dimension B S hS (fieldFibreStackSquare B S hS f p).pt
          (isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS f hf p)) :=
  ⟨isQuasiDMAbs_fieldFibreStackSquare B S hS f hqdm p,
    zero_le_dimensionAtPoint_fieldFibreStackSquare.{u, w} B S hS f hqdm hf p,
    fun ⟨x⟩ => (zero_le_dimensionAtPoint_fieldFibreStackSquare.{u, w} B S hS f hqdm hf p x).trans
      (le_iSup (fun y => dimensionAtPoint B S hS (fieldFibreStackSquare B S hS f p).pt
        (isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS f hf p) y) x)⟩

/-- Let `f : 𝒯 ⟶ 𝒳` be a quasi-compact, locally of finite type 1-morphism of Jacobson,
pseudo-catenary, locally Noetherian algebraic stacks over `S`, whose source is irreducible and
whose target is quasi-separated, and let `𝒵 ↪ 𝒳`, cut out by `P`, be the scheme theoretic image of
`f` — the situation of Stacks 0DS4. If `f` is moreover quasi-DM, then its fibres have non-negative
dimension, `dim_t(𝒯_{f(t)}) ≥ 0` at every `t ∈ |𝒯|`, and Stacks 0DS4 then gives `dim 𝒵 ≤ dim 𝒯`. -/
@[stacks 0DS5 "in the quasi-DM case the lemma implies dim T ≥ dim Z"]
theorem zero_le_relativeStackDimensionAt_and_closedSubstackDimension_le_dimension
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hfQC : IsQuasiCompactMorphism B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hDM : AlgebraicStacks.IsQuasiDM B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    (∀ t : points B S hS 𝒯.val.val 𝒯.val.property,
        0 ≤ relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t) ∧
      closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 ≤
        dimension B S hS 𝒯 h𝒯 :=
  ⟨fun t => zero_le_relativeStackDimensionAt.{u, w} B S hS f hDM hf h𝒯 h𝒳 t,
    closedSubstackDimension_le_dimension_of_isQuasiCompactMorphism B S hS f hfQC hf hDM h𝒯 h𝒳
      h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible h𝒳QuasiSeparated hP⟩

end AlgebraicGeometry.Stack

end
