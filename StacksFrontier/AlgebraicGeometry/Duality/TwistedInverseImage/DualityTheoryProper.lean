module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# A duality theory: the upper shriek of a proper morphism is the right adjoint of `Rf_*`

[Stacks, Section 0AU3] summarises the duality theory obtained for `FTS S`, the schemes separated
and of finite type over a Noetherian base `S`, in nine numbered statements. This file proves the
first of the two assertions of its clause (2):

> if `f : X ⟶ Y` is a proper morphism of `FTS S`, then `f^!` is the restriction of the right
> adjoint of `Rf_*` to `D⁺_QCoh(𝒪_Y)`.

Both halves of that assertion are available in this repository. The upper shriek functor of
[Stacks, Tag 0A9Y] is `Stacks.Duality.upperShriek f j` for a compactification `j` of `X` over
`Y`; a proper morphism is its own compactification, `Stacks.Duality.properCompactification`, and
at that compactification `f^!` *is* the right adjoint of `Rf_*` on the whole of `D_QCoh(𝒪_Y)`,
which is `Stacks.Duality.upperShriekProperAdjunction`. That the right adjoint carries
`D⁺_QCoh(𝒪_Y)` into `D⁺_QCoh(𝒪_X)`, so that the word "restriction" means something, is
[Stacks, Tag 0A9I], formalized as
`Stacks.Duality.isBoundedBelow_twistedInverseImage_obj_and_exists_bound`.

## Main results

All in the namespace `Stacks.Duality`.

* `isBoundedBelow_upperShriek_properCompactification_obj` — for a proper `f`, the upper shriek
  functor carries bounded-below complexes to bounded-below complexes.
* `upperShriek_isRightAdjointOnBoundedBelow_of_isProper` — **[Stacks, Section 0AU3], clause (2),
  first assertion**.

## Implementation notes

*Which `f^!`.* The upper shriek functor of [Stacks, Tag 0A9Y] is built from a compactification,
and the statements below are made at the canonical one available for a proper morphism, where
`X̄ = X` and the open immersion is the identity — which is the compactification the source itself
uses for a proper morphism. That the functor does not depend on the compactification is
[Stacks, Tag 0AA0]; in this repository that independence is
`Stacks.Duality.DominatingCompactification.upperShriekObjIsoOfIsIso`, which still carries two
invertibility hypotheses for the maps of [Stacks, Tag 0A9L] — these are supplied on `D⁺_QCoh` by
[Stacks, Tag 0A9P], which is not available here. The clause label on the statement below says
so.

*The second assertion of clause (2)* is the duality isomorphism
`Rf_*R𝓗om_{𝒪_X}(K, f^!M) ⟶ R𝓗om_{𝒪_Y}(Rf_*K, M)` for `K ∈ D⁻_Coh(𝒪_X)` and
`M ∈ D⁺_QCoh(𝒪_Y)`. The map itself is `Stacks.Duality.sheafyTrace` ([Stacks, Tag 0B6H]); that it
is invertible for a proper morphism of Noetherian schemes is [Stacks, Tag 0GEW], and
`Stacks.Duality.isIso_sheafyTrace_of_isProper` carries [Stacks, Tag 0GEV] — the whole
mathematical content — and [Stacks, Tag 08E2] as hypotheses. So that assertion is not proved
here and no attribute claims it.

*The base.* The source takes `S` Noetherian. Everything below uses only that `S` is
quasi-compact and quasi-separated, which is what makes `X` and `Y` quasi-compact and
quasi-separated and so puts [Stacks, Tag 0A9E] and [Stacks, Tag 0A9I] in force; the statements
are made under that weaker hypothesis and apply in the source's situation by instance search.

## References

* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y) [IsProper f.left]

/-- **The upper shriek functor of a proper morphism preserves `D⁺`.** For a proper `f` the upper
shriek functor at the identity compactification is the right adjoint of `Rf_*`, and that right
adjoint carries bounded-below complexes with quasi-coherent cohomology to bounded-below
complexes with quasi-coherent cohomology by [Stacks, Tag 0A9I]. -/
theorem isBoundedBelow_upperShriek_properCompactification_obj
    (K : quasiCoherentDerivedCategory Y.left)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    DerivedCategoryB.IsBoundedBelow
      ((upperShriek f (properCompactification f)).obj K).obj :=
  DerivedCategoryB.isBoundedBelow_of_iso
    ((ObjectProperty.ι _).mapIso ((upperShriekProperIso f).app K)).symm
    (isBoundedBelow_twistedInverseImage_obj f.left K hK)

/-- **Stacks Project, Section 0AU3, clause (2), first assertion.** Let `S` be a quasi-compact
quasi-separated scheme (in the source, a Noetherian one) and let `f : X ⟶ Y` be a morphism of
`AlgebraicGeometry.FTS S`, the schemes separated and of finite type over `S`, whose underlying
morphism of schemes is proper. Then `f^!` is the restriction of the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` to `D⁺_QCoh(𝒪_Y)`: the upper shriek functor of
[Stacks, Tag 0A9Y] is a right adjoint of `Rf_*`, and it carries `D⁺_QCoh(𝒪_Y)` into
`D⁺_QCoh(𝒪_X)`.

Both conjuncts are needed for the clause: the first says `f^!` *is* the right adjoint, the second
says the restriction of that right adjoint to the bounded-below parts is defined. -/
@[stacks 0AU3 "clause (2), first assertion: for a proper morphism f^! is a right adjoint of Rf_* \
  and carries the bounded-below part of D_QCoh into the bounded-below part, so it is the \
  restriction of that right adjoint to D^+_QCoh. The f^! is Stacks.Duality.upperShriek at the \
  identity compactification, which is the one the source uses for a proper morphism; \
  independence of the compactification is Tag 0AA0, which in this repository still carries the \
  Tag 0A9L invertibility of Tag 0A9P. The SECOND assertion of clause (2), the duality \
  isomorphism Rf_* RHom(K, f^! M) = RHom(Rf_* K, M), is not claimed: its map is \
  Stacks.Duality.sheafyTrace and its invertibility is Tag 0GEW, which is open here"]
theorem upperShriek_isRightAdjointOnBoundedBelow_of_isProper :
    Nonempty (DerivedPushforward.qcqsRestrictedDerivedPushforward f.left ⊣
        upperShriek f (properCompactification f)) ∧
      ∀ K : quasiCoherentDerivedCategory Y.left, DerivedCategoryB.IsBoundedBelow K.obj →
        DerivedCategoryB.IsBoundedBelow
          ((upperShriek f (properCompactification f)).obj K).obj :=
  ⟨⟨upperShriekProperAdjunction f⟩, isBoundedBelow_upperShriek_properCompactification_obj f⟩

end Stacks.Duality

end
