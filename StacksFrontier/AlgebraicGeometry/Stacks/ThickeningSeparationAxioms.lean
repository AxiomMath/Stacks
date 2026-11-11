module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFppfCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IdentityCospan

/-!
# The separation axioms of a thickening of algebraic stacks (Stacks 0BPW)

Stacks 0BPW reads, verbatim:

> Let `𝒳 ⊂ 𝒳'` be a thickening of algebraic stacks. Then
> 1. `𝒳` is an algebraic space if and only if `𝒳'` is an algebraic space,
> 2. `𝒳` is a scheme if and only if `𝒳'` is a scheme,
> 3. `𝒳` is DM if and only if `𝒳'` is DM,
> 4. `𝒳` is quasi-DM if and only if `𝒳'` is quasi-DM,
> 5. `𝒳` is separated if and only if `𝒳'` is separated, and
> 6. `𝒳` is quasi-separated if and only if `𝒳'` is quasi-separated.

This file carries **one implication of each of clauses (1), (3), (4), (5) and (6)**: the
implication from the ambient stack `𝒳'` to the closed substack `𝒳`. That implication is the
base-change half of the source's argument and is proved here with no hypothesis beyond the
thickening.

For clauses (5) and (6) the **converse** implication is proved in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse`, which assembles the two
halves into the `if and only if` the source states; those two clauses are registered there, as
`AlgebraicGeometry.Stack.isSeparatedOver_iff_isThickening` and
`AlgebraicGeometry.Stack.isQuasiSeparatedOver_iff_isThickening`, and the two one-directional
statements below are the halves they are built from. For clauses (3) and (4) the converse is
proved in `StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford` — items (9) and
(8) of **Stacks 0CJ9** at the same viewing of a thickening as a morphism of thickenings over the
base — and those two clauses are registered there, as
`AlgebraicGeometry.Stack.isDMOver_iff_isThickening` and
`AlgebraicGeometry.Stack.isQuasiDMOver_iff_isThickening`, with the two one-directional
statements below again the easy halves. The converse implication of clause (1), and clause (2),
are **not** proved unconditionally; the implementation notes below name the missing input for
each. For clause (1) that input is now a single `Prop`:
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_iff_isThickening` in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford` proves the whole
equivalence with part (3) of **Stacks 04S6** as its one hypothesis, and carries no clause key
for that reason.

The thickening is the library's own notion `AlgebraicGeometry.Stack.IsThickening`
(**Stacks 0BPP**, part (1)): a closed immersion of algebraic stacks over `S` which is surjective
on points. Being an algebraic space is `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace`,
and the four separation axioms are `AlgebraicGeometry.Stack.IsDMOver`,
`AlgebraicGeometry.Stack.IsQuasiDMOver`, `AlgebraicGeometry.Stack.IsSeparatedOver` and
`AlgebraicGeometry.Stack.IsQuasiSeparatedOver` — parts (1)–(4) of **Stacks 050D**, the separation
axioms relative to the base scheme `S` of the site.

## Main definitions

* `AlgebraicGeometry.Stack.structureThickeningMorphism`: a thickening `i : 𝒳 ⟶ 𝒳'` of algebraic
  stacks over `S`, read as a morphism of thickenings
  `(𝒳 ⊂ 𝒳') → (S ⊂ S)` over the identity of the algebraic stack represented by `S`. This is the
  viewing the source's proof opens with, at the base of the site rather than at `Spec(ℤ)`.

## Main results

* `AlgebraicGeometry.Stack.isThickening_id_of_isRepresentableByAlgebraicSpace` and
  `AlgebraicGeometry.Stack.isThickening_id_schemeStack`: the identity 1-morphism of an algebraic
  stack which is representable by an algebraic space — in particular of the stack represented by
  an object of the site — is a thickening.
* `AlgebraicGeometry.Stack.isSeparated_inner_of_outer`,
  `AlgebraicGeometry.Stack.isQuasiSeparated_inner_of_outer`,
  `AlgebraicGeometry.Stack.isQuasiDM_inner_of_outer` and
  `AlgebraicGeometry.Stack.isDM_inner_of_outer`: for a morphism of thickenings of algebraic
  stacks, each of the four separation axioms of **Stacks 04YW** passes from the ambient
  1-morphism `f'` to the restricted 1-morphism `f`. These are the base-change halves of the
  properness, quasi-compactness, quasi-separatedness, local-quasi-finiteness and unramifiedness
  clauses of **Stacks 0BPV**.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isThickening`: **Stacks 0BPW**,
  clause (1), in the direction from the ambient stack to the closed substack.
* `AlgebraicGeometry.Stack.isDMOver_of_isThickening` and
  `AlgebraicGeometry.Stack.isQuasiDMOver_of_isThickening`: the same direction of clauses (3) and
  (4). These two carry no tag of their own: they are one half each of
  `AlgebraicGeometry.Stack.isDMOver_iff_isThickening` and
  `AlgebraicGeometry.Stack.isQuasiDMOver_iff_isThickening` in
  `StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford`, where the two clauses
  are registered as the full equivalences.
* `AlgebraicGeometry.Stack.isSeparatedOver_of_isThickening` and
  `AlgebraicGeometry.Stack.isQuasiSeparatedOver_of_isThickening`: the same direction of clauses
  (5) and (6). These two carry no tag of their own either: they are one half each of
  `AlgebraicGeometry.Stack.isSeparatedOver_iff_isThickening` and
  `AlgebraicGeometry.Stack.isQuasiSeparatedOver_iff_isThickening` in
  `StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse`, where the two clauses are
  registered as the full equivalences.
* `AlgebraicGeometry.Space.isClosedImmersion_id`: an identity morphism of presheaves on the big
  fppf site of `S` is a closed immersion of algebraic spaces.

## Implementation notes

**Where the content is.** Each of clauses (3)–(6) is a condition of Properties of Stacks,
Section 04XB, on the absolute diagonal, and the single input is that the diagonal of `𝒳` is a
*base change* of the diagonal of `𝒳'`: the diagonal square of **Stacks 0BPU** is cartesian, which
the library has fully proved as
`AlgebraicGeometry.Stack.isTwoFibreProduct_selfProductDiagonalSquare`. A condition of Stacks 04XB
is inherited by the projection of a 2-fibre-product square for an arbitrary property of morphisms
of algebraic spaces and with no hypothesis on that property — this is Stacks 045C in the longhand
form `AlgebraicGeometry.Stack.prop_baseChange_of_isTwoFibreProduct` — so the five transfers below
are that one statement at properness, quasi-compactness, quasi-separatedness, local
quasi-finiteness and unramifiedness. The representability conjunct of
`AlgebraicGeometry.Stack.IsDM` travels the same way, by
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange` at the same square.

Clause (1) does not go through the diagonal at all. Its ambient-to-substack direction is
**Stacks 04ZP**, the implication (1) ⟹ (2)
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`), applied to the
degenerate 2-fibre product `𝒳 = 𝒳' ×_{𝒳'} 𝒳` of
`CategoryTheory.Bicategory.TwoCommSq.idCospan`: a thickening is representable by algebraic spaces,
being a closed immersion, so the apex of that square is representable by an algebraic space as
soon as `𝒳'` is. Only the closed-immersion half of `IsThickening` is used, as in the source,
which deduces clause (1) from a condition on the diagonal; the two arguments are different and
this one is shorter.

**Why the statements are relative to the base scheme of the site.** The source reads clauses
(3)–(6) at the absolute separation axioms, parts (5)–(8) of Stacks 050D, which this library
defines by viewing an algebraic stack over `S` as one over `Spec(ℤ)`
(`AlgebraicGeometry.Stack.viewOverInt`, **Stacks 04X6**). Reading the statements below there
needs `AlgebraicGeometry.Stack.IsThickening` to be stable under that change of base, which the
library does not carry: `StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBaseQuantifier`
transports the *conditions* of Stacks 04XB across a change of base, but there is no
`isThickening_changeBase`, so the morphism of thickenings the argument needs over `Spec(ℤ)`
cannot be formed. The statements here are therefore at parts (1)–(4) of Stacks 050D, for an
arbitrary base scheme `S` of the site; clause (1) is unaffected, being a condition on `𝒳` alone.

*Clauses (3) and (4) do reach the absolute axioms, by a route that needs no such stability.*
Parts (1) and (2) of **Stacks 050N** are equivalences — an algebraic stack is DM exactly when it
is DM over the base scheme of its site, and likewise for quasi-DM — proved unconditionally as
`AlgebraicGeometry.Stack.isDMAbs_iff_isDMOver` and
`AlgebraicGeometry.Stack.isQuasiDMAbs_iff_isQuasiDMOver` in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationSourceOverBase`, so each side of the equivalence
over the base may simply be rewritten and the thickening is never viewed over `Spec(ℤ)` at all.
That gives `AlgebraicGeometry.Stack.isDMAbs_iff_isThickening` and
`AlgebraicGeometry.Stack.isQuasiDMAbs_iff_isThickening` in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford`, which carry the clause
keys at parts (5) and (6) of Stacks 050D beside the ones at parts (1) and (2). Clauses (5) and
(6) are **not** reachable this way: parts (3) and (4) of Stacks 050N are only the implications
from the absolute axiom to the axiom over the base, the converses failing for a base scheme whose
own diagonal over `Spec(ℤ)` is not separated. For those two the missing
`isThickening_changeBase` is still the obstruction.

**Where the converse implications are proved.** All four are the half of **Stacks 0BPV** that
moves a condition of Stacks 04XB from the restricted relative diagonal to the ambient one, and
all four are proved. For clauses (5) and (6) the route is
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse`: the factorisation
`Δ ≫ k ≅ i ≫ Δ'` of the diagonal square together with the cancellation of a surjective closed
immersion off the front of a composite at the level of morphisms of algebraic spaces.

Clauses (3) and (4) are the conditions of Stacks 04XB at
`AlgebraicGeometry.Space.IsUnramified` and `AlgebraicGeometry.Space.IsLocallyQuasiFinite`, and
for those two that cancellation is *false*: both notions contain being locally of finite type,
which a thickening of the source destroys. (Take `Spec(k) ⊂ Spec(R)` with `R` a `k`-algebra that
is not finitely generated and has nilpotent augmentation ideal: `Spec(k) → Spec(k)` is
unramified and locally quasi-finite, `Spec(R) → Spec(k)` is neither.) The source's Stacks 0BPV
sends exactly those clauses — its (k)–(q) — through **Stacks 0BPJ** instead, using the
*cartesian* diagonal square, and that is the route
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford` takes: it runs 0BPJ at
the §04XB point test, which yields items (8) and (9) of **Stacks 0CJ9** and hence clauses (3)
and (4) at the viewing of this file. Clause (5) escapes the cancellation problem by a different
device: properness splits off its locally-of-finite-type conjunct, which a relative diagonal has
unconditionally by part (2) of **Stacks 04XS**.

Clause (1) is not a condition on the diagonal in this library. The source reads it through
**Stacks 0AHJ** — an algebraic stack is an algebraic space exactly when its diagonal is a
monomorphism — and both reverse directions of 0AHJ, in
`StacksFrontier.AlgebraicGeometry.Stacks.HigherDiagonalMonomorphism`, carry the hypothesis named
`hrep` there, which is the implication (2) ⟹ (3) of **Stacks 04Y5**. The cancellation route of
clauses (5) and (6) does not reach clause (1) either: being a monomorphism does not cancel a
surjective closed immersion off the front of a composite — `Spec(k) ⟶ Spec(k[t]/t²) ⟶ Spec(k)`
is a monomorphism whose second factor is not one.

*Clause (1) is proved in full, elsewhere.*
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_iff_isThickening` of
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford` proves the whole
equivalence from item (12) of **Stacks 0CJ9** at
`AlgebraicGeometry.Stack.structureThickeningMorphism`, and carries the clause key for it. Of
item (12)'s two `hrep` hypotheses only the outer one is needed: in the direction that this file
does not prove the closed substack is already an algebraic space, so the inner one is free by
**Stacks 045G** (3) ⟹ (7). The outer one is
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`, proved
unconditionally, whose bootstrap input — part (3) of **Stacks 04S6**, the same `Prop` the
implication (1) ⟹ (3) of **Stacks 04SZ** rests on — is supplied by
`AlgebraicGeometry.Stack.bootstrap04S6Spaces`. The declaration tagged in this file proves only
the implication from the ambient stack to the closed substack, which is why its clause string
says so.

Clause (2) needs **Stacks 05ZR**, the scheme clause for a thickening of algebraic spaces, and
the converse of clause (1) on top of it; 05ZR is proved with no hypotheses as
`AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable` in
`StacksFrontier.AlgebraicGeometry.Spaces.ThickeningSchemeRepresentableClosedImmersion`. The notion
of an algebraic stack being a scheme needed to state the clause is
`Stacks.RepresentableMorphism.IsRepresentableCFG` (**Stacks 02Y3**), and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isRepresentableCFG`
of `StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceSources` is the step from
it to being an algebraic space, so the clause is statable; what is missing is only the two
geometric inputs. It is in fact stated and proved:
`AlgebraicGeometry.Stack.isRepresentableCFG_iff_isThickening` of
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSchemeStack` is the whole equivalence, with one
named hypothesis `hAffineCase`: the affine case of **Stacks 05ZR**, that an algebraic space
receiving a surjective closed immersion from an affine algebraic space is affine (the
closed-immersion case of **Stacks 07VS**). It has no clause key for that reason. The elementary
direction for algebraic *spaces* is
`AlgebraicGeometry.Space.isRepresentable_of_isThickening`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Scheme`), whose implementation notes record
the same obstruction.

**What Stacks 09ZY actually supplies.** Besides the
surjectivity clause of 09ZY in `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Morphisms`,
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed` carries parts (3), (4) and
the separated half of part (6) as genuine equivalences for a morphism of thickenings of
algebraic spaces, in exactly the shape the converse needs, and
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.QuasiSeparatedTransfer` adds the
quasi-separated half of part (6). Those four are what the converse implications of clauses (5)
and (6) consume at the level of algebraic spaces.

**The identity thickening.** `AlgebraicGeometry.Stack.isThickening_id_schemeStack` is needed only
to form `AlgebraicGeometry.Stack.structureThickeningMorphism`, whose second thickening is the
identity of the stack represented by `S`. It is proved the way
`AlgebraicGeometry.Stack.isRelativelySmooth_id` is: for a stack representable by an algebraic
space `F` the condition of Stacks 04XB is the corresponding property of the induced morphism of
representing presheaves (`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`),
the identity induces the identity of `F` (`AlgebraicGeometry.Stack.representingMap_id`), and the
identity is a closed immersion. The locality instance that bridge asks for is **Stacks 0420** in
its fppf form, obtained from `AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fpqc`.
Surjectivity on points is `AlgebraicGeometry.Stack.isSurjective_id`.

## References

* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04X6](https://stacks.math.columbia.edu/tag/04X6)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0BPU](https://stacks.math.columbia.edu/tag/0BPU)
* [Stacks Project, Tag 0BPV](https://stacks.math.columbia.edu/tag/0BPV)
* [Stacks Project, Tag 0BPW](https://stacks.math.columbia.edu/tag/0BPW)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An identity morphism of presheaves is a closed immersion of algebraic spaces.** Being a
closed immersion (**Stacks 02YU**, part (3)) is the `CategoryTheory.MorphismProperty.presheaf`
construction at the inverse image of `AlgebraicGeometry.IsClosedImmersion` along the forgetful
functor to schemes, and `AlgebraicGeometry.presheaf_of_isIso` reduces it, for an isomorphism of
presheaves, to the property holding for isomorphisms of the site — which it does, an isomorphism
of schemes being a closed immersion. -/
theorem isClosedImmersion_id (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsClosedImmersion B S hS (𝟙 F) := by
  refine _root_.AlgebraicGeometry.presheaf_of_isIso B S hS _ ?_ (𝟙 F) inferInstance
  intro X Y a ha
  have := ha
  change AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map a)
  infer_instance

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The identity 1-morphism of a represented algebraic stack is a thickening -/

/-- **The identity of an algebraic stack representable by an algebraic space is a thickening.**
Both halves of **Stacks 0BPP**, part (1), hold: the closed-immersion condition of Stacks 04XB
becomes, through
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap` and
`AlgebraicGeometry.Stack.representingMap_id`, the statement that the identity of the representing
presheaf is a closed immersion of algebraic spaces, and surjectivity on points is
`AlgebraicGeometry.Stack.isSurjective_id`.

The locality instance the bridge asks for is **Stacks 0420** restricted to the fppf precoverage,
obtained from `AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fpqc`; it is produced
here rather than hypothesised, so the statement carries no instance argument. -/
theorem isThickening_id_of_isRepresentableByAlgebraicSpace
    (𝒰 : AlgebraicStacks.{u, w} B S hS)
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰.val) :
    IsThickening (𝟙 𝒰) := by
  have _hloc : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    have := Space.isClosedImmersion_isLocalAtTarget_fpqc.{u, u} B S hS
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  obtain ⟨F, hF, ⟨eF⟩⟩ := h𝒰
  have hrep := isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
    (𝟙 𝒰.val) ⟨F, hF, ⟨eF⟩⟩ ⟨F, hF, ⟨eF⟩⟩
  refine ⟨⟨hrep, ?_⟩, isSurjective_id B S hS 𝒰⟩
  refine (isClosedImmersion_iff_hasRelativeProperty B S hS (𝟙 𝒰.val) hrep).2 ?_
  refine (hasRelativeProperty_iff_prop_representingMap B S hS
    (Space.closedImmersionProperty B S hS) (𝟙 𝒰.val) hrep F F hF hF eF eF).2 ?_
  rw [representingMap_id]
  exact Space.isClosedImmersion_id B S hS F

/-- **The identity of the algebraic stack represented by an object of the site is a thickening.**
A represented category fibred in groupoids is representable by an algebraic space
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory`), so
`AlgebraicGeometry.Stack.isThickening_id_of_isRepresentableByAlgebraicSpace` applies. -/
theorem isThickening_id_schemeStack (U : BigFppfOver B S hS) :
    IsThickening (𝟙 (schemeStack.{u, w} B S hS U)) :=
  isThickening_id_of_isRepresentableByAlgebraicSpace.{u, w} B S hS _
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)

/-! ### A thickening as a morphism of thickenings over the base -/

section StructureThickening

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- **A thickening of algebraic stacks over `S`, read as a morphism of thickenings over the
base.** For a thickening `i : 𝒳 ⟶ 𝒳'` the pair of structure morphisms is a morphism of
thickenings `(𝒳 ⊂ 𝒳') → (S ⊂ S)`, the target thickening being the identity of the algebraic
stack represented by `S` (`AlgebraicGeometry.Stack.isThickening_id_schemeStack`). The restriction
square commutes on the nose, by naturality of the structure morphism
(`AlgebraicGeometry.Stack.comp_structureMorphism`), so its filler is an `eqToIso`.

This is the viewing the source's proof of **Stacks 0BPW** opens with — there at `Spec(ℤ)`, here
at the base scheme of the site; see the implementation notes of this file. -/
def structureThickeningMorphism (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    ThickeningMorphism i (𝟙 (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))) hi
      (isThickening_id_schemeStack.{u, w} B S hS _) where
  outer := structureMorphism B S hS 𝒳'
  inner := structureMorphism B S hS 𝒳
  comm := eqToIso (by rw [Category.comp_id, comp_structureMorphism])

end StructureThickening

/-! ### The separation axioms along a morphism of thickenings -/

section Diagonal

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
  (m : ThickeningMorphism i j hi hj)

/-- The condition of Stacks 04XB that the relative diagonal of `f` has property `P`. -/
private abbrev DiagonalHasProp (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
    (_hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p =
      Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
          (CatFiberedInGroupoids.homFunctor
            (AlgebraicStacks.relativeDiagonal B S hS f).hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))

/-- A property of the relative diagonal passes from the ambient 1-morphism of a morphism of
thickenings to the restricted one, since the diagonal is a base change. -/
private theorem diagonalHasProp_inner_of_outer (P : MorphismProperty (AlgebraicSpaces B S hS))
    (h : DiagonalHasProp B S hS P m.outer) : DiagonalHasProp B S hS P m.inner :=
  prop_baseChange_of_isTwoFibreProduct.{u, u, u} B S hS P 𝒳'.val _ _
    (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
    (selfProductDiagonalMap B S hS m).hom
    (AlgebraicStacks.toCatFiberedInGroupoids B S hS (selfProductDiagonalSquare B S hS m))
    (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS _
      (isTwoFibreProduct_selfProductDiagonalSquare B S hS m)) h

/-- **Representability by algebraic spaces passes from the ambient relative diagonal to the
restricted one.** For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` the diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is a base change of `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` — the second assertion of
**Stacks 0BPU**, `AlgebraicGeometry.Stack.isTwoFibreProduct_selfProductDiagonalSquare` — and
representability by algebraic spaces is stable under base change (**Stacks 0302**). -/
theorem isRepresentableByAlgebraicSpaces_relativeDiagonal_inner_of_outer
    (h : IsRepresentableByAlgebraicSpaces B S hS
      (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom.hom) :
    IsRepresentableByAlgebraicSpaces B S hS
      (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom.hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, u, u} B S hS 𝒳'.val _ _
    (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
    (selfProductDiagonalMap B S hS m).hom
    (AlgebraicStacks.toCatFiberedInGroupoids B S hS (selfProductDiagonalSquare B S hS m))
    (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS _
      (isTwoFibreProduct_selfProductDiagonalSquare B S hS m)) h

/-- **Separatedness passes from the ambient 1-morphism of a morphism of thickenings to the
restricted one.** If `f' : 𝒳' ⟶ 𝒴'` is separated in the sense of **Stacks 04YW** then so is
`f : 𝒳 ⟶ 𝒴`: the diagonal of `f` is a base change of the diagonal of `f'` by the second
assertion of **Stacks 0BPU**, and properness in the sense of Stacks 04XB is stable under base
change (`AlgebraicGeometry.Stack.prop_baseChange_of_isTwoFibreProduct`).

This is the base-change half of the properness clause (q) of **Stacks 0BPV**. -/
theorem isSeparated_inner_of_outer (h : AlgebraicStacks.IsSeparated B S hS m.outer) :
    AlgebraicStacks.IsSeparated B S hS m.inner :=
  diagonalHasProp_inner_of_outer B S hS m (fun _ _ f => Space.IsProper B S hS f.hom) h

/-- **Quasi-separatedness passes from the ambient 1-morphism of a morphism of thickenings to the
restricted one.** The companion of `AlgebraicGeometry.Stack.isSeparated_inner_of_outer` at the
two conditions quasi-separatedness of **Stacks 04YW** is the conjunction of: quasi-compactness
and quasi-separatedness of the diagonal, each inherited by the base change.

This is the base-change half of clauses (d) and (g) of **Stacks 0BPV**. -/
theorem isQuasiSeparated_inner_of_outer (h : AlgebraicStacks.IsQuasiSeparated B S hS m.outer) :
    AlgebraicStacks.IsQuasiSeparated B S hS m.inner :=
  ⟨diagonalHasProp_inner_of_outer B S hS m (fun _ _ f => Space.IsQuasiCompact B S hS f.hom) h.1,
    diagonalHasProp_inner_of_outer B S hS m (fun _ _ f => Space.IsQuasiSeparated B S hS f.hom) h.2⟩

/-- **The quasi-DM condition passes from the ambient 1-morphism of a morphism of thickenings to
the restricted one.** The companion of `AlgebraicGeometry.Stack.isSeparated_inner_of_outer` at
local quasi-finiteness of the diagonal, which is quasi-DM-ness in **Stacks 04YW**.

This is the base-change half of clause (k) of **Stacks 0BPV**. -/
theorem isQuasiDM_inner_of_outer (h : AlgebraicStacks.IsQuasiDM B S hS m.outer) :
    AlgebraicStacks.IsQuasiDM B S hS m.inner :=
  diagonalHasProp_inner_of_outer B S hS m
    (fun _ _ f => Space.IsLocallyQuasiFinite B S hS f.hom) h

/-- **The DM condition passes from the ambient 1-morphism of a morphism of thickenings to the
restricted one.** Both conjuncts of `AlgebraicGeometry.Stack.IsDM` are inherited by the base
change of the diagonal: representability by algebraic spaces by
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_inner_of_outer`, and
unramifiedness in the sense of Stacks 04XB by
`AlgebraicGeometry.Stack.prop_baseChange_of_isTwoFibreProduct`.

This is the base-change half of clause (m) of **Stacks 0BPV**. -/
theorem isDM_inner_of_outer (h : IsDM B S hS m.outer) : IsDM B S hS m.inner :=
  ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_inner_of_outer B S hS m h.choose,
    diagonalHasProp_inner_of_outer B S hS m (fun _ _ f => Space.IsUnramified B S hS f.hom)
      h.choose_spec⟩

end Diagonal

/-! ### Stacks 0BPW -/

section Thickening

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0BPW, clause (1), from the ambient stack to the closed substack.** If `𝒳 ⊂ 𝒳'` is a
thickening of algebraic stacks over `S` and `𝒳'` is an algebraic space, then so is `𝒳`.

The thickening `i` is a closed immersion, hence representable by algebraic spaces, and `𝒳` is the
apex of the degenerate 2-fibre product `𝒳' ×_{𝒳'} 𝒳` of
`CategoryTheory.Bicategory.TwoCommSq.idCospan`; so **Stacks 04ZP**, the implication (1) ⟹ (2)
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`), applies. Only
the closed-immersion half of `AlgebraicGeometry.Stack.IsThickening` is used. -/
@[stacks 0BPW "clause (1): algebraic space -- only part of the clause, namely the implication \
from the ambient stack to the closed substack; the whole equivalence is \
AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_iff_isThickening"]
theorem isRepresentableByAlgebraicSpace_of_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i)
    (h : IsRepresentableByAlgebraicSpace B S hS 𝒳'.val) :
    IsRepresentableByAlgebraicSpace B S hS 𝒳.val :=
  isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS
    𝒳.val 𝒳'.val 𝒳'.val i.hom (𝟙 𝒳'.val)
    (Bicategory.TwoCommSq.idCospan i.hom) (Bicategory.isTwoFibreProduct_idCospan i.hom)
    hi.1.1 h

/-- **One half of Stacks 0BPW, clause (3).** If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks
over `S` and `𝒳'` is DM over `S`, then so is `𝒳`.

The thickening is read as a morphism of thickenings over the base
(`AlgebraicGeometry.Stack.structureThickeningMorphism`) and
`AlgebraicGeometry.Stack.isDM_inner_of_outer` applies to it. The separation axiom is part (1) of
**Stacks 050D**, DM over the base scheme of the site; see the implementation notes of this file
for why the statement is not at the absolute form, part (5).

Untagged: the clause itself is the equivalence
`AlgebraicGeometry.Stack.isDMOver_iff_isThickening` in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford`, which is item (9) of
**Stacks 0CJ9** at the same viewing and carries the part key. -/
@[stacks 0BPW "clause (3): DM over the base -- only part of the clause, namely the \
implication from the ambient stack to the closed substack; the whole equivalence is \
AlgebraicGeometry.Stack.isDMOver_iff_isThickening"]
theorem isDMOver_of_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i)
    (h : IsDMOver B S hS 𝒳') : IsDMOver B S hS 𝒳 :=
  isDM_inner_of_outer B S hS (structureThickeningMorphism B S hS i hi) h

/-- **One half of Stacks 0BPW, clause (4).** If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks
over `S` and `𝒳'` is quasi-DM over `S`, then so is `𝒳`. The companion of
`AlgebraicGeometry.Stack.isDMOver_of_isThickening` at part (2) of **Stacks 050D**.

Untagged: the clause itself is the equivalence
`AlgebraicGeometry.Stack.isQuasiDMOver_iff_isThickening` in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford`, which is item (8) of
**Stacks 0CJ9** at the same viewing and carries the part key. -/
@[stacks 0BPW "clause (4): quasi-DM over the base -- only part of the clause, namely the \
implication from the ambient stack to the closed substack; the whole equivalence is \
AlgebraicGeometry.Stack.isQuasiDMOver_iff_isThickening"]
theorem isQuasiDMOver_of_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i)
    (h : IsQuasiDMOver B S hS 𝒳') : IsQuasiDMOver B S hS 𝒳 :=
  isQuasiDM_inner_of_outer B S hS (structureThickeningMorphism B S hS i hi) h

/-- **One half of Stacks 0BPW, clause (5).** If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over
`S` and `𝒳'` is separated over `S`, then so is `𝒳`. The companion of
`AlgebraicGeometry.Stack.isDMOver_of_isThickening` at part (3) of **Stacks 050D**.

Untagged: the clause itself is the equivalence
`AlgebraicGeometry.Stack.isSeparatedOver_iff_isThickening` in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse`, which is built from this
implication and its converse and carries the part key. -/
@[stacks 0BPW "clause (5): separated over the base -- only part of the clause, namely the \
implication from the ambient stack to the closed substack; the whole equivalence is \
AlgebraicGeometry.Stack.isSeparatedOver_iff_isThickening"]
theorem isSeparatedOver_of_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i)
    (h : IsSeparatedOver B S hS 𝒳') : IsSeparatedOver B S hS 𝒳 :=
  isSeparated_inner_of_outer B S hS (structureThickeningMorphism B S hS i hi) h

/-- **One half of Stacks 0BPW, clause (6).** If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over
`S` and `𝒳'` is quasi-separated over `S`, then so is `𝒳`. The companion of
`AlgebraicGeometry.Stack.isDMOver_of_isThickening` at part (4) of **Stacks 050D**.

Untagged: the clause itself is the equivalence
`AlgebraicGeometry.Stack.isQuasiSeparatedOver_iff_isThickening` in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse`, which is built from this
implication and its converse and carries the part key. -/
@[stacks 0BPW "clause (6): quasi-separated over the base -- only part of the clause, namely \
the implication from the ambient stack to the closed substack; the whole equivalence is \
AlgebraicGeometry.Stack.isQuasiSeparatedOver_iff_isThickening"]
theorem isQuasiSeparatedOver_of_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i)
    (h : IsQuasiSeparatedOver B S hS 𝒳') : IsQuasiSeparatedOver B S hS 𝒳 :=
  isQuasiSeparated_inner_of_outer B S hS (structureThickeningMorphism B S hS i hi) h

end Thickening

end AlgebraicGeometry.Stack

end
