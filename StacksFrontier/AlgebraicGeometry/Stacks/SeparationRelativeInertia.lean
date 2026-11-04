module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.HigherDiagonalSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalSeparatednessRelativeInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE

/-!
# Stacks 0CL0, parts (1) and (2): the relative inertia detects separatedness of the diagonal

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`. Parts (1) and (2) of **Stacks 0CL0** each assert the equivalence of
three conditions, all in the relative sense of Properties of Stacks, Section 04XB:

* **(1)** (a) the relative inertia projection `π : I_{𝒳/𝒴} ⟶ 𝒳` is separated; (b) the first
  relative diagonal `Δ_{f, 1} = Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is separated; (c)
  `Δ_{f, 2} = e : 𝒳 ⟶ I_{𝒳/𝒴}`, the neutral section of the relative inertia, is a closed
  immersion;
* **(2)** (a) `π` is quasi-separated; (b) `Δ_f` is quasi-separated; (c) `e` is quasi-compact.

Part (3), the locally separated member of the same family, is
`StacksFrontier/AlgebraicGeometry/Stacks/LocalSeparatednessRelativeInertia.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/SecondRelativeDiagonalInertia.lean`; parts (4) and (5) are
`StacksFrontier/AlgebraicGeometry/Stacks/DeligneMumfordRelativeInertia.lean`. Nothing in those files
is changed here.

## The route, and why the group law is not needed

The source proves (a) ⇔ (c) by choosing a surjective smooth 1-morphism from an algebraic space
`U`, forming `G = U ×_𝒳 I_{𝒳/𝒴}` as a *group* algebraic space over `U` (Stacks 050Q, with the
composition law of Remark 050R) and citing Groupoids in Spaces, Lemma **06P6** — that a group
algebraic space is separated, quasi-separated, locally separated over its base exactly when its
identity section is a closed immersion, quasi-compact, an immersion. **That route is not taken
here, and it is not needed.** Both parts go the way part (3) already goes, which needs no group
law at all:

* `π` **is** a base change of `Δ_f`: the relative inertia is the 2-fibre product of `Δ_f` with
  itself (Stacks 034H, part (1)) and `π` is the first projection of that square. So Stacks 045C,
  in the hypothesis-free form `AlgebraicGeometry.Stack.relativeProperty_baseChange`, carries any
  property of morphisms of algebraic spaces from `Δ_f` to `π`. That is (b) ⇒ (a).
* `Δ_{f, 2}` **is a section** of that projection — strictly, `Δ_{f,2} ≫ pr₁ = 𝟙 𝒳` holds by
  `rfl`. A section of a separated 1-morphism is a closed immersion, and a section of a
  quasi-separated one is quasi-compact; Stacks 04YS and 04YT read at `Δ_f` turn those back into
  (b). That is (a) ⇒ (b).
* (b) ⇔ (c) is Stacks 04YZ, parts (1) and (2) — Stacks 04YS and 04YT read at `Δ_f` rather than
  at `f` — composed with the identification of `Δ_{f, 2}` with the neutral section `e` supplied
  by `StacksFrontier.AlgebraicGeometry.Stacks.SecondRelativeDiagonalInertia`. This is what the
  source means by *"since `Δ_{f, 2}` is the diagonal of `Δ_f` we have (b) ⇔ (c) by definition"*.

So all three conditions of each part are proved equivalent outright, with no hypothesis beyond
`f` being a 1-morphism of algebraic stacks, and Groupoids in Spaces — Chapter 78, with no
library site — is not used.

## Main results

* `AlgebraicGeometry.Stack.isSeparated_relativeInertiaProjection_iff_relativeDiagonal`:
  **Stacks 0CL0, part (1), (a) ⇔ (b)**.
* `AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_iff_isClosedImmersion_neutralSection`:
  **Stacks 0CL0, part (1), (b) ⇔ (c)**.
* `AlgebraicGeometry.Stack.isQuasiSeparated_relativeInertiaProjection_iff_relativeDiagonal`:
  **Stacks 0CL0, part (2), (a) ⇔ (b)**.
* `AlgebraicGeometry.Stack.isQuasiSeparated_relativeDiagonal_iff_isQuasiCompact_neutralSection`:
  **Stacks 0CL0, part (2), (b) ⇔ (c)**.
* `AlgebraicGeometry.Stack.isClosedImmersion_section_of_isSeparated`: a section of a separated
  1-morphism representable by algebraic spaces is a closed immersion, and
  `AlgebraicGeometry.Stack.isRelativelyQuasiCompact_section_of_isQuasiSeparated` the
  quasi-separated analogue.
* `AlgebraicGeometry.Stack.isSeparated_relativeInertiaProjection_iff_twoFibreProductFst` and
  `AlgebraicGeometry.Stack.isQuasiSeparated_relativeInertiaProjection_iff_twoFibreProductFst`:
  the identification of each condition (a) with the same condition on the first projection of
  the 2-fibre product of `Δ_f` with itself.

## Implementation notes

The closed-immersion instances of the three hypothesis-free transfers — a section is its own
graph up to an equivalence (`AlgebraicGeometry.Stack.relativeProperty_section_of_graph`), a
graph is the comparison 1-morphism of Stacks 050H up to an equivalence
(`AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison`), and that comparison is a base
change of the relative diagonal of the structure 1-morphism — are proved here. They are the
siblings of the immersion instances in
`StacksFrontier.AlgebraicGeometry.Stacks.LocalSeparatednessRelativeInertia` and of the
quasi-compact instances in
`StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalPermanence`, and each is a single
application of a transfer stated for an arbitrary property with no hypothesis on it.

The quasi-compact instances are *not* re-proved: the chain ending in
`AlgebraicGeometry.Stack.isRelativelyQuasiCompact_section_of_isQuasiCompact_relativeDiagonal`
is already proved, so part (2) only needs it composed with Stacks 04YT.

Neither `AlgebraicGeometry.Stack.isClosedImmersion_section_of_isSeparated` nor
`AlgebraicGeometry.Stack.isRelativelyQuasiCompact_section_of_isQuasiSeparated` carries a
`@[stacks]` attribute. Stacks 050J collects what a section inherits from its morphism, and its
part (4) gives *properness* from separatedness, not closed immersion — the closed-immersion
statement is the composite of that with Stacks 04YS and is an assertion of no tag of the source;
the same reasoning is already recorded at the immersion instance in
`StacksFrontier.AlgebraicGeometry.Stacks.LocalSeparatednessRelativeInertia`. Part (5) of Stacks 050J
does give quasi-compactness from quasi-separatedness, but under the hypothesis on the morphism
that the untagged
`AlgebraicGeometry.Stack.isRelativelyQuasiCompact_section_of_isQuasiCompact_relativeDiagonal`
already restates on the diagonal, so that tag is not claimed here either.

Conditions (1)(c) and (2)(c) are stated at different levels of the tower, and that is the
source's own asymmetry rather than a choice: being a closed immersion of algebraic stacks is
part (2) of Stacks 04YL, a conjunction of representability by algebraic spaces with the
Section 04XB predicate, so (1)(c) is `AlgebraicGeometry.Stack.AlgebraicStacks.IsClosedImmersion`
and its representability conjunct transports by
`Stack.isRepresentableByAlgebraicSpaces_secondRelativeDiagonal_iff_neutralSection`;
quasi-compactness is not one of the three parts of Stacks 04YL, so (2)(c) is the bare
Section 04XB predicate `AlgebraicGeometry.Stack.IsQuasiCompact`.

The two conditions (b) are written as the Section 04XB predicates `IsSeparated` and
`IsQuasiSeparated` of the relative diagonal, not as Definition 04YW separatedness and
quasi-separatedness of `f` — those are *different statements* about different 1-morphisms, and
the bridges between the absolute and relative notions are the ones
`StacksFrontier.AlgebraicGeometry.Stacks.HigherDiagonalSeparation` records this library as not
having.

`AlgebraicGeometry.Stack.relativeDiagonal` is written `.{u, u, u + 1}` at every term occurrence,
for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.SecondRelativeDiagonalInertia`: without the pin its three
universe arguments are not determined by the explicit arguments.
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences` is applied with its two
`CategoryTheory.Functor.IsEquivalence` arguments given explicitly, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.LocalSeparatednessRelativeInertia`: the source of the
comparison 1-morphism is a reducible abbreviation while the statement spells it with a `def`, so
instance search does not see through the mismatch.

## References

* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
* [Stacks Project, Tag 034H](https://stacks.math.columbia.edu/tag/034H)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 04YT](https://stacks.math.columbia.edu/tag/04YT)
* [Stacks Project, Tag 04YZ](https://stacks.math.columbia.edu/tag/04YZ)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 050J](https://stacks.math.columbia.edu/tag/050J)
* [Stacks Project, Tag 06P6](https://stacks.math.columbia.edu/tag/06P6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A section of a separated 1-morphism is a closed immersion -/

section Section

variable {𝒳 𝒴 𝒵 𝒯 : AlgebraicStacks.{u, w} B S hS}

/-- **The comparison 1-morphism of Stacks 050H is a closed immersion as soon as the relative
diagonal of `h` is.** The comparison `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is a base change of `Δ_h` by
Stacks 04Z1, and Stacks 045C in the hypothesis-free form
`AlgebraicGeometry.Stack.relativeProperty_baseChange` carries being a closed immersion across
that square.

This is the sibling at closed immersions of
`AlgebraicGeometry.Stack.isImmersion_comparison_of_isImmersion_relativeDiagonal`, and the
hypothesis is on `Δ_h` rather than on `h` because that is the form Stacks 04YS delivers. -/
theorem isClosedImmersion_comparison_of_isClosedImmersion_relativeDiagonal
    (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hh : IsClosedImmersion B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val h.hom)) :
    IsClosedImmersion B S hS (comparison B S hS f g h).hom :=
  fun U y hy F hF he =>
    relativeProperty_baseChange.{u, u, u + 1} B S hS
      (fun _ _ k => Space.IsClosedImmersion B S hS k.hom)
      𝒵.val (twoFibreProductAlgebraicStack B S hS h h).val
      (twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h)).val
      (relativeDiagonalAlgebraicStacks B S hS h).hom
      (comparisonCospanRight B S hS f g h).hom
      (comparisonSquare B S hS f g h)
      (isTwoFibreProduct_comparisonSquare B S hS f g h) hh U y hy F hF he

/-- **The graph of `g : 𝒳 ⟶ 𝒴` over `𝒯` is a closed immersion as soon as the relative diagonal
of `q : 𝒴 ⟶ 𝒯` is.** The graph is identified with the comparison 1-morphism of the previous
result by `AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison`, which transfers any
property with no hypothesis on it.

This is the sibling at closed immersions of
`AlgebraicGeometry.Stack.isImmersion_graph_of_isImmersion_relativeDiagonal`. -/
theorem isClosedImmersion_graph_of_isClosedImmersion_relativeDiagonal
    (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q)
    (hq : IsClosedImmersion B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val 𝒯.val q.hom)) :
    IsClosedImmersion B S hS (graph B S hS g p q η).hom :=
  relativeProperty_graph_of_comparison B S hS
    (fun _ _ k => Space.IsClosedImmersion B S hS k.hom) g p q η
    (isClosedImmersion_comparison_of_isClosedImmersion_relativeDiagonal B S hS g (𝟙 𝒴) q hq)

/-- **A section of `f : 𝒳 ⟶ 𝒯` is a closed immersion as soon as the relative diagonal of `f`
is.** A section is its own graph up to an equivalence, and
`AlgebraicGeometry.Stack.relativeProperty_section_of_graph` carries any property across that
identification with no hypothesis on it.

This is the sibling at closed immersions of
`AlgebraicGeometry.Stack.isImmersion_section_of_isImmersion_relativeDiagonal`. -/
theorem isClosedImmersion_section_of_isClosedImmersion_relativeDiagonal
    (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : IsClosedImmersion B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒯.val f.hom)) :
    IsClosedImmersion B S hS s.hom := by
  obtain ⟨η⟩ := hs
  exact relativeProperty_section_of_graph B S hS
    (fun _ _ k => Space.IsClosedImmersion B S hS k.hom) f s η
    (isClosedImmersion_graph_of_isClosedImmersion_relativeDiagonal B S hS s (𝟙 𝒯) f η.symm hf)

/-- **A section of a separated 1-morphism is a closed immersion.** Let `f : 𝒳 ⟶ 𝒯` be a
1-morphism of algebraic stacks over `S` which is representable by algebraic spaces and
separated in the relative sense of Properties of Stacks, Section 04XB. Then every section of
`f` is a closed immersion in that sense.

Stacks 04YS turns separatedness of `f` into `Δ_f` being a closed immersion, and
`AlgebraicGeometry.Stack.isClosedImmersion_section_of_isClosedImmersion_relativeDiagonal`
concludes. Stacks 050J, part (4), states the weaker conclusion that such a section is proper,
so this is an assertion of no tag of the source. -/
theorem isClosedImmersion_section_of_isSeparated
    (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (h : IsSeparated B S hS f.hom) :
    IsClosedImmersion B S hS s.hom :=
  isClosedImmersion_section_of_isClosedImmersion_relativeDiagonal B S hS f s hs
    ((isSeparated_iff_isClosedImmersion_relativeDiagonal B S hS f hf).mp h)

/-- **A section of a quasi-separated 1-morphism is quasi-compact.** Let `f : 𝒳 ⟶ 𝒯` be a
1-morphism of algebraic stacks over `S` which is representable by algebraic spaces and
quasi-separated in the relative sense of Properties of Stacks, Section 04XB. Then every section
of `f` is quasi-compact in that sense.

Stacks 04YT turns quasi-separatedness of `f` into `Δ_f` being quasi-compact, and
`AlgebraicGeometry.Stack.isRelativelyQuasiCompact_section_of_isQuasiCompact_relativeDiagonal`
concludes. -/
theorem isRelativelyQuasiCompact_section_of_isQuasiSeparated
    (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (h : IsQuasiSeparated B S hS f.hom) :
    IsQuasiCompact B S hS s.hom :=
  isRelativelyQuasiCompact_section_of_isQuasiCompact_relativeDiagonal B S hS f s hs
    ((isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS f hf).mpr h)

end Section

/-! ### Stacks 0CL0, parts (1) and (2) -/

section Inertia

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The relative inertia projection has a relative property exactly when the first projection of
the 2-fibre product of `Δ_f` with itself does. -/
private theorem relativeProperty_relativeInertiaProjection_iff
    (P : MorphismProperty (AlgebraicSpaces B S hS)) (f : 𝒳 ⟶ 𝒴) :
    RelativeProperty B S hS P (relativeInertiaProjection B S hS f).hom ↔
      RelativeProperty B S hS P
        (twoFibreProductSquareAlgebraicStacks B S hS
          (relativeDiagonalAlgebraicStacks B S hS f)
          (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom :=
  ⟨@relativeProperty_of_equivalences B S hS _ _ _ _ P
      (twoFibreProductSquareAlgebraicStacks B S hS
        (relativeDiagonalAlgebraicStacks B S hS f)
        (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom.hom
      (relativeInertiaProjection B S hS f).hom.hom
      (secondRelativeDiagonalToRelativeInertia B S hS f.hom).hom
      (BasedFunctor.id 𝒳.val.val) (eqToIso rfl)
      (isEquivalence_secondRelativeDiagonalToRelativeInertia B S hS f.hom)
      (isEquivalence_basedFunctorId B S hS 𝒳.val),
    @relativeProperty_of_equivalences B S hS _ _ _ _ P
      (relativeInertiaProjection B S hS f).hom.hom
      (twoFibreProductSquareAlgebraicStacks B S hS
        (relativeDiagonalAlgebraicStacks B S hS f)
        (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom.hom
      (relativeInertiaToSecondRelativeDiagonal B S hS f.hom).hom
      (BasedFunctor.id 𝒳.val.val) (eqToIso rfl)
      (isEquivalence_relativeInertiaToSecondRelativeDiagonal B S hS f.hom)
      (isEquivalence_basedFunctorId B S hS 𝒳.val)⟩

/-- A relative property of `Δ_f` passes to the first projection of the 2-fibre product of `Δ_f`
with itself, which is a base change of `Δ_f`. -/
private theorem relativeProperty_twoFibreProductFst_of_relativeDiagonal
    (P : MorphismProperty (AlgebraicSpaces B S hS)) (f : 𝒳 ⟶ 𝒴)
    (h : RelativeProperty B S hS P (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)) :
    RelativeProperty B S hS P
      (twoFibreProductSquareAlgebraicStacks B S hS
        (relativeDiagonalAlgebraicStacks B S hS f)
        (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom :=
  relativeProperty_baseChange.{u, u, u + 1} B S hS P
      𝒳.val (twoFibreProductAlgebraicStack B S hS f f).val 𝒳.val
      (relativeDiagonalAlgebraicStacks B S hS f).hom
      (relativeDiagonalAlgebraicStacks B S hS f).hom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (relativeDiagonalAlgebraicStacks B S hS f).hom
        (relativeDiagonalAlgebraicStacks B S hS f).hom)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (relativeDiagonalAlgebraicStacks B S hS f).hom
        (relativeDiagonalAlgebraicStacks B S hS f).hom) h

/-- **Condition (a) of part (1) of Stacks 0CL0 is a condition on a base change of `Δ_f`.** The
relative inertia projection `π : I_{𝒳/𝒴} ⟶ 𝒳` is separated in the sense of Properties of
Stacks, Section 04XB exactly when the first projection of the 2-fibre product of `Δ_f` with
itself is.

This is Stacks 0457 for the relative property of Stacks 03YK, in the hypothesis-free form
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, applied along the comparison
1-morphism `AlgebraicGeometry.Stack.secondRelativeDiagonalToRelativeInertia` in one direction
and along its quasi-inverse in the other. Both 2-commutativity data are `eqToIso rfl`: the
comparison composed with `π` **is** the first projection, and the quasi-inverse composed with
the first projection **is** `π`. -/
theorem isSeparated_relativeInertiaProjection_iff_twoFibreProductFst (f : 𝒳 ⟶ 𝒴) :
    IsSeparated B S hS (relativeInertiaProjection B S hS f).hom ↔
      IsSeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS
          (relativeDiagonalAlgebraicStacks B S hS f)
          (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom :=
  relativeProperty_relativeInertiaProjection_iff B S hS (Space.separatedProperty B S hS) f

/-- **Condition (a) of part (2) of Stacks 0CL0 is a condition on a base change of `Δ_f`.** The
relative inertia projection `π : I_{𝒳/𝒴} ⟶ 𝒳` is quasi-separated in the sense of Properties of
Stacks, Section 04XB exactly when the first projection of the 2-fibre product of `Δ_f` with
itself is. The proof is that of
`AlgebraicGeometry.Stack.isSeparated_relativeInertiaProjection_iff_twoFibreProductFst` at the
packaged property of quasi-separatedness. -/
theorem isQuasiSeparated_relativeInertiaProjection_iff_twoFibreProductFst (f : 𝒳 ⟶ 𝒴) :
    IsQuasiSeparated B S hS (relativeInertiaProjection B S hS f).hom ↔
      IsQuasiSeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS
          (relativeDiagonalAlgebraicStacks B S hS f)
          (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom :=
  relativeProperty_relativeInertiaProjection_iff B S hS (Space.quasiSeparatedProperty B S hS) f

/-- **Stacks 0CL0, part (1), conditions (a) and (b).** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S`, the relative inertia projection `π : I_{𝒳/𝒴} ⟶ 𝒳` is separated, in
the relative sense of Properties of Stacks, Section 04XB, exactly when the first relative
diagonal `Δ_{f, 1} = Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is.

Both conditions are first read at the first projection `pr₁` of the 2-fibre product of `Δ_f`
with itself, by
`AlgebraicGeometry.Stack.isSeparated_relativeInertiaProjection_iff_twoFibreProductFst`. Then:

* (b) ⇒ (a) is Stacks 045C: `pr₁` is a base change of `Δ_f`, so it inherits separatedness, and
  no hypothesis on the property is needed.
* (a) ⇒ (b) is the section argument. `Δ_{f, 2} ≫ pr₁ = 𝟙 𝒳`, so `Δ_{f, 2}` is a section of
  `pr₁`, and `AlgebraicGeometry.Stack.isClosedImmersion_section_of_isSeparated` — Stacks 04YS at
  `pr₁`, which is representable by
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_twoFibreProductFst_relativeDiagonal`,
  followed by the three hypothesis-free transfers — makes `Δ_{f, 2}` a closed immersion.
  Stacks 04YS read at `Δ_f` instead of at `pr₁` turns that back into separatedness of `Δ_f`.

**Neither direction uses the group law of the relative inertia**, so Groupoids in Spaces,
Lemma 06P6 — the source's route, and Chapter 78 — is not needed; see the module docstring.

This theorem and
`AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_iff_isClosedImmersion_neutralSection`,
which is (b) ⇔ (c), are together the covering set of part (1) of Stacks 0CL0, and both carry
it. -/
@[stacks 0CL0 "part (1), conditions (a) and (b): the relative inertia projection is separated \
exactly when the first relative diagonal is"]
theorem isSeparated_relativeInertiaProjection_iff_relativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    IsSeparated B S hS (relativeInertiaProjection B S hS f).hom ↔
      IsSeparated B S hS
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :=
  (isSeparated_relativeInertiaProjection_iff_twoFibreProductFst B S hS f).trans
    ⟨fun h => (isSeparated_iff_isClosedImmersion_relativeDiagonal B S hS
        (relativeDiagonalAlgebraicStacks B S hS f)
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)).mpr
      (isClosedImmersion_section_of_isSeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS
          (relativeDiagonalAlgebraicStacks B S hS f)
          (relativeDiagonalAlgebraicStacks B S hS f)).fst
        (relativeDiagonalAlgebraicStacks B S hS (relativeDiagonalAlgebraicStacks B S hS f))
        ⟨eqToIso rfl⟩
        (isRepresentableByAlgebraicSpaces_twoFibreProductFst_relativeDiagonal B S hS f) h),
      fun h => relativeProperty_twoFibreProductFst_of_relativeDiagonal B S hS
        (Space.separatedProperty B S hS) f h⟩

/-- **Stacks 0CL0, part (2), conditions (a) and (b).** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S`, the relative inertia projection `π : I_{𝒳/𝒴} ⟶ 𝒳` is
quasi-separated, in the relative sense of Properties of Stacks, Section 04XB, exactly when the
first relative diagonal `Δ_{f, 1} = Δ_f` is.

The argument is that of
`AlgebraicGeometry.Stack.isSeparated_relativeInertiaProjection_iff_relativeDiagonal` one step
down the scale: (b) ⇒ (a) is Stacks 045C at quasi-separatedness, and (a) ⇒ (b) is Stacks 04YT
at `pr₁` — making the section `Δ_{f, 2}` quasi-compact through
`AlgebraicGeometry.Stack.isRelativelyQuasiCompact_section_of_isQuasiSeparated` — followed by
Stacks 04YT read at `Δ_f`.

This theorem and
`AlgebraicGeometry.Stack.isQuasiSeparated_relativeDiagonal_iff_isQuasiCompact_neutralSection`,
which is (b) ⇔ (c), are together the covering set of part (2) of Stacks 0CL0, and both carry
it. -/
@[stacks 0CL0 "part (2), conditions (a) and (b): the relative inertia projection is \
quasi-separated exactly when the first relative diagonal is"]
theorem isQuasiSeparated_relativeInertiaProjection_iff_relativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    IsQuasiSeparated B S hS (relativeInertiaProjection B S hS f).hom ↔
      IsQuasiSeparated B S hS
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :=
  (isQuasiSeparated_relativeInertiaProjection_iff_twoFibreProductFst B S hS f).trans
    ⟨fun h => (isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS
        (relativeDiagonalAlgebraicStacks B S hS f)
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)).mp
      (isRelativelyQuasiCompact_section_of_isQuasiSeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS
          (relativeDiagonalAlgebraicStacks B S hS f)
          (relativeDiagonalAlgebraicStacks B S hS f)).fst
        (relativeDiagonalAlgebraicStacks B S hS (relativeDiagonalAlgebraicStacks B S hS f))
        ⟨eqToIso rfl⟩
        (isRepresentableByAlgebraicSpaces_twoFibreProductFst_relativeDiagonal B S hS f) h),
      fun h => relativeProperty_twoFibreProductFst_of_relativeDiagonal B S hS
        (Space.quasiSeparatedProperty B S hS) f h⟩

/-- **Stacks 0CL0, part (1), conditions (b) and (c).** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S`, the relative diagonal `Δ_{f, 1} = Δ_f` is separated in the sense of
Stacks 04XB exactly when `Δ_{f, 2} = e : 𝒳 ⟶ I_{𝒳/𝒴}`, the neutral section of the relative
inertia, is a closed immersion of algebraic stacks in the sense of part (2) of Stacks 04YL.

This is part (1) of Stacks 04YZ — Stacks 04YS read at `Δ_f`, whose representability hypothesis
is automatic by part (1) of Stacks 04XS — composed with the identification of `Δ_{f, 2}` with
the neutral section, which is what the source means by "since `Δ_{f, 2}` is the diagonal of
`Δ_f` we have (b) ⇔ (c) by definition". The transports of the two conjuncts of part (2) of
Stacks 04YL are `Stack.isRepresentableByAlgebraicSpaces_secondRelativeDiagonal_iff_neutralSection`
and `Stack.isClosedImmersion_secondRelativeDiagonal_iff_neutralSection`. -/
@[stacks 0CL0 "part (1), conditions (b) and (c): the relative diagonal is separated exactly \
when the neutral section of the relative inertia is a closed immersion"]
theorem isSeparated_relativeDiagonal_iff_isClosedImmersion_neutralSection (f : 𝒳 ⟶ 𝒴) :
    IsSeparated B S hS
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) ↔
      AlgebraicStacks.IsClosedImmersion B S hS (relativeInertiaStackNeutralSection B S hS f) := by
  have h := (isSeparated_firstRelativeDiagonal_tfae B S hS f).out 1 2
  exact h.trans
    (and_congr
      (isRepresentableByAlgebraicSpaces_secondRelativeDiagonal_iff_neutralSection B S hS f.hom)
      (isClosedImmersion_secondRelativeDiagonal_iff_neutralSection B S hS f.hom))

/-- **Stacks 0CL0, part (2), conditions (b) and (c).** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S`, the relative diagonal `Δ_{f, 1} = Δ_f` is quasi-separated in the
sense of Stacks 04XB exactly when `Δ_{f, 2} = e : 𝒳 ⟶ I_{𝒳/𝒴}`, the neutral section of the
relative inertia, is quasi-compact in that sense.

This is part (2) of Stacks 04YZ — Stacks 04YT read at `Δ_f` — composed with
`AlgebraicGeometry.Stack.isQuasiCompact_secondRelativeDiagonal_iff_neutralSection`. Being
quasi-compact is not one of the three parts of Stacks 04YL, so unlike condition (1)(c) there is
no representability conjunct to transport alongside. -/
@[stacks 0CL0 "part (2), conditions (b) and (c): the relative diagonal is quasi-separated \
exactly when the neutral section of the relative inertia is quasi-compact"]
theorem isQuasiSeparated_relativeDiagonal_iff_isQuasiCompact_neutralSection (f : 𝒳 ⟶ 𝒴) :
    IsQuasiSeparated B S hS
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) ↔
      IsQuasiCompact B S hS (relativeInertiaStackNeutralSection B S hS f).hom := by
  have h := (isQuasiSeparated_firstRelativeDiagonal_tfae B S hS f).out 1 3
  exact h.trans (isQuasiCompact_secondRelativeDiagonal_iff_neutralSection B S hS f.hom)

end Inertia

end AlgebraicGeometry.Stack

end
