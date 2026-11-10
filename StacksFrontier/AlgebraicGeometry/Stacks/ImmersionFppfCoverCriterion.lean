module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpacesOfFppfCover
import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces

/-!
# Testing an immersion of algebraic stacks on an fppf cover by an algebraic space (Stacks 0503)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `W` be an algebraic space
over `S` and let `W ⟶ 𝒴` be surjective, flat and locally of finite presentation.
**Stacks 0503** says that the following are equivalent:

1. `f` is an immersion, respectively a closed immersion, respectively an open immersion, and
2. `V = W ×_𝒴 𝒳` is an algebraic space, and `V ⟶ W` is an immersion, respectively a closed
   immersion, respectively an open immersion, of algebraic spaces.

Clause (2) is read here as it is written: an existential over algebraic spaces `V` representing
the apex of the 2-fibre product square, asserting of one of them that the induced morphism
`V ⟶ W` of representing presheaves — `AlgebraicGeometry.Stack.representingMap` — has the
property in question. In the forward direction that `V` is produced, not assumed: it comes from
**Stacks 0300**, which is also the implication (1) `⟹` (2) of **Stacks 04ZP**.

## Main results

* `AlgebraicGeometry.Stack.isImmersion_iff_exists_isImmersion_representingMap`,
  `AlgebraicGeometry.Stack.isClosedImmersion_iff_exists_isClosedImmersion_representingMap` and
  `AlgebraicGeometry.Stack.isOpenImmersion_iff_exists_isOpenImmersion_representingMap`: the
  three readings of Stacks 0503 for the Stacks 04XB properties of a 1-morphism of categories
  fibred in groupoids.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isImmersion_iff_exists_isImmersion_representingMap`
  and its closed and open companions: **Stacks 0503**, in its three readings, for the three
  notions of immersion of *algebraic stacks* of **Stacks 04YL**.

## What the source's proof needs

Stacks 0503 cites two lemmas. One is **Stacks 04XD**, the biconditional that a 1-morphism
representable by algebraic spaces has a relative property exactly when the morphism of
algebraic spaces obtained by base change to the cover has it; that is the engine, and it is in
the library as
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap_of_fppf`. The other is
**Stacks 04ZP**, the biconditional that `f` is representable by algebraic spaces exactly when
`W ×_𝒴 𝒳` is an algebraic space. In the algebraic-stacks statements the implication (1) `⟹` (2)
reads representability off clause (1) itself — it is the first conjunct of each notion of
Stacks 04YL — and the implication (2) `⟹` (1) obtains it from the converse of Stacks 04ZP,
`isRepresentableByAlgebraicSpaces_of_isTwoFibreProduct_of_bootstrap` in the namespace
`AlgebraicGeometry.Stack.AlgebraicStacks`.
Representability of `W ⟶ 𝒴` by algebraic spaces is Stacks 045G, the diagonal of `𝒴` being
representable: `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`.
The statements for categories fibred in groupoids, where neither is available, take both as
hypotheses `hf` and `hgr`.

The locality hypothesis of Stacks 04XD on the property — that it is local at the target for the
fppf precoverage of algebraic spaces — is **discharged** for all three readings:

* immersions: `AlgebraicGeometry.Space.isImmersion_isLocalAtTarget_fppf`, **Stacks 042U**;
* closed immersions: `AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fpqc`,
  **Stacks 0420** in its fpqc form, restricted along
  `AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage` (**Stacks 0DFQ**);
* open immersions: `AlgebraicGeometry.Space.openImmersion_isLocalAtTarget_fppf`,
  **Stacks 041X** at the fppf precoverage.

Every other hypothesis of the algebraic-stacks statements is one the source makes: `g` with
surjective, flat and locally finitely presented base changes is "`W ⟶ 𝒴` surjective, flat,
locally of finite presentation"; `W`, `hW`, `eW` are "`W` is an algebraic space"; and `Q`, `hQ`
are "`V = W ×_𝒴 𝒳`".

## Implementation notes

The statements are at `CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, the universe assignment of
Stacks 04XD in this library and the one underlying
`AlgebraicGeometry.Stack.AlgebraicStacks`, so the algebraic-stacks readings instantiate the
categories-fibred-in-groupoids ones with no universe work. `W` is left as a category fibred in
groupoids represented by an algebraic space even in the algebraic-stacks readings: the source
makes it an algebraic space, not an algebraic stack, and asking a user to exhibit it as an
object of `AlgebraicGeometry.Stack.AlgebraicStacks` would be a hypothesis the source does not
make.

The forward direction produces `V` from
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct` at the universes
`.{u, u, u + 1}`, where the saturated pattern
`{u, max u v, u + 1, max (max (u + 1) w) v}` of that statement collapses to
`{u, u, u + 1, u + 1}`. The algebraic space representing `𝒲` is fed to it as the witness that
`𝒲` is represented by an algebraic space, assembled from `W`, `hW` and `eW`.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 042U](https://stacks.math.columbia.edu/tag/042U)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 0503](https://stacks.math.columbia.edu/tag/0503)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The hypothesis Stacks 04XD and Stacks 0503 make on the cover `g : 𝒲 ⟶ 𝒴`: every algebraic
space representing its base change along a scheme-valued point of `𝒴` has surjective, flat and
locally finitely presented structural morphism, read as a morphism of algebraic spaces over
`S`. This is the notion of Stacks 03YK at those three properties, written out as in
`AlgebraicGeometry.Stack.IsImmersion`. -/
abbrev IsSurjectiveFlatLocallyOfFinitePresentation
    {𝒴 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒲 ⟶ 𝒴) : Prop :=
  ∀ (V : BigFppfOver B S hS)
    (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
    (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
    (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.p 𝒴.val.p yv
        (CatFiberedInGroupoids.homFunctor g))
      (presheafOfCategories (F ⋙ typeToCat)).p) →
    (let h := (algebraicSpaceMap B S hS V
      ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
     Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
       Space.IsLocallyOfFinitePresentation B S hS h)

section FiberedInGroupoids

variable (𝒳 𝒴 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **The apex of the square is represented by an algebraic space.** This is Stacks 0300, in the
form the forward implication of Stacks 0503 uses it: if `f` is representable by algebraic spaces
and `𝒲` is represented by the algebraic space `W`, then the apex of a 2-fibre product square
over the cospan `(g, f)` is represented by an algebraic space. It is the implication
(1) `⟹` (2) of Stacks 04ZP. -/
theorem exists_isAlgebraicSpace_pt
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (eW : StacksRepresentableCFG.EquivalenceOver
      𝒲.val.p (presheafOfCategories (W ⋙ typeToCat)).p) :
    ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS V ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p) :=
  isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS 𝒳 𝒴 𝒲 f g Q hQ hf
    ⟨W, hW, ⟨eW⟩⟩

variable (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴)
  (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
  (hgr : IsRepresentableByAlgebraicSpaces B S hS g.hom)
  (hg : IsSurjectiveFlatLocallyOfFinitePresentation B S hS g)
  (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
  (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
  (eW : StacksRepresentableCFG.EquivalenceOver
    𝒲.val.p (presheafOfCategories (W ⋙ typeToCat)).p)

include hf hgr hg hQ hW

/-- Stacks 04XD with the algebraic space `V` representing the apex of `Q` produced by Stacks 0300:
a relative property holds exactly when some such `V` has `V ⟶ W` in the property. -/
private theorem hasRelativeProperty_iff_exists_prop_representingMap
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)] :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P f hf ↔
      ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
        (eV : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p),
        P (ObjectProperty.homMk (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) :
          (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ (⟨W, hW⟩ : AlgebraicSpaces B S hS)) := by
  constructor
  · intro himm
    obtain ⟨V, hV, ⟨eV⟩⟩ := exists_isAlgebraicSpace_pt B S hS 𝒳 𝒴 𝒲 f g hf Q hQ W hW eW
    exact ⟨V, hV, eV, (hasRelativeProperty_iff_prop_representingMap_of_fppf.{u, u} B S hS
      P 𝒳 𝒴 𝒲 f g hf hgr hg Q hQ V W hV hW eV eW).mp himm⟩
  · rintro ⟨V, hV, eV, hVW⟩
    exact (hasRelativeProperty_iff_prop_representingMap_of_fppf.{u, u} B S hS
      P 𝒳 𝒴 𝒲 f g hf hgr hg Q hQ V W hV hW eV eW).mpr hVW

/-- **Stacks 0503 for the immersion property of Stacks 04XB.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism
of categories fibred in groupoids over the big fppf site of `S` which is representable by
algebraic spaces, let `g : 𝒲 ⟶ 𝒴` be representable by algebraic spaces with surjective, flat
and locally finitely presented base changes, let `W` be an algebraic space representing `𝒲`,
and let `Q` be a 2-fibre product square over the cospan `(g, f)`. Then `f` is an immersion in
the sense of Stacks 04XB exactly when the apex of `Q` is represented by an algebraic space `V`
whose induced morphism `V ⟶ W` is an immersion of algebraic spaces.

The locality hypothesis Stacks 04XD makes on the property is discharged by Stacks 042U. -/
theorem isImmersion_iff_exists_isImmersion_representingMap :
    Stack.IsImmersion B S hS f ↔
      ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hV : IsAlgebraicSpace B S hS V)
        (eV : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p),
        Space.IsImmersion B S hS (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) := by
  have _hloc := Space.isImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  exact hasRelativeProperty_iff_exists_prop_representingMap B S hS 𝒳 𝒴 𝒲 f g hf hgr hg Q hQ
    W hW eW (Space.immersionProperty B S hS)

/-- **Stacks 0503 for the closed-immersion property of Stacks 04XB.** In the situation of
`AlgebraicGeometry.Stack.isImmersion_iff_exists_isImmersion_representingMap`, `f` is a closed
immersion in the sense of Stacks 04XB exactly when the apex of `Q` is represented by an
algebraic space `V` whose induced morphism `V ⟶ W` is a closed immersion of algebraic spaces.

The locality hypothesis Stacks 04XD makes on the property is discharged by Stacks 0420 in its
fpqc form, restricted to the fppf precoverage by Stacks 0DFQ. -/
theorem isClosedImmersion_iff_exists_isClosedImmersion_representingMap :
    Stack.IsClosedImmersion B S hS f ↔
      ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hV : IsAlgebraicSpace B S hS V)
        (eV : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p),
        Space.IsClosedImmersion B S hS (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) := by
  have _hloc : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    have := Space.isClosedImmersion_isLocalAtTarget_fpqc.{u, u} B S hS
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact hasRelativeProperty_iff_exists_prop_representingMap B S hS 𝒳 𝒴 𝒲 f g hf hgr hg Q hQ
    W hW eW (Space.closedImmersionProperty B S hS)

/-- **Stacks 0503 for the open-immersion property of Stacks 04XB.** In the situation of
`AlgebraicGeometry.Stack.isImmersion_iff_exists_isImmersion_representingMap`, `f` is an open
immersion in the sense of Stacks 04XB exactly when the apex of `Q` is represented by an
algebraic space `V` whose induced morphism `V ⟶ W` is an open immersion of algebraic spaces.

The locality hypothesis Stacks 04XD makes on the property is Stacks 041X,
`AlgebraicGeometry.Space.openImmersion_isLocalAtTarget_fppf`. -/
theorem isOpenImmersion_iff_exists_isOpenImmersion_representingMap :
    Stack.IsOpenImmersion B S hS f ↔
      ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hV : IsAlgebraicSpace B S hS V)
        (eV : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p),
        Space.IsOpenImmersion B S hS (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) := by
  have := Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  exact hasRelativeProperty_iff_exists_prop_representingMap B S hS 𝒳 𝒴 𝒲 f g hf hgr hg Q hQ
    W hW eW (Space.openImmersionProperty B S hS)

end FiberedInGroupoids

/-! ### Stacks 0503 -/

namespace AlgebraicStacks

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
  (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴.val)
  (hg : IsSurjectiveFlatLocallyOfFinitePresentation B S hS g)
  (Q : Bicategory.TwoCommSq g f.hom) (hQ : Bicategory.IsTwoFibreProduct Q)
  (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
  (eW : StacksRepresentableCFG.EquivalenceOver
    𝒲.val.p (presheafOfCategories (W ⋙ typeToCat)).p)

include hg hQ hW

/-- `(representable ∧ P) ↔ ∃ V, T V` follows from its fibred-in-groupoids form, given that
representability of `f` follows from the existence of `V` (Stacks 04ZP). -/
private theorem isRepresentable_and_iff_exists
    (eW : StacksRepresentableCFG.EquivalenceOver
      𝒲.val.p (presheafOfCategories (W ⋙ typeToCat)).p) {P : Prop}
    {T : ∀ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS V →
      StacksRepresentableCFG.EquivalenceOver
        Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p → Prop}
    (h : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom →
      IsRepresentableByAlgebraicSpaces B S hS g.hom →
      (P ↔ ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
        (eV : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p), T V hV eV)) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧ P ↔
      ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
        (eV : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p), T V hV eV :=
  have hgr := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property
    ⟨W, hW, ⟨eW⟩⟩ g
  ⟨fun hP => (h hP.1 hgr).mp hP.2, fun hV =>
    have hf := isRepresentableByAlgebraicSpaces_of_isTwoFibreProduct_of_bootstrap B S hS 𝒲
      ⟨W, hW, ⟨eW⟩⟩ f g hg Q hQ (let ⟨V, hV, eV, _⟩ := hV; ⟨V, hV, ⟨eV⟩⟩)
    ⟨hf, (h hf hgr).mpr hV⟩⟩

/-- **Stacks 0503 for immersions.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over
`S`, let `W` be an algebraic space over `S` and let `g : W ⟶ 𝒴` be surjective, flat and locally
of finite presentation. Then `f` is an immersion of algebraic stacks (Stacks 04YL, part (3))
exactly when `V = W ×_𝒴 𝒳` is an algebraic space and `V ⟶ W` is an immersion of algebraic
spaces.

The forward implication reads representability by algebraic spaces off clause (1); the backward
one obtains it from Stacks 04ZP. The content of both is Stacks 04XD at the immersion property. -/
@[stacks 0503 "immersions"]
theorem isImmersion_iff_exists_isImmersion_representingMap :
    IsImmersion B S hS f ↔
      ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hV : IsAlgebraicSpace B S hS V)
        (eV : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p),
        Space.IsImmersion B S hS (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) :=
  isRepresentable_and_iff_exists B S hS 𝒲 f g hg Q hQ W hW eW fun hf hgr =>
    Stack.isImmersion_iff_exists_isImmersion_representingMap B S hS
      𝒳.val 𝒴.val 𝒲 f.hom g hf hgr hg Q hQ W hW eW

/-- **Stacks 0503 for closed immersions.** In the situation of
`AlgebraicGeometry.Stack.AlgebraicStacks.isImmersion_iff_exists_isImmersion_representingMap`,
`f` is a closed immersion of algebraic stacks (Stacks 04YL, part (2)) exactly when
`V = W ×_𝒴 𝒳` is an algebraic space and `V ⟶ W` is a closed immersion of algebraic spaces. -/
@[stacks 0503 "closed immersions"]
theorem isClosedImmersion_iff_exists_isClosedImmersion_representingMap :
    IsClosedImmersion B S hS f ↔
      ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hV : IsAlgebraicSpace B S hS V)
        (eV : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p),
        Space.IsClosedImmersion B S hS (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) :=
  isRepresentable_and_iff_exists B S hS 𝒲 f g hg Q hQ W hW eW fun hf hgr =>
    Stack.isClosedImmersion_iff_exists_isClosedImmersion_representingMap B S hS
      𝒳.val 𝒴.val 𝒲 f.hom g hf hgr hg Q hQ W hW eW

/-- **Stacks 0503 for open immersions.** In the situation of
`AlgebraicGeometry.Stack.AlgebraicStacks.isImmersion_iff_exists_isImmersion_representingMap`,
`f` is an open immersion of algebraic stacks (Stacks 04YL, part (1)) exactly when
`V = W ×_𝒴 𝒳` is an algebraic space and `V ⟶ W` is an open immersion of algebraic spaces. -/
@[stacks 0503 "open immersions"]
theorem isOpenImmersion_iff_exists_isOpenImmersion_representingMap :
    IsOpenImmersion B S hS f ↔
      ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hV : IsAlgebraicSpace B S hS V)
        (eV : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p),
        Space.IsOpenImmersion B S hS (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) :=
  isRepresentable_and_iff_exists B S hS 𝒲 f g hg Q hQ W hW eW fun hf hgr =>
    Stack.isOpenImmersion_iff_exists_isOpenImmersion_representingMap B S hS
      𝒳.val 𝒴.val 𝒲 f.hom g hf hgr hg Q hQ W hW eW

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
