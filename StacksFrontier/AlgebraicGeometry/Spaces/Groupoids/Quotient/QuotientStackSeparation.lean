module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalStructureMorphismComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence

/-!
# Separation axioms for the quotient stack of a flat groupoid in algebraic spaces

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S` of a big fppf site,
with `s` and `t` flat and locally of finite presentation, and let `𝒳` be an algebraic stack over
`S` which is a model of the quotient stack `[U/R]` of Stacks 044Q. **Stacks 0DTY** reads three
separation properties of `𝒳` off the morphism `j = (t, s) : R ⟶ U ×_S U`:

* if `j` is separated then the diagonal `Δ_𝒳` is separated, and the same holds when `U` and `R`
  are separated;
* if `j` is locally quasi-finite then `𝒳` is quasi-DM, and the same holds when `s` and `t` are
  locally quasi-finite;
* if `j` is proper then `𝒳` is separated, and the same holds when `s` and `t` are proper and `U`
  is separated.

The source's proof is one observation and three cancellations. The observation is that the base
change of `Δ_𝒳` along `U × U ⟶ 𝒳 × 𝒳` is `j` (**Stacks 04M9**), so that `Δ_𝒳` has a property of
Properties of Stacks, Section 04XB exactly when `j` has it (**Stacks 06FH**, **Stacks 04XD**).
That observation is `AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_iff_sourceTarget`; the
three cancellations are the content of parts (2), (4) and (6).

## Main results

* `AlgebraicGeometry.Stack.isSeparated_diagonal_of_isSeparated_sourceTarget`: **Stacks 0DTY**,
  part (1).
* `AlgebraicGeometry.Stack.isSeparated_diagonal_of_isSeparated_spaces`: **Stacks 0DTY**,
  part (2).
* `AlgebraicGeometry.Stack.isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_sourceTarget`:
  **Stacks 0DTY**, part (3).
* `AlgebraicGeometry.Stack.isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_source_target`:
  **Stacks 0DTY**, part (4).
* `AlgebraicGeometry.Stack.isSeparatedOver_of_isProper_sourceTarget` and
  `AlgebraicGeometry.Stack.isSeparatedOver_of_isProper_source_target`: **Stacks 0DTY**, parts (5)
  and (6): separatedness over the base scheme `S`.
* `AlgebraicGeometry.Stack.isAbsolutelySeparated_of_isProper_sourceTarget` and
  `AlgebraicGeometry.Stack.isAbsolutelySeparated_of_isProper_source_target`: parts (5) and (6)
  with absolute separatedness as the conclusion, for a separated base.

## Implementation notes

The quotient stack `AlgebraicGeometry.Stack.quotientStack` is a based category whose morphisms
live one universe up from those of an `AlgebraicGeometry.Stack.AlgebraicStacks`, because it is
built by stackification; so the algebraic stack `𝒳` the separation properties are asserted of is
an argument, tied to the groupoid by an equivalence over the site. Algebraicity of a model is
**Stacks 06FI**.

The groupoid is a groupoid in algebraic spaces over `S` as in the source, that is over the final
algebraic space `AlgebraicGeometry.Space.terminalSpace`, so that the square of the object space
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.objectPairs` is `U ×_S U`. The relation morphism is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.sourceTarget`, the `(t, s)` of the source; its
orientation is immaterial to each clause, the swap of the two factors being an isomorphism.

Parts (2), (4) and (6) contain mathematics beyond their companions: part (2) is the cancellation
of the structure morphism of the square off a separated morphism, part (4) the cancellation of a
projection off a locally quasi-finite one (**Stacks 03XN**), and part (6) the same against a
separated projection for properness (**Stacks 04NX**, part (2)), the projection being separated as
a base change of the structure morphism of the object space.

**Which separatedness.** Parts (3) and (4) conclude the absolute quasi-DM property of
**Stacks 050D**, part (6), through the biconditional **Stacks 050N**, part (2). For separatedness
there is no such biconditional: **Stacks 050N**, part (3) says only that an absolutely separated
algebraic stack is separated over its base. What the source's cartesian square delivers is
properness of the diagonal over `S`, that is separatedness over `S` in the sense of
**Stacks 050D**, part (3), and that is the conclusion of
`isSeparatedOver_of_isProper_sourceTarget` and `isSeparatedOver_of_isProper_source_target`. The
absolute notion of Stacks 050D, part (7), does not follow without a condition on the base — the
trivial groupoid `R = U = S` on a non-separated scheme `S` has `[U/R] = S` and `(t, s)` an
isomorphism — and it is reached from separatedness over `S` by **Stacks 050L**, part (7) at the
structure 1-morphism, given separatedness of the algebraic stack of the base scheme of the site
(the hypothesis `hBase` of `isAbsolutelySeparated_of_isProper_sourceTarget` and
`isAbsolutelySeparated_of_isProper_source_target`). The registered clauses for parts (5) and (6)
are the ones over `S`: in the source, separatedness of an algebraic stack over `S` means
separatedness over `S`.

The same question does not arise for parts (1) and (2): their conclusion is separatedness of the
diagonal over the base scheme of the site, and separatedness, unlike properness, is stable under
composition with the comparison `𝒳 ×_S 𝒳 ⟶ 𝒳 ×_{Spec ℤ} 𝒳`, which is a base change of the
diagonal of a scheme and so an immersion.

Clause (7) of the source is the editorial note *Add more here* and states nothing.

## References

* [Stacks Project, Tag 03XN](https://stacks.math.columbia.edu/tag/03XN)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 0DTY](https://stacks.math.columbia.edu/tag/0DTY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_quotientStackSeparation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the pullbacks of presheaves on the big fppf site in the statement
/-- The structure morphism of the square of the object space, composed with `(t, s)`, is the
structure morphism of the arrow space. -/
theorem sourceTarget_comp_objectPairs_toBase {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A) :
    (GroupoidInAlgebraicSpaces.sourceTarget G).hom ≫
        (GroupoidInAlgebraicSpaces.objectPairsTarget G).hom ≫ G.objectsToBase.hom =
      G.arrowsToBase.hom := by
  rw [← Category.assoc, GroupoidInAlgebraicSpaces.sourceTarget_target_projection G]
  simpa using congrArg (fun k : G.arrows ⟶ A => k.hom) G.target_over

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the pullbacks of presheaves on the big fppf site in the statement
/-- The source projection of the square of the object space is separated when the structure
morphism of the object space is: it is a base change of that morphism. -/
theorem isSeparated_objectPairsSource {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A)
    (hU : Space.IsSeparated B S hS G.objectsToBase.hom) :
    Space.IsSeparated B S hS (GroupoidInAlgebraicSpaces.objectPairsSource G).hom :=
  Space.isSeparated_pullbackSnd B S hS G.objectsToBase.hom hU

section Clauses

variable (G : GroupoidInAlgebraicSpaces B S hS (Space.terminalSpace B S hS))
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0DTY, part (1).** Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S` with
`s` and `t` flat and locally of finite presentation, and let `𝒳` be an algebraic stack equivalent
over the site to its quotient stack `[U/R]`. If `(t, s) : R ⟶ U ×_S U` is separated, then the
diagonal of `𝒳` is separated in the sense of Properties of Stacks, Section 04XB. -/
@[stacks 0DTY "part (1): a separated relation gives a separated diagonal, the diagonal being \
the one over the base scheme of the site"]
theorem isSeparated_diagonal_of_isSeparated_sourceTarget
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack G).p 𝒳.val.val.p))
    (_hsFlat : Space.IsFlat B S hS G.source.hom)
    (_htFlat : Space.IsFlat B S hS G.target.hom)
    (_hsLfp : Space.IsLocallyOfFinitePresentation B S hS G.source.hom)
    (_htLfp : Space.IsLocallyOfFinitePresentation B S hS G.target.hom)
    (hj : Space.IsSeparated B S hS (GroupoidInAlgebraicSpaces.sourceTarget G).hom) :
    Stack.IsSeparated B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val) := by
  have : (Space.separatedProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  exact (hasRelativeProperty_diagonal_iff_sourceTarget G 𝒳 (Space.separatedProperty B S hS)
    hequiv).mpr hj

/-- **Stacks 0DTY, part (2).** Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S` with
`s` and `t` flat and locally of finite presentation, and let `𝒳` be an algebraic stack equivalent
over the site to its quotient stack `[U/R]`. If `U` and `R` are separated, then the diagonal of `𝒳`
is separated in the sense of Properties of Stacks, Section 04XB. -/
@[stacks 0DTY "part (2): separated object and arrow spaces give a separated diagonal, the \
diagonal being the one over the base scheme of the site"]
theorem isSeparated_diagonal_of_isSeparated_spaces
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack G).p 𝒳.val.val.p))
    (_hsFlat : Space.IsFlat B S hS G.source.hom)
    (_htFlat : Space.IsFlat B S hS G.target.hom)
    (_hsLfp : Space.IsLocallyOfFinitePresentation B S hS G.source.hom)
    (_htLfp : Space.IsLocallyOfFinitePresentation B S hS G.target.hom)
    (_hU : Space.IsSeparated B S hS G.objectsToBase.hom)
    (hR : Space.IsSeparated B S hS G.arrowsToBase.hom) :
    Stack.IsSeparated B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val) := by
  refine isSeparated_diagonal_of_isSeparated_sourceTarget.{u, w} G 𝒳 hequiv _hsFlat _htFlat
    _hsLfp _htLfp (Space.isSeparated_of_comp B S hS
      (GroupoidInAlgebraicSpaces.sourceTarget G).hom
      ((GroupoidInAlgebraicSpaces.objectPairsTarget G).hom ≫ G.objectsToBase.hom) ?_)
  rw [sourceTarget_comp_objectPairs_toBase G]
  exact hR

/-- **Stacks 0DTY, part (3).** Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S` with
`s` and `t` flat and locally of finite presentation, and let `𝒳` be an algebraic stack equivalent
over the site to its quotient stack `[U/R]`. If `(t, s) : R ⟶ U ×_S U` is locally quasi-finite, then
`𝒳` is quasi-DM. -/
@[stacks 0DTY "part (3): a locally quasi-finite relation gives a quasi-DM quotient"]
theorem isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_sourceTarget
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack G).p 𝒳.val.val.p))
    (_hsFlat : Space.IsFlat B S hS G.source.hom)
    (_htFlat : Space.IsFlat B S hS G.target.hom)
    (_hsLfp : Space.IsLocallyOfFinitePresentation B S hS G.source.hom)
    (_htLfp : Space.IsLocallyOfFinitePresentation B S hS G.target.hom)
    (hj : Space.IsLocallyQuasiFinite B S hS
      (GroupoidInAlgebraicSpaces.sourceTarget G).hom) :
    AlgebraicStacks.IsAbsolutelyQuasiDM.{u, w} B S hS hZ 𝒳 := by
  have : (Space.locallyQuasiFiniteProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact AlgebraicStacks.isAbsolutelyQuasiDM_of_isQuasiDMOver.{u, w} B S hS hZ 𝒳
    ((relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w} B S hS 𝒳
      (Space.locallyQuasiFiniteProperty B S hS)).mp
      ((hasRelativeProperty_diagonal_iff_sourceTarget G 𝒳 _ hequiv).mpr hj))

/-- **Stacks 0DTY, part (4).** Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S` with
`s` and `t` flat and locally of finite presentation, and let `𝒳` be an algebraic stack equivalent
over the site to its quotient stack `[U/R]`. If `s` and `t` are locally quasi-finite, then `𝒳` is
quasi-DM. -/
@[stacks 0DTY "part (4): a locally quasi-finite source and target give a quasi-DM quotient"]
theorem isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_source_target
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack G).p 𝒳.val.val.p))
    (_hsFlat : Space.IsFlat B S hS G.source.hom)
    (_htFlat : Space.IsFlat B S hS G.target.hom)
    (_hsLfp : Space.IsLocallyOfFinitePresentation B S hS G.source.hom)
    (_htLfp : Space.IsLocallyOfFinitePresentation B S hS G.target.hom)
    (hs : Space.IsLocallyQuasiFinite B S hS G.source.hom)
    (_ht : Space.IsLocallyQuasiFinite B S hS G.target.hom) :
    AlgebraicStacks.IsAbsolutelyQuasiDM.{u, w} B S hS hZ 𝒳 := by
  refine isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_sourceTarget.{u, w} G 𝒳 hZ hequiv
    _hsFlat _htFlat _hsLfp _htLfp
    (Space.isLocallyQuasiFinite_of_comp B S hS G.arrows.property
      (GroupoidInAlgebraicSpaces.objectPairs G).property G.objects.property
      (GroupoidInAlgebraicSpaces.sourceTarget G).hom
      (GroupoidInAlgebraicSpaces.objectPairsSource G).hom ?_)
  simpa [GroupoidInAlgebraicSpaces.sourceTarget_source_projection G] using hs

/-- **Stacks 0DTY, part (5).** Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S` with
`s` and `t` flat and locally of finite presentation, and let `𝒳` be an algebraic stack equivalent
over the site to its quotient stack `[U/R]`. If `(t, s) : R ⟶ U ×_S U` is proper, then `𝒳` is
separated over the base scheme of the site (Stacks 050D, part (3)). -/
@[stacks 0DTY "part (5): a proper relation gives a quotient separated over the base scheme `S` \
(Stacks 050D part (3)), the source's `separated` for an algebraic stack over `S`"]
theorem isSeparatedOver_of_isProper_sourceTarget
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack G).p 𝒳.val.val.p))
    (_hsFlat : Space.IsFlat B S hS G.source.hom)
    (_htFlat : Space.IsFlat B S hS G.target.hom)
    (_hsLfp : Space.IsLocallyOfFinitePresentation B S hS G.source.hom)
    (_htLfp : Space.IsLocallyOfFinitePresentation B S hS G.target.hom)
    (hj : Space.IsProper B S hS (GroupoidInAlgebraicSpaces.sourceTarget G).hom) :
    IsSeparatedOver.{u, w} B S hS 𝒳 := by
  have : (Space.properProperty B S hS).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange B S hS
  have : (Space.properProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.proper_isLocalAtTarget_fppf B S hS
  exact (relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w} B S hS 𝒳
    (Space.properProperty B S hS)).mp
    ((hasRelativeProperty_diagonal_iff_sourceTarget G 𝒳 _ hequiv).mpr hj)

/-- **Stacks 0DTY, part (6).** Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S` with
`s` and `t` flat and locally of finite presentation, and let `𝒳` be an algebraic stack equivalent
over the site to its quotient stack `[U/R]`. If `s` and `t` are proper and `U` is separated, then
`𝒳` is separated over the base scheme of the site (Stacks 050D, part (3)). -/
@[stacks 0DTY "part (6): a proper source and target over a separated object space give a \
quotient separated over the base scheme `S` (Stacks 050D part (3)), the source's `separated` for \
an algebraic stack over `S`"]
theorem isSeparatedOver_of_isProper_source_target
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack G).p 𝒳.val.val.p))
    (_hsFlat : Space.IsFlat B S hS G.source.hom)
    (_htFlat : Space.IsFlat B S hS G.target.hom)
    (_hsLfp : Space.IsLocallyOfFinitePresentation B S hS G.source.hom)
    (_htLfp : Space.IsLocallyOfFinitePresentation B S hS G.target.hom)
    (hs : Space.IsProper B S hS G.source.hom)
    (_ht : Space.IsProper B S hS G.target.hom)
    (hU : Space.IsSeparated B S hS G.objectsToBase.hom) :
    IsSeparatedOver.{u, w} B S hS 𝒳 := by
  refine isSeparatedOver_of_isProper_sourceTarget.{u, w} G 𝒳 hequiv _hsFlat _htFlat
    _hsLfp _htLfp
    (Space.isProper_of_comp_of_isSeparated B S hS G.arrows.property
      (GroupoidInAlgebraicSpaces.objectPairs G).property G.objects.property
      (GroupoidInAlgebraicSpaces.sourceTarget G).hom
      (GroupoidInAlgebraicSpaces.objectPairsSource G).hom ?_
      (isSeparated_objectPairsSource G hU))
  simpa [GroupoidInAlgebraicSpaces.sourceTarget_source_projection G] using hs

/-- Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S` with `s` and `t` flat and
locally of finite presentation, and let `𝒳` be an algebraic stack equivalent over the site to its
quotient stack `[U/R]`. If `(t, s) : R ⟶ U ×_S U` is proper, then `𝒳` is separated, in the
unqualified, absolute sense of Stacks 050D, part (7), provided the algebraic stack of the base
scheme of the site is separated. -/
theorem isAbsolutelySeparated_of_isProper_sourceTarget
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hBase : AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))))
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack G).p 𝒳.val.val.p))
    (_hsFlat : Space.IsFlat B S hS G.source.hom)
    (_htFlat : Space.IsFlat B S hS G.target.hom)
    (_hsLfp : Space.IsLocallyOfFinitePresentation B S hS G.source.hom)
    (_htLfp : Space.IsLocallyOfFinitePresentation B S hS G.target.hom)
    (hj : Space.IsProper B S hS (GroupoidInAlgebraicSpaces.sourceTarget G).hom) :
    AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ 𝒳 :=
  AlgebraicStacks.isAbsolutelySeparated_of_isSeparated.{u, w} B S hS hZ
    (structureMorphism.{u, w} B S hS 𝒳) hBase
    (isSeparatedOver_of_isProper_sourceTarget.{u, w} G 𝒳 hequiv _hsFlat _htFlat _hsLfp
      _htLfp hj)

/-- Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S` with `s` and `t` flat and
locally of finite presentation, and let `𝒳` be an algebraic stack equivalent over the site to its
quotient stack `[U/R]`. If `s` and `t` are proper and `U` is separated, then `𝒳` is separated, in
the unqualified, absolute sense of Stacks 050D, part (7), provided the algebraic stack of the base
scheme of the site is separated. -/
theorem isAbsolutelySeparated_of_isProper_source_target
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hBase : AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))))
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack G).p 𝒳.val.val.p))
    (_hsFlat : Space.IsFlat B S hS G.source.hom)
    (_htFlat : Space.IsFlat B S hS G.target.hom)
    (_hsLfp : Space.IsLocallyOfFinitePresentation B S hS G.source.hom)
    (_htLfp : Space.IsLocallyOfFinitePresentation B S hS G.target.hom)
    (hs : Space.IsProper B S hS G.source.hom)
    (ht : Space.IsProper B S hS G.target.hom)
    (hU : Space.IsSeparated B S hS G.objectsToBase.hom) :
    AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ 𝒳 :=
  AlgebraicStacks.isAbsolutelySeparated_of_isSeparated.{u, w} B S hS hZ
    (structureMorphism.{u, w} B S hS 𝒳) hBase
    (isSeparatedOver_of_isProper_source_target.{u, w} G 𝒳 hequiv _hsFlat _htFlat _hsLfp
      _htLfp hs ht hU)

end Clauses

end AlgebraicGeometry.Stack

end
