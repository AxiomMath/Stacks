module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion

/-!
# Separation, finiteness and properness of a morphism of algebraic spaces read as stacks

A morphism `g : T ⟶ G` of algebraic spaces over `S` induces a 1-morphism
`AlgebraicGeometry.Stack.algebraicSpaceStackMap g` between the algebraic stacks the two spaces
determine (Stacks 0458 and 03YS). This file shows that `g` is separated, quasi-compact, of finite
type, universally closed or proper as a morphism of algebraic spaces exactly when that 1-morphism
is, in each of the two readings the library has: the relative notions of Properties of Stacks,
Section 04XB, and the notions of Morphisms of Stacks for an arbitrary 1-morphism of algebraic
stacks (Stacks 04YW, 06FS, 050U, 0513, 0CL5).

The statement "these definitions do not conflict with the already existing notions" is used
throughout Morphisms of Stacks without a tag of its own; the comparisons below are the instances
of it that the proofs of Stacks 0CQM and Stacks 0CQ8 read on morphisms between algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_algebraicSpaceStackMap_iff`: for a property `P`
  of morphisms of algebraic spaces stable under base change and fppf local on the target, the
  relative property of Stacks 03YK of the induced 1-morphism is `P` of `g`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_iff_isProper_hom`: for a 1-morphism of
  algebraic stacks representable by algebraic spaces, properness in the sense of Stacks 0CL5 is
  properness in the sense of Stacks 04XB.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_algebraicSpaceStackMap_iff`,
  `isFiniteType_algebraicSpaceStackMap_iff`, `universallyClosed_algebraicSpaceStackMap_iff` and
  `isProper_algebraicSpaceStackMap_iff`: the comparisons for the notions of Morphisms of Stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_iff_isProper_representingMap`, with its
  companions for separatedness, quasi-compactness, local finite type, finite type and universal
  closedness: the same comparisons for any 1-morphism between algebraic stacks represented by
  algebraic spaces, read on the morphism of representing presheaves of Stacks 04SW.

## Implementation notes

The relative notions go through
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap` at the identity comparisons
of the two categories of elements, where the induced morphism of representing presheaves is `g`
itself (`AlgebraicGeometry.Stack.representingMap_associatedMap`). The notions of Morphisms of
Stacks are then reached by Stacks 04YS (separatedness), Stacks 050T (quasi-compactness), Stacks
06FM (local finite type) and Stacks 0512 (universal closedness), all of which hold for 1-morphisms
representable by algebraic spaces.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 0512](https://stacks.math.columbia.edu/tag/0512)
* [Stacks Project, Tag 0CL5](https://stacks.math.columbia.edu/tag/0CL5)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (g : T ⟶ G)

/-- The 1-morphism of algebraic stacks induced by a morphism of algebraic spaces is representable
by algebraic spaces: its source is represented by an algebraic space and its target is an
algebraic stack. -/
theorem isRepresentableByAlgebraicSpaces_algebraicSpaceStackMap :
    IsRepresentableByAlgebraicSpaces B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hT hG g).hom.hom :=
  isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
    (algebraicSpaceStack.{u, w} B S hS G hG).property
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT) _

/-- **The relative property of Stacks 03YK of the 1-morphism induced by a morphism of algebraic
spaces is the property of that morphism.** For `P` stable under base change and local on the
target for the fppf topology, the 1-morphism `algebraicSpaceStackMap g` has `P` in the sense of
Properties of Stacks, Section 04XB, exactly when `g` has `P`. -/
theorem hasRelativeProperty_algebraicSpaceStackMap_iff
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)] :
    HasRelativeProperty B S hS P
        (algebraicSpaceStackMap.{u, w} B S hS hT hG g).hom
        (isRepresentableByAlgebraicSpaces_algebraicSpaceStackMap.{u, w} B S hS hT hG g) ↔
      P (ObjectProperty.homMk g :
        (⟨T, hT⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) := by
  have h := hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS P
    (algebraicSpaceStackMap.{u, w} B S hS hT hG g).hom
    (isRepresentableByAlgebraicSpaces_algebraicSpaceStackMap.{u, w} B S hS hT hG g) T G hT hG
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  rwa [representingMap_associatedMap] at h

/-- Separatedness of morphisms of algebraic spaces is local on the target for the fppf topology. -/
private theorem isLocalAtTarget_fppf_separatedProperty :
    (Space.separatedProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
  .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)

/-- Universal closedness of morphisms of algebraic spaces is local on the target for the fppf
topology. -/
private theorem isLocalAtTarget_fppf_universallyClosedProperty :
    (Space.universallyClosedProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
  .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)

/-- **Separatedness in the sense of Stacks 04XB of the 1-morphism induced by a morphism of
algebraic spaces is separatedness of that morphism**, through Stacks 0421 for the fppf locality
of separatedness. -/
theorem isSeparated_algebraicSpaceStackMap_hom_iff :
    IsSeparated B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g).hom ↔
      Space.IsSeparated B S hS g := by
  have := isLocalAtTarget_fppf_separatedProperty B S hS
  exact hasRelativeProperty_algebraicSpaceStackMap_iff.{u, w} B S hS hT hG g
    (Space.separatedProperty B S hS)

/-- **Quasi-compactness in the sense of Stacks 04XB of the 1-morphism induced by a morphism of
algebraic spaces is quasi-compactness of that morphism**, through Stacks 041L for the fppf
locality of quasi-compactness. -/
theorem isQuasiCompact_algebraicSpaceStackMap_hom_iff :
    IsQuasiCompact B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g).hom ↔
      Space.IsQuasiCompact B S hS g :=
  hasRelativeProperty_algebraicSpaceStackMap_iff.{u, w} B S hS hT hG g
    (Space.quasiCompactProperty B S hS)

/-- **Universal closedness in the sense of Stacks 04XB of the 1-morphism induced by a morphism of
algebraic spaces is universal closedness of that morphism**, through Stacks 041O for the fppf
locality of universal closedness. -/
theorem universallyClosed_algebraicSpaceStackMap_hom_iff :
    UniversallyClosed B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g).hom ↔
      Space.UniversallyClosed B S hS g := by
  have := isLocalAtTarget_fppf_universallyClosedProperty B S hS
  exact hasRelativeProperty_algebraicSpaceStackMap_iff.{u, w} B S hS hT hG g
    (Space.universallyClosedProperty B S hS)

/-- **Properness in the sense of Stacks 04XB of the 1-morphism induced by a morphism of
algebraic spaces is properness of that morphism**, through Stacks 0422 for the fppf locality of
properness. -/
theorem isProper_algebraicSpaceStackMap_hom_iff :
    IsProper B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g).hom ↔
      Space.IsProper B S hS g :=
  hasRelativeProperty_algebraicSpaceStackMap_iff.{u, w} B S hS hT hG g
    (Space.properProperty B S hS)

namespace AlgebraicStacks

/-- **A morphism of algebraic spaces is separated exactly when the 1-morphism of algebraic stacks
it induces is separated** in the sense of Stacks 04YW: by Stacks 04YS a 1-morphism representable
by algebraic spaces has proper relative diagonal exactly when it is separated in the sense of
Stacks 04XB. -/
theorem isSeparated_algebraicSpaceStackMap_iff :
    IsSeparated B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g) ↔
      Space.IsSeparated B S hS g :=
  ((isSeparated_relativeDiagonal_tfae B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g)
    (isRepresentableByAlgebraicSpaces_algebraicSpaceStackMap.{u, w} B S hS hT hG g)).out 3 1).trans
    (isSeparated_algebraicSpaceStackMap_hom_iff.{u, w} B S hS hT hG g)

/-- **A morphism of algebraic spaces is quasi-compact exactly when the 1-morphism of algebraic
stacks it induces is quasi-compact** in the sense of Stacks 050U, by Stacks 050T. -/
theorem isQuasiCompactMorphism_algebraicSpaceStackMap_iff :
    IsQuasiCompactMorphism.{u, w} B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g) ↔
      Space.IsQuasiCompact B S hS g :=
  (isQuasiCompact_iff_baseChange_quasiCompact B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hT hG g)
    (isRepresentableByAlgebraicSpaces_algebraicSpaceStackMap.{u, w} B S hS hT hG g)).symm.trans
    (isQuasiCompact_algebraicSpaceStackMap_hom_iff.{u, w} B S hS hT hG g)

/-- **A morphism of algebraic spaces is of finite type exactly when the 1-morphism of algebraic
stacks it induces is of finite type** in the sense of Stacks 06FS, part (2): local finite type is
compared by Stacks 06FM and quasi-compactness by Stacks 050T. -/
theorem isFiniteType_algebraicSpaceStackMap_iff :
    IsFiniteType B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g) ↔
      Space.IsFiniteType B S hS g :=
  and_congr (isLocallyOfFiniteType_algebraicSpaceStackMap_iff.{u, w} B S hS hT hG g)
    (isQuasiCompactMorphism_algebraicSpaceStackMap_iff.{u, w} B S hS hT hG g)

/-- **A morphism of algebraic spaces is universally closed exactly when the 1-morphism of
algebraic stacks it induces is universally closed** in the sense of Stacks 0513, part (2), by
Stacks 0512 for a 1-morphism representable by algebraic spaces. -/
theorem universallyClosed_algebraicSpaceStackMap_iff :
    UniversallyClosed B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g) ↔
      Space.UniversallyClosed B S hS g :=
  (representable_universallyClosed_iff_closedMap_baseChange B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hT hG g)
    (isRepresentableByAlgebraicSpaces_algebraicSpaceStackMap.{u, w} B S hS hT hG g)).symm.trans
    (universallyClosed_algebraicSpaceStackMap_hom_iff.{u, w} B S hS hT hG g)

/-- **A morphism of algebraic spaces is proper exactly when the 1-morphism of algebraic stacks it
induces is proper** in the sense of Stacks 0CL5: separatedness, finite type and universal
closedness are compared one at a time. -/
theorem isProper_algebraicSpaceStackMap_iff :
    IsProper B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g) ↔
      Space.IsProper B S hS g :=
  and_congr (isSeparated_algebraicSpaceStackMap_iff.{u, w} B S hS hT hG g)
    (and_congr (isFiniteType_algebraicSpaceStackMap_iff.{u, w} B S hS hT hG g)
      (universallyClosed_algebraicSpaceStackMap_iff.{u, w} B S hS hT hG g))

/-- Local finite type is stable under base change. -/
private instance isStableUnderBaseChange_spaceProperty_lft :
    (spaceProperty B S hS
    (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)).IsStableUnderBaseChange :=
  Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS

/-- Local finite type is fppf local on the target. -/
private instance isLocalAtTarget_fppf_spaceProperty_lft :
    (spaceProperty B S hS
    (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
  .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)

/-- Local finite type on every smooth diagram of a 1-morphism representable by algebraic spaces is
the relative property of its representing morphism. -/
private theorem hasPropertyOnEverySmoothDiagram_lft_iff_relative
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    HasPropertyOnEverySmoothDiagram B S hS (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)
        f.hom ↔
      HasRelativeProperty B S hS
        (spaceProperty B S hS (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)) f.hom hf :=
  (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS) 𝒳.property
    𝒴.property f.hom).trans (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳.property 𝒴.property f.hom hf)

/-- **For a 1-morphism representable by algebraic spaces, properness in the sense of Stacks 0CL5
is properness in the sense of Stacks 04XB.** The 04XB condition is the conjunction, at every
represented base change along a scheme-valued point, of separatedness, local finite type,
quasi-compactness and universal closedness; the four are compared with the notions of
Morphisms of Stacks by Stacks 04YS, Stacks 06FM (for a representable morphism, through the
equivalence of its two smooth-diagram tests), Stacks 050T and Stacks 0512. -/
theorem isProper_iff_isProper_hom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    IsProper B S hS f ↔ Stack.IsProper B S hS f.hom := by
  have hsep := (isSeparated_relativeDiagonal_tfae B S hS f hf).out 3 1
  have hqc := isQuasiCompact_iff_baseChange_quasiCompact B S hS f hf
  have huc := representable_universallyClosed_iff_closedMap_baseChange B S hS f hf
  have hlft := hasPropertyOnEverySmoothDiagram_lft_iff_relative B S hS f hf
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩ U y hy F hF e
    exact ⟨hsep.1 h1 U y hy F hF e, ⟨hlft.1 h2 U y hy F hF e, hqc.2 h3 U y hy F hF e⟩,
      huc.2 h4 U y hy F hF e⟩
  · intro h
    exact ⟨hsep.2 fun U y hy F hF e => (h U y hy F hF e).1,
      ⟨hlft.2 fun U y hy F hF e => (h U y hy F hF e).2.1.1,
        hqc.1 fun U y hy F hF e => (h U y hy F hF e).2.1.2⟩,
      huc.1 fun U y hy F hF e => (h U y hy F hF e).2.2⟩

/-! ### 1-morphisms between algebraic stacks represented by algebraic spaces -/

section Represented

variable {𝒜 𝒞 : AlgebraicStacks.{u, w} B S hS} (F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eH : StacksRepresentableCFG.EquivalenceOver 𝒞.val.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
  (c : 𝒜 ⟶ 𝒞)

/-- A 1-morphism out of an algebraic stack represented by an algebraic space is representable by
algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_of_representing (hF : IsAlgebraicSpace B S hS F)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    IsRepresentableByAlgebraicSpaces B S hS c.hom.hom :=
  isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒞.property ⟨F, hF, ⟨eF⟩⟩ c.hom

/-- **A 1-morphism between algebraic stacks represented by algebraic spaces is separated exactly
when the morphism of representing algebraic spaces it induces is** (Stacks 04YS and 04SW). -/
theorem isSeparated_iff_isSeparated_representingMap (hF : IsAlgebraicSpace B S hS F)
    (hH : IsAlgebraicSpace B S hS H) :
    IsSeparated B S hS c ↔
      Space.IsSeparated B S hS (representingMap B S hS 𝒜.val 𝒞.val F H eF eH c.hom) := by
  have := isLocalAtTarget_fppf_separatedProperty B S hS
  have hc := isRepresentableByAlgebraicSpaces_of_representing B S hS F c hF eF
  exact ((isSeparated_relativeDiagonal_tfae B S hS c hc).out 3 1).trans
    (hasRelativeProperty_iff_prop_representingMap B S hS (Space.separatedProperty B S hS) c.hom hc
      F H hF hH eF eH)

/-- **A 1-morphism between algebraic stacks represented by algebraic spaces is quasi-compact
exactly when the morphism of representing algebraic spaces it induces is** (Stacks 050T and
04SW). -/
theorem isQuasiCompactMorphism_iff_isQuasiCompact_representingMap (hF : IsAlgebraicSpace B S hS F)
    (hH : IsAlgebraicSpace B S hS H) :
    IsQuasiCompactMorphism.{u, w} B S hS c ↔
      Space.IsQuasiCompact B S hS (representingMap B S hS 𝒜.val 𝒞.val F H eF eH c.hom) := by
  have hc := isRepresentableByAlgebraicSpaces_of_representing B S hS F c hF eF
  exact (isQuasiCompact_iff_baseChange_quasiCompact B S hS c hc).symm.trans
    (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS (Space.quasiCompactProperty B S hS)
      c.hom hc F H hF hH eF eH)

/-- **A 1-morphism between algebraic stacks represented by algebraic spaces is locally of finite
type exactly when the morphism of representing algebraic spaces it induces is** (Stacks 06FM and
04SW). -/
theorem isLocallyOfFiniteType_iff_isLocallyOfFiniteType_representingMap
    (hF : IsAlgebraicSpace B S hS F)
    (hH : IsAlgebraicSpace B S hS H) :
    IsLocallyOfFiniteType B S hS c ↔
      Space.IsLocallyOfFiniteType B S hS (representingMap B S hS 𝒜.val 𝒞.val F H eF eH c.hom) := by
  have hc := isRepresentableByAlgebraicSpaces_of_representing B S hS F c hF eF
  exact (hasPropertyOnEverySmoothDiagram_lft_iff_relative B S hS c hc).trans
    (hasRelativeProperty_iff_prop_representingMap B S hS _ c.hom hc F H hF hH eF eH)

/-- **A 1-morphism between algebraic stacks represented by algebraic spaces is of finite type
exactly when the morphism of representing algebraic spaces it induces is.** -/
theorem isFiniteType_iff_isFiniteType_representingMap (hF : IsAlgebraicSpace B S hS F)
    (hH : IsAlgebraicSpace B S hS H) :
    IsFiniteType B S hS c ↔
      Space.IsFiniteType B S hS (representingMap B S hS 𝒜.val 𝒞.val F H eF eH c.hom) :=
  and_congr
    (isLocallyOfFiniteType_iff_isLocallyOfFiniteType_representingMap B S hS F H eF eH c hF hH)
    (isQuasiCompactMorphism_iff_isQuasiCompact_representingMap B S hS F H eF eH c hF hH)

/-- **A 1-morphism between algebraic stacks represented by algebraic spaces is universally closed
exactly when the morphism of representing algebraic spaces it induces is** (Stacks 0512 and
04SW). -/
theorem universallyClosed_iff_universallyClosed_representingMap (hF : IsAlgebraicSpace B S hS F)
    (hH : IsAlgebraicSpace B S hS H) :
    UniversallyClosed B S hS c ↔
      Space.UniversallyClosed B S hS (representingMap B S hS 𝒜.val 𝒞.val F H eF eH c.hom) := by
  have := isLocalAtTarget_fppf_universallyClosedProperty B S hS
  have hc := isRepresentableByAlgebraicSpaces_of_representing B S hS F c hF eF
  exact (representable_universallyClosed_iff_closedMap_baseChange B S hS c hc).symm.trans
    (hasRelativeProperty_iff_prop_representingMap B S hS (Space.universallyClosedProperty B S hS)
      c.hom hc F H hF hH eF eH)

/-- **A 1-morphism between algebraic stacks represented by algebraic spaces is proper exactly
when the morphism of representing algebraic spaces it induces is.** -/
theorem isProper_iff_isProper_representingMap (hF : IsAlgebraicSpace B S hS F)
    (hH : IsAlgebraicSpace B S hS H) :
    IsProper B S hS c ↔
      Space.IsProper B S hS (representingMap B S hS 𝒜.val 𝒞.val F H eF eH c.hom) :=
  and_congr (isSeparated_iff_isSeparated_representingMap B S hS F H eF eH c hF hH)
    (and_congr (isFiniteType_iff_isFiniteType_representingMap B S hS F H eF eH c hF hH)
      (universallyClosed_iff_universallyClosed_representingMap B S hS F H eF eH c hF hH))

end Represented

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
