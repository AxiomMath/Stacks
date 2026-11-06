module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Separatedness and universal closedness across a morphism of thickenings of algebraic spaces

A morphism of thickenings of algebraic spaces over a scheme `S` is a commutative square

```
X --a--→ Y
|        |
i        j
↓        ↓
X' --b-→ Y'
```

whose vertical arrows are the inclusions of thickenings, that is a morphism in the arrow
category whose source and target arrows are the inclusions `G.ι` and `H.ι` of closed
subspaces that are surjective on points. Then `a` is universally closed, quasi-compact,
respectively separated exactly when `b` is. More generally this holds for any commutative square
whose vertical arrows are closed immersions, the left one surjective.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_iff_universallyClosed_of_isThickening`: `a` is
  universally closed if and only if `b` is.
* `AlgebraicGeometry.Space.isQuasiCompact_iff_isQuasiCompact_of_isThickening`: `a` is
  quasi-compact if and only if `b` is.
* `AlgebraicGeometry.Space.isSeparated_iff_isSeparated_of_isThickening`: `a` is separated if and
  only if `b` is.
* `AlgebraicGeometry.Space.isSeparated_iff_universallyClosed_pullback_diagonal`: a morphism of
  algebraic spaces over `S` is separated exactly when its relative diagonal is universally
  closed.
* `AlgebraicGeometry.Space.universallyClosed_iff_universallyClosed_of_isClosedImmersion_square`,
  `AlgebraicGeometry.Space.isQuasiCompact_iff_isQuasiCompact_of_isClosedImmersion_square`,
  `AlgebraicGeometry.Space.isSeparated_iff_isSeparated_of_isClosedImmersion_square`: the three
  comparisons for a commutative square whose vertical arrows are closed immersions, the left one
  surjective.

## References

* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 05W8](https://stacks.math.columbia.edu/tag/05W8)
* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_SeparatedAndClosed :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for pullbacks of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_SeparatedAndClosed
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The relative diagonal -/

section Diagonal

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The relative diagonal of a morphism of algebraic spaces over `S` is locally of finite
type. -/
theorem isLocallyOfFiniteType_pullback_diagonal (hX : IsAlgebraicSpace B S hS X) (q : X ⟶ Y) :
    IsLocallyOfFiniteType B S hS (pullback.diagonal q) :=
  presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType B S hS (pullback.diagonal q)
    (presheaf_of_isPullback B S hS (isPullback_pullbackDiagonal_diag B S hS q)
      (presheaf_locallyOfFiniteType_diag B S hS X hX))

/-- A morphism of algebraic spaces over `S` is separated exactly when its relative diagonal is
universally closed. -/
theorem isSeparated_iff_universallyClosed_pullback_diagonal (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (q : X ⟶ Y) :
    IsSeparated B S hS q ↔ UniversallyClosed B S hS (pullback.diagonal q) := by
  refine Iff.trans ((closedImmersion_conditions_tfae B S hS hX
    (isAlgebraicSpace_pullback B S hS q q hX hX hY) (pullback.diagonal q)).out 1 4) ?_
  exact ⟨And.left, fun h ↦ ⟨h, isLocallyOfFiniteType_pullback_diagonal B S hS hX q,
    IsSplitMono.mono _⟩⟩

end Diagonal

/-! ### A square whose vertical arrows are closed immersions -/

section Square

variable {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- In a commutative square `a ≫ j = i ≫ b` of morphisms of algebraic spaces over `S` whose
vertical arrows `i` and `j` are closed immersions, the comparison
`X ×[Y] X ⟶ X' ×[Y'] X'` of relative diagonal objects is a closed immersion. -/
theorem isClosedImmersion_pullbackMap {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {b : X' ⟶ Y'}
    (hi : IsClosedImmersion B S hS i) (hj : IsClosedImmersion B S hS j)
    (hw : a ≫ j = i ≫ b) :
    IsClosedImmersion B S hS (pullback.map a a b b i i j hw hw) := by
  have := isClosedImmersion_isStableUnderBaseChange B S hS
  have := isClosedImmersion_isStableUnderComposition B S hS
  have hw' : (a ≫ j) ≫ 𝟙 Y' = i ≫ b := (Category.comp_id _).trans hw
  have hm : IsClosedImmersion B S hS
      (pullback.map (a ≫ j) (a ≫ j) b b i i (𝟙 Y') hw' hw') :=
    MorphismProperty.pullbackMap hi hi hw hw
  have hmd : IsClosedImmersion B S hS (pullback.mapDesc a a j) :=
    isClosedImmersion_mapDesc B S hS a a j (isSeparated_of_isClosedImmersion B S hS j hj)
  have heq : pullback.map a a b b i i j hw hw =
      pullback.mapDesc a a j ≫ pullback.map (a ≫ j) (a ≫ j) b b i i (𝟙 Y') hw' hw' := by
    apply pullback.hom_ext <;>
      simp [pullback.map, pullback.mapDesc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  rw [heq]
  exact MorphismProperty.comp_mem _ _ _ hmd hm

/-- The two relative diagonals of a commutative square `a ≫ j = i ≫ b` sit in a commutative
square over the comparison of relative diagonal objects. -/
theorem pullback_diagonal_comp_pullbackMap {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {b : X' ⟶ Y'}
    (hw : a ≫ j = i ≫ b) :
    pullback.diagonal a ≫ pullback.map a a b b i i j hw hw = i ≫ pullback.diagonal b := by
  apply pullback.hom_ext <;> simp [pullback.map, pullback.lift_fst, pullback.lift_snd]

/-- In a commutative square
`a ≫ j = i ≫ b` of morphisms of algebraic spaces over `S` whose vertical arrows are closed
immersions, the left one surjective, `a` is universally closed if and only if `b` is. -/
theorem universallyClosed_iff_universallyClosed_of_isClosedImmersion_square
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b) :
    UniversallyClosed B S hS a ↔ UniversallyClosed B S hS b :=
  ⟨fun ha ↦ universallyClosed_of_isSurjective_comp B S hS hX hX' hY' i b
      (hw ▸ universallyClosed_comp B S hS hY hY' a j ha
        (universallyClosed_of_isClosedImmersion B S hS hY hY' j hj)) hisurj,
    fun hb ↦ universallyClosed_of_comp_of_isSeparated B S hS hX hY hY' a j
      (hw ▸ universallyClosed_comp B S hS hX' hY' i b
        (universallyClosed_of_isClosedImmersion B S hS hX hX' i hi) hb)
      (isSeparated_of_isClosedImmersion B S hS j hj)⟩

/-- In a commutative square
`a ≫ j = i ≫ b` of morphisms of algebraic spaces over `S` whose vertical arrows are closed
immersions, the left one surjective, `a` is quasi-compact if and only if `b` is. -/
theorem isQuasiCompact_iff_isQuasiCompact_of_isClosedImmersion_square
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b) :
    IsQuasiCompact B S hS a ↔ IsQuasiCompact B S hS b :=
  ⟨fun ha ↦ isQuasiCompact_of_comp_surjective B S hS hX hX' hY' i (i ≫ b) b rfl hisurj
      (hw ▸ isQuasiCompact_comp B S hS hY hY' a j ha
        (isQuasiCompact_of_isClosedImmersion' B S hS hj)),
    fun hb ↦ isQuasiCompact_of_comp_of_isQuasiSeparated B S hS a j hX hY'
      (hw ▸ isQuasiCompact_comp B S hS hX' hY' i b
        (isQuasiCompact_of_isClosedImmersion' B S hS hi) hb)
      (isQuasiCompact_of_isClosedImmersion' B S hS
        (isSeparated_of_isClosedImmersion B S hS j hj))⟩

/-- In a commutative square `a ≫ j = i ≫ b` of morphisms of algebraic spaces over `S` whose
vertical arrows are closed immersions, the left one surjective, `a` is separated if and only if
`b` is. -/
theorem isSeparated_iff_isSeparated_of_isClosedImmersion_square
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b) :
    IsSeparated B S hS a ↔ IsSeparated B S hS b := by
  have hXX : IsAlgebraicSpace B S hS (pullback a a) :=
    isAlgebraicSpace_pullback B S hS a a hX hX hY
  have hX'X' : IsAlgebraicSpace B S hS (pullback b b) :=
    isAlgebraicSpace_pullback B S hS b b hX' hX' hY'
  refine ⟨fun ha ↦ (isSeparated_iff_universallyClosed_pullback_diagonal B S hS hX' hY' b).mpr ?_,
    fun hb ↦ isSeparated_of_comp B S hS a j
      (hw ▸ isSeparated_comp B S hS i b (isSeparated_of_isClosedImmersion B S hS i hi) hb)⟩
  have h : UniversallyClosed B S hS
      (pullback.diagonal a ≫ pullback.map a a b b i i j hw hw) :=
    universallyClosed_comp B S hS hXX hX'X' _ _
      ((isSeparated_iff_universallyClosed_pullback_diagonal B S hS hX hY a).mp ha)
      (universallyClosed_of_isClosedImmersion B S hS hXX hX'X' _
        (isClosedImmersion_pullbackMap B S hS hi hj hw))
  rw [pullback_diagonal_comp_pullbackMap B S hS hw] at h
  exact universallyClosed_of_isSurjective_comp B S hS hX hX' hX'X' i (pullback.diagonal b) h hisurj

end Square

/-! ### Morphisms of thickenings -/

section Thickening

variable {X Y : AlgebraicSpaces B S hS} {G : Subfunctor X.1} {H : Subfunctor Y.1}

/-- In a morphism of thickenings of algebraic spaces over `S` the
morphism on the closed subspaces is universally closed if and only if the morphism on the
ambient spaces is. -/
@[stacks 09ZY "part (4): universally closed"]
theorem universallyClosed_iff_universallyClosed_of_isThickening
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι) :
    UniversallyClosed B S hS f.left ↔ UniversallyClosed B S hS f.right :=
  universallyClosed_iff_universallyClosed_of_isClosedImmersion_square B S hS hG.1.1 X.2
    hH.1.1 Y.2 f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f)

/-- In a morphism of thickenings of algebraic spaces over `S` the
morphism on the closed subspaces is quasi-compact if and only if the morphism on the ambient
spaces is. -/
@[stacks 09ZY "part (3): quasi-compact"]
theorem isQuasiCompact_iff_isQuasiCompact_of_isThickening
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι) :
    IsQuasiCompact B S hS f.left ↔ IsQuasiCompact B S hS f.right :=
  isQuasiCompact_iff_isQuasiCompact_of_isClosedImmersion_square B S hS hG.1.1 X.2
    hH.1.1 Y.2 f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f)

/-- In a morphism of thickenings of algebraic spaces over `S` the morphism on the closed
subspaces is separated if and only if the morphism on the ambient spaces is. -/
@[stacks 09ZY "part (6): the separated half only, not quasi-separated"]
theorem isSeparated_iff_isSeparated_of_isThickening
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι) :
    IsSeparated B S hS f.left ↔ IsSeparated B S hS f.right :=
  isSeparated_iff_isSeparated_of_isClosedImmersion_square B S hS hG.1.1 X.2
    hH.1.1 Y.2 f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f)

end Thickening

end AlgebraicGeometry.Space

end
