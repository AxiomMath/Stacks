module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.QuasiSeparatedTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversallyOpenTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyCancelFirst
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationAxioms

/-!
# From the closed substack to the ambient stack in a thickening of algebraic stacks

`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationAxioms` proves the implication from
the ambient stack `𝒳'` to the closed substack `𝒳` of each of clauses (1), (3), (4), (5) and (6)
of **Stacks 0BPW**. This file proves the converse implication — from `𝒳` to `𝒳'` — of clauses
(5) and (6), so that each of those is an `if and only if`.

The same mechanism, read at the two relative diagonals of a morphism of thickenings rather than
at the structure morphisms over the base, proves six of the seventeen properties of **Stacks
0BPV**: (d) quasi-compactness, (e) universal closedness, (g) quasi-separatedness, (h)
separatedness, (j) universal openness and (q) properness, each as the `if and only if` the source
states.

## The mechanism

Each of clauses (3)–(6) is a condition of Properties of Stacks, Section 04XB, on the relative
diagonal. The ambient-to-substack direction is base change along the cartesian diagonal square of
**Stacks 0BPU**. The substack-to-ambient direction is not a base change, and the route taken here
is the factorisation that square gives:

`Δ ≫ k ≅ i ≫ Δ'`,

where `k : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` is the comparison of
`AlgebraicGeometry.Stack.selfProductDiagonalMap`, itself a thickening by the first assertion of
Stacks 0BPU. So a condition of Stacks 04XB enjoyed by `Δ` and by `k` is enjoyed by `i ≫ Δ'`
(**Stacks 045B**, composition, and **Stacks 0457** to move it along the 2-isomorphism), and what
remains is to cancel the thickening `i` off the front. That cancellation is
`AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_spaceCancelFirst`, and it asks for the
corresponding cancellation at the level of morphisms of *algebraic spaces*: a composite `a ≫ b`
with the property whose first factor `a` is a surjective closed immersion has `b` with the
property.

For quasi-separatedness of **Stacks 04YW** — the conjunction of quasi-compactness and
quasi-separatedness of `Δ` in the sense of Stacks 04XB — both space-level cancellations are
available: quasi-compactness is **Stacks 040W** part (2)
(`AlgebraicGeometry.Space.isQuasiCompact_of_comp_surjective`) and quasi-separatedness is the
quasi-separated half of **Stacks 09ZY** part (6),
`AlgebraicGeometry.Space.isQuasiSeparated_iff_isQuasiSeparated_of_isClosedImmersion_square`
read at an identity right-hand inclusion.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_outer_of_inner`: the transfer of
  a condition of Stacks 04XB from the restricted relative diagonal to the ambient one, for a
  morphism of thickenings of algebraic stacks. This is the engine; the clauses below are
  instances of it.
* `AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_inner_of_outer`: the converse
  transfer, which is base change along the cartesian diagonal square of **Stacks 0BPU**.
* `AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_iff`: the two together, in the
  shape every clause of **Stacks 0BPV** has, with the space-level cancellation as the only input.
* `AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_iff`,
  `AlgebraicGeometry.Stack.universallyClosed_relativeDiagonal_iff`,
  `AlgebraicGeometry.Stack.isQuasiSeparated_relativeDiagonal_iff`,
  `AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_iff`,
  `AlgebraicGeometry.Stack.universallyOpen_relativeDiagonal_iff` and
  `AlgebraicGeometry.Stack.isProper_relativeDiagonal_iff`: **Stacks 0BPV** at its properties (d),
  (e), (g), (h), (j) and (q).
* `AlgebraicGeometry.Stack.isQuasiSeparated_outer_of_inner` and
  `AlgebraicGeometry.Stack.isSeparated_outer_of_inner`: quasi-separatedness and separatedness in
  the sense of **Stacks 04YW** pass from the restricted 1-morphism of a morphism of thickenings
  to the ambient one, being conjunctions of the clauses above.
* `AlgebraicGeometry.Stack.isQuasiSeparatedOver_iff_isThickening` and
  `AlgebraicGeometry.Stack.isSeparatedOver_iff_isThickening`: **Stacks 0BPW**, clauses (6) and
  (5), as the `if and only if` the source states.

## Implementation notes

The two clauses of a thickening are fed to the cancellation as two separate properties of
morphisms of algebraic spaces, `AlgebraicGeometry.Space.closedImmersionProperty` and
`AlgebraicGeometry.Space.surjectiveMorphismProperty`; each has its own base-change and
fppf-target-locality instances, and the surjectivity clause of a thickening of algebraic stacks
is already in the relative form of Stacks 03YK, through
`AlgebraicGeometry.Stack.isRelativeThickening_of_isThickening`.

The space-level cancellation for quasi-separatedness is read off the square comparison with the
right-hand inclusion taken to be an identity, which is a closed immersion by
`AlgebraicGeometry.Space.isClosedImmersion_id`.

Clause (5) of Stacks 0BPW is a condition of Stacks 04XB at `AlgebraicGeometry.Space.IsProper`,
and for *that* property the space-level cancellation the engine asks for is false: a thickening
of the source destroys being locally of finite type, which properness contains. (An affine
thickening `Spec(k) ⊂ Spec(R)` with `R` a non-finitely generated `k`-algebra with residue field
`k` is locally of finite type over `k` downstairs and not upstairs.) It is nevertheless proved
below, because properness splits: its other three conjuncts are clauses (h), (d) and (e) of
Stacks 0BPV, and the locally-of-finite-type conjunct is free for a relative diagonal by part (2)
of **Stacks 04XS**.

Clauses (3) and (4) of Stacks 0BPW are conditions of Stacks 04XB at
`AlgebraicGeometry.Space.IsLocallyQuasiFinite` and `AlgebraicGeometry.Space.IsUnramified`, and
those do *not* split: the finite-type conjunct is not separable from the rest, so the false
cancellation is the whole obstruction and no instance of
`AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_iff` reaches them.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03Z2](https://stacks.math.columbia.edu/tag/03Z2)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 042R](https://stacks.math.columbia.edu/tag/042R)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04CG](https://stacks.math.columbia.edu/tag/04CG)
* [Stacks Project, Tag 04CH](https://stacks.math.columbia.edu/tag/04CH)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04ZT](https://stacks.math.columbia.edu/tag/04ZT)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
* [Stacks Project, Tag 06U2](https://stacks.math.columbia.edu/tag/06U2)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
* [Stacks Project, Tag 0BPU](https://stacks.math.columbia.edu/tag/0BPU)
* [Stacks Project, Tag 0BPV](https://stacks.math.columbia.edu/tag/0BPV)
* [Stacks Project, Tag 0BPW](https://stacks.math.columbia.edu/tag/0BPW)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The engine: transferring a condition of Stacks 04XB to the ambient diagonal -/

section Diagonal

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
  (m : ThickeningMorphism i j hi hj)

/-- **A condition of Stacks 04XB passes from the restricted relative diagonal of a morphism of
thickenings of algebraic stacks to the ambient one.** The hypotheses are the condition for the
restricted diagonal `Δ`, the condition for the comparison `k` of
`AlgebraicGeometry.Stack.selfProductDiagonalMap`, and the cancellation of the condition against a
surjective closed immersion for morphisms of algebraic spaces. -/
theorem hasRelativeProperty_relativeDiagonal_outer_of_inner
    (P R₁ R₂ : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [P.IsStableUnderComposition]
    [R₁.IsStableUnderBaseChange]
    [R₁.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [R₂.IsStableUnderBaseChange]
    [R₂.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hcancel : ∀ {A C D : AlgebraicSpaces B S hS} (a : A ⟶ C) (b : C ⟶ D),
      P (a ≫ b) → R₁ a → R₂ a → P b)
    (hR₁ : HasRelativeProperty.{u, u, u + 1, u} B S hS R₁ i.hom hi.1.1)
    (hR₂ : HasRelativeProperty.{u, u, u + 1, u} B S hS R₂ i.hom hi.1.1)
    (hPk : HasRelativeProperty.{u, u, u + 1, u} B S hS P
      (selfProductDiagonalMap B S hS m).hom
      (isThickening_selfProductDiagonalMap B S hS m).1.1)
    (h : HasRelativeProperty.{u, u, u + 1, u} B S hS P
      (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner)) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P
      (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer) := by
  have hk := isThickening_selfProductDiagonalMap B S hS m
  have hcomp := hasRelativeProperty_comp.{u, u, u + 1, u} B S hS P
    (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
    (selfProductDiagonalMap B S hS m).hom
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner)
    hk.1.1 h hPk
  have hmoved := hasRelativeProperty_congr_twoIso.{u, u, u + 1, u} B S hS P
    (algebraicStacksTwoIsoHom B S hS (diagonalThickeningMorphism B S hS m hk).comm)
    (isRepresentableByAlgebraicSpaces_comp B S hS
      (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
      (selfProductDiagonalMap B S hS m).hom
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner)
      hk.1.1)
    (isRepresentableByAlgebraicSpaces_comp B S hS i.hom
      (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom hi.1.1
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer))
    hcomp
  exact hasRelativeProperty_of_comp_of_spaceCancelFirst.{u, u} B S hS P R₁ R₂ hcancel i.hom
    (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom hi.1.1
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer) _
    hR₁ hR₂ hmoved

/-- The closed-immersion clause of a thickening of algebraic stacks, in the relative form of Stacks
03YK. -/
theorem hasRelativeProperty_closedImmersion_of_isThickening {𝒰 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {p : 𝒰 ⟶ 𝒵} (hp : IsThickening p) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.closedImmersionProperty B S hS) p.hom
      hp.1.1 :=
  (isClosedImmersion_iff_hasRelativeProperty.{u, u} B S hS p.hom hp.1.1).1 hp.1.2

/-- The surjectivity clause of a thickening of algebraic stacks, in the relative form of Stacks
03YK. -/
theorem hasRelativeProperty_surjective_of_isThickening {𝒰 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {p : 𝒰 ⟶ 𝒵} (hp : IsThickening p) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS) p.hom
      hp.1.1 :=
  (isRelativeThickening_of_isThickening B S hS hp).2.2 hp.1.1

/-- A thickening of algebraic stacks is quasi-compact in the sense of Stacks 04XB. -/
theorem isQuasiCompact_of_isThickening {𝒰 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {p : 𝒰 ⟶ 𝒵} (hp : IsThickening p) : Stack.IsQuasiCompact B S hS p.hom :=
  fun U y hy F hF he => Space.isQuasiCompact_of_isClosedImmersion' B S hS (hp.1.2 U y hy F hF he)

/-- A thickening of algebraic stacks is quasi-separated in the sense of Stacks 04XB. -/
theorem isQuasiSeparated_of_isThickening {𝒰 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {p : 𝒰 ⟶ 𝒵} (hp : IsThickening p) : Stack.IsQuasiSeparated B S hS p.hom :=
  fun U y hy F hF he => Space.isQuasiCompact_of_isClosedImmersion' B S hS
    (Space.isSeparated_of_isClosedImmersion B S hS _ (hp.1.2 U y hy F hF he))

/-- A thickening of algebraic stacks is separated in the sense of Stacks 04XB. -/
theorem isSeparated_of_isThickening {𝒰 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {p : 𝒰 ⟶ 𝒵} (hp : IsThickening p) : Stack.IsSeparated B S hS p.hom :=
  fun U y hy F hF he => Space.isSeparated_of_isClosedImmersion B S hS _ (hp.1.2 U y hy F hF he)

/-- A thickening of algebraic stacks is universally closed in the sense of Stacks 04XB. -/
theorem universallyClosed_of_isThickening {𝒰 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {p : 𝒰 ⟶ 𝒵} (hp : IsThickening p) : Stack.UniversallyClosed B S hS p.hom :=
  fun U y hy F hF he => Space.universallyClosed_of_isClosedImmersion B S hS
    ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
    (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) _ (hp.1.2 U y hy F hF he)

/-- A thickening of algebraic stacks is universally open in the sense of Stacks 04XB. -/
theorem universallyOpen_of_isThickening {𝒰 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {p : 𝒰 ⟶ 𝒵} (hp : IsThickening p) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.universallyOpenMorphismProperty B S hS)
      p.hom hp.1.1 :=
  fun U y hy F hF he => Space.universallyOpen_of_isClosedImmersion_of_isSurjective B S hS
    (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom))
    ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
    (hp.1.2 U y hy F hF he)
    (hasRelativeProperty_surjective_of_isThickening B S hS hp U y hy F hF he)

/-! ### The clauses of Stacks 0BPV the cancellation reaches -/

/-- A condition of Stacks 04XB passes from the ambient relative diagonal of a morphism of
thickenings of algebraic stacks to the restricted one. -/
theorem hasRelativeProperty_relativeDiagonal_inner_of_outer
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (h : HasRelativeProperty.{u, u, u + 1, u} B S hS P
      (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer)) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P
      (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) :=
  prop_baseChange_of_isTwoFibreProduct.{u, u, u} B S hS P 𝒳'.val _ _
    (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
    (selfProductDiagonalMap B S hS m).hom
    (AlgebraicStacks.toCatFiberedInGroupoids B S hS (selfProductDiagonalSquare B S hS m))
    (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS _
      (isTwoFibreProduct_selfProductDiagonalSquare B S hS m)) h

/-- **A condition of Stacks 04XB holds for the restricted relative diagonal of a morphism of
thickenings of algebraic stacks exactly when it holds for the ambient one.** The hypotheses are the
condition for the comparison `AlgebraicGeometry.Stack.selfProductDiagonalMap` and the cancellation
of `P` against a surjective closed immersion at the level of morphisms of algebraic spaces. -/
theorem hasRelativeProperty_relativeDiagonal_iff
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [P.IsStableUnderComposition]
    (hcancel : ∀ {A C D : AlgebraicSpaces B S hS} (a : A ⟶ C) (b : C ⟶ D),
      P (a ≫ b) → Space.closedImmersionProperty B S hS a →
        Space.surjectiveMorphismProperty B S hS a → P b)
    (hPk : HasRelativeProperty.{u, u, u + 1, u} B S hS P
      (selfProductDiagonalMap B S hS m).hom
      (isThickening_selfProductDiagonalMap B S hS m).1.1) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS P
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer) :=
  ⟨hasRelativeProperty_relativeDiagonal_outer_of_inner B S hS m P
      (Space.closedImmersionProperty B S hS) (Space.surjectiveMorphismProperty B S hS) hcancel
      (hasRelativeProperty_closedImmersion_of_isThickening B S hS hi)
      (hasRelativeProperty_surjective_of_isThickening B S hS hi) hPk,
    hasRelativeProperty_relativeDiagonal_inner_of_outer B S hS m P⟩

/-- A property of morphisms of algebraic spaces local at the target for the fpqc precoverage is
local at the target for the fppf precoverage. -/
private instance isLocalAtTarget_fppf_of_fpqc
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Space.Topology.fpqc.precoverage.{u, u} B S hS)] :
    P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
  .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is quasi-compact in the sense of Stacks 04XB (**Stacks 03HE**)
if and only if `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
@[stacks 0BPV "property (d) of seventeen: quasi-compact"]
theorem isQuasiCompact_relativeDiagonal_iff :
    Stack.IsQuasiCompact B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsQuasiCompact B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom :=
  hasRelativeProperty_relativeDiagonal_iff B S hS m (Space.quasiCompactProperty B S hS)
    (fun {A C D} a b hab _hci hsurj => Space.isQuasiCompact_of_comp_surjective B S hS
      A.2 C.2 D.2 a.hom (a.hom ≫ b.hom) b.hom rfl hsurj hab)
    (isQuasiCompact_of_isThickening B S hS (isThickening_selfProductDiagonalMap B S hS m))

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is quasi-separated in the sense of Stacks 04XB (**Stacks 03HL**
part (3)) if and only if `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
@[stacks 0BPV "property (g) of seventeen: quasi-separated"]
theorem isQuasiSeparated_relativeDiagonal_iff :
    Stack.IsQuasiSeparated B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsQuasiSeparated B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom :=
  hasRelativeProperty_relativeDiagonal_iff B S hS m (Space.quasiSeparatedProperty B S hS)
    (fun {A C D} a b hab hci hsurj =>
      (Space.isQuasiSeparated_iff_isQuasiSeparated_of_isClosedImmersion_square B S hS
        A.2 C.2 D.2 D.2 (i := a.hom) (j := 𝟙 D.1) (a.hom ≫ b.hom) b.hom hci hsurj
        (Space.isClosedImmersion_id B S hS D.1) (Category.comp_id _)).1 hab)
    (isQuasiSeparated_of_isThickening B S hS (isThickening_selfProductDiagonalMap B S hS m))

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is separated in the sense of Stacks 04XB (**Stacks 03HL** part
(1)) if and only if `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
@[stacks 0BPV "property (h) of seventeen: separated"]
theorem isSeparated_relativeDiagonal_iff :
    Stack.IsSeparated B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsSeparated B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom :=
  hasRelativeProperty_relativeDiagonal_iff B S hS m (Space.separatedProperty B S hS)
    (fun {A C D} a b hab hci hsurj =>
      (Space.isSeparated_iff_isSeparated_of_isClosedImmersion_square B S hS
        A.2 C.2 D.2 D.2 (i := a.hom) (j := 𝟙 D.1) (a.hom ≫ b.hom) b.hom hci hsurj
        (Space.isClosedImmersion_id B S hS D.1) (Category.comp_id _)).1 hab)
    (isSeparated_of_isThickening B S hS (isThickening_selfProductDiagonalMap B S hS m))

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is universally closed in the sense of Stacks 04XB
(**Stacks 03HI** part (2)) if and only if `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
@[stacks 0BPV "property (e) of seventeen: universally closed"]
theorem universallyClosed_relativeDiagonal_iff :
    Stack.UniversallyClosed B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.UniversallyClosed B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom :=
  hasRelativeProperty_relativeDiagonal_iff B S hS m
    (Space.universallyClosedProperty B S hS)
    (fun {A C D} a b hab _hci hsurj => Space.universallyClosed_of_isSurjective_comp B S hS
      A.2 C.2 D.2 a.hom b.hom hab hsurj)
    (universallyClosed_of_isThickening B S hS (isThickening_selfProductDiagonalMap B S hS m))

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is universally open in the sense of Stacks 04XB
(**Stacks 03Z2** part (2)) if and only if `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
@[stacks 0BPV "property (j) of seventeen: universally open"]
theorem universallyOpen_relativeDiagonal_iff :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.universallyOpenMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.universallyOpenMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer) :=
  hasRelativeProperty_relativeDiagonal_iff B S hS m
    (Space.universallyOpenMorphismProperty B S hS)
    (fun {A C D} a b hab _hci hsurj => Space.universallyOpen_of_isSurjective_comp B S hS
      A.2 C.2 D.2 a.hom b.hom hab hsurj)
    (universallyOpen_of_isThickening B S hS (isThickening_selfProductDiagonalMap B S hS m))

/-- Quasi-separatedness in the sense of Stacks 04YW passes from the restricted 1-morphism of a
morphism of thickenings of algebraic stacks to the ambient one. -/
theorem isQuasiSeparated_outer_of_inner
    (h : AlgebraicStacks.IsQuasiSeparated B S hS m.inner) :
    AlgebraicStacks.IsQuasiSeparated B S hS m.outer :=
  ⟨(isQuasiCompact_relativeDiagonal_iff B S hS m).1 h.1,
    (isQuasiSeparated_relativeDiagonal_iff B S hS m).1 h.2⟩

/-- Separatedness in the sense of Stacks 04YW passes from the restricted 1-morphism of a morphism
of thickenings of algebraic stacks to the ambient one. -/
theorem isSeparated_outer_of_inner (h : AlgebraicStacks.IsSeparated B S hS m.inner) :
    AlgebraicStacks.IsSeparated B S hS m.outer := by
  have hsep := (isSeparated_relativeDiagonal_iff B S hS m).1
    (fun U y hy F hF he => (h U y hy F hF he).1)
  have hqc := (isQuasiCompact_relativeDiagonal_iff B S hS m).1
    (fun U y hy F hF he => (h U y hy F hF he).2.1.2)
  have huc := (universallyClosed_relativeDiagonal_iff B S hS m).1
    (fun U y hy F hF he => (h U y hy F hF he).2.2)
  have hlft :=
    (isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack.{u, w} B S hS m.outer).choose_spec
  exact fun U y hy F hF he => ⟨hsep U y hy F hF he,
    ⟨hlft U y hy F hF he, hqc U y hy F hF he⟩, huc U y hy F hF he⟩

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is proper in the sense of Stacks 04XB (**Stacks 03ZM**) if and
only if `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
@[stacks 0BPV "property (q) of seventeen: proper"]
theorem isProper_relativeDiagonal_iff :
    Stack.IsProper B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsProper B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom :=
  ⟨isSeparated_outer_of_inner B S hS m, isSeparated_inner_of_outer B S hS m⟩

end Diagonal

/-! ### Stacks 0BPW, clauses (5) and (6) -/

section Thickening

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over `S` then `𝒳` is quasi-separated over `S`
if and only if `𝒳'` is. Here quasi-separatedness over `S` is part (4) of **Stacks 050D**. -/
@[stacks 0BPW "clause (6): quasi-separated over the base"]
theorem isQuasiSeparatedOver_iff_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    IsQuasiSeparatedOver B S hS 𝒳 ↔ IsQuasiSeparatedOver B S hS 𝒳' :=
  ⟨isQuasiSeparated_outer_of_inner B S hS (structureThickeningMorphism B S hS i hi),
    isQuasiSeparatedOver_of_isThickening B S hS i hi⟩

/-- If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over `S` then `𝒳` is separated over `S` if and
only if `𝒳'` is. Here separatedness over `S` is part (3) of **Stacks 050D**. -/
@[stacks 0BPW "clause (5): separated over the base"]
theorem isSeparatedOver_iff_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    IsSeparatedOver B S hS 𝒳 ↔ IsSeparatedOver B S hS 𝒳' :=
  ⟨isSeparated_outer_of_inner B S hS (structureThickeningMorphism B S hS i hi),
    isSeparatedOver_of_isThickening B S hS i hi⟩

end Thickening

end AlgebraicGeometry.Stack

end
