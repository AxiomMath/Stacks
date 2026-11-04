module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.Separation
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Blowup

/-!
# Flattening a morphism by a pair of almost blowup squares

Let `f : X ⟶ Y` be a morphism of finite presentation and let `V ⊆ Y` be an open over which `f`
is flat. Stacks tag 0EVC produces a commutative diagram

```
E ---------> D
|  \       /  |
|   Y' <- X'  |
|   |     |   |
|   Y  <- X   |
Z ---------> T
```

whose left-hand square `(E, Y', Y, Z)` and right-hand square `(D, X', X, T)` are almost blowup
squares, whose lower square `(Z, T, Y, X)` and top square `(E, D, Y', X')` are cartesian, whose
left-hand centre `Z` misses `V`, and whose relative morphism `X' ⟶ Y'` is flat and of finite
presentation.

## Main definitions

* `AlgebraicGeometry.HasFlatAlmostBlowUpSquarePair` is the conclusion of Stacks tag 0EVC.

## Main results

* `AlgebraicGeometry.lowerSquareIso` and `AlgebraicGeometry.topSquareIso` exhibit the lower and
  the top square of the diagram as cartesian.
* `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_flat_strictTransformToBlowUp` builds the
  diagram from a centre on `Y` whose blowup flattens the strict transform of `X`.
* `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair` is Stacks tag 0EVC for a locally Noetherian
  base, feeding that construction from the flattening blowup of Stacks tag 081R.

## Implementation notes

An almost blowup square is recorded by its base, its centre — a quasi-coherent ideal sheaf — and
its modification, as `AlgebraicGeometry.IsAlmostBlowUpSquare`; the two remaining corners are the
closed subscheme cut out by the centre and the closed subscheme cut out by the inverse image of
the centre in the modification. Writing the right-hand square with centre `Z·𝒪_X` therefore makes
both cartesianness assertions of the tag automatic rather than extra data:

* the lower square is cartesian because `(Z·𝒪_X).subscheme ≅ X ×_Y Z.subscheme`, which is
  `AlgebraicGeometry.Scheme.IdealSheafData.comapIso`; this is
  `AlgebraicGeometry.lowerSquareIso`;
* the top square is cartesian because `(Z·𝒪_X)·𝒪_{X'} = (Z·𝒪_{Y'})·𝒪_{X'}` as soon as the two
  routes `X' ⟶ Y` agree, so the same `comapIso` identifies `D` with `E ×_{Y'} X'`; this is
  `AlgebraicGeometry.topSquareIso`.

The construction follows the Noetherian case of the Stacks proof. The left-hand square is the
honest blowup square of the flattening centre `Z` produced by tag 081R, which is an almost blowup
square over a locally Noetherian base
(`AlgebraicGeometry.isAlmostBlowUpSquare_blowUpToBase_of_fg`). The right-hand square is the
honest blowup square of `Z·𝒪_X` in `X`, which is locally Noetherian because `f` is locally of
finite type; this is where the Stacks proof's parenthetical "we also use that strict transforms
are blow ups" enters, as `AlgebraicGeometry.strictTransformBlowUpIso` (tag 080E, part 1): it
transports the flatness of the strict transform over `Y'` to flatness of `Bl_{Z·𝒪_X}(X) ⟶ Y'`.
Finite presentation of that morphism is then automatic, the blowup of a locally Noetherian scheme
being locally Noetherian; this is why tag 081R's unproved finite-presentation assertion is not
needed here.

What this file does *not* do is the reduction of the general quasi-compact and quasi-separated
case to the Noetherian one by absolute Noetherian approximation.

## References

* [Stacks Project, Tag 0EVC](https://stacks.math.columbia.edu/tag/0EVC)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 0EVA](https://stacks.math.columbia.edu/tag/0EVA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **The conclusion of Stacks Project, Tag 0EVC.** There are a centre `Z` on `Y` and a centre
`Z·𝒪_X` on `X`, a modification `b : Y' ⟶ Y` and a modification `c : X' ⟶ X` making both the
left-hand and the right-hand square of the tag's diagram almost blowup squares, with `Z` disjoint
from `V`, together with a morphism `g : X' ⟶ Y'` over `Y` which is flat and of finite
presentation.

The remaining two assertions of the tag — that the lower and the top square are cartesian — are
consequences of this shape, by `AlgebraicGeometry.lowerSquareIso` and
`AlgebraicGeometry.topSquareIso`. -/
public def HasFlatAlmostBlowUpSquarePair (f : X ⟶ Y) (V : Y.Opens) : Prop :=
  ∃ (Z : Y.IdealSheafData) (Y' : Scheme.{u}) (b : Y' ⟶ Y) (X' : Scheme.{u}) (c : X' ⟶ X)
      (g : X' ⟶ Y'),
    IsAlmostBlowUpSquare Z b ∧ IsAlmostBlowUpSquare (Z.comap f) c ∧
      Disjoint (V : Set Y) (Z.support : Set Y) ∧
        g ≫ b = c ≫ f ∧ Flat g ∧ FinitePresentation g

/-- **The lower square of the diagram of Stacks Project, Tag 0EVC is cartesian.** The centre `T`
of the right-hand almost blowup square, namely the closed subscheme cut out by `Z·𝒪_X`, is the
fibre product of `X ⟶ Y` with the centre `Z` of the left-hand square. -/
public def lowerSquareIso (f : X ⟶ Y) (Z : Y.IdealSheafData) :
    (Z.comap f).subscheme ≅ pullback f Z.subschemeι :=
  Z.comapIso f

/-- The inverse image of `Z·𝒪_X` in `X'` and the inverse image of `Z·𝒪_{Y'}` in `X'` agree, as
soon as the two routes `X' ⟶ Y` agree: both are the inverse image of `Z` along the common
composite. -/
public theorem comap_comap_eq_comap_comap {X' Y' : Scheme.{u}} (f : X ⟶ Y) (b : Y' ⟶ Y)
    (c : X' ⟶ X) (g : X' ⟶ Y') (Z : Y.IdealSheafData) (h : g ≫ b = c ≫ f) :
    (Z.comap f).comap c = (Z.comap b).comap g := by
  rw [← Scheme.IdealSheafData.comap_comp Z c f, ← Scheme.IdealSheafData.comap_comp Z g b, h]

/-- **The top square of the diagram of Stacks Project, Tag 0EVC is cartesian.** The exceptional
subscheme `D` of the right-hand almost blowup square, namely the closed subscheme cut out by
`(Z·𝒪_X)·𝒪_{X'}`, is the fibre product of `X' ⟶ Y'` with the exceptional subscheme `E` of the
left-hand square. -/
public def topSquareIso {X' Y' : Scheme.{u}} (f : X ⟶ Y) (b : Y' ⟶ Y) (c : X' ⟶ X)
    (g : X' ⟶ Y') (Z : Y.IdealSheafData) (h : g ≫ b = c ≫ f) :
    ((Z.comap f).comap c).subscheme ≅ pullback g (Z.comap b).subschemeι :=
  eqToIso (congrArg (fun I : X'.IdealSheafData ↦ I.subscheme)
    (comap_comap_eq_comap_comap f b c g Z h)) ≪≫ (Z.comap b).comapIso g

/-- Over a locally Noetherian base every centre is finitely generated, so its blowup square is an
almost blowup square. -/
private theorem isAlmostBlowUpSquare_blowUpToBase_of_isLocallyNoetherian
    [IsLocallyNoetherian Y] (I : Y.IdealSheafData) :
    IsAlmostBlowUpSquare I (blowUpToBase I) :=
  isAlmostBlowUpSquare_blowUpToBase_of_fg I fun U ↦
    have := IsLocallyNoetherian.component_noetherian U
    Ideal.fg_of_isNoetherianRing _

/-- **The diagram of Stacks Project, Tag 0EVC from a flattening centre.** Given a centre `J` on a
locally Noetherian `Y`, disjoint from `V`, whose blowup flattens the strict transform of `X`, the
two honest blowup squares of `J` in `Y` and of `J·𝒪_X` in `X` are the two almost blowup squares
the tag asks for.

Over a locally Noetherian base a blowup square in a finitely generated centre is an almost blowup
square, and `X` is locally Noetherian because `f` is locally of finite type. The morphism
`X' ⟶ Y'` is the structure morphism of the strict transform of `X` read through the identification
of the strict transform with the blowup of the inverse-image centre (tag 080E), which is where its
flatness comes from; it is of finite presentation because it is of finite type over the locally
Noetherian `Y'`. -/
public theorem hasFlatAlmostBlowUpSquarePair_of_flat_strictTransformToBlowUp
    [IsLocallyNoetherian Y] (f : X ⟶ Y) (hf : FinitePresentation f) (V : Y.Opens)
    (J : Y.IdealSheafData) (hJdisj : Disjoint (V : Set Y) (J.support : Set Y))
    (hJflat : Flat (strictTransformToBlowUp f J)) :
    HasFlatAlmostBlowUpSquarePair f V := by
  have hlfp : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have hqc : QuasiCompact f := hf.quasiCompact
  have hLNX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hLNY' : IsLocallyNoetherian (blowUp J) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase J)
  have hiso : IsIso (strictTransformBlowUpIso f J).inv.left :=
    (Over.forget X).map_isIso (strictTransformBlowUpIso f J).inv
  have hflat : Flat (strictTransformToBlowUp f J) := hJflat
  refine ⟨J, blowUp J, blowUpToBase J, blowUp (J.comap f), blowUpToBase (J.comap f),
    (strictTransformBlowUpIso f J).inv.left ≫ strictTransformToBlowUp f J,
    isAlmostBlowUpSquare_blowUpToBase_of_isLocallyNoetherian J,
    isAlmostBlowUpSquare_blowUpToBase_of_isLocallyNoetherian (J.comap f),
    hJdisj, ?_, inferInstance, ?_⟩
  · have hw : (strictTransformBlowUpIso f J).inv.left ≫
        (Stacks.StrictTransform.ideal f (blowUpToBase J) (exceptionalIdeal J)).subschemeι ≫
          pullback.fst f (blowUpToBase J) = blowUpToBase (J.comap f) :=
      Over.w (strictTransformBlowUpIso f J).inv
    simp only [strictTransformToBlowUp, Category.assoc, ← pullback.condition]
    rw [reassoc_of% hw]
  · exact finitePresentation_of_finiteType _

/-- **Stacks Project, Tag 0EVC.** Let `Y` be a quasi-compact and quasi-separated scheme, let `X`
be a scheme of finite presentation over `Y`, and let `V ⊆ Y` be a quasi-compact open. Then there
is a diagram as in the tag: two almost blowup squares, over `Y` with a centre disjoint from `V`
and over `X` with the inverse-image centre, whose lower and top squares are cartesian
(`AlgebraicGeometry.lowerSquareIso`, `AlgebraicGeometry.topSquareIso`) and whose relative
morphism `X' ⟶ Y'` is flat and of finite presentation.

The flattening centre comes from
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform`, the library's form of Stacks tag
081R, and two things are carried beyond the tag's own hypotheses. The base is assumed locally
Noetherian: this is the case the Stacks proof calls immediate, the general case being reduced to
it by absolute Noetherian approximation, which is not done here. And the affine case of the
flatness half of Stacks tag 0815 is carried as
`AlgebraicGeometry.AffineChartFlatteningCentre f X.unitModule V`, exactly as that form of
tag 081R carries it. The tag's remaining hypothesis that `X_V ⟶ V` be flat is not assumed
separately, because in the source it enters only through that affine case; so the statement below
is a generalization in that respect. -/
@[stacks 0EVC "locally Noetherian base; the affine case of the flatness half of [Stacks, Tag \
0815] carried as the hypothesis `AlgebraicGeometry.AffineChartFlatteningCentre`, inherited from \
the library's form of [Stacks, Tag 081R]"]
public theorem hasFlatAlmostBlowUpSquarePair [IsLocallyNoetherian Y] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (f : X ⟶ Y) (hf : FinitePresentation f) (V : Y.Opens)
    (hV : IsCompact (V : Set Y)) (H : AffineChartFlatteningCentre f X.unitModule V) :
    HasFlatAlmostBlowUpSquarePair f V := by
  have hlfp : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have hqc : QuasiCompact f := hf.quasiCompact
  have hqs : QuasiSeparated f := hf.quasiSeparated
  have hlft : LocallyOfFiniteType f := inferInstance
  obtain ⟨J, -, hJdisj, -, hJflat⟩ := exists_isAdmissibleBlowup_flat_strictTransform f V hV H
  exact hasFlatAlmostBlowUpSquarePair_of_flat_strictTransformToBlowUp f hf V J hJdisj hJflat

end AlgebraicGeometry

end
