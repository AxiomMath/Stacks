module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ConstructibleSets
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization

/-!
# The normalized blowing up of an algebraic space at a closed point

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `z ∈ |X|` be a closed
point.  The *normalized blowing up of `X` at `z`* is the composite `X'' ⟶ X' ⟶ X` in which
`X' ⟶ X` is the blowing up of `X` at `z` and `X'' ⟶ X'` is the normalization of `X'`; this is
**Stacks 0BHJ**.  When `X` is Nagata the normalized blowing up is a normal Nagata algebraic
space proper over `X`, which is **Stacks 0BHK**.

## Main definitions

* `AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint` is **Stacks 0BHJ**: the blowing up of
  `X` at `z` together with normalization data for it.
* `AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint.space` and
  `AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint.hom` are the algebraic space `X''` and
  the composite `X'' ⟶ X` which the source calls the normalized blowing up.

## Main results

* `AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint.hasEtaleLocalProperty_isNormal_space`
  is normality of `X''`, which needs no hypothesis on `X`.
* `AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint.isFinite_normalizationHom` is
  finiteness of `X'' ⟶ X'`, and
  `AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint.hasEtaleLocalProperty_isNagataScheme_space`
  is the Nagata property of `X''`.
* `AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint.isProper_hom` is properness of
  `X'' ⟶ X`.
* `AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint.isNormal_and_isNagata_and_isProper`
  is **Stacks 0BHK**: all four assertions of the source, namely that `X''` is an algebraic
  space, that it is normal, that it is Nagata and that `X'' ⟶ X` is proper.

## What is assumed

Stacks 0BHK is **not** proved outright: properness of the blowing up `X' ⟶ X` itself is carried
as the named hypothesis `hproperBlowup` of every statement that needs it.  That properness is
**Stacks 085Z**, a different tag, and it is logically prior to — and strictly weaker than — any
conclusion drawn from it here; the clause string of the `@[stacks 0BHK]` attribute says so.  The
library's Stacks 085Z, `AlgebraicGeometry.Space.isProper_of_isBlowupAlong`, is itself available
only given the existence of a proper blowing up, which is the relative `Proj` construction of
Stacks 085Q together with Stacks 085R; that construction is absent, as the prose of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupPropernessAndStrictTransformImage.lean` records.
Once it lands, `hproperBlowup` is discharged by that lemma and nothing else here changes.

In the source properness of `X' ⟶ X` comes from `X` being locally Noetherian, which it is
because a Nagata ring is Noetherian; the hypothesis is therefore implied by the Nagata
hypothesis that is already present, and carrying it assumes no more than Stacks 085Z gives.

Nothing is weakened in exchange: each of the four conclusions below is what Stacks 0BHK
asserts, and normality is proved with no hypothesis at all.

## Implementation notes

The blowing up of an algebraic space at a closed point is
`AlgebraicGeometry.Space.IsBlowupAtClosedPoint` of Stacks 0BHE, a condition on a morphism, and
the normalization is `AlgebraicGeometry.Space.NormalizationData`, which packages a normalization
morphism with its identification over every surjective étale scheme chart.  The normalized
blowing up is accordingly *data* — the blowing up, the witness that it is one, and normalization
data for it — in the same idiom as `AlgebraicGeometry.Space.BlowupFactorization`.  Existence of
normalization data is the open half of Stacks 07U4, so quantifying over the data is both the
only available form and the stronger statement; this is also why "is an algebraic space", the
fourth assertion of Stacks 0BHK, is read off the normalization data rather than constructed.

Normality and the Nagata property of an algebraic space are the étale-local scheme properties of
Stacks 03E6, which is the form in which Stacks 0BHK's first two assertions are meaningful for an
algebraic space.

## References

* [Stacks Project, Tag 0BHJ](https://stacks.math.columbia.edu/tag/0BHJ)
* [Stacks Project, Tag 0BHK](https://stacks.math.columbia.edu/tag/0BHK)
* [Stacks Project, Tag 0BHE](https://stacks.math.columbia.edu/tag/0BHE)
* [Stacks Project, Tag 085Z](https://stacks.math.columbia.edu/tag/085Z)
* [Stacks Project, Tag 0BAU](https://stacks.math.columbia.edu/tag/0BAU)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
* [Stacks Project, Tag 0BB5](https://stacks.math.columbia.edu/tag/0BB5)
* [Stacks Project, Tag 04NZ](https://stacks.math.columbia.edu/tag/04NZ)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0BHJ.** The **normalized blowing up of `X` at a closed point `z`**: the blowing up
`X' ⟶ X` of `X` at `z` together with normalization data for `X'`.

The morphism `X'' ⟶ X' ⟶ X` which the source calls the normalized blowing up is
`AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint.hom`.  Normalization data exists for `X'`
exactly when `X'` satisfies the equivalent conditions of Stacks 0BB1, which is the hypothesis
the source imposes on `X`; carrying the data makes that hypothesis part of the datum. -/
structure NormalizedBlowupAtClosedPoint (X : AlgebraicSpaces B S hS)
    (z : points B S hS X.obj) (hz : IsClosed ({z} : Set (points B S hS X.obj))) where
  /-- The blowing up `X'` of `X` at `z`. -/
  blowup : AlgebraicSpaces B S hS
  /-- The blowing up morphism `X' ⟶ X`. -/
  proj : blowup ⟶ X
  /-- `X' ⟶ X` is the blowing up of `X` at the closed point `z`. -/
  isBlowup : IsBlowupAtClosedPoint B S hS z hz proj
  /-- The normalization `X'' ⟶ X'` of the blowing up. -/
  normalization : NormalizationData B S hS blowup.obj

namespace NormalizedBlowupAtClosedPoint

variable {B S hS} {X : AlgebraicSpaces B S hS} {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))}
    (N : NormalizedBlowupAtClosedPoint B S hS X z hz)

/-- The normalization `X''` of the blowing up, as an algebraic space over `S`. -/
def space : AlgebraicSpaces B S hS :=
  ⟨N.normalization.space, N.normalization.isAlgebraicSpace⟩

/-- The normalization morphism `X'' ⟶ X'`. -/
def normalizationHom : N.space ⟶ N.blowup :=
  ObjectProperty.homMk N.normalization.hom

/-- **Stacks 0BHJ.** The normalized blowing up of `X` at `z`: the composite `X'' ⟶ X' ⟶ X` of
the normalization of the blowing up with the blowing up. -/
def hom : N.space ⟶ X :=
  N.normalizationHom ≫ N.proj

/-- The normalized blowing up is, on underlying presheaves, the normalization morphism followed
by the blowing up morphism. -/
theorem hom_hom : N.hom.hom = N.normalization.hom ≫ N.proj.hom := rfl

/-- **Stacks 0BHK, normality.**  The normalized blowing up of `X` at a closed point is a normal
algebraic space.

This is Stacks 0BB4 part (1) for the normalization of the blowing up, and it needs no hypothesis
on `X`: the normalization of any algebraic space carrying normalization data is normal. -/
theorem hasEtaleLocalProperty_isNormal_space :
    HasEtaleLocalProperty B S hS N.space.obj
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal T) :=
  N.normalization.hasEtaleLocalProperty_isNormal N.blowup.property

/-- **The blowing up of a Nagata algebraic space at a closed point is Nagata.**  A proper
morphism is locally of finite type, so this is Stacks 0BAU applied to `X' ⟶ X`.

The hypothesis `hproperBlowup` is properness of the blowing up, which is Stacks 085Z; see the
"what is assumed" section of the module documentation. -/
theorem hasEtaleLocalProperty_isNagataScheme_blowup
    (hNagata : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsNagataScheme T))
    (hproperBlowup : IsProper B S hS N.proj.hom) :
    HasEtaleLocalProperty B S hS N.blowup.obj (fun T : Scheme.{u} => IsNagataScheme T) :=
  isNagata_of_isLocallyOfFiniteType B S hS N.blowup.property X.property N.proj.hom
    hproperBlowup.2.1.1 hNagata

/-- **The normalization of the blowing up is finite.**  The blowing up of a Nagata algebraic
space at a closed point is Nagata, and the normalization morphism of a Nagata algebraic space is
finite by Stacks 0BB5. -/
theorem isFinite_normalizationHom
    (hNagata : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsNagataScheme T))
    (hproperBlowup : IsProper B S hS N.proj.hom) :
    IsFinite B S hS N.normalization.hom :=
  N.normalization.isFinite_hom N.blowup.property
    (N.hasEtaleLocalProperty_isNagataScheme_blowup hNagata hproperBlowup)

/-- **The normalization of the blowing up is proper.**  It is finite, and a finite morphism of
algebraic spaces is affine and proper by Stacks 04NZ. -/
theorem isProper_normalizationHom
    (hNagata : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsNagataScheme T))
    (hproperBlowup : IsProper B S hS N.proj.hom) :
    IsProper B S hS N.normalization.hom :=
  ((isFinite_iff_isAffineHom_and_isProper B S hS N.normalization.isAlgebraicSpace
    N.blowup.property N.normalization.hom).mp
      (N.isFinite_normalizationHom hNagata hproperBlowup)).2

/-- **Stacks 0BHK, the Nagata property.**  The normalized blowing up of a Nagata algebraic space
at a closed point is Nagata.

The blowing up `X'` is Nagata, the normalization `X'' ⟶ X'` is finite hence locally of finite
type, and Stacks 0BAU applies again. -/
theorem hasEtaleLocalProperty_isNagataScheme_space
    (hNagata : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsNagataScheme T))
    (hproperBlowup : IsProper B S hS N.proj.hom) :
    HasEtaleLocalProperty B S hS N.space.obj (fun T : Scheme.{u} => IsNagataScheme T) :=
  isNagata_of_isLocallyOfFiniteType B S hS N.normalization.isAlgebraicSpace N.blowup.property
    N.normalization.hom (N.isProper_normalizationHom hNagata hproperBlowup).2.1.1
    (N.hasEtaleLocalProperty_isNagataScheme_blowup hNagata hproperBlowup)

/-- **Stacks 0BHK, properness.**  The normalized blowing up of a Nagata algebraic space at a
closed point is proper over `X`.

The normalization `X'' ⟶ X'` is finite, hence proper by Stacks 04NZ, and a composite of proper
morphisms is proper by Stacks 04XY. -/
theorem isProper_hom
    (hNagata : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsNagataScheme T))
    (hproperBlowup : IsProper B S hS N.proj.hom) :
    IsProper B S hS N.hom.hom := by
  rw [hom_hom]
  exact isProper_comp B S hS N.normalization.isAlgebraicSpace N.blowup.property X.property
    N.normalization.hom N.proj.hom (N.isProper_normalizationHom hNagata hproperBlowup)
    hproperBlowup

/-- **Stacks 0BHK.**  If `X` is Nagata, then the normalized blowing up of `X` at a closed point
`z` is a normal Nagata algebraic space proper over `X`.

All four assertions of the source are listed: `X''` is an algebraic space over `S`, it is
normal, it is Nagata, and the normalized blowing up `X'' ⟶ X` is proper.

The hypothesis `hproperBlowup` is properness of the blowing up `X' ⟶ X`, which is Stacks 085Z;
see the "what is assumed" section of the module documentation. -/
@[stacks 0BHK "all four assertions — the normalized blowing up is an algebraic space, it is
normal, it is Nagata, and it is proper over X — with properness of the blowing up X' ⟶ X
itself, which is Stacks 085Z, as the named hypothesis hproperBlowup"]
theorem isNormal_and_isNagata_and_isProper
    (hNagata : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsNagataScheme T))
    (hproperBlowup : IsProper B S hS N.proj.hom) :
    IsAlgebraicSpace B S hS N.space.obj ∧
      HasEtaleLocalProperty B S hS N.space.obj
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal T) ∧
      HasEtaleLocalProperty B S hS N.space.obj (fun T : Scheme.{u} => IsNagataScheme T) ∧
      IsProper B S hS N.hom.hom :=
  ⟨N.space.property, N.hasEtaleLocalProperty_isNormal_space,
    N.hasEtaleLocalProperty_isNagataScheme_space hNagata hproperBlowup,
    N.isProper_hom hNagata hproperBlowup⟩

end NormalizedBlowupAtClosedPoint

end AlgebraicGeometry.Space

end
