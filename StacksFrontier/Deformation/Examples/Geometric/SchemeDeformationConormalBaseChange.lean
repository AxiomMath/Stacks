module

public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBase
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationConormal
public import StacksFrontier.Deformation.Examples.Geometric.SchemesCofibered

/-!
# The conormal sheaf of the special fibre is functorial in the deformation

Let `X` be a scheme over a field `k` and let `φ : P ⟶ Q` be an arrow of the deformation category
of `X` of [Stacks Project, Tag 0DY7], over a morphism `φ.base : A ⟶ B` of `𝒞_Λ`. Its morphism of
total spaces goes the other way, `φ.map : Q.scheme ⟶ P.scheme`, and it carries the special fibre
of `Q` to the special fibre of `P` on the nose, that being the `special_compat` field of
`Deformation.Examples.SchemeDeformationCategory.Hom`. So `φ` is a commutative square of
immersions whose horizontal edges are the two special-fibre immersions and whose edge on the
closed subschemes is the *identity* of `X`, and [Stacks Project, Tag 01R4] attaches to it a
canonical map

`𝒞_{X/P.scheme} ⟶ 𝒞_{X/Q.scheme}`

of conormal sheaves. This file builds that map, and the companion map

`𝒞_{Spec k/Spec A} ⟶ 𝒞_{Spec k/Spec B}`

on the base, and identifies the first with the second: the conormal map of an arrow of
deformations is the *unique* conormal datum compatible with the base, in the sense of
[Stacks Project, Tag 0CK2].

## The identification

`Deformation.Examples.deformationConormalBaseChangeIso` is flat base change for the conormal sheaf
of the special fibre, `p_X^* 𝒞_{Spec k/Spec A} ≅ 𝒞_{X/P.scheme}`, and it is the canonical map of
[Stacks Project, Tag 01R4] for the square identifying the special fibre. An arrow `φ : P ⟶ Q`
produces a *second* square over the closed point of `Spec A`, namely the special-fibre immersion
of `Q` sitting over `Spec A` through `Q.toBase ≫ Spec φ.base`, and that square factors in two
ways:

* through `P.scheme`, by the arrow's square followed by the special-fibre square of `P`;
* through `Spec B`, by the special-fibre square of `Q` followed by the square of closed points
  `Deformation.Examples.residueSpecMap_naturality`.

`Stacks.Immersion.immersionConormalSheafMap_comp` reads the canonical map of the composite square
along each factorisation, and the two readings are what
`Stacks.Thickenings.IsBaseCompatibleConormalMap` asserts of the conormal map of the arrow and of
the flat-base-change map respectively. Since the special-fibre square of `P` is cartesian, the
conormal datum compatible with the base is unique
(`Stacks.Thickenings.eq_of_isBaseCompatibleConormalMap`), so the conormal map of the arrow is
pinned by the base object and nothing else.

## Main definitions

* `Deformation.Examples.deformationConormalMap`: **the map `𝒞_{X/P.scheme} ⟶ 𝒞_{X/Q.scheme}` of
  conormal sheaves of special fibres induced by an arrow of deformations.**
* `Deformation.Examples.residueConormalMap`: the map `𝒞_{Spec k/Spec A} ⟶ 𝒞_{Spec k/Spec B}` of
  conormal sheaves of closed points induced by a morphism of `𝒞_Λ`.

## Main results

* `Deformation.Examples.isBaseCompatibleConormalMap_deformationConormalMap`: **the conormal map of
  an arrow of deformations is compatible with the base**, the composite with the flat-base-change
  map of `P` being the canonical map of the composite square.
* `Deformation.Examples.isBaseCompatibleConormalMap_deformationConormalBaseChangeIso`: the
  flat-base-change map of `Q` is compatible with the base in the same sense, along the other
  factorisation of that composite square.
* `Deformation.Examples.eq_of_isBaseCompatibleConormalMap_deformationConormalMap`: **the conormal
  map of an arrow of deformations is the unique conormal datum compatible with the base.** This is
  the sense in which it "is" the map of the base objects: any map of conormal sheaves of special
  fibres satisfying the compatibility of [Stacks Project, Tag 0CK2] for the arrow's square equals
  it.
* `Deformation.Examples.isBaseCompatibleConormalMap_baseChangeDeformationHom`: the same at the
  base change of a deformation along a morphism of `𝒞_Λ`, which is the arrow
  `Deformation.Examples.baseChangeDeformationHom` the cofibered structure produces.

## Implementation notes

**Why the pullback along the identity appears.** The canonical map of [Stacks Project, Tag 01R4]
for a square is a map out of the *pullback* along the edge on the closed subschemes, and for an
arrow of deformations that edge is `𝟙 X.left`. The two definitions here strip that pullback with
`RingedSpaceModuleAdjunction.modulePullbackId`, as
`Stacks.Immersion.conormalSequenceRightMap` does for the conormal sequence, so that the maps
compose with the conormal sheaves of the library on the nose. The compatibility statements are
stated on the *unstripped* map instead, because that is the shape
`Stacks.Thickenings.IsBaseCompatibleConormalMap` and
`Stacks.Thickenings.eq_of_isBaseCompatibleConormalMap` consume; the two shapes are exchanged by
`Deformation.Examples.deformationConormalMap_eq` and
`Deformation.Examples.residueConormalMap_eq`.

**What is not here.** The two compatibilities below say that the conormal map of the arrow and the
flat base change of `Q` are the two factorisations of one canonical map; they do not identify the
map `𝒞_{Spec k/Spec A} ⟶ 𝒞_{Spec k/Spec B}` on the base with the map `𝔪_A ⟶ 𝔪_B` of maximal
ideals. That identification is a computation of global sections on a one-point space, as in
`Deformation.Examples.residueConormalIso`, and it needs the behaviour of
`Stacks.ClosedImmersion.idealSheafMap` on the global sections of the two spectra; nothing of it is
proved here, and so no statement here mentions `Deformation.Examples.deformationConormalIso` or a
coefficient sheaf.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Thickenings (immersionConormalSheaf IsBaseCompatibleConormalMap
  eq_of_isBaseCompatibleConormalMap)
open Stacks.Immersion (immersionConormalSheafMap immersionConormalSheafMap_comp
  toShHom_square square_comp)

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

attribute [local instance] residueSpecMap_isClosedImmersion
  deformationSpecialMap_isClosedImmersion

/-! ### The conormal sheaf of the closed point is functorial in the base object -/

section Base

variable {A B : ArtinianLocalAlgCat.{u, u, u} Λ k}

/-- **The square of closed points of a morphism of `𝒞_Λ`, with its edge on the closed
subschemes read as an identity.** This is
`Deformation.Examples.residueSpecMap_naturality` in the shape
[Stacks Project, Tag 01R4] consumes: a commutative square of immersions whose edge on the
closed subschemes is `𝟙 (Spec k)`. -/
theorem residueSpecMap_comp_baseSpecMap' (g : A ⟶ B) :
    residueSpecMap B ≫ baseSpecMap g =
      𝟙 (Spec (CommRingCat.of k)) ≫ residueSpecMap A := by
  rw [Category.id_comp, residueSpecMap_naturality]

/-- **The map `𝒞_{Spec k/Spec A} ⟶ 𝒞_{Spec k/Spec B}` of conormal sheaves of the closed points
induced by a morphism `A ⟶ B` of `𝒞_Λ`.** The closed point of `Spec A` is the closed point of
`Spec B` followed by `Spec g`, so the two closed points form a commutative square of immersions
whose edge on the closed subschemes is the identity of `Spec k`; this is the canonical map of
[Stacks Project, Tag 01R4] for that square, read through
`RingedSpaceModuleAdjunction.modulePullbackId`. -/
def residueConormalMap (g : A ⟶ B) :
    immersionConormalSheaf (residueSpecMap A) ⟶ immersionConormalSheaf (residueSpecMap B) :=
  ((modulePullbackId (Spec (CommRingCat.of k)).toLocallyRingedSpace.toRingedSpace).app
      (immersionConormalSheaf (residueSpecMap A))).inv ≫
    immersionConormalSheafMap (residueSpecMap B) (residueSpecMap A)
      (𝟙 (Spec (CommRingCat.of k))) (baseSpecMap g)
      (toShHom_square (residueSpecMap_comp_baseSpecMap' g))

/-- `Deformation.Examples.residueConormalMap` with the pullback along the identity restored, which
is the shape [Stacks Project, Tag 01R4] produces. -/
theorem residueConormalMap_eq (g : A ⟶ B) :
    ((modulePullbackId (Spec (CommRingCat.of k)).toLocallyRingedSpace.toRingedSpace).app
          (immersionConormalSheaf (residueSpecMap A))).hom ≫ residueConormalMap g =
      immersionConormalSheafMap (residueSpecMap B) (residueSpecMap A)
        (𝟙 (Spec (CommRingCat.of k))) (baseSpecMap g)
        (toShHom_square (residueSpecMap_comp_baseSpecMap' g)) :=
  Iso.hom_inv_id_assoc _ _

end Base

/-! ### The conormal sheaf of the special fibre is functorial in the deformation -/

section Arrow

variable {X : Over (Spec (CommRingCat.of k))}
  {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X}

/-- **The square of special fibres of an arrow of deformations, with its edge on the closed
subschemes read as an identity.** This is the `special_compat` field of
`Deformation.Examples.SchemeDeformationCategory.Hom` in the shape
[Stacks Project, Tag 01R4] consumes. -/
theorem specialMap_comp_map (φ : P ⟶ Q) :
    Q.specialMap ≫ φ.map = 𝟙 X.left ≫ P.specialMap := by
  rw [Category.id_comp]
  exact φ.special_compat

/-- **The map `𝒞_{X/P.scheme} ⟶ 𝒞_{X/Q.scheme}` of conormal sheaves of the special fibres
induced by an arrow of deformations.** An arrow `φ : P ⟶ Q` carries the special fibre of `Q` to
the special fibre of `P` on the nose, so the two special-fibre immersions form a commutative
square of immersions whose edge on the closed subschemes is the identity of `X`; this is the
canonical map of [Stacks Project, Tag 01R4] for that square, read through
`RingedSpaceModuleAdjunction.modulePullbackId`.

Note the directions: the arrow goes from `P` to `Q`, its morphism of total spaces goes from
`Q.scheme` to `P.scheme`, and the conormal map goes from the conormal sheaf of `P` to that of
`Q`. -/
def deformationConormalMap (φ : P ⟶ Q) :
    immersionConormalSheaf P.specialMap ⟶ immersionConormalSheaf Q.specialMap :=
  ((modulePullbackId X.left.toLocallyRingedSpace.toRingedSpace).app
      (immersionConormalSheaf P.specialMap)).inv ≫
    immersionConormalSheafMap Q.specialMap P.specialMap (𝟙 X.left) φ.map
      (toShHom_square (specialMap_comp_map φ))

/-- `Deformation.Examples.deformationConormalMap` with the pullback along the identity restored,
which is the shape [Stacks Project, Tag 01R4] produces. -/
theorem deformationConormalMap_eq (φ : P ⟶ Q) :
    ((modulePullbackId X.left.toLocallyRingedSpace.toRingedSpace).app
          (immersionConormalSheaf P.specialMap)).hom ≫ deformationConormalMap φ =
      immersionConormalSheafMap Q.specialMap P.specialMap (𝟙 X.left) φ.map
        (toShHom_square (specialMap_comp_map φ)) :=
  Iso.hom_inv_id_assoc _ _

/-! ### The two factorisations of the composite square -/

/-- **The conormal map of an arrow of deformations is compatible with the base.** The
special-fibre immersion of `Q` sits over the closed point of `Spec A` through
`Q.toBase ≫ Spec φ.base`, and that square factors through `P.scheme`: the arrow's square followed
by the special-fibre square of `P`. Reading the canonical map of [Stacks Project, Tag 01R4] along
that factorisation is exactly the compatibility of [Stacks Project, Tag 0CK2] for the conormal
map of the arrow, with the flat-base-change map of `P` as the datum coming from the base.

This is `Stacks.Immersion.immersionConormalSheafMap_comp` and nothing else; the content is that
the two squares of a deformation and of an arrow of deformations stack to the square the
flat-base-change map of the target is read on. -/
@[stacks 0CK2 "the conormal map of an arrow of deformations is a conormal datum compatible with \
the base: its composite with the flat base change of the source deformation is the canonical map \
of Tag 01R4 for the square carrying the special fibre of the target over the closed point of the \
source's base. This is the factorisation through the total space of the source, not an \
identification of the map on the base with the map of maximal ideals"]
theorem isBaseCompatibleConormalMap_deformationConormalMap (φ : P ⟶ Q) :
    IsBaseCompatibleConormalMap Q.specialMap P.specialMap (residueSpecMap P.base)
      X.hom P.toBase (φ.map ≫ P.toBase) (𝟙 X.left)
      P.specialCartesian.w (square_comp (specialMap_comp_map φ) P.specialCartesian.w)
      (immersionConormalSheafMap Q.specialMap P.specialMap (𝟙 X.left) φ.map
        (toShHom_square (specialMap_comp_map φ))) :=
  (immersionConormalSheafMap_comp Q.specialMap P.specialMap (residueSpecMap P.base)
    (𝟙 X.left) φ.map (specialMap_comp_map φ) X.hom P.toBase P.specialCartesian.w).symm

/-- **The flat base change of the target deformation is compatible with the base, along the other
factorisation of the same composite square.** The square carrying the special fibre of `Q` over
the closed point of `Spec A` also factors through `Spec B`: the special-fibre square of `Q`
followed by the square of closed points
`Deformation.Examples.residueSpecMap_naturality`. Reading the canonical map of
[Stacks Project, Tag 01R4] along *that* factorisation makes
`Deformation.Examples.deformationConormalBaseChangeIso` at `Q` the compatible datum, the map
coming from the base being the conormal map
`Deformation.Examples.residueConormalMap` of `φ.base`.

Together with `Deformation.Examples.isBaseCompatibleConormalMap_deformationConormalMap` this is
the naturality of flat base change for the conormal sheaf of a special fibre in the base object
of `𝒞_Λ`: the two statements are the two readings of one canonical map. -/
@[stacks 0473 "naturality in the base object: the flat base change for the conormal sheaf of the \
special fibre of the target of an arrow of deformations is the conormal datum compatible with the \
base along the factorisation through the spectrum of the source's base object, the map on the \
base being the conormal map of the morphism of base objects. This is one of the two readings of a \
single canonical map of Tag 01R4, not a computation of either reading on sections"]
theorem isBaseCompatibleConormalMap_deformationConormalBaseChangeIso (φ : P ⟶ Q) :
    IsBaseCompatibleConormalMap Q.specialMap (residueSpecMap Q.base) (residueSpecMap P.base)
      (𝟙 (Spec (CommRingCat.of k))) (baseSpecMap φ.base) (Q.toBase ≫ baseSpecMap φ.base) X.hom
      (residueSpecMap_comp_baseSpecMap' φ.base)
      (square_comp Q.specialCartesian.w (residueSpecMap_comp_baseSpecMap' φ.base))
      (deformationConormalBaseChangeIso Q).hom :=
  (immersionConormalSheafMap_comp Q.specialMap (residueSpecMap Q.base) (residueSpecMap P.base)
    X.hom Q.toBase Q.specialCartesian.w (𝟙 (Spec (CommRingCat.of k))) (baseSpecMap φ.base)
    (residueSpecMap_comp_baseSpecMap' φ.base)).symm

/-- **The conormal map of an arrow of deformations is the unique conormal datum compatible with
the base.** The special-fibre square of `P` is cartesian, so
`Stacks.Thickenings.eq_of_isBaseCompatibleConormalMap` applies: any map
`𝟙_X^* 𝒞_{X/P.scheme} ⟶ 𝒞_{X/Q.scheme}` whose composite with the flat base change of `P` is the
canonical map of the composite square is the conormal map of `φ`.

This is the sense in which the conormal map of an arrow of deformations "is" the map of the base
objects: it is determined by the square over `Spec A`, and
`Deformation.Examples.isBaseCompatibleConormalMap_deformationConormalBaseChangeIso` exhibits that
square as the one the flat base change of `Q` and the conormal map of `φ.base` are read on. -/
@[stacks 0CK2 "the conormal map of an arrow of deformations is the UNIQUE conormal datum \
compatible with the base, the special-fibre square of the source being cartesian. This pins the \
map by the base object; it does not compute it on sections"]
theorem eq_of_isBaseCompatibleConormalMap_deformationConormalMap (φ : P ⟶ Q)
    {A : (modulePullback (Scheme.Hom.toLRSHom (𝟙 X.left)).toShHom).obj
        (immersionConormalSheaf P.specialMap) ⟶ immersionConormalSheaf Q.specialMap}
    (hA : IsBaseCompatibleConormalMap Q.specialMap P.specialMap (residueSpecMap P.base)
      X.hom P.toBase (φ.map ≫ P.toBase) (𝟙 X.left)
      P.specialCartesian.w (square_comp (specialMap_comp_map φ) P.specialCartesian.w) A) :
    A = immersionConormalSheafMap Q.specialMap P.specialMap (𝟙 X.left) φ.map
      (toShHom_square (specialMap_comp_map φ)) :=
  eq_of_isBaseCompatibleConormalMap P.specialCartesian
    (square_comp (specialMap_comp_map φ) P.specialCartesian.w) hA
    (isBaseCompatibleConormalMap_deformationConormalMap φ)

/-! ### The naturality square -/

/-- **The flat base change of the conormal sheaf of a special fibre is natural in the base object
of `𝒞_Λ`.** For an arrow `φ : P ⟶ Q` of deformations of `X` the square

`p_X^* 𝒞_{Spec k/Spec A} ⟶ 𝒞_{X/P.scheme}`, `p_X^* 𝒞_{Spec k/Spec B} ⟶ 𝒞_{X/Q.scheme}`

commutes, the horizontal maps being
`Deformation.Examples.deformationConormalBaseChangeIso` and the vertical ones the pullback along
`p_X` of the conormal map of `φ.base` and the conormal map of `φ`. **This is the statement that
the conormal map of an arrow of deformations corresponds, under flat base change, to the conormal
map of the morphism of base objects.**

Both maps of conormal sheaves are written in the unstripped shape [Stacks Project, Tag 01R4]
produces — that is, out of the pullback along the edge on the closed subschemes, which is an
identity — so each composite begins with the comparison
`RingedSpaceModuleAdjunction.modulePullbackComp` of the pullback along a composite with the
composite of the pullbacks, and the two composites `𝟙_X ≫ p_X` and `p_X ≫ 𝟙_{Spec k}` of those
edges differ by a `CategoryTheory.eqToHom`. The stripped maps are
`Deformation.Examples.deformationConormalMap` and
`Deformation.Examples.residueConormalMap`.

The proof is the two factorisations
`Deformation.Examples.isBaseCompatibleConormalMap_deformationConormalBaseChangeIso` and
`Deformation.Examples.isBaseCompatibleConormalMap_deformationConormalMap` of the one canonical
map, compared by `Stacks.Immersion.immersionConormalSheafMap_congr` along the equality of edges;
the right-hand edges of the two squares over `Spec A` are identified by the cartesian square
`Deformation.Examples.SchemeDeformationCategory.Hom.cartesian` of the arrow. -/
@[stacks 0473 "naturality of flat base change for the conormal sheaf of a special fibre in the \
base object: for an arrow of deformations, the pullback along the structure morphism of the \
conormal map of the morphism of base objects, followed by the flat base change of the target, is \
the flat base change of the source followed by the conormal map of the arrow -- up to the \
eqToHom comparing the two unit composites of the edge on the closed subschemes. Both conormal \
maps are the canonical maps of Tag 01R4; nothing is computed on sections and the map on the base \
is NOT identified with the map of maximal ideals"]
theorem deformationConormalBaseChangeIso_naturality (φ : P ⟶ Q) :
    (modulePullbackComp X.hom.toLRSHom.toShHom
            (Scheme.Hom.toLRSHom (𝟙 (Spec (CommRingCat.of k)))).toShHom).hom.app
          (immersionConormalSheaf (residueSpecMap P.base)) ≫
        (modulePullback X.hom.toLRSHom.toShHom).map
            (immersionConormalSheafMap (residueSpecMap Q.base) (residueSpecMap P.base)
              (𝟙 (Spec (CommRingCat.of k))) (baseSpecMap φ.base)
              (toShHom_square (residueSpecMap_comp_baseSpecMap' φ.base))) ≫
          (deformationConormalBaseChangeIso Q).hom =
      eqToHom (congrArg (fun p : X.left ⟶ Spec (CommRingCat.of k) =>
            (modulePullback p.toLRSHom.toShHom).obj
              (immersionConormalSheaf (residueSpecMap P.base)))
            ((Category.id_comp X.hom).trans (Category.comp_id X.hom).symm).symm) ≫
        (modulePullbackComp (Scheme.Hom.toLRSHom (𝟙 X.left)).toShHom
              X.hom.toLRSHom.toShHom).hom.app
            (immersionConormalSheaf (residueSpecMap P.base)) ≫
          (modulePullback (Scheme.Hom.toLRSHom (𝟙 X.left)).toShHom).map
              (deformationConormalBaseChangeIso P).hom ≫
            immersionConormalSheafMap Q.specialMap P.specialMap (𝟙 X.left) φ.map
              (toShHom_square (specialMap_comp_map φ)) := by
  have hcongr := Stacks.Immersion.immersionConormalSheafMap_congr Q.specialMap
    (residueSpecMap P.base) ((Category.id_comp X.hom).trans (Category.comp_id X.hom).symm)
    φ.cartesian.w
    (toShHom_square (square_comp (specialMap_comp_map φ) P.specialCartesian.w))
    (toShHom_square (square_comp Q.specialCartesian.w
      (residueSpecMap_comp_baseSpecMap' φ.base)))
  exact (isBaseCompatibleConormalMap_deformationConormalBaseChangeIso φ).trans
    (hcongr.trans (congrArg (eqToHom _ ≫ ·)
      (isBaseCompatibleConormalMap_deformationConormalMap φ).symm))

end Arrow

/-! ### The base change of a deformation -/

section BaseChange

variable {X : Over (Spec (CommRingCat.of k))}
  (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
  {B : ArtinianLocalAlgCat.{u, u, u} Λ k} (g : P.base ⟶ B)

/-- **The conormal map of the arrow of a deformation onto its base change is compatible with the
base.** This is `Deformation.Examples.isBaseCompatibleConormalMap_deformationConormalMap` at
`Deformation.Examples.baseChangeDeformationHom`, the arrow the cofibered structure of the
deformation category produces, whose morphism of total spaces is the first projection of the
fibre product and whose base component is `g`.

Taken together with
`Deformation.Examples.isBaseCompatibleConormalMap_deformationConormalBaseChangeIso` and the
uniqueness `Deformation.Examples.eq_of_isBaseCompatibleConormalMap_deformationConormalMap`, this
says that the conormal map `𝒞_{X/P.scheme} ⟶ 𝒞_{X/(P ×_A B).scheme}` of the base change is
determined by `g` through the conormal map
`Deformation.Examples.residueConormalMap` of the base objects. -/
@[stacks 0CK2 "at the base change of a deformation: the conormal map of the arrow of a \
deformation onto its base change along a morphism of C_Lambda is a conormal datum compatible \
with the base. This is the general statement for an arrow of deformations instantiated at \
baseChangeDeformationHom, not a separate computation"]
theorem isBaseCompatibleConormalMap_baseChangeDeformationHom :
    IsBaseCompatibleConormalMap (baseChangeDeformation P g).specialMap P.specialMap
      (residueSpecMap P.base) X.hom P.toBase
      ((baseChangeDeformationHom P g).map ≫ P.toBase) (𝟙 X.left)
      P.specialCartesian.w
      (square_comp (specialMap_comp_map (baseChangeDeformationHom P g)) P.specialCartesian.w)
      (immersionConormalSheafMap (baseChangeDeformation P g).specialMap P.specialMap
        (𝟙 X.left) (baseChangeDeformationHom P g).map
        (toShHom_square (specialMap_comp_map (baseChangeDeformationHom P g)))) :=
  isBaseCompatibleConormalMap_deformationConormalMap (baseChangeDeformationHom P g)

end BaseChange

end Deformation.Examples

end
