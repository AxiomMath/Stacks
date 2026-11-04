module

public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits

/-!
# The two forms of Situation 084R and the passage between them

Situation 084R of the Stacks project fixes a scheme `S`, a directed set `I` with a chosen
element, an inverse system of algebraic spaces over `S` indexed by `I` whose transition
morphisms are affine and whose stages are quasi-compact and quasi-separated, and the limit
`X` of that system. This development carries two renderings of it, which differ only in how
the index set and the limit are presented:

* `AlgebraicGeometry.Space.DescentSituation` takes the index set as a *parameter*, in a
  universe independent of the universe of the site, and carries its own limiting cone
  together with the assertion that the vertex of that cone is an algebraic space.
* `AlgebraicGeometry.Space.LimitSituation` takes the index set as a *field*, necessarily in
  the universe of the site, and is attached to a presheaf `X` given in advance, which it
  asserts to be the limit; it makes no claim that `X` is an algebraic space.

Neither subsumes the other: the first has the freer index universe and the stronger
conclusion about the limit, the second attaches to a presheaf one already has. This file
provides the passage between them in both directions, for an index set in the universe of
the site, where the two are equivalent.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.toLimitSituation` reads a descent situation
  whose index set lies in the universe of the site as a limit situation for the vertex of
  its chosen limiting cone.
* `AlgebraicGeometry.Space.LimitSituation.toDescentSituation` reads a limit situation for an
  algebraic space `X` as a descent situation indexed by its index field, the algebraicity of
  `X` being the one piece of data a limit situation does not carry.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.toLimitSituation_cone` and
  `AlgebraicGeometry.Space.DescentSituation.toLimitSituation_isLimitCone`: the limiting cone
  of the limit situation produced from a descent situation, and the proof that it is
  limiting, are the ones the descent situation already carried.
* `AlgebraicGeometry.Space.DescentSituation.toLimitSituation_toDescentSituation` and
  `AlgebraicGeometry.Space.LimitSituation.toDescentSituation_toLimitSituation`: the two
  passages are mutually inverse, so for an index set in the universe of the site a descent
  situation is the same thing as a limit situation together with the algebraicity of its
  limit.
* `AlgebraicGeometry.Space.DescentSituation.isAffineHom_limitCone_π_of_isSiteSmall` is **Stacks
07SF, part
  (1), for a descent situation**: every projection from the limit to a stage is affine, under
  the smallness hypothesis `AlgebraicGeometry.Space.IsSiteSmall` that Stacks 07SF asks for. It
  is the limit situation's `AlgebraicGeometry.Space.LimitSituation.isAffineHom_π` carried
  across the passage.

## Implementation notes

*Why the passage is definitional.* The two structures impose the same conditions on the same
data: the fields `system`, `algebraicSpace`, `transition_affine`, `quasiCompact`,
`quasiSeparated` and `base` of a descent situation have the same types as the fields
`system`, `isAlgebraicSpace`, `transition_affine`, `quasiCompact`, `quasiSeparated` and
`base` of a limit situation once the index field of the latter is set to the index parameter
of the former. The only genuine difference is bundling: a descent situation carries the cone
`limitCone` whose vertex is the limit, whereas a limit situation carries the projections `π`
out of a presheaf fixed in advance. Taking that presheaf to be `limitCone.pt` makes the cone
`AlgebraicGeometry.Space.LimitSituation.cone` the very cone `limitCone`, by the
eta-expansion of a structure, so `isLimit` transfers with no proof and every compatibility
statement below holds by `rfl`.

*The smallness hypothesis.* Constructing the passage asks nothing of the index set; it is
only the consequences of Stacks 07SF that do. The condition used here,
`AlgebraicGeometry.Space.IsSiteSmall` of the inverse system, is the one carried by
`AlgebraicGeometry.Space.LimitSituation.isAffineHom_π` and by Stacks 084T,
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isSiteSmall`,
and it
transfers across the passage unchanged because the inverse system does: the system field of
`AlgebraicGeometry.Space.DescentSituation.toLimitSituation` is the system of the descent
situation itself. An index set below the cofinality of the site's size cutoff supplies it by
`AlgebraicGeometry.Space.IsSiteSmall.of_lt_cof_op`, the companion bound on the morphism types
that Stacks 07SF also asks for being automatic, a preorder being a thin category; monomorphic
transition morphisms supply it with nothing asked of the index.

*Where this is needed.* Statements about the *sections* of a module on the limit, Stacks 07SI
among them, are stated on a limit situation, because at a free index universe the
scheme-level colimit statement they rest on is false; statements about *descent of properties
to a stage*, Stacks 084T and 07SQ among them, are stated on a descent situation, because only
that structure asserts the limit to be an algebraic space. The passage is what lets a result
of the first kind be consumed by a proof of the second: for `D` a descent situation,
`D.toLimitSituation` is a limit situation for `D.limitCone.pt` and `D.limitAlgebraicSpace` is
exactly the algebraicity hypothesis the first kind of statement takes.

## References

* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})}

/-! ### From a descent situation to a limit situation -/

namespace DescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **A descent situation indexed in the universe of the site is a limit situation for the
vertex of its chosen limiting cone.** The inverse system, the affineness of its transition
morphisms, the quasi-compactness and quasi-separatedness of its stages and the distinguished
index are carried over unchanged, and the projections of the chosen cone are the projections
of the limit situation.

The assertion of a descent situation that the limit is an algebraic space is not part of a
limit situation and is dropped; it remains available as
`AlgebraicGeometry.Space.DescentSituation.limitAlgebraicSpace`, which is the hypothesis that
the statements made on a limit situation take. -/
def toLimitSituation : LimitSituation B S hS hZ D.limitCone.pt where
  I := I
  system := D.system
  isAlgebraicSpace := D.algebraicSpace
  transition_affine := D.transition_affine
  quasiCompact := D.quasiCompact
  quasiSeparated := D.quasiSeparated
  π := D.limitCone.π
  isLimit := D.isLimit
  base := D.base

/-- The index set of the limit situation of a descent situation is the index parameter. -/
@[simp]
theorem toLimitSituation_I : D.toLimitSituation.I = I := rfl

/-- The inverse system of the limit situation of a descent situation is the inverse system of
the descent situation. -/
@[simp]
theorem toLimitSituation_system : D.toLimitSituation.system = D.system := rfl

/-- The projections of the limit situation of a descent situation are the projections of the
chosen limiting cone of the descent situation. -/
@[simp]
theorem toLimitSituation_π : D.toLimitSituation.π = D.limitCone.π := rfl

/-- The distinguished index of the limit situation of a descent situation is that of the
descent situation. -/
@[simp]
theorem toLimitSituation_base : D.toLimitSituation.base = D.base := rfl

/-- The order on the index set of the limit situation of a descent situation is the order on
the index parameter. -/
theorem toLimitSituation_preorder {I : Type u} [inst : Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) : D.toLimitSituation.preorder = inst := rfl

/-- **The limiting cone of the limit situation of a descent situation is the chosen limiting
cone of the descent situation.** No comparison isomorphism intervenes: the cone of a limit
situation is assembled from its vertex and its projections, which here are the vertex and the
projections of `limitCone`. -/
@[simp]
theorem toLimitSituation_cone : D.toLimitSituation.cone = D.limitCone := rfl

/-- **The two proofs that the cone is limiting agree.** The limit situation of a descent
situation is limiting by the descent situation's own `isLimit`. -/
theorem toLimitSituation_isLimitCone : D.toLimitSituation.isLimitCone = D.isLimit := rfl

/-- **Stacks 07SF, part (1), in a descent situation.** Every projection from the limit of a
descent situation to one of its stages is affine, provided the inverse system is small for the
site, `AlgebraicGeometry.Space.IsSiteSmall`.

This is `AlgebraicGeometry.Space.LimitSituation.isAffineHom_π` read through
`AlgebraicGeometry.Space.DescentSituation.toLimitSituation`; the smallness hypothesis is
literally the same one, the inverse system being unchanged by that passage. -/
theorem isAffineHom_limitCone_π_of_isSiteSmall (hb : IsSiteSmall B S hS D.system) (i : Iᵒᵖ) :
    IsAffineHom B S hS (D.limitCone.π.app i) :=
  D.toLimitSituation.isAffineHom_π_of_isSiteSmall hb i

/-- **Stacks 07SF, part (1), in a descent situation.** Every projection from the limit of a
descent situation to one of its stages is affine, provided the index set is small enough for
the site: it has cardinality below the cofinality of the site's size cutoff.

This is `AlgebraicGeometry.Space.LimitSituation.isAffineHom_π` read through
`AlgebraicGeometry.Space.DescentSituation.toLimitSituation`; the size hypothesis is literally
the same one, the index set being unchanged by that passage. -/
theorem isAffineHom_limitCone_π (hI : #I < B.cutoff.ord.cof) (i : Iᵒᵖ) :
    IsAffineHom B S hS (D.limitCone.π.app i) :=
  isAffineHom_limitCone_π_of_isSiteSmall D (Space.IsSiteSmall.of_lt_cof_op hI) i

end DescentSituation

/-! ### From a limit situation to a descent situation -/

namespace LimitSituation

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : LimitSituation B S hS hZ X)

/-- **A limit situation for an algebraic space is a descent situation indexed by its index
field.** The inverse system, the affineness of its transition morphisms, the
quasi-compactness and quasi-separatedness of its stages and the distinguished index are
carried over unchanged, the chosen limiting cone is
`AlgebraicGeometry.Space.LimitSituation.cone`, and the hypothesis `hX` supplies the one field
of a descent situation that a limit situation does not have, namely that the limit is an
algebraic space.

That hypothesis is not vacuous and is not automatic: it is the existence assertion of Stacks
07SF, `AlgebraicGeometry.Space.Limits.isAlgebraicSpace_limit`, which holds under that tag's
size hypotheses on the index category. -/
def toDescentSituation (hX : IsAlgebraicSpace B S hS X) : DescentSituation B S hS hZ A.I where
  system := A.system
  algebraicSpace := A.isAlgebraicSpace
  transition_affine := A.transition_affine
  quasiCompact := A.quasiCompact
  quasiSeparated := A.quasiSeparated
  limitCone := A.cone
  isLimit := A.isLimitCone
  limitAlgebraicSpace := hX
  base := A.base

/-- The inverse system of the descent situation of a limit situation is the inverse system of
the limit situation. -/
@[simp]
theorem toDescentSituation_system (hX : IsAlgebraicSpace B S hS X) :
    (A.toDescentSituation hX).system = A.system := rfl

/-- The chosen limiting cone of the descent situation of a limit situation is the limiting
cone of the limit situation; in particular its vertex is the presheaf the limit situation is
attached to. -/
@[simp]
theorem toDescentSituation_limitCone (hX : IsAlgebraicSpace B S hS X) :
    (A.toDescentSituation hX).limitCone = A.cone := rfl

/-- The distinguished index of the descent situation of a limit situation is that of the limit
situation. -/
@[simp]
theorem toDescentSituation_base (hX : IsAlgebraicSpace B S hS X) :
    (A.toDescentSituation hX).base = A.base := rfl

/-- **The two proofs that the cone is limiting agree.** The descent situation of a limit
situation is limiting by the limit situation's own `isLimit`. -/
theorem toDescentSituation_isLimit (hX : IsAlgebraicSpace B S hS X) :
    (A.toDescentSituation hX).isLimit = A.isLimitCone := rfl

/-- **Passing to a descent situation and back recovers the limit situation.** -/
@[simp]
theorem toDescentSituation_toLimitSituation (hX : IsAlgebraicSpace B S hS X) :
    (A.toDescentSituation hX).toLimitSituation = A := rfl

end LimitSituation

/-- **Passing to a limit situation and back recovers the descent situation**, the algebraicity
of the limit being restored from the field it was dropped from. -/
@[simp]
theorem DescentSituation.toLimitSituation_toDescentSituation {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I) :
    D.toLimitSituation.toDescentSituation D.limitAlgebraicSpace = D := rfl

end AlgebraicGeometry.Space

end
