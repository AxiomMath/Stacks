module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# Abelian varieties

An abelian variety over a field is a group scheme whose structure morphism is a proper variety
and is geometrically integral.  Every abelian variety is commutative, and the class of abelian
varieties is stable under extension of the ground field.

## Main definitions

* `AlgebraicGeometry.IsAbelianVariety` is the predicate that a group scheme over a field is an
  abelian variety.

## Main results

The parent-class instances of `IsAbelianVariety` exhibit an abelian variety as a proper variety
and as a geometrically integral scheme over its ground field.

* `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` says that a proper,
  geometrically integral group scheme over a field is commutative.
* `AlgebraicGeometry.isAbelianVariety_pullbackObj` says that the base change `A_K` of an abelian
  variety `A` over `k` along a field extension `K/k` is an abelian variety over `K`.

## Implementation notes

A group scheme over `Spec k` is represented by a group object in the category of schemes over
`Spec k`.  Thus the group-object structure is an input to `IsAbelianVariety`, while its two
property fields are the proper-variety and geometric-integrality conditions.

Commutativity is stated directly under those two properties, and hence in the slightly more
general form that does not require the bundled `IsAbelianVariety` hypothesis; that more
general result is adopted rather than restated through the bundled predicate.

The base change `A_K` is the value at `A` of the pullback functor along the morphism
`Spec K ⟶ Spec k` of the extension, so it is again a scheme over the new base by construction
and inherits its group-object structure from the fact that pullback along a morphism preserves
finite products.  Integrality of the underlying scheme of `A_K` is not a base-change-stable
property of the structure morphism; it is exactly one instance of geometric integrality of
`A ⟶ Spec k`, which is why that hypothesis is part of the definition.

## References

* [Stacks Project, Tag 03RO](https://stacks.math.columbia.edu/tag/03RO)
* [Stacks Project, Proposition 39.9.11 (Tag 03RP)](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Lemma 39.9.3 (Tag 0BFB)](https://stacks.math.columbia.edu/tag/0BFB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 03RO.** A group scheme over a field is an abelian variety if its
structure morphism makes its underlying scheme a proper, geometrically integral variety. -/
@[stacks 03RO]
class IsAbelianVariety (k : Type u) [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] : Prop extends IsProperVariety k A.hom, GeometricallyIntegral A.hom

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The base change of a group scheme over `Spec k` along a field extension `K/k` is a group
scheme over `Spec K`. -/
noncomputable instance grpObjPullbackObj (A : Over (Spec (.of k))) [GrpObj A] :
    GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj (.mk A)).grp

/-- **Stacks Project, Tag 0BFB.** For a field extension `K/k`, the base change `A_K` of an
abelian variety `A` over `k` is an abelian variety over `K`. -/
@[stacks 0BFB]
instance isAbelianVariety_pullbackObj (A : Over (Spec (.of k))) [GrpObj A]
    [IsAbelianVariety k A] :
    IsAbelianVariety K
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A) := by
  set g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hint : IsIntegral ((Over.pullback g).obj A).left :=
    GeometricallyIntegral.geometrically_isIntegral (f := A.hom) g _ _
      (IsPullback.of_hasPullback A.hom g)
  have hproper : IsProper ((Over.pullback g).obj A).hom :=
    inferInstanceAs (IsProper (pullback.snd A.hom g))
  have hgeom : GeometricallyIntegral ((Over.pullback g).obj A).hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd A.hom g))
  exact .mk (toIsProperVariety := .mk (toIsVariety := .mk))

end AlgebraicGeometry

add_to_stacks 03RP "commutative" AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral
add_to_sga "3 VIB 12.3" "special case"
  AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral

end
