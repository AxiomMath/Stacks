module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# Being an isomorphism is fpqc local on the base for algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism of algebraic spaces over `S`
is an isomorphism exactly when its base change to every member of some fpqc covering family of
its target is an isomorphism. This is **Stacks 041Y**.

The decomposition is the source's: a morphism of algebraic spaces is an isomorphism exactly
when it is an open immersion and surjective (**Stacks 03MD** and **Stacks 02YU**, part (1)),
being an open immersion is fpqc local on the base by **Stacks 041X** and surjectivity by
**Stacks 041Q**, and locality on the base passes to an infimum of morphism properties.

## Main results

* `AlgebraicGeometry.Space.isIso_iff_isOpenImmersion_and_isSurjective`: a morphism of algebraic
  spaces over `S` is an isomorphism exactly when it is an open immersion and surjective on
  points.
* `AlgebraicGeometry.Space.isomorphisms_eq_openImmersionProperty_inf_surjective`: the same
  statement as an identity of morphism properties.
* `AlgebraicGeometry.Space.isomorphisms_isLocalAtTarget_fpqc`: **Stacks 041Y**.
* `AlgebraicGeometry.Space.isomorphisms_isLocalAtTarget_fppf`: the same at the fppf
  precoverage, which is the form the relative properties of Stacks 03YK consume.

## Implementation notes

Being an isomorphism needs no packaging of its own: it is Mathlib's
`CategoryTheory.MorphismProperty.isomorphisms` on the category
`AlgebraicGeometry.AlgebraicSpaces` of algebraic spaces over `S`, and the equivalence with the
conjunction of the two factors is read off one morphism at a time through
`CategoryTheory.ObjectProperty.isIso_hom_iff`, which identifies invertibility in that category
with invertibility of the underlying morphism of presheaves.

The nontrivial half of the equivalence is that a surjective open immersion is invertible,
which is `AlgebraicGeometry.Space.isIso_of_presheaf_isOpenImmersion_of_presheafSurjective`.
It asks for surjectivity in the representable sense — every represented base change is a
surjective morphism of schemes — whereas
`AlgebraicGeometry.Space.surjectiveMorphismProperty` is surjectivity of the induced map on the
point sets of Stacks 03BU; the two agree for a representable morphism by Stacks 03MD, and the
representability witness is the one carried by the open immersion.

Stacks 041X enters as `AlgebraicGeometry.Space.openImmersion_isLocalAtTarget_fpqc`, which is
unconditional: the fpqc sheaf condition for algebraic spaces it rests on is Gabber's
**Stacks 0APL**, proved in this library as
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc`.

The index universe of a covering family is a free universe parameter of
`AlgebraicGeometry.Space.Topology.precoverage` and stays free here, as it does in Stacks 041Q
and Stacks 041X.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041Q](https://stacks.math.columbia.edu/tag/041Q)
* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of algebraic spaces over `S` is an isomorphism exactly when it is an open
immersion (**Stacks 02YU**, part (1)) and surjective on the point sets of Stacks 03BU.

An isomorphism is an open immersion and induces a bijection on points. Conversely an open
immersion is representable, so its surjectivity on points is surjectivity of each of its
represented base changes by **Stacks 03MD**; each such base change is then a surjective open
immersion of schemes, hence invertible, and the inverses assemble into an inverse of the
morphism itself. -/
theorem isIso_iff_isOpenImmersion_and_isSurjective {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion B S hS f.hom ∧ IsSurjective B S hS f.hom := by
  constructor
  · intro hf
    have hhom : IsIso f.hom := (ObjectProperty.isIso_hom_iff f).mpr hf
    refine ⟨isOpenImmersion_of_isIso B S hS f.hom,
      fun y => ⟨pointsMap B S hS Y.obj (inv f.hom) y, ?_⟩⟩
    have h := congrFun (pointsMap_comp B S hS Y.obj (inv f.hom) f.hom) y
    rw [IsIso.inv_hom_id, pointsMap_id] at h
    exact h.symm
  · rintro ⟨ho, hs⟩
    exact (ObjectProperty.isIso_hom_iff f).mp <|
      isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS f.hom ho
        (presheafSurjective_of_isSurjective B S hS f.hom ho.rep hs)

/-- Being an isomorphism is, as a property of morphisms of algebraic spaces over `S`, the
infimum of being an open immersion (**Stacks 02YU**, part (1)) and being surjective
(**Stacks 03MD**). -/
theorem isomorphisms_eq_openImmersionProperty_inf_surjective :
    MorphismProperty.isomorphisms (AlgebraicSpaces B S hS) =
      openImmersionProperty B S hS ⊓ surjectiveMorphismProperty B S hS := by
  funext X Y f
  exact propext (isIso_iff_isOpenImmersion_and_isSurjective B S hS f)

/-- **Stacks 041Y.** Being an isomorphism is, for morphisms of algebraic spaces over `S`, local
on the base for the fpqc topology of Stacks 03YH: such a morphism is an isomorphism exactly
when its base change to every member of some fpqc covering family of its target is an
isomorphism.

A morphism is an isomorphism exactly when it is a surjective open immersion, surjectivity is
fpqc local on the base by **Stacks 041Q** and being an open immersion by **Stacks 041X**, so
their conjunction is. -/
@[stacks 041Y, sga "4 IV 8.5.5" "more general"]
instance isomorphisms_isLocalAtTarget_fpqc :
    (MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have : (openImmersionProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
    openImmersion_isLocalAtTarget_fpqc.{u, v} B S hS
  rw [isomorphisms_eq_openImmersionProperty_inf_surjective]
  exact MorphismProperty.IsLocalAtTarget.inf _ _

/-- **Stacks 041Y** at the fppf precoverage: being an isomorphism is local on the target for
the fppf topology of algebraic spaces. This is the form in which Stacks 03YK's relative
properties ask for it, and it follows from the fpqc form because every fppf covering family of
algebraic spaces is an fpqc covering family (**Stacks 0DFQ**). -/
instance isomorphisms_isLocalAtTarget_fppf :
    (MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fppf B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
