module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.LocalFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Descent.Algebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.SyntomicLocus.Basic

/-!
# A faithfully flat factor of a syntomic morphism is syntomic

Let `X ⟶ Y ⟶ S` be morphisms of schemes with `f : X ⟶ Y` surjective, flat and locally of finite
presentation. If the composite `f ≫ q` is syntomic then `f` is syntomic.

By Lemma 02KL the morphism `q : Y ⟶ S` is locally of finite presentation, so by Lemma 01UE it
suffices to show that the local ring of the fibre of `f` at each point of `X` is a complete
intersection over the residue field of its image. At a point `x : X` the three local rings form
a tower `𝒪_{S, s} → 𝒪_{Y, y} → 𝒪_{X, x}` of local homomorphisms whose second map is flat, and
the closed fibre of the composite is a complete intersection because `f ≫ q` is syntomic;
Avramov's criterion 09Q7, in the form
`LocalCompleteIntersection.isCompleteIntersection_closedFibre_of_flat`, gives the closed fibre
of the second map.

The same argument gives the companion conclusion of the source, that `q` is syntomic; that
statement is already in this development as
`AlgebraicGeometry.syntomic_of_comp_of_fppf`, proved there by reduction to the affine case, and
is not reproved here.

## Main results

* `AlgebraicGeometry.isCompleteIntersectionFibreAt_pair_of_comp_of_flat`: the fibres of `q` and
  of `f` at a point are complete intersections as soon as the fibre of `f ≫ q` is.
* `AlgebraicGeometry.syntomic_of_syntomic_comp_of_fppf`: `f` is syntomic.

## Implementation notes

The morphism called `p : X ⟶ S` in the source is the composite `f ≫ q`, so the source's
commutative triangle is expressed by writing `p` in that form.

Syntomicity at a point is `AlgebraicGeometry.SyntomicAt`, while the complete-intersection
criterion of Lemma 01UE is stated for the definitionally equal
`AlgebraicGeometry.IsSyntomicAt`; `AlgebraicGeometry.syntomicAt_iff_isSyntomicAt` records that
the two agree.

## References

* [Stacks Project, Tag 05B7](https://stacks.math.columbia.edu/tag/05B7)
* [Stacks Project, Tag 01UE](https://stacks.math.columbia.edu/tag/01UE)
* [Stacks Project, Tag 09Q7](https://stacks.math.columbia.edu/tag/09Q7)
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The two spellings of Definition 01UC agree: `AlgebraicGeometry.SyntomicAt` and
`AlgebraicGeometry.IsSyntomicAt` are the same condition. -/
theorem syntomicAt_iff_isSyntomicAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    SyntomicAt f x ↔ IsSyntomicAt f x := Iff.rfl

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)

/-- Both closed fibres of the tower of local rings at a point. If the fibre of the composite
`f ≫ q` at `x` is a complete intersection over the residue field of its image, then so is the
fibre of `q` at `f x` and the fibre of `f` at `x`.

The two maps on local rings `𝒪_{S, q(f x)} → 𝒪_{Y, f x} → 𝒪_{X, x}` are local homomorphisms,
the second is flat since `f` is, and both are essentially of finite type since `q` and `f` are
locally of finite type; this is Avramov's criterion on the closed fibres of such a tower. -/
theorem isCompleteIntersectionFibreAt_pair_of_comp_of_flat
    [Flat f] [LocallyOfFiniteType f] [LocallyOfFiniteType q] (x : X)
    (h : IsCompleteIntersectionFibreAt (f ≫ q) x) :
    IsCompleteIntersectionFibreAt q (f x) ∧ IsCompleteIntersectionFibreAt f x := by
  let R := S.presheaf.stalk (q (f x))
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let _ : Algebra R A := (q.stalkMap (f x)).hom.toAlgebra
  let _ : Algebra A B := (f.stalkMap x).hom.toAlgebra
  let _ : Algebra R B := ((f ≫ q).stalkMap x).hom.toAlgebra
  have hcomp : ((f ≫ q).stalkMap x).hom = (f.stalkMap x).hom.comp (q.stalkMap (f x)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f q x)
  have _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' hcomp
  have _ : IsLocalHom (algebraMap R A) := q.toLRSHom.prop (f x)
  have _ : IsLocalHom (algebraMap A B) := f.toLRSHom.prop x
  have _ : Module.Flat A B := RingHom.flat_algebraMap_iff.mp (Flat.stalkMap f x)
  have _ : Algebra.EssFiniteType R A :=
    RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.stalkMap q (f x))
  have _ : Algebra.EssFiniteType A B :=
    RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.stalkMap f x)
  exact ⟨LocalCompleteIntersection.isCompleteIntersection_closedFibre_base_of_flat R A B h,
    LocalCompleteIntersection.isCompleteIntersection_closedFibre_of_flat R A B h⟩

/-- **Stacks Project, Tag 05B7.** A surjective flat morphism locally of finite presentation is
syntomic as soon as its composite with another morphism is syntomic. -/
@[stacks 05B7 "f_syntomic"]
theorem syntomic_of_syntomic_comp_of_fppf [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] (hp : Syntomic (f ≫ q)) : Syntomic f := by
  have _ : LocallyOfFinitePresentation (f ≫ q) := locallyOfFinitePresentation hp
  have _ : Flat (f ≫ q) := flat hp
  have _ : LocallyOfFinitePresentation q := locallyOfFinitePresentation_of_comp_of_fppf f q
  intro x
  rw [syntomicAt_iff_isSyntomicAt, isSyntomicAt_iff_isCompleteIntersectionFibreAt f x]
  exact (isCompleteIntersectionFibreAt_pair_of_comp_of_flat f q x
    ((isSyntomicAt_iff_isCompleteIntersectionFibreAt (f ≫ q) x).mp (hp x))).2

end AlgebraicGeometry
