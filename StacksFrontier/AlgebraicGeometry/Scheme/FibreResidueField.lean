module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# The residue field of a scheme-theoretic fibre

A morphism of schemes which is surjective on stalks induces a *surjective* map of residue
fields, and a map of fields is injective, so the induced map is an isomorphism. The projection
of a scheme-theoretic fibre to the ambient scheme is a preimmersion, hence surjective on stalks,
so the residue field of the fibre of `f : X ⟶ Y` over `y` at a point `p` agrees with the residue
field of `X` at the image of `p`. This file records that comparison in the form needed to read a
transcendence degree over the residue field of the image point off the fibre or off the ambient
scheme interchangeably.

## Main results

* `AlgebraicGeometry.trdeg_residueField_comp_of_surjectiveOnStalks`: restricting the source of a
  morphism along a morphism surjective on stalks does not change the transcendence degree of the
  residue field extension at a point.
* `AlgebraicGeometry.trdeg_residueField_fiber`: the special case of the projection of a
  scheme-theoretic fibre.

## Implementation notes

The extension is recorded as an `Algebra` instance built from
`AlgebraicGeometry.Scheme.Hom.residueFieldMap`, the convention in which the three numerical
invariants of Stacks 04NM are stated, rather than the `Scheme.ΓSpecIso`/`Scheme.Γevaluation`
convention used for a morphism to the spectrum of a literal field in
`StacksFrontier/AlgebraicGeometry/Variety/Defs/Dimension/ResidueField.lean`. The two statements are
therefore not interchangeable, and the surjectivity-of-residue-fields step is repeated here;
what is new is that the comparison is available over the residue field of the image point, which
is what a fibre of a morphism of schemes comes with.

The point of the fibre is left as an arbitrary `p`, with its image written out as
`f.fiberι y p`; a client holding the distinguished point of the fibre through `x` rewrites with
`AlgebraicGeometry.Scheme.Hom.fiberι_asFiber`.

## References

* [Stacks Project, Tag 01J9](https://stacks.math.columbia.edu/tag/01J9)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes which is surjective on stalks induces a surjective map of residue
fields. -/
public theorem surjective_residueFieldMap_of_surjectiveOnStalks {X Z : Scheme.{u}} (i : Z ⟶ X)
    [SurjectiveOnStalks i] (z : Z) : Function.Surjective (i.residueFieldMap z).hom := by
  have h := (Z.residue_surjective z).comp (i.stalkMap_surjective z)
  change Function.Surjective (i.stalkMap z ≫ Z.residue z).hom at h
  rw [← Scheme.residue_residueFieldMap i z] at h
  intro a
  obtain ⟨b, hb⟩ := h a
  exact ⟨(X.residue (i z)).hom b, hb⟩

/-- Restricting the source of a morphism of schemes along a morphism surjective on stalks does
not change the transcendence degree of the residue field extension at a point: such a morphism
induces an isomorphism of residue fields over the residue field of the image point. -/
public theorem trdeg_residueField_comp_of_surjectiveOnStalks {X Y Z : Scheme.{u}} (i : Z ⟶ X)
    [SurjectiveOnStalks i] (f : X ⟶ Y) (z : Z) :
    letI : Algebra (Y.residueField (f (i z))) (X.residueField (i z)) :=
      (f.residueFieldMap (i z)).hom.toAlgebra
    letI : Algebra (Y.residueField (f (i z))) (Z.residueField z) :=
      ((i ≫ f).residueFieldMap z).hom.toAlgebra
    Algebra.trdeg (Y.residueField (f (i z))) (Z.residueField z) =
      Algebra.trdeg (Y.residueField (f (i z))) (X.residueField (i z)) := by
  let _ : Algebra (Y.residueField (f (i z))) (X.residueField (i z)) :=
    (f.residueFieldMap (i z)).hom.toAlgebra
  let _ : Algebra (Y.residueField (f (i z))) (Z.residueField z) :=
    ((i ≫ f).residueFieldMap z).hom.toAlgebra
  let e : X.residueField (i z) ≃ₐ[Y.residueField (f (i z))] Z.residueField z :=
    { RingEquiv.ofBijective (i.residueFieldMap z).hom
        ⟨(i.residueFieldMap z).hom.injective,
          surjective_residueFieldMap_of_surjectiveOnStalks i z⟩ with
      commutes' := fun a ↦
        (congrArg (fun m : CommRingCat.Hom _ _ ↦ m.hom a)
          (Scheme.residueFieldMap_comp i f z)).symm }
  exact e.trdeg_eq.symm

/-- The residue field of the scheme-theoretic fibre of `f` over `y` at a point `p` has the same
transcendence degree over the residue field of the image of `p` as the residue field of the
ambient scheme there. -/
public theorem trdeg_residueField_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (p : f.fiber y) :
    letI : Algebra (Y.residueField (f (f.fiberι y p))) (X.residueField (f.fiberι y p)) :=
      (f.residueFieldMap (f.fiberι y p)).hom.toAlgebra
    letI : Algebra (Y.residueField (f (f.fiberι y p))) ((f.fiber y).residueField p) :=
      ((f.fiberι y ≫ f).residueFieldMap p).hom.toAlgebra
    Algebra.trdeg (Y.residueField (f (f.fiberι y p))) ((f.fiber y).residueField p) =
      Algebra.trdeg (Y.residueField (f (f.fiberι y p))) (X.residueField (f.fiberι y p)) :=
  trdeg_residueField_comp_of_surjectiveOnStalks (f.fiberι y) f p

end AlgebraicGeometry

end
