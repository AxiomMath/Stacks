module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.Etale.GeometricPoint

/-!
# A bound on geometric fibres bounds every set-theoretic fibre

Every point of a scheme is the image of a geometric point, obtained from an algebraic closure of
its residue field. Consequently a uniform bound on the number of points of the geometric fibres
of a morphism bounds the number of points of each of its set-theoretic fibres.

## Main definitions

* `Stacks.Etale.ofPoint` is the geometric point attached to a point of a scheme by taking an
  algebraic closure of its residue field.

## Main results

* `Stacks.Etale.ofPoint_liesOver` says that this geometric point lies over the given point.
* `Stacks.Etale.cardinalMk_fibre_le` transfers a uniform cardinality bound on the geometric
  fibres of a morphism to each of its set-theoretic fibres.

## Implementation notes

The set-theoretic fibre is expressed as the subtype of points of the source mapping to the given
point, and the bound is a `Cardinal` inequality, so neither side presupposes finiteness. The
bounding map is the second projection of the base change along the geometric point; it is
surjective onto the fibre because a point of a fibre product exists above any pair of points
with the same image.

## References

* [Stacks Project, Tag 03PO](https://stacks.math.columbia.edu/tag/03PO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

/-- The geometric point of `S` attached to a point `s`, with residue field an algebraic closure
of the residue field of `S` at `s`. -/
def ofPoint {S : Scheme.{u}} (s : S) : GeometricPoint S where
  residueField := AlgebraicClosure (S.residueField s)
  hom := Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
    S.fromSpecResidueField s

/-- Every point of the spectrum of the algebraic closure maps to `s` under the geometric point
`ofPoint s`. -/
@[simp]
lemma ofPoint_hom_base {S : Scheme.{u}} (s : S) (z : (ofPoint s).source) :
    (ofPoint s).hom z = s :=
  Scheme.fromSpecResidueField_apply s _

/-- The geometric point attached to a point lies over that point. -/
lemma ofPoint_liesOver {S : Scheme.{u}} (s : S) : (ofPoint s).LiesOver s :=
  ofPoint_hom_base s default

/-- A uniform bound on the number of points of the geometric fibres of a morphism bounds the
number of points of each of its set-theoretic fibres. -/
theorem cardinalMk_fibre_le {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Cardinal.{u})
    (h : ∀ p : GeometricPoint Y, Cardinal.mk (pullback p.hom f : Scheme.{u}) ≤ c)
    (y : Y) : Cardinal.mk {x : X // f.base x = y} ≤ c := by
  have key : ∀ z : (pullback (ofPoint y).hom f : Scheme.{u}),
      f ((pullback.snd (ofPoint y).hom f) z) = y := by
    intro z
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply,
      ofPoint_hom_base]
  refine le_trans (Cardinal.mk_le_of_surjective
    (f := fun z : (pullback (ofPoint y).hom f : Scheme.{u}) =>
      (⟨(pullback.snd (ofPoint y).hom f) z, key z⟩ : {x : X // f.base x = y})) ?_)
    (h (ofPoint y))
  rintro ⟨x, hx⟩
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (ofPoint y).hom) (g := f) default x (by rw [ofPoint_hom_base]; exact hx.symm)
  exact ⟨z, Subtype.ext hz⟩

end Stacks.Etale

end
