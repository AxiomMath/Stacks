module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace

/-!
# Orbits of a pre-relation at a field-valued point

Fix a scheme `S` in a big fppf site `B` and a presheaf `Z` on the big fppf site of `S`, and
let `j : R ⟶ U ×_Z U` be a pre-relation. For a field-valued point `p` of `Z` the pre-relation
induces a binary relation on the `U`-valued points of the spectrum of the field of `p` lying
over `p`. Two such points are *weakly equivalent* when they are joined by a finite chain of
arrows of `j` over that field, and *equivalent* when they become weakly equivalent after one
extension of the field. The corresponding classes of a point are its *weak orbit* and its
*orbit*; the source takes them at a geometric point, that is at an algebraically closed
field.

If `j` is a pre-equivalence relation the relation on points over each field is already an
equivalence relation, so weak equivalence needs a single arrow, and equivalence a single
arrow after a field extension.

## Main definitions

* `AlgebraicGeometry.Space.PreRelation.WeaklyEquivalent` and
  `AlgebraicGeometry.Space.PreRelation.Equivalent`: the two relations on the points of `U`
  over a field-valued point of `Z`.
* `AlgebraicGeometry.Space.PreRelation.weakOrbit` and
  `AlgebraicGeometry.Space.PreRelation.orbit`: their classes at a geometric point.

## Main results

* `AlgebraicGeometry.Space.PreRelation.weakOrbit_eq_targets`: for a pre-equivalence relation
  the weak orbit of a point consists of the targets of the arrows whose source it is.
* `AlgebraicGeometry.Space.PreRelation.orbit_eq_targets_after_extension`: the same
  description of the orbit, after one field extension.

## Implementation notes

The points of `U` over a field-valued point `p` of `Z` are the test points of
`AlgebraicGeometry.Space.TestPoint` for the object of the site represented by `p` and the
morphism `yonedaEquiv.symm p.value` to `Z`; no separate notion is introduced for them, and
the relation they carry is `AlgebraicGeometry.Space.PreRelation.Rel`. In an arrow
`j.Rel b y x` the target comes before the source, which is why the right-hand sides below
have the arrow pointing from `x` to `y`.

Weak equivalence is defined for every field-valued point, not only for a geometric one, so
that it also applies over the extension field appearing in `Equivalent`. A field extension is
a morphism of the corresponding objects of the site whose restriction carries the section of
`p` to the section of the extension; the two points over the extension are required to be
precisely the Yoneda precompositions of the original pair.

## References

* [Stacks Project, Tag 048Q](https://stacks.math.columbia.edu/tag/048Q)
* [Stacks Project, Tag 048R](https://stacks.math.columbia.edu/tag/048R)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}

namespace PreRelation

/-- Two points of `U` over a field-valued point `p` of `Z` are
*weakly equivalent* when they are joined by a finite chain of arrows of the pre-relation over
the field of `p`, traversed in either direction and with stationary steps allowed. -/
@[stacks 048Q "part (1): weak equivalence"]
abbrev WeaklyEquivalent (j : PreRelation R U) (p : FieldValuedPoint B S hS Z)
    (x y : TestPoint (p.siteObject B S hS Z) (yonedaEquiv.symm p.value) U) : Prop :=
  Relation.EqvGen (j.Rel (yonedaEquiv.symm p.value)) x y

/-- Two points of `U` over a field-valued point `p` of `Z` are
*equivalent* when their restrictions to some extension of the field of `p` are weakly
equivalent. -/
@[stacks 048Q "part (2): equivalence after extension"]
abbrev Equivalent (j : PreRelation R U) (p : FieldValuedPoint B S hS Z)
    (x y : TestPoint (p.siteObject B S hS Z) (yonedaEquiv.symm p.value) U) : Prop :=
  ∃ (q : FieldValuedPoint B S hS Z) (f : q.siteObject B S hS Z ⟶ p.siteObject B S hS Z),
    Z.map f.op p.value = q.value ∧
      ∃ x' y' : TestPoint (q.siteObject B S hS Z) (yonedaEquiv.symm q.value) U,
        x'.1 = yoneda.map f ≫ x.1 ∧ y'.1 = yoneda.map f ≫ y.1 ∧ j.WeaklyEquivalent q x' y'

/-- The *weak orbit* of a point of `U` over a geometric point of
`Z`: its class for weak equivalence over the given algebraically closed field. -/
@[stacks 048Q "part (3): weak orbit"]
abbrev weakOrbit (j : PreRelation R U) (p : GeometricPoint B S hS Z)
    (x : TestPoint (p.val.siteObject B S hS Z) (yonedaEquiv.symm p.val.value) U) :
    Set (TestPoint (p.val.siteObject B S hS Z) (yonedaEquiv.symm p.val.value) U) :=
  {y | j.WeaklyEquivalent p.val x y}

/-- The *orbit* of a point of `U` over a geometric point of `Z`:
its class for equivalence, that is after allowing one extension of the field. -/
@[stacks 048Q "part (4): orbit"]
abbrev orbit (j : PreRelation R U) (p : GeometricPoint B S hS Z)
    (x : TestPoint (p.val.siteObject B S hS Z) (yonedaEquiv.symm p.val.value) U) :
    Set (TestPoint (p.val.siteObject B S hS Z) (yonedaEquiv.symm p.val.value) U) :=
  {y | j.Equivalent p.val x y}

/-- For an equivalence relation, being joined by a chain of arrows is the same as a single arrow. -/
private theorem eqvGen_iff_rel_symm {α : Type*} {r : α → α → Prop} (hr : Equivalence r) {x y : α} :
    Relation.EqvGen r x y ↔ r y x :=
  ⟨fun h ↦ hr.symm (hr.eqvGen_iff.mp h), fun h ↦ .rel _ _ (hr.symm h)⟩

/-- For a pre-equivalence relation the weak orbit of a point is cut out by a
single arrow: it consists of the targets of the arrows whose source is that point. -/
@[stacks 048R "weak orbit"]
theorem weakOrbit_eq_targets (j : PreRelation R U) (hj : IsPreEquivalenceRelation j)
    (p : GeometricPoint B S hS Z)
    (x : TestPoint (p.val.siteObject B S hS Z) (yonedaEquiv.symm p.val.value) U) :
    j.weakOrbit p x = {y | j.Rel (yonedaEquiv.symm p.val.value) y x} := by
  ext y
  exact eqvGen_iff_rel_symm (hj _ _)

/-- For a pre-equivalence relation the orbit of a point is cut out by a
single arrow over some extension of the field of the geometric point. -/
@[stacks 048R "orbit"]
theorem orbit_eq_targets_after_extension (j : PreRelation R U)
    (hj : IsPreEquivalenceRelation j) (p : GeometricPoint B S hS Z)
    (x : TestPoint (p.val.siteObject B S hS Z) (yonedaEquiv.symm p.val.value) U) :
    j.orbit p x =
      {y | ∃ (q : FieldValuedPoint B S hS Z)
          (f : q.siteObject B S hS Z ⟶ p.val.siteObject B S hS Z),
          Z.map f.op p.val.value = q.value ∧
            ∃ x' y' : TestPoint (q.siteObject B S hS Z) (yonedaEquiv.symm q.value) U,
              x'.1 = yoneda.map f ≫ x.1 ∧ y'.1 = yoneda.map f ≫ y.1 ∧
                j.Rel (yonedaEquiv.symm q.value) y' x'} := by
  ext y
  constructor
  · rintro ⟨q, f, hf, x', y', hx, hy, h⟩
    exact ⟨q, f, hf, x', y', hx, hy, (eqvGen_iff_rel_symm (hj _ _)).mp h⟩
  · rintro ⟨q, f, hf, x', y', hx, hy, h⟩
    exact ⟨q, f, hf, x', y', hx, hy, (eqvGen_iff_rel_symm (hj _ _)).mpr h⟩

end PreRelation

end AlgebraicGeometry.Space

end
