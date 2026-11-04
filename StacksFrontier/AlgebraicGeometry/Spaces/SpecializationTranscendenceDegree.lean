module

public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.SpecializationTrdeg

/-!
# The germ transcendence degree drops strictly along a specialization

On a scheme locally of finite type over a field, the transcendence degree of the residue field
strictly decreases along a nontrivial specialization. That statement is already available as
`AlgebraicGeometry.trdeg_residueField_lt_of_specialization`, where the `k`-algebra structure on a
residue field is the canonical composite from `k` through global sections and evaluation at the
point. This file restates it for the germ invariant of Tag 04NK, whose base field is instead the
residue field of the target at the image point, which is the form in which the transcendence
degree at a point of an algebraic space is read off a chart.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.trdeg_residueField_eq_trdeg_base`: over the spectrum of a field, the
  transcendence degree of a residue field over the residue field of the base at the image point
  is its transcendence degree over the field itself.
* `AlgebraicGeometry.lt_trdeg_of_specialization_of_ne`: the strict drop, stated for
  `AlgebraicGeometry.MorphismOfGerms.HasResidueFieldTranscendenceDegree`.

## Implementation notes

The two conventions for the `Algebra` structure on a residue field differ, and the comparison is
the content of `AlgebraicGeometry.trdeg_residueField_eq_trdeg_base`: the residue field of
`Spec k` at its unique point is `k` itself, because that point is the maximal ideal `⊥`, so the
structure map `k ⟶ κ(p)` is surjective and `κ(p)` is algebraic over `k`; the dimension formula
`trdeg_add_eq` for the tower `k ⊆ κ(p) ⊆ κ(x)`, whose scalar-tower hypothesis is Tag 04NK's
`AlgebraicGeometry.residueField_isScalarTower`, then kills the bottom step.

The germ invariant takes values in `ℕ∞` while `Algebra.trdeg` is a `Cardinal`, so the strict
inequality has to be transported along `Cardinal.toENat`, which is only strictly monotone below
`ℵ₀`. Both transcendence degrees are finite because the morphism is locally of finite type
(`AlgebraicGeometry.residueField_finTrdeg`), which is why that hypothesis cannot be dropped even
though the cardinal-valued statement would not need `Cardinal.toENat` at all.

No new statement of the mathematics of Tag 0A21 is made here, so no `@[stacks]` attribute is
attached: the tag sits on `AlgebraicGeometry.trdeg_residueField_lt_of_specialization`, and this
file only changes the convention in which the degrees are measured.

## References

* [Stacks Project, Tag 02JX](https://stacks.math.columbia.edu/tag/02JX)
* [Stacks Project, Tag 04NK](https://stacks.math.columbia.edu/tag/04NK)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The canonical map from a field `k` to the residue field of `Spec k` at a point is surjective:
that point is the maximal ideal `⊥`, and the map factors as the surjection onto `k ⧸ ⊥` followed
by an isomorphism. -/
private theorem surjective_spec_residueField_algebraMap (k : Type u) [Field k]
    (p : Spec (CommRingCat.of k)) :
    Function.Surjective
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation p).hom := by
  have : p.asIdeal.IsPrime := p.isPrime
  have : p.asIdeal.IsMaximal := by
    simpa [p.asIdeal.eq_bot_of_prime] using (Ideal.bot_isMaximal : (⊥ : Ideal k).IsMaximal)
  have hcomp : ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation p).hom =
      (Scheme.Spec.residueFieldIso (.of k) p).inv.hom.comp
        (algebraMap k p.asIdeal.ResidueField) := by
    simpa [Scheme.Γevaluation, Scheme.evaluation, RingHom.comp_assoc] using
      (congrArg CommRingCat.Hom.hom
        (Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) p)).symm
  rw [hcomp]
  exact (Scheme.Spec.residueFieldIso (.of k) p).symm.commRingCatIsoToRingEquiv.surjective.comp
    p.asIdeal.algebraMap_residueField_surjective

/-- **The base residue field of a scheme over a field contributes nothing.** For a morphism to the
spectrum of a field, the transcendence degree of a residue field over the residue field of the
base at the image point agrees with its transcendence degree over the field itself. -/
theorem trdeg_residueField_eq_trdeg_base (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    letI : Algebra ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg ((Spec (.of k)).residueField (f x)) (X.residueField x) =
      Algebra.trdeg k (X.residueField x) := by
  let _ : Algebra k ((Spec (.of k)).residueField (f x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)).hom.toAlgebra
  let _ : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let _ : Algebra ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower k ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
    residueField_isScalarTower k f x
  have : Algebra.IsIntegral k ((Spec (.of k)).residueField (f x)) :=
    Algebra.isIntegral_of_surjective (surjective_spec_residueField_algebraMap k (f x))
  have h := trdeg_add_eq k ((Spec (.of k)).residueField (f x)) (A := X.residueField x)
  rwa [trdeg_eq_zero, zero_add] at h

/-- **The strict drop of the germ transcendence degree along a specialization.** Let `U` be a
scheme locally of finite type over a field `k` and let `u ⤳ u'` be a nontrivial specialization in
`U`. Then the residue-field transcendence degree of the germ of the structure morphism at `u'` is
strictly smaller than the one at `u`.

This is the convention-change of `AlgebraicGeometry.trdeg_residueField_lt_of_specialization` into
the germ invariant of Tag 04NK; see
`AlgebraicGeometry.trdeg_residueField_eq_trdeg_base` for the comparison of the two base fields and
`AlgebraicGeometry.residueField_finTrdeg` for the finiteness that makes `Cardinal.toENat`
strictly monotone on the two values. -/
theorem lt_trdeg_of_specialization_of_ne
    {k : Type u} [Field k] {U : Scheme.{u}} (h : U ⟶ Spec (.of k))
    [AlgebraicGeometry.LocallyOfFiniteType h] {u u' : U} (hspec : u ⤳ u') (hne : u ≠ u')
    (r r' : ℕ∞)
    (hr : MorphismOfGerms.HasResidueFieldTranscendenceDegree r
      (MorphismOfGerms.ofSchemeHom h u))
    (hr' : MorphismOfGerms.HasResidueFieldTranscendenceDegree r'
      (MorphismOfGerms.ofSchemeHom h u')) :
    r' < r := by
  let _ : Algebra k (U.residueField u) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop ≫ U.Γevaluation u).hom.toAlgebra
  let _ : Algebra k (U.residueField u') :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop ≫ U.Γevaluation u').hom.toAlgebra
  let _ : Algebra ((Spec (.of k)).residueField (h u)) (U.residueField u) :=
    (h.residueFieldMap u).hom.toAlgebra
  let _ : Algebra ((Spec (.of k)).residueField (h u')) (U.residueField u') :=
    (h.residueFieldMap u').hom.toAlgebra
  rw [← (MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff h u r).mp hr,
    ← (MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff h u' r').mp hr',
    trdeg_residueField_eq_trdeg_base k h u, trdeg_residueField_eq_trdeg_base k h u']
  exact Cardinal.toENat_strictMonoOn (finTrdeg_iff_trdeg.mp (residueField_finTrdeg k h u')).le
    (finTrdeg_iff_trdeg.mp (residueField_finTrdeg k h u)).le
    (trdeg_residueField_lt_of_specialization k U h hspec hne)

end AlgebraicGeometry

end
