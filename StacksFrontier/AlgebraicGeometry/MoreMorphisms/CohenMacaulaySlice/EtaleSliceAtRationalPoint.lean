module

public import StacksFrontier.AlgebraicGeometry.Curves.JacobianCriterionNodal
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Separatedness
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.EtaleSlice
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField

/-!
# Étale slices through a rational point of a smooth morphism

Let `p : S' ⟶ S` be a smooth morphism of schemes and let `s' : S'` be a point at which the
residue field extension `κ(s')/κ(p s')` is trivial, in the sense that the induced map
`κ(p s') ⟶ κ(s')` is an isomorphism;  that is, `s'` is a rational point of the fibre of `p` over
`p s'`.  Then `s'` lies on an immersed subscheme `V ⊆ S'` which is étale over `S` and at whose
distinguished point the residue field extension is still trivial.

This is the case of Stacks tag 057G in which the hypotheses on the point hold automatically:  a
rational point of a fibre is closed in that fibre, and a trivial residue field extension is
separable.  Carrying the triviality of the residue field extension through to the slice makes the
result an étale neighbourhood statement:  `V ⟶ S` is étale and `v` has the same residue field as
its image.

## Main results

* `Stacks.AlgebraicGeometry.exists_etale_immersion_of_smooth_of_isIso_residueFieldMap`:  the
  étale slice through a rational point of a smooth morphism, with the residue field extension at
  the distinguished point of the slice again trivial.

## Implementation notes

The three hypotheses of Stacks tag 057G are discharged as follows.  Smoothness at `s'` comes from
smoothness of `p` by `AlgebraicGeometry.InfinitesimalLifting.smoothAt_of_smooth`.  Closedness of
`s'` in the fibre comes from `AlgebraicGeometry.isClosed_asFiber_of_isAlgebraic_residueField`,
the residue field extension being algebraic because its structure map is surjective.  Separability
in the sense of Stacks tag 030O is `Stacks.Curves.isSeparableExtension_of_surjective_algebraMap`
for the same reason.

The extra conclusion about the residue field at the distinguished point of the slice splits along
`AlgebraicGeometry.Scheme.residueFieldMap_comp`:  the factor coming from `p` is the hypothesis,
transported along the equality of points, and the factor coming from the immersion is
`AlgebraicGeometry.isIso_residueFieldMap_of_isImmersion`.

The fibre of the slice is a single point by Stacks tag 057G, but that conclusion is not recorded
here.

## References

* [Stacks Project, Tag 057G](https://stacks.math.columbia.edu/tag/057G)
* [Stacks Project, Tag 030O](https://stacks.math.columbia.edu/tag/030O)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Stacks.AlgebraicGeometry

universe u

/-- **The étale slice through a rational point of a smooth morphism.**  Let `p : S' ⟶ S` be smooth
and let `s' : S'` be a point whose residue field map `κ(p s') ⟶ κ(s')` is an isomorphism.  Then
there is an immersion `i : V ⟶ S'` hitting `s'` at a point `v` such that `V ⟶ S` is étale and the
residue field map of `i ≫ p` at `v` is again an isomorphism.  This is Stacks tag 057G, whose two
hypotheses on the point are automatic here:  a rational point of a fibre is closed in it, and a
trivial residue field extension is separable. -/
public theorem exists_etale_immersion_of_smooth_of_isIso_residueFieldMap
    {S' S : Scheme.{u}} (p : S' ⟶ S) [AlgebraicGeometry.Smooth p] (s' : S')
    (hres : IsIso (p.residueFieldMap s')) :
    ∃ (V : Scheme.{u}) (i : V ⟶ S') (v : V),
      AlgebraicGeometry.IsImmersion i ∧ i v = s' ∧
      AlgebraicGeometry.Etale (i ≫ p) ∧ IsIso ((i ≫ p).residueFieldMap v) := by
  let : Algebra (S.residueField (p s')) (S'.residueField s') :=
    (p.residueFieldMap s').hom.toAlgebra
  have hsurj : Function.Surjective (algebraMap (S.residueField (p s')) (S'.residueField s')) :=
    (ConcreteCategory.bijective_of_isIso (p.residueFieldMap s')).surjective
  have : Algebra.IsSeparable (S.residueField (p s')) (S'.residueField s') :=
    Stacks.Curves.isSeparable_of_surjective_algebraMap hsurj
  obtain ⟨V, i, v, hi, hiv, het, -⟩ :=
    exists_etale_immersion_with_singleton_fiber p s'
      (InfinitesimalLifting.smoothAt_of_smooth p s')
      (isClosed_asFiber_of_isAlgebraic_residueField p s' inferInstance)
      (Stacks.Curves.isSeparableExtension_of_surjective_algebraMap hsurj)
  have : IsImmersion i := hi
  refine ⟨V, i, v, hi, hiv, het, ?_⟩
  have h₁ : IsIso (p.residueFieldMap (i v)) := by rw [hiv]; exact hres
  have h₂ : IsIso (i.residueFieldMap v) := isIso_residueFieldMap_of_isImmersion i v
  rw [Scheme.residueFieldMap_comp]
  exact CategoryTheory.IsIso.comp_isIso' h₁ h₂

end Stacks.AlgebraicGeometry

end
