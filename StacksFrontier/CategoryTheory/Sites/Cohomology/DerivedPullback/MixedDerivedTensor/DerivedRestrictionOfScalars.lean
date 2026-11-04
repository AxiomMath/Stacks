module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.AuxiliaryRingedSite

/-!
# The derived category of `f⁻¹O'`-modules receives the derived category of `O`-modules

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi.  Restriction of scalars
along the structure map `f⁻¹O' ⟶ O` reads a sheaf of `O`-modules as a sheaf of
`f⁻¹O'`-modules; it is an exact functor of abelian categories, so it induces an exact functor
of triangulated categories

`D(O) ⟶ D(f⁻¹O')`

with no left- or right-derived subtlety: an exact functor carries a quasi-isomorphism of
cochain complexes to a quasi-isomorphism, so the composite with the localization of the
homotopy category inverts the quasi-isomorphisms and factors through `D(O)` on the nose.  There
is nothing to resolve and no comparison morphism that has to be checked to be invertible, and
in particular the functor below agrees with degreewise restriction of scalars on every complex
rather than only on a class of representatives.

This is the functor in which the right-hand side of Stacks 08I6 is read: the tag compares
`F ⊗^L_O Lf^*G`, an object of `D(O)`, with `F ⊗^L_{f⁻¹O'} f⁻¹G`, an object of `D(f⁻¹O')`, and
the comparison is a statement about the image of the first in `D(f⁻¹O')`.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.derivedRestrictToInvRing`: **the functor
  `D(O) ⥤ D(f⁻¹O')` induced by restriction of scalars along `f⁻¹O' ⟶ O`.**
* `Stacks.Cohomology.MixedDerivedTensor.restrictComplexInvRing`: degreewise restriction of
  scalars on cochain complexes, the functor the derived one is induced by.
* `Stacks.Cohomology.MixedDerivedTensor.derivedRestrictToInvRingFactors`: the factorization
  `Q ⋙ D(restriction) ≅ (degreewise restriction) ⋙ Q`, which is what computes the derived
  functor on a complex.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.exactFunctor_restrictToInvRing`: restriction of scalars
  along `f⁻¹O' ⟶ O` is exact.
* **The induced functor is an exact functor of triangulated categories**: Mathlib's
  `IsTriangulated` instance for `CategoryTheory.Functor.mapDerivedCategory`, which instance
  search finds since `derivedRestrictToInvRing` is an abbreviation.
* `Stacks.Cohomology.MixedDerivedTensor.derivedRestrictToInvRing_obj_Q`: the derived functor of
  the class of a complex is the class of the degreewise restriction of that complex.

## Implementation notes

**Nothing is constructed here.**  `CategoryTheory.Functor.mapDerivedCategory` builds the induced
functor, together with its shift commutation and its triangulatedness, from an additive functor
between abelian categories with derived categories which preserves finite limits and finite
colimits.  The three hypotheses hold for restriction of scalars of sheaves of modules on a site:
additivity is Mathlib's instance, and exactness is
`Stacks.SheafOfModules.ChangeOfRings.exactFunctor_restrictScalars`.  So the content of this file
is that the general construction applies, and the reason it is worth recording is that no
functor `D(O) ⥤ D(f⁻¹O')` existed in the development before.

**Why no derived-functor existence hypothesis appears.**  The derived pullback `Lf^*` of
Stacks 06YY carries `CategoryTheory.Functor.HasLeftDerivedFunctor` as an instance argument,
because degreewise pullback does not invert quasi-isomorphisms and the functor exists only as a
left derived functor.  Restriction of scalars does invert them, in both directions, so the
localization lifts it directly and no such argument is needed.

**Universes.**  Everything is at `AlgebraicGeometry.RingedTopos.{u, u, u}`, as in
`StacksPullbackFactorization`, and the derived categories are at the standard choice
`CategoryTheory.HasDerivedCategory.standard`, as in the derived pullback statements of
this directory.

**No tag is placed in this file.**  Stacks 08I6 is the comparison of two derived tensor
products, and nothing here concludes that; what is below is the category in which that
comparison lives.

## References

* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
* [The Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Cohomology.MixedDerivedTensor

open StacksPullbackFactorization

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : AlgebraicGeometry.RingedToposSiteHom X Y)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Restriction of scalars along `f⁻¹O' ⟶ O` is exact.**  It preserves finite limits and
finite colimits, by `Stacks.SheafOfModules.ChangeOfRings.exactFunctor_restrictScalars` at the
structure map of the ring-theoretic half of the factorization. -/
theorem exactFunctor_restrictToInvRing :
    exactFunctor (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O))
      (restrictToInvRing f) :=
  Stacks.SheafOfModules.ChangeOfRings.exactFunctor_restrictScalars (structureMapOfInvRing f)

/-- Degreewise restriction of scalars along `f⁻¹O' ⟶ O`, on unbounded cochain complexes.  This
is the functor of complexes whose induced functor on derived categories is
`derivedRestrictToInvRing`. -/
abbrev restrictComplexInvRing :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)) ℤ :=
  (restrictToInvRing f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The functor `D(O) ⥤ D(f⁻¹O')` induced by restriction of scalars along `f⁻¹O' ⟶ O`.**

Restriction of scalars is exact, so it carries quasi-isomorphisms of cochain complexes to
quasi-isomorphisms and the localization `D(O)` lifts it directly; see
`derivedRestrictToInvRing_obj_Q` for the resulting computation on a complex. -/
abbrev derivedRestrictToInvRing :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)) :=
  (restrictToInvRing f).mapDerivedCategory

/-- The factorization `Q ⋙ D(restriction) ≅ (degreewise restriction) ⋙ Q`: the derived functor
is computed by degreewise restriction of scalars on every complex, with no resolution. -/
abbrev derivedRestrictToInvRingFactors :
    DerivedCategory.Q ⋙ derivedRestrictToInvRing f ≅
      restrictComplexInvRing f ⋙ DerivedCategory.Q :=
  (restrictToInvRing f).mapDerivedCategoryFactors

/-- The derived functor carries the class of a cochain complex of `O`-modules to the class of
its degreewise restriction of scalars. -/
def derivedRestrictToInvRing_obj_Q
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedRestrictToInvRing f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((restrictComplexInvRing f).obj K) :=
  (derivedRestrictToInvRingFactors f).app K

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The computation of the derived functor on a complex is natural in that complex. -/
lemma derivedRestrictToInvRing_obj_Q_naturality
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : K ⟶ L) :
    (derivedRestrictToInvRing f).map (DerivedCategory.Q.map φ) ≫
        (derivedRestrictToInvRing_obj_Q f L).hom =
      (derivedRestrictToInvRing_obj_Q f K).hom ≫
        DerivedCategory.Q.map ((restrictComplexInvRing f).map φ) :=
  (restrictToInvRing f).mapDerivedCategoryFactors.hom.naturality φ

end Stacks.Cohomology.MixedDerivedTensor

end
