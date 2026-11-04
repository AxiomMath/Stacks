module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.CoefficientChangeTotalComplex

/-!
# The pullback of modules along a change of coefficient rings is extension of scalars

A map `α : O ⟶ O'` of sheaves of commutative rings on a site `(C, J)` presents a morphism of
ringed topoi `(Sh(J), O') ⟶ (Sh(J), O)` whose underlying continuous functor is the identity.
Its pushforward of sheaves of modules is restriction of scalars along `α` on the nose, so its
pullback and the extension of scalars `O' ⊗_O -` are two left adjoints of one functor and are
therefore isomorphic. This file records that isomorphism and the two consequences the derived
projection formula needs: the degreewise extension of scalars of a K-flat complex with flat
terms is K-flat, and the derived change of coefficients is computed on such a complex by that
degreewise extension.

## Main definitions

* `Stacks.Cohomology.CoefficientChange.pullbackToposIsoExtendScalars`: the pullback of sheaves
  of modules along a change of coefficient rings is extension of scalars.
* `Stacks.Cohomology.CoefficientChange.extendScalarsComplex`: degreewise extension of scalars
  on cochain complexes.
* `Stacks.Cohomology.CoefficientChange.derivedCoefficientChangeFlatIso`: **the derived change
  of coefficients at a K-flat complex with flat terms** is the class of its degreewise
  extension of scalars.

## Main results

* `Stacks.Cohomology.CoefficientChange.kFlat_extendScalarsComplex`: the degreewise extension of
  scalars of a K-flat complex of `O`-modules with flat terms is a K-flat complex of
  `O'`-modules.

## Implementation notes

Both consequences are instances of statements already in the tree about the pullback along a
morphism of ringed topoi — Stacks 0G7E as
`Stacks.Sheaves.DerivedPullback.kFlat_pullbackComplex'` and Stacks 06YY as
`Stacks.Sheaves.DerivedPullback.flatPullbackIso` — transported along the isomorphism of
functors above. The morphism-of-sites hypothesis both of them carry is discharged outright by
`CategoryTheory.Functor.isMorphismOfSites_id`, the underlying functor of a coefficient change
being the identity of the site.

Neither the additivity of the pullback of modules nor the additivity of its pushforward is
found by instance search at this spelling, although both are declared as instances: the search
does not see through the structure literal that a change of coefficient rings writes its source
and target ringed topoi as. `additive_pullbackTopos_coefficientChange` names the instance once
at that spelling, which is what lets the degreewise functor on cochain complexes be written
down at all.

`CochainComplex.KFlatBifunctor.KFlat.of_iso` is applied with its bifunctor and both complexes
passed explicitly. Left to the elaborator, the unification of the two spellings of the
complexes exhausts the heartbeat budget; named, the declaration elaborates in seconds.

## References

* [The Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [The Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [The Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.DerivedPullback Stacks.Sheaves.DerivedPullback.KFlatPullback

universe u

namespace Stacks.Cohomology.CoefficientChange

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O O' : Sheaf J CommRingCat.{u}}

/-- The pullback of sheaves of modules along a change of coefficient rings is additive. The
instance `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_additive` is not found by search
at this spelling, so it is named here. -/
instance additive_pullbackTopos_coefficientChange (α : O ⟶ O') :
    (RingedToposSiteHom.coefficientChange.{u, u, u} J α).pullbackTopos.Additive :=
  RingedToposSiteHom.pullbackTopos_additive _

/-- **The pullback of sheaves of modules along a change of coefficient rings is extension of
scalars.** The pushforward along a coefficient change is restriction of scalars along it, by
`Stacks.Cohomology.pushforwardTopos_toposHom`, and extension of scalars is the other left
adjoint of that functor, by `Stacks.FlatChangeOfRings.extendScalarsAdjunction`. -/
def pullbackToposIsoExtendScalars (α : O ⟶ O') :
    (RingedToposSiteHom.coefficientChange.{u, u, u} J α).pullbackTopos ≅
      Stacks.FlatChangeOfRings.extendScalars α :=
  Adjunction.leftAdjointUniq
    (RingedToposSiteHom.pullbackPushforwardAdjunctionTopos
      (RingedToposSiteHom.coefficientChange.{u, u, u} J α))
    (Stacks.FlatChangeOfRings.extendScalarsAdjunction α)

/-- Degreewise extension of scalars on cochain complexes of sheaves of modules. -/
abbrev extendScalarsComplex (α : O ⟶ O') :
    CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf O')) ℤ :=
  (Stacks.FlatChangeOfRings.extendScalars α).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The degreewise pullback along a change of coefficient rings is degreewise extension of
scalars. -/
def pullbackComplexIsoExtendScalars (α : O ⟶ O') :
    pullbackComplex (X := Stacks.Cohomology.ringedTopos J O')
        (Y := Stacks.Cohomology.ringedTopos J O)
        (RingedToposSiteHom.coefficientChange.{u, u, u} J α) ≅
      extendScalarsComplex α :=
  NatIso.mapHomologicalComplex (pullbackToposIsoExtendScalars α) (ComplexShape.up ℤ)

/-- **Stacks 0G7E at a change of coefficient rings**: the degreewise extension of scalars of a
K-flat complex of `O`-modules with flat terms is a K-flat complex of `O'`-modules. -/
theorem kFlat_extendScalarsComplex (α : O ⟶ O')
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O) P)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O) (P.X i)) :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O')
      ((extendScalarsComplex α).obj P) :=
  CochainComplex.KFlatBifunctor.KFlat.of_iso
    (F := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O')
    (K := (pullbackComplex (RingedToposSiteHom.coefficientChange.{u, u, u} J α)).obj P)
    (K' := (extendScalarsComplex α).obj P)
    (kFlat_pullbackComplex' (RingedToposSiteHom.coefficientChange.{u, u, u} J α)
      (Functor.isMorphismOfSites_id J) P hP hflat)
    ((pullbackComplexIsoExtendScalars α).app P)

/-- **Stacks 06YY at a change of coefficient rings**: the derived change of coefficients of the
class of a K-flat complex of `O`-modules with flat terms is the class of its degreewise
extension of scalars. -/
def derivedCoefficientChangeFlatIso (α : O ⟶ O')
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O) P)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O) (P.X i)) :
    (Stacks.Cohomology.derivedCoefficientChange α).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((extendScalarsComplex α).obj P) :=
  flatPullbackIso (RingedToposSiteHom.coefficientChange.{u, u, u} J α)
      (Functor.isMorphismOfSites_id J) P hP hflat ≪≫
    DerivedCategory.Q.mapIso ((pullbackComplexIsoExtendScalars α).app P)

end Stacks.Cohomology.CoefficientChange

end
