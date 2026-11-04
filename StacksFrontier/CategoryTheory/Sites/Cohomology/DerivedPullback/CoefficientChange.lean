module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Modules.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.Identity
import StacksCore.Tactic.StacksAttribute

/-!
# The derived change of coefficient rings on a fixed site

Let `α : O ⟶ O'` be a map of sheaves of commutative rings on a site `(C, J)`. Change of
coefficients along `α` is a morphism of ringed topoi `(Sh(J), O') ⟶ (Sh(J), O)` whose underlying
morphism of sites is the identity, so the derived pullback of Stacks 06YY applies to it and
gives an exact functor `D(O) ⥤ D(O')`. On a K-flat complex of `O`-modules with flat terms it is
degreewise extension of scalars, that is `- ⊗_O O'`.

## Main definitions

* `Stacks.Cohomology.derivedCoefficientChange`: the functor `D(O) ⥤ D(O')`.

## Main results

* `Stacks.Cohomology.hasLeftDerivedFunctor_pullbackOnHomotopy_coefficientChange`: the derived
  pullback along a change of coefficient rings exists, so the functor is defined on all of
  `D(O)`.

## Implementation notes

The construction is the derived pullback along
`AlgebraicGeometry.RingedToposSiteHom.coefficientChange`, whose existence hypothesis is
discharged by `CategoryTheory.Functor.isMorphismOfSites_id`: the derived pullback exists along
every morphism of ringed topoi, and the identity functor of a site is a morphism of sites. The
hypothesis is recorded as an instance so that the derived pullback and all of its API are
available at a coefficient change without further arguments.

The universes collapse to one. That is forced by the derived pullback of ringed topoi, which is
stated for `AlgebraicGeometry.RingedTopos` with its site, its hom types and the sections of its
structure sheaf in a single universe; the derived-category hom universe is likewise the one
supplied by `HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The ringed topos on a fixed site with a given sheaf of commutative rings as its structure
sheaf. -/
abbrev ringedTopos (J : GrothendieckTopology C) (O : Sheaf J CommRingCat.{u}) :
    RingedTopos.{u, u, u} :=
  { C := C, J := J, O := O }

variable {O O' : Sheaf J CommRingCat.{u}}

/-- **The derived pullback along a change of coefficient rings exists.** The derived pullback
exists along every morphism of ringed topoi, and the identity functor of a site, which is the
morphism of sites underlying a coefficient change, is a morphism of sites. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_coefficientChange (α : O ⟶ O') :
    (pullbackOnHomotopy
        (RingedToposSiteHom.coefficientChange.{u, u, u} J α)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos J O).O))
        (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposSiteHom.coefficientChange.{u, u, u} J α) (Functor.isMorphismOfSites_id J)

/-- **The derived change of coefficient rings** `D(O) ⥤ D(O')` attached to a map `α : O ⟶ O'` of
sheaves of commutative rings on a fixed site, the derived pullback along the morphism of ringed
topoi that `α` presents. -/
abbrev derivedCoefficientChange (α : O ⟶ O') :
    DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos J O).O)) ⥤
      DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos J O').O)) :=
  derivedPullback (RingedToposSiteHom.coefficientChange.{u, u, u} J α)

/-- The canonical comparison of the derived change of coefficient rings with degreewise
extension of scalars. The underlying morphism of sites being the identity, which is a morphism
of sites by `CategoryTheory.Functor.isMorphismOfSites_id`, it is invertible on every K-flat
complex of `O`-modules with flat terms. -/
abbrev derivedCoefficientChangeComparison (α : O ⟶ O') :
    DerivedCategory.Qh ⋙ derivedCoefficientChange α ⟶
      pullbackOnHomotopy (RingedToposSiteHom.coefficientChange.{u, u, u} J α) :=
  derivedPullbackComparison (RingedToposSiteHom.coefficientChange.{u, u, u} J α)

end Stacks.Cohomology

end
