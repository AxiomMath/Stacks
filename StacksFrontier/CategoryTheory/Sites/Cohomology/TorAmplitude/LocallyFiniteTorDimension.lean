module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Locally finite Tor dimension on a ringed site

Let `(C, O)` be a ringed site. An object `E` of `D(O)` *locally has finite Tor dimension* if
every object `U` of `C` admits a covering on each member `V` of which the restriction `E|_V`
has finite Tor dimension on the localized ringed site `(C/V, O_V)`.

Restriction of sheaves of modules to a slice is exact, so it descends to derived categories;
the resulting functor is `AlgebraicGeometry.RingedSite.derivedRestriction`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedRestriction`: restriction to a slice of the site, on
  unbounded derived categories.
* `Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension`: finite Tor
  dimension after restriction to the members of a covering of every object.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_forall`: an object
  all of whose restrictions have finite Tor dimension locally has finite Tor dimension, by the
  maximal covering.

## Implementation notes

Finite Tor dimension on a slice is measured against a derived tensor product datum on that
slice, so the predicate takes a *family* `T : ∀ V, DerivedTensorProduct (X.over V)` rather than a
single datum. That is forced, not a convenience: `Stacks.SheafOfModules.DerivedTensorProduct` is
universe-polymorphic while the construction of an inhabitant of it is available only on a
diagonal, and `X.over V` has its objects in `Type (max u v)` even when `X` has them in `Type u`,
so no datum on `X` can measure Tor amplitude on a slice. Instantiating the family specialises
every consequence.

The covering is a `Presieve` together with the membership of the sieve it generates, which is the
shape the source's `{U_i → U}` takes elsewhere in this development (see
`AlgebraicGeometry.RingedSite.IsPerfectComplex` and
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally`); only members of the covering
family, not all of their precompositions, are required to have finite Tor dimension.

The hypotheses on the slices are stated as `∀ U : X.C, …` and re-seated as instances at the
`X.over U` spelling, because an instance proved at one spelling of a non-reducible definition
does not fire at the other even though the two types are equal by `rfl`. The one place where the
structure sheaf of a slice has to be reconciled with the slice of the structure sheaf is the
codomain of `derivedRestriction`, where it is pinned by a type ascription so the conversion is
checked once.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

-- The sections universe `w` is free, so Mathlib's size-restricted instances do not supply the
-- sheaf-condition composition that the module category of a ringed site is formed through.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Sheafification on a slice, at the spelling of the localized ringed site. -/
local instance sliceHasSheafify (U : X.C) : HasSheafify (X.over U).J AddCommGrpCat.{w} :=
  (inferInstance : ∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}) U

/-- Local bijectivity of the weak equivalences on a slice, at the localized spelling. -/
local instance sliceWEqualsLocallyBijective (U : X.C) :
    (X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  (inferInstance : ∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}) U

/-- Restriction to a slice preserves finite limits, by Stacks 04IX. -/
local instance sliceRestrictionPreservesFiniteLimits (U : X.C) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction to a slice preserves finite colimits, by Stacks 04IX. -/
local instance sliceRestrictionPreservesFiniteColimits (U : X.C) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, w} (X.over U))]

/-- The derived category of the modules on a slice, at the spelling in which the restriction
functor produces them: the modules over the slice of the structure sheaf. -/
local instance sliceHasDerivedCategory (U : X.C) :
    HasDerivedCategory.{d}
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over U)) :=
  hSliceDerived U

/-- Restriction of sheaves of modules to the slice of the site over `U`, as a functor on
unbounded derived categories. Restriction is exact, by Stacks 04IX, so it descends. -/
def derivedRestriction (U : X.C) :
    RingedSite.DerivedModules.{u, v, w, d} X ⥤
      RingedSite.DerivedModules.{max u v, v, w, d} (X.over U) :=
  (SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O) U).mapDerivedCategory

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, w} (X.over U))]

/-- The derived category of the modules on a slice, at the localized spelling. -/
local instance sliceDerived (U : X.C) :
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, w} (X.over U)) :=
  hSliceDerived U

variable
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max u v, v, w} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

/-- The tensor bifunctor of a slice is additive, at the localized spelling. -/
local instance sliceTensorAdditive (U : X.C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (X.over U).O).Additive :=
  (inferInstance : ∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (X.over U).O).Additive) U

/-- The tensor bifunctor of a slice is additive in its second variable. -/
local instance sliceTensorObjAdditive (U : X.C)
    (M : RingedSite.Modules.{max u v, v, w} (X.over U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w}
      (X.over U).O).obj M).Additive :=
  (inferInstance : ∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w}
      (X.over U).O).obj M).Additive) U M

/-- Total complexes of the tensor bifunctor of a slice exist. -/
local instance sliceHasMapBifunctor (U : X.C)
    (K L : CochainComplex (RingedSite.Modules.{max u v, v, w} (X.over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ) :=
  (inferInstance : ∀ (U : X.C) (K L : CochainComplex
      (RingedSite.Modules.{max u v, v, w} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)) U K L

/-- **Stacks 08FZ (3).** An object `E` of `D(O)` *locally has finite Tor dimension* if every
object `U` of `C` carries a covering family on each member `V` of which the restriction of `E` to
the localized ringed site has finite Tor dimension. Finite Tor dimension on the slice over `V`
is measured against the given derived tensor product `T V` on that slice. -/
@[stacks 08FZ "locally finite tor dimension"]
def LocallyHasFiniteTorDimension
    (T : ∀ U : X.C, DerivedTensorProduct.{max u v, v, w, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, v, w, d} X) : Prop :=
  ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
    ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      HasFiniteTorDimension (T V) ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj E)

/-- The covering-family criterion for locally finite Tor dimension, which is the definition. -/
theorem locallyHasFiniteTorDimension_iff
    (T : ∀ U : X.C, DerivedTensorProduct.{max u v, v, w, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, v, w, d} X) :
    LocallyHasFiniteTorDimension T E ↔
      ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
        ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
          HasFiniteTorDimension (T V)
            ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj E) :=
  Iff.rfl

/-- If every restriction of `E` to a slice has finite Tor dimension, then `E` locally has finite
Tor dimension, witnessed by the maximal covering of each object. -/
theorem locallyHasFiniteTorDimension_of_forall
    (T : ∀ U : X.C, DerivedTensorProduct.{max u v, v, w, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, v, w, d} X)
    (hres : ∀ V : X.C, HasFiniteTorDimension (T V)
      ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj E)) :
    LocallyHasFiniteTorDimension T E :=
  fun U => ⟨⊤, by simp, fun {V} _ _ => hres V⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end
