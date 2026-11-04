module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite presentations of étale module sheaves by extensions by zero

Let `U` be a scheme étale over `X`. Extension by zero along `U ⟶ X` carries the constant
sheaf with value the free rank-one module to a sheaf of modules on the small étale site of
`X`, and a *finite shriek presentation* of a sheaf of modules on `X` is an identification of
it with the cokernel of a map between finite direct sums of such sheaves. On a quasi-compact
and quasi-separated scheme these are exactly the constructible sheaves of modules over a
Noetherian ring (Stacks Project, Tag 095N); this file sets up the notion itself.

Sheafification of module-valued presheaves on the small étale site is not automatic: the
forgetful functor must preserve filtered colimits indexed by the site, whose objects and
morphisms both live in `Type (u + 1)`. So the module universe is taken to be
`max (u + 1) r w`, large enough for the site and for the ring, and
`AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat` builds the sheafification there.

## Main definitions

* `AlgebraicGeometry.moduleShriekConstant` — the extension by zero from an étale object of the
  constant free rank-one module sheaf.
* `AlgebraicGeometry.HasFiniteShriekPresentation` — a finite cokernel presentation by such
  sheaves, whose étale objects satisfy a prescribed property.

## Main results

* `AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat` — module-valued presheaves on a small
  étale site have sheafification in a universe containing both the site and the ring.

## Implementation notes

The rank-one module is `ULift R`, lifted into the common module universe. The natural
isomorphism in a presentation identifies the underlying presheaf of the cokernel with the
pointwise universe lift of the given sheaf, which lets the site, the ring and the module
universe of the presented sheaf vary independently instead of forcing extra existence
hypotheses on the presentation.

## References

* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

universe u r w

namespace AlgebraicGeometry

/-- Presheaves of `R`-modules on a small étale site have sheafification, provided the module
universe contains both the universe of the site and that of the ring.

The standard filtered-colimit instance for modules ties the module universe to the ring
universe, so the required instance is assembled through abelian groups and then its diagram
size is shrunk to that of the small étale site. -/
public theorem SmallEtale.hasSheafify_moduleCat (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) [Ring R] :
    HasSheafify (SmallEtale.topology B X.1 X.property)
      (ModuleCat.{max (u + 1) r w} R) := by
  let : PreservesColimits
      (forget₂ (ModuleCat.{max (u + 1) r w} R) AddCommGrpCat) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r w, r,
      max (u + 1) r w, max (u + 1) r w} R
  let : PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) r w} R)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{max (u + 1) r w} R) AddCommGrpCat) (forget AddCommGrpCat)
  let : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget (ModuleCat.{max (u + 1) r w} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, max r w, u + 1, max r w} _
  infer_instance

/-- The extension by zero, from an étale object `U` of `X`, of the constant sheaf with value
the free rank-one `R`-module. -/
public abbrev moduleShriekConstant (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) [Ring R] (U : SmallEtale B X.1 X.property) :
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r w} R) := by
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, w} B X R
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, w} B U.obj.left R
  exact (Functor.sheafPullbackConstruction.sheafPullback
    (smallEtalePostcompose B X.1 X.property U)
    (ModuleCat.{max (u + 1) r w} R)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X.1 X.property)).obj
      ((constantSheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (ModuleCat.{max (u + 1) r w} R)).obj
          (ModuleCat.of R (ULift.{max (u + 1) w} R)))

/-- A presentation of `F` as the cokernel of a map between finite direct sums of extensions by
zero of constant free rank-one module sheaves, all of whose étale objects satisfy `P`. The
isomorphism identifies the underlying presheaf of the cokernel with the pointwise universe
lift of `F`. -/
public def HasFiniteShriekPresentation (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) [Ring R]
    (P : SmallEtale B X.1 X.property → Prop)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{w} R)) : Prop := by
  let := SmallEtale.hasSheafify_moduleCat.{u, r, w} B X R
  exact ∃ (n m : ℕ) (U : Fin n → SmallEtale B X.1 X.property)
    (V : Fin m → SmallEtale B X.1 X.property),
    (∀ i, P (U i)) ∧ (∀ j, P (V j)) ∧
      ∃ (f : (∐ fun j ↦ moduleShriekConstant.{u, r, w} B X R (V j)) ⟶
          (∐ fun i ↦ moduleShriekConstant.{u, r, w} B X R (U i))),
        Nonempty ((cokernel f).obj ≅ F.obj ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} R)

end AlgebraicGeometry

end
