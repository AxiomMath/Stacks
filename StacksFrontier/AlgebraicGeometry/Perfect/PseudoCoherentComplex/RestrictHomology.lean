module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Restricting the cohomology of a complex to an open

The two shapes of restriction to an open `U` of a scheme `X` —
`AlgebraicGeometry.RingedSpace.restrictModules`, which lands in modules on the restricted ringed
space and is the one in which [Stacks, Tag 08CM] states perfectness, and
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which lands in
modules on the open subscheme and is the one the scheme-level theory uses — are isomorphic.
Restriction is exact, so it commutes with the cohomology of a complex; combining the two facts
turns a strictly perfect model of a complex over `U` into a description of the restriction to
`U` of its cohomology modules.

## Main definitions

* `Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict`:
  `AlgebraicGeometry.RingedSpace.restrictModules X U ≅
  AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`.
* `Stacks.AlgebraicGeometry.PerfectCohomology.mapHomologyIso`: an exact functor commutes with
  the cohomology of a cochain complex.
* `Stacks.AlgebraicGeometry.PerfectCohomology.strictModelHomologyIso`: a quasi-isomorphism from
  a complex `P` to the restriction of `E` to `U` identifies the cohomology of `P` with the
  restriction to `U` of the cohomology of `E`.
* `Stacks.AlgebraicGeometry.PerfectCohomology.derivedHomologyRestrictIso`: the same, for an
  object of the derived category represented by `E`.

## Main results

* `Stacks.AlgebraicGeometry.PerfectCohomology.isZero_stalk_of_isZero`: a zero module has zero
  stalks.
* `Stacks.AlgebraicGeometry.PerfectCohomology.notMem_supp_of_isZero_restrictModules`: a point of
  `U` is outside the support of a module whose restriction to `U` vanishes.

## Implementation notes

`restrictModulesIsoRestrict` is immediate:
`AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp` factors
`AlgebraicGeometry.RingedSpace.restrictModules` through `SheafOfModules.overFunctor` and
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` factors
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` through the same functor, both through the
*same* equivalence `TopologicalSpace.Opens.sheafOfModulesEquivOver`.

`mapHomologyIso` duplicates a private definition of
`StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory`; de-privatising that one and
deleting this is the dedup owed.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SheafOfModules

universe u v v' u' d

namespace Stacks.AlgebraicGeometry.PerfectCohomology

/-! ### The two restrictions agree -/

/-- **Restriction to an open subspace and restriction to an open subscheme agree.** Both
`AlgebraicGeometry.RingedSpace.restrictModules` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` factor
`SheafOfModules.overFunctor` through `TopologicalSpace.Opens.sheafOfModulesEquivOver`. -/
noncomputable def restrictModulesIsoRestrict (X : Scheme.{u}) (U : X.Opens) :
    RingedSpace.restrictModules X.toRingedSpace U ≅ Scheme.Modules.restrictFunctor U.ι :=
  (RingedSpace.restrictModulesIsoOverComp X.toRingedSpace U).symm ≪≫
    Scheme.Modules.overFunctorEquiv U

/-- **A zero module has zero stalks.** The forgetful functor to presheaves of abelian groups
and the stalk functor are both additive. -/
theorem isZero_stalk_of_isZero {Y : Scheme.{u}} (N : Y.Modules) (hN : IsZero N) (p : Y) :
    IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf p) := by
  have hpres : (Scheme.Modules.toPresheaf Y).PreservesZeroMorphisms := by
    show (SheafOfModules.forget _ ⋙
      PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).PreservesZeroMorphisms
    infer_instance
  have := Functor.preservesZeroMorphisms_of_additive
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p)
  exact Functor.map_isZero (Scheme.Modules.toPresheaf Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p) hN

/-- A point of `U` at which a module vanishes after restriction to `U` is outside the support of
the module: the stalk there is the stalk of the restriction. -/
theorem notMem_supp_of_isZero_restrictModules (X : Scheme.{u}) (U : X.Opens)
    (M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)
    (hM : IsZero ((RingedSpace.restrictModules X.toRingedSpace U).obj M))
    (x : X) (hx : x ∈ U) : x ∉ SheafOfModules.supp M := by
  have hres : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj M) :=
    hM.of_iso ((restrictModulesIsoRestrict X U).app M).symm
  have hglobal : IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x) :=
    (isZero_stalk_of_isZero ((Scheme.Modules.restrictFunctor U.ι).obj M) hres ⟨x, hx⟩).of_iso
      ((Scheme.Modules.restrictStalkNatIso U.ι ⟨x, hx⟩).app M).symm
  intro hsupp
  obtain ⟨a, ha⟩ := hsupp
  exact ha ((AddCommGrpCat.isZero_iff_subsingleton.mp hglobal).elim a 0)

/-! ### Exact functors and the cohomology of a complex -/

/-- **An exact functor commutes with the cohomology of a cochain complex.** -/
noncomputable def mapHomologyIso {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'}
    [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (K : CochainComplex C ℤ) (i : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i ≅ F.obj (K.homology i) :=
  (K.sc i).mapHomologyIso F

/-! ### The cohomology of a strictly perfect model -/

/-- **A quasi-isomorphism onto the restriction of `E` to `U` computes the restriction to `U` of
the cohomology of `E`.** -/
noncomputable def strictModelHomologyIso (X : Scheme.{u}) (U : X.Opens)
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) ℤ}
    {P : CochainComplex
      (StrictlyPerfect.OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) ℤ}
    (q : P ⟶ RingedSpace.restrictComplex E U) (hq : QuasiIso q) (n : ℤ) :
    P.homology n ≅ (RingedSpace.restrictModules X.toRingedSpace U).obj (E.homology n) :=
  have : PreservesFiniteLimits (RingedSpace.restrictModules X.toRingedSpace U) :=
    RingedSpace.restrictModules_preservesFiniteLimits X.toRingedSpace U
  have : PreservesFiniteColimits (RingedSpace.restrictModules X.toRingedSpace U) :=
    RingedSpace.restrictModules_preservesFiniteColimits X.toRingedSpace U
  have : IsIso (HomologicalComplex.homologyMap q n) :=
    (quasiIsoAt_iff_isIso_homologyMap q n).mp (hq.quasiIsoAt n)
  asIso (HomologicalComplex.homologyMap q n) ≪≫
    mapHomologyIso (RingedSpace.restrictModules X.toRingedSpace U) E n

/-- **The same, for an object of the derived category represented by `E`.** -/
noncomputable def derivedHomologyRestrictIso (X : Scheme.{u})
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)] (U : X.Opens)
    {K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)}
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) ℤ}
    (eEK : DerivedCategory.Q.obj E ≅ K)
    {P : CochainComplex
      (StrictlyPerfect.OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) ℤ}
    (q : P ⟶ RingedSpace.restrictComplex E U) (hq : QuasiIso q) (n : ℤ) :
    P.homology n ≅ (RingedSpace.restrictModules X.toRingedSpace U).obj
      ((DerivedCategory.homologyFunctor
        (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) n).obj K) :=
  strictModelHomologyIso X U q hq n ≪≫
    (RingedSpace.restrictModules X.toRingedSpace U).mapIso
      ((DerivedCategory.homologyFunctorFactors
        (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) n).app E).symm ≪≫
    (RingedSpace.restrictModules X.toRingedSpace U).mapIso
      ((DerivedCategory.homologyFunctor
        (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) n).mapIso eEK)

end Stacks.AlgebraicGeometry.PerfectCohomology

end
